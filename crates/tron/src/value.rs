#[derive(Debug, PartialEq)]
pub enum ValueType<'a> {
    Nil,
    Bit(bool),
    I64(i64),
    F64(f64),
    Txt(&'a str),
    Bin(&'a [u8]),
    Arr(u32),
    Map(u32),
}

impl<'a> ValueType<'a> {
    pub fn new(data: &'a [u8]) -> Option<Self> {
        let first_byte = data.first()?;
        match first_byte >> 5 {
            // nil
            0 => {
                // low bits must be 0
                (first_byte & 0b00011111 == 0).then_some(ValueType::Nil)
            }
            // bit
            1 => {
                // low bits excl. last must be 0
                (first_byte & 0b00011110 == 0).then_some(ValueType::Bit(first_byte & 1 == 1))
            }
            // i64
            2 => Some(ValueType::I64(i64::from_le_bytes(
                data.get(1..9)?.try_into().ok()?,
            ))),
            // f64
            3 => Some(ValueType::F64(f64::from_le_bytes(
                data.get(1..9)?.try_into().ok()?,
            ))),
            // txt - utf8 encoded string
            4 => {
                let (length, offset) = Self::decode_length(data)?;
                Some(ValueType::Txt(
                    std::str::from_utf8(data.get(offset..offset + length)?).ok()?,
                ))
            }
            // bin - raw bytes
            5 => {
                let (length, offset) = Self::decode_length(data)?;
                Some(ValueType::Bin(data.get(offset..offset + length)?))
            }
            // arr - root node offset (1-4 bytes, little-endian)
            6 => {
                let (length, offset) = Self::decode_length(data)?;
                let bytes = data.get(offset..offset + length)?;
                let mut buf = [0u8; 4];
                buf[..length].copy_from_slice(bytes);
                Some(ValueType::Arr(u32::from_le_bytes(buf)))
            }
            // map - root node offset (1-4 bytes, little-endian)
            7 => {
                let (length, offset) = Self::decode_length(data)?;
                let bytes = data.get(offset..offset + length)?;
                let mut buf = [0u8; 4];
                buf[..length].copy_from_slice(bytes);
                Some(ValueType::Map(u32::from_le_bytes(buf)))
            }
            _ => unreachable!(),
        }
    }

    /// Returns (length, offset) for variable-length types
    fn decode_length(data: &[u8]) -> Option<(usize, usize)> {
        let first_byte = data.first()?;
        let is_packed = first_byte & 0b00010000 != 0;
        if is_packed {
            Some(((first_byte & 0b00001111) as usize, 1))
        } else {
            let n = (first_byte & 0b00001111) as usize;
            let bytes = data.get(1..1 + n)?;
            let mut buf = [0u8; 8];
            buf[..n].copy_from_slice(bytes);
            let length = usize::from_le_bytes(buf);
            Some((length, 1 + n))
        }
    }

    /// Returns total byte length of value record (tag + payload)
    pub fn byte_len(data: &[u8]) -> Option<usize> {
        match data.first()? >> 5 {
            0 | 1 => Some(1), // nil, bit: just tag
            2 | 3 => Some(9), // i64, f64: tag + 8 bytes
            4..=7 => {
                // txt, bin, arr, map
                let (length, offset) = Self::decode_length(data)?;
                Some(offset + length)
            }
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_nil() {
        let data = [0x00];
        assert_eq!(ValueType::new(&data), Some(ValueType::Nil));
        assert_eq!(ValueType::byte_len(&data), Some(1));
    }

    #[test]
    fn parse_bit_false() {
        let data = [0x20];
        assert_eq!(ValueType::new(&data), Some(ValueType::Bit(false)));
        assert_eq!(ValueType::byte_len(&data), Some(1));
    }

    #[test]
    fn parse_bit_true() {
        let data = [0x21];
        assert_eq!(ValueType::new(&data), Some(ValueType::Bit(true)));
        assert_eq!(ValueType::byte_len(&data), Some(1));
    }

    #[test]
    fn parse_i64() {
        let data = [0x40, 0xD2, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        assert_eq!(ValueType::new(&data), Some(ValueType::I64(1234)));
        assert_eq!(ValueType::byte_len(&data), Some(9));
    }

    #[test]
    fn parse_f64() {
        let data = [0x60, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xF8, 0x3F];
        assert_eq!(ValueType::new(&data), Some(ValueType::F64(1.5)));
        assert_eq!(ValueType::byte_len(&data), Some(9));
    }

    #[test]
    fn parse_txt_packed() {
        let data = [0x92, 0x68, 0x69]; // "hi"
        assert_eq!(ValueType::new(&data), Some(ValueType::Txt("hi")));
        assert_eq!(ValueType::byte_len(&data), Some(3));
    }

    #[test]
    fn parse_txt_unpacked() {
        // "0123456789abcdef" (16 chars, can't fit in packed 0-15)
        let data = [
            0x81, // tag: txt (100), unpacked (0), N=1 byte for length
            0x10, // length: 16
            // payload
            0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, // "0123456789"
            0x61, 0x62, 0x63, 0x64, 0x65, 0x66, // "abcdef"
        ];
        assert_eq!(
            ValueType::new(&data),
            Some(ValueType::Txt("0123456789abcdef"))
        );
        assert_eq!(ValueType::byte_len(&data), Some(18)); // 1 tag + 1 len + 16 payload
    }

    #[test]
    fn parse_bin_packed() {
        let data = [0xB3, 0xAA, 0xBB, 0xCC];
        assert_eq!(
            ValueType::new(&data),
            Some(ValueType::Bin(&[0xAA, 0xBB, 0xCC]))
        );
        assert_eq!(ValueType::byte_len(&data), Some(4));
    }

    #[test]
    fn parse_bin_unpacked() {
        // 16 bytes (can't fit in packed 0-15)
        let data = [
            0xA1, // tag: bin (101), unpacked (0), N=1 byte for length
            0x10, // length: 16
            // payload
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D,
            0x0E, 0x0F,
        ];
        assert_eq!(
            ValueType::new(&data),
            Some(ValueType::Bin(&[
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D,
                0x0E, 0x0F,
            ]))
        );
        assert_eq!(ValueType::byte_len(&data), Some(18)); // 1 tag + 1 len + 16 payload
    }

    #[test]
    fn parse_arr_packed() {
        let data = [0xD1, 0x10]; // offset 0x10
        assert_eq!(ValueType::new(&data), Some(ValueType::Arr(0x10)));
        assert_eq!(ValueType::byte_len(&data), Some(2));
    }

    #[test]
    fn parse_arr_unpacked() {
        // offset 0x12345678 (needs 4 bytes, can't fit in packed llll=1-15)
        let data = [
            0xC1, // tag: arr (110), unpacked (0), N=1 byte for L
            0x04, // L: 4 bytes for offset
            0x78, 0x56, 0x34, 0x12, // offset: 0x12345678 (little-endian)
        ];
        assert_eq!(ValueType::new(&data), Some(ValueType::Arr(0x12345678)));
        assert_eq!(ValueType::byte_len(&data), Some(6)); // 1 tag + 1 L + 4 offset
    }

    #[test]
    fn parse_map_packed() {
        let data = [0xF1, 0x20]; // offset 0x20
        assert_eq!(ValueType::new(&data), Some(ValueType::Map(0x20)));
        assert_eq!(ValueType::byte_len(&data), Some(2));
    }

    #[test]
    fn parse_map_unpacked() {
        // offset 0x12345678 (needs 4 bytes, can't fit in packed llll=1-15)
        let data = [
            0xE1, // tag: map (111), unpacked (0), N=1 byte for L
            0x04, // L: 4 bytes for offset
            0x78, 0x56, 0x34, 0x12, // offset: 0x12345678 (little-endian)
        ];
        assert_eq!(ValueType::new(&data), Some(ValueType::Map(0x12345678)));
        assert_eq!(ValueType::byte_len(&data), Some(6)); // 1 tag + 1 L + 4 offset
    }
}
