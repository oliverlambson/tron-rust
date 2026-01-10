#[derive(Debug, PartialEq)]
pub struct ArrRootValue<'a> {
    pub(crate) is_branch: bool,
    pub(crate) node_len: u32,
    pub(crate) shift: u8,
    pub(crate) bitmap: u16,
    pub(crate) length: u32,
    pub(crate) entries_buffer: &'a [u8],
}
impl<'a> ArrRootValue<'a> {
    pub fn entries(&self) -> impl Iterator<Item = u32> + '_ {
        to_u32_iterator(self.entries_buffer)
    }

    /// Get the length of the array.
    pub fn len(&self) -> u32 {
        self.length
    }

    /// Check if the array is empty.
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }
}
#[derive(Debug, PartialEq)]
pub struct ArrChildValue<'a> {
    pub(crate) is_branch: bool,
    pub(crate) node_len: u32,
    pub(crate) shift: u8,
    pub(crate) bitmap: u16,
    pub(crate) entries_buffer: &'a [u8],
}
impl<'a> ArrChildValue<'a> {
    pub fn entries(&self) -> impl Iterator<Item = u32> + '_ {
        to_u32_iterator(self.entries_buffer)
    }
}
fn to_u32_iterator(bytes: &[u8]) -> impl Iterator<Item = u32> + '_ {
    bytes
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
}
#[derive(Debug, PartialEq)]
pub enum ArrValue<'a> {
    Root(ArrRootValue<'a>),
    Child(ArrChildValue<'a>),
}
#[derive(Debug, PartialEq)]
pub struct MapBranchValue<'a> {
    pub(crate) node_len: u32,
    pub(crate) bitmap: u32,
    pub(crate) entries_buffer: &'a [u8],
}
impl<'a> MapBranchValue<'a> {
    pub fn entries(&self) -> impl Iterator<Item = u32> + '_ {
        to_u32_iterator(self.entries_buffer)
    }
}
#[derive(Debug, PartialEq)]
pub struct MapLeafValue<'a> {
    pub(crate) node_len: u32,
    pub(crate) entries_buffer: &'a [u8],
}
impl<'a> MapLeafValue<'a> {
    pub fn pairs(&self) -> impl Iterator<Item = (u32, u32)> + '_ {
        self.entries_buffer.chunks_exact(8).map(|c| {
            (
                u32::from_le_bytes([c[0], c[1], c[2], c[3]]),
                u32::from_le_bytes([c[4], c[5], c[6], c[7]]),
            )
        })
    }
}
#[derive(Debug, PartialEq)]
pub enum MapValue<'a> {
    Branch(MapBranchValue<'a>),
    Leaf(MapLeafValue<'a>),
}
#[derive(Debug, PartialEq)]
pub enum ValueNode<'a> {
    // For small primitive values (bool, i64, f64, u32), we copy them into Rust
    // types rather than storing references into the byte array. This is more
    // faster to access and actually memory-efficient (a reference is 8+ bytes).
    Nil,
    Bit(bool),
    I64(i64),
    F64(f64),
    Txt(&'a str),
    Bin(&'a [u8]),
    Arr(ArrValue<'a>),
    Map(MapValue<'a>),
}

impl<'a> ValueNode<'a> {
    pub fn new(data: &'a [u8]) -> Option<Self> {
        let tag_header = data.first()?;
        match tag_header & 0b00000111 {
            // nil
            0b000 => {
                // high bits must be 0
                (tag_header & 0b11111000 == 0).then_some(ValueNode::Nil)
            }
            // bit
            0b001 => {
                // high bits excl. last must be 0
                (tag_header & 0b11110000 == 0)
                    .then_some(ValueNode::Bit(tag_header & 0b00001000 == 0b00001000))
            }
            // i64
            0b010 => Some(ValueNode::I64(i64::from_le_bytes(
                data.get(1..9)?.try_into().ok()?,
            ))),
            // f64
            0b011 => Some(ValueNode::F64(f64::from_le_bytes(
                data.get(1..9)?.try_into().ok()?,
            ))),
            // txt - utf8 encoded string
            0b100 => {
                let (l, offset) = Self::decode_length(data)?;
                Some(ValueNode::Txt(
                    std::str::from_utf8(data.get(offset..offset + l)?).ok()?,
                ))
            }
            // bin - raw bytes
            0b101 => {
                let (l, offset) = Self::decode_length(data)?;
                Some(ValueNode::Bin(data.get(offset..offset + l)?))
            }
            // arr - root node offset (1-4 bytes, little-endian)
            0b110 => {
                let is_root = ((tag_header >> 6) & 0b1) == 0b0;
                let m = ((tag_header >> 4) & 0b11) as usize;
                let n = m + 1;
                let is_branch = ((tag_header >> 3) & 0b1) == 0b0;

                let mut i: usize = 1;
                let mut node_len_buf = [0u8; 4];
                node_len_buf[..n].copy_from_slice(data.get(i..i + n)?);
                let node_len = u32::from_le_bytes(node_len_buf);
                i += n;
                let shift = *data.get(i)?;
                i += 1;
                let bitmap = u16::from_le_bytes(data.get(i..i + 2)?.try_into().ok()?);
                i += 2;

                if is_root {
                    let length = u32::from_le_bytes(data.get(i..i + 4)?.try_into().ok()?);
                    i += 4;
                    let entries_buffer = data.get(i..)?;

                    Some(ValueNode::Arr(ArrValue::Root(ArrRootValue {
                        is_branch,
                        node_len,
                        shift,
                        bitmap,
                        length,
                        entries_buffer,
                    })))
                } else {
                    let entries_buffer = data.get(i..)?;

                    Some(ValueNode::Arr(ArrValue::Child(ArrChildValue {
                        is_branch,
                        node_len,
                        shift,
                        bitmap,
                        entries_buffer,
                    })))
                }
            }
            // map - root node offset (1-4 bytes, little-endian)
            0b111 => {
                let m = ((tag_header >> 4) & 0b11) as usize;
                let n = m + 1;
                let is_branch = ((tag_header >> 3) & 0b1) == 0b0;

                let mut i: usize = 1;
                let mut node_len_buf = [0u8; 4];
                node_len_buf[..n].copy_from_slice(data.get(i..i + n)?);
                let node_len = u32::from_le_bytes(node_len_buf);
                i += n;

                if is_branch {
                    let bitmap = u32::from_le_bytes(data.get(i..i + 4)?.try_into().ok()?);
                    i += 4;
                    let entries_buffer = data.get(i..)?;
                    Some(ValueNode::Map(MapValue::Branch(MapBranchValue {
                        node_len,
                        bitmap,
                        entries_buffer,
                    })))
                } else {
                    let entries_buffer = data.get(i..)?;
                    Some(ValueNode::Map(MapValue::Leaf(MapLeafValue {
                        node_len,
                        entries_buffer,
                    })))
                }
            }
            _ => unreachable!(),
        }
    }

    /// Returns (length, offset) for variable-length types
    fn decode_length(data: &[u8]) -> Option<(usize, usize)> {
        let first_byte = data.first()?;
        let l = (first_byte >> 4) as usize;
        let is_packed = first_byte & 0b00001000 == 0b00001000;
        if is_packed {
            Some((l, 1))
        } else {
            let n = l;
            let bytes = data.get(1..1 + n)?;
            let mut buf = [0u8; 8];
            buf[..n].copy_from_slice(bytes);
            let length = usize::from_le_bytes(buf);
            Some((length, 1 + n))
        }
    }

    /// Returns total byte length of value record (tag + payload)
    pub fn byte_len(data: &[u8]) -> Option<usize> {
        match data.first()? & 0b111 {
            0 | 1 => Some(1), // nil, bit: just tag
            2 | 3 => Some(9), // i64, f64: tag + 8 bytes
            4 | 5 => {
                // txt, bin
                let (length, offset) = Self::decode_length(data)?;
                Some(offset + length) // tag + (offset - 1) + length
            }
            6 | 7 => {
                //  arr, map
                let m = ((data.first()? >> 4) & 0b11) as usize;
                let l = 1 + m;
                Some(1 + l) // tag + L bytes
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
        let data = [
            0x00, // tag: nil (000)
        ];
        assert_eq!(ValueNode::new(&data), Some(ValueNode::Nil));
        assert_eq!(ValueNode::byte_len(&data), Some(1));
    }

    #[test]
    fn parse_bit_false() {
        let data = [
            0x01, // tag: bit (001); bool=true
        ];
        assert_eq!(ValueNode::new(&data), Some(ValueNode::Bit(false)));
        assert_eq!(ValueNode::byte_len(&data), Some(1));
    }

    #[test]
    fn parse_bit_true() {
        let data = [
            0x09, // tag: bit (001); bool=true
        ];
        assert_eq!(ValueNode::new(&data), Some(ValueNode::Bit(true)));
        assert_eq!(ValueNode::byte_len(&data), Some(1));
    }

    #[test]
    fn parse_i64() {
        let data = [
            0x02, // tag: i64 (010)
            0xD2, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // payload: 1234
        ];
        assert_eq!(ValueNode::new(&data), Some(ValueNode::I64(1234)));
        assert_eq!(ValueNode::byte_len(&data), Some(9));
    }

    #[test]
    fn parse_f64() {
        let data = [
            0x03, // tag: f64 (011)
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xF8, 0x3F, // payload: 1.5
        ];
        assert_eq!(ValueNode::new(&data), Some(ValueNode::F64(1.5)));
        assert_eq!(ValueNode::byte_len(&data), Some(9));
    }

    #[test]
    fn parse_txt_packed() {
        let data = [
            0x2C, // tag: 1x1, packed, L=2
            0x68, 0x69, // payload: "hi"
        ];
        assert_eq!(ValueNode::new(&data), Some(ValueNode::Txt("hi")));
        assert_eq!(ValueNode::byte_len(&data), Some(3));
    }

    #[test]
    fn parse_txt_unpacked() {
        // "0123456789abcdef" (16 chars, can't fit in packed 0-15)
        let data = [
            0x14, // tag: txt (100), unpacked (0), N=1 byte for length
            0x10, // length: 16
            // payload
            0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, // "0123456789"
            0x61, 0x62, 0x63, 0x64, 0x65, 0x66, // "abcdef"
        ];
        assert_eq!(
            ValueNode::new(&data),
            Some(ValueNode::Txt("0123456789abcdef"))
        );
        assert_eq!(ValueNode::byte_len(&data), Some(18)); // 1 tag + 1 len + 16 payload
    }

    #[test]
    fn parse_bin_packed() {
        let data = [
            0x3D, // tag: bin (101), packed (1), L=3 byte for length
            0xAA, 0xBB, 0xCC, // payload
        ];
        assert_eq!(
            ValueNode::new(&data),
            Some(ValueNode::Bin(&[0xAA, 0xBB, 0xCC]))
        );
        assert_eq!(ValueNode::byte_len(&data), Some(4));
    }

    #[test]
    fn parse_bin_unpacked() {
        // 16 bytes (can't fit in packed 0-15)
        let data = [
            0x15, // tag: bin (101), unpacked (0), N=1 byte for length
            0x10, // length: 16
            // payload
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D,
            0x0E, 0x0F,
        ];
        assert_eq!(
            ValueNode::new(&data),
            Some(ValueNode::Bin(&[
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D,
                0x0E, 0x0F,
            ]))
        );
        assert_eq!(ValueNode::byte_len(&data), Some(18)); // 1 tag + 1 len + 16 payload
    }

    #[test]
    fn parse_arr() {
        // leaf root arr with one value node at address 0x10
        let data = [
            0x0E, // type=arr; B=1=leaf; M=0 (0b00_00_1_110)
            0x0D, // node_len=13
            0x00, // shift=0
            0x01, 0x00, // bitmap=0b1 (slots 0)
            0x01, 0x00, 0x00, 0x00, // length=1
            0x10, 0x00, 0x00, 0x00, // entry[0] address = @0x10
        ];
        assert_eq!(
            ValueNode::new(&data),
            Some(ValueNode::Arr(ArrValue::Root(ArrRootValue {
                is_branch: false,
                node_len: 13,
                shift: 0,
                bitmap: 1,
                length: 1,
                entries_buffer: &data[9..],
            })))
        );
        assert_eq!(ValueNode::byte_len(&data), Some(2));
    }

    #[test]
    fn parse_map() {
        // leaf map with key node at 0x20 and value node at 0x30:
        let data = [
            0x0F, // type=map; B=1=leaf; M=0 (0b00_00_1_111)
            0x0A, // node_len=10
            0x20, 0x00, 0x00, 0x00, // entry[0].key address   = @0x20
            0x30, 0x00, 0x00, 0x00, // entry[0].value address = @0x30
        ];
        assert_eq!(
            ValueNode::new(&data),
            Some(ValueNode::Map(MapValue::Leaf(MapLeafValue {
                node_len: 10,
                entries_buffer: &data[2..],
            })))
        );
        assert_eq!(ValueNode::byte_len(&data), Some(2));
    }

    mod fixtures {
        use super::*;
        use serde::Deserialize;

        fn hex_to_bytes(hex: &str) -> Vec<u8> {
            (0..hex.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).unwrap())
                .collect()
        }

        #[derive(Deserialize)]
        struct Fixtures {
            nil: Vec<NilFixture>,
            bit: Vec<BitFixture>,
            i64: Vec<I64Fixture>,
            f64: Vec<F64Fixture>,
            txt: Vec<TxtFixture>,
            bin: Vec<BinFixture>,
            arr: Vec<ArrFixture>,
            map: Vec<MapFixture>,
        }

        #[derive(Deserialize)]
        struct NilFixture {
            bytes: String,
        }

        #[derive(Deserialize)]
        struct BitFixture {
            bytes: String,
            parsed: BitParsed,
        }
        #[derive(Deserialize)]
        struct BitParsed {
            value: bool,
        }

        #[derive(Deserialize)]
        struct I64Fixture {
            bytes: String,
            parsed: I64Parsed,
        }
        #[derive(Deserialize)]
        struct I64Parsed {
            value: i64,
        }

        #[derive(Deserialize)]
        struct F64Fixture {
            bytes: String,
            parsed: F64Parsed,
        }
        #[derive(Deserialize)]
        struct F64Parsed {
            value: f64,
        }

        #[derive(Deserialize)]
        struct TxtFixture {
            bytes: String,
            parsed: TxtParsed,
        }
        #[derive(Deserialize)]
        struct TxtParsed {
            value: String,
        }

        #[derive(Deserialize)]
        struct BinFixture {
            bytes: String,
            parsed: BinParsed,
        }
        #[derive(Deserialize)]
        struct BinParsed {
            value: String, // hex-encoded
        }

        #[derive(Deserialize)]
        struct ArrFixture {
            bytes: String,
            parsed: ArrParsed,
        }
        #[derive(Deserialize)]
        struct ArrParsed {
            is_root: bool,
            is_branch: bool,
            node_len: u32,
            shift: u8,
            bitmap: u16,
            length: Option<u32>,
            entries: Vec<u32>,
        }

        #[derive(Deserialize)]
        struct MapFixture {
            bytes: String,
            parsed: MapParsed,
        }
        #[derive(Deserialize)]
        struct MapParsed {
            is_branch: bool,
            node_len: u32,
            bitmap: Option<u32>,
            entries: serde_json::Value, // can be array of u32 or array of {key, value}
        }

        fn load_fixtures() -> Fixtures {
            let path = concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../../tron-shared/shared/testdata/tron/value_nodes.json"
            );
            let content = std::fs::read_to_string(path).expect("failed to read fixtures");
            serde_json::from_str(&content).expect("failed to parse fixtures")
        }

        #[test]
        fn test_nil_fixtures() {
            let fixtures = load_fixtures();
            for fixture in &fixtures.nil {
                let bytes = hex_to_bytes(&fixture.bytes);
                let parsed = ValueNode::new(&bytes);
                assert_eq!(parsed, Some(ValueNode::Nil), "bytes: {}", fixture.bytes);
            }
        }

        #[test]
        fn test_bit_fixtures() {
            let fixtures = load_fixtures();
            for fixture in &fixtures.bit {
                let bytes = hex_to_bytes(&fixture.bytes);
                let parsed = ValueNode::new(&bytes);
                assert_eq!(
                    parsed,
                    Some(ValueNode::Bit(fixture.parsed.value)),
                    "bytes: {}",
                    fixture.bytes
                );
            }
        }

        #[test]
        fn test_i64_fixtures() {
            let fixtures = load_fixtures();
            for fixture in &fixtures.i64 {
                let bytes = hex_to_bytes(&fixture.bytes);
                let parsed = ValueNode::new(&bytes);
                assert_eq!(
                    parsed,
                    Some(ValueNode::I64(fixture.parsed.value)),
                    "bytes: {}",
                    fixture.bytes
                );
            }
        }

        #[test]
        fn test_f64_fixtures() {
            let fixtures = load_fixtures();
            for fixture in &fixtures.f64 {
                let bytes = hex_to_bytes(&fixture.bytes);
                let parsed = ValueNode::new(&bytes);
                assert_eq!(
                    parsed,
                    Some(ValueNode::F64(fixture.parsed.value)),
                    "bytes: {}",
                    fixture.bytes
                );
            }
        }

        #[test]
        fn test_txt_fixtures() {
            let fixtures = load_fixtures();
            for fixture in &fixtures.txt {
                let bytes = hex_to_bytes(&fixture.bytes);
                let parsed = ValueNode::new(&bytes);
                assert_eq!(
                    parsed,
                    Some(ValueNode::Txt(&fixture.parsed.value)),
                    "bytes: {}",
                    fixture.bytes
                );
            }
        }

        #[test]
        fn test_bin_fixtures() {
            let fixtures = load_fixtures();
            for fixture in &fixtures.bin {
                let bytes = hex_to_bytes(&fixture.bytes);
                let expected_bin = hex_to_bytes(&fixture.parsed.value);
                let parsed = ValueNode::new(&bytes);
                assert_eq!(
                    parsed,
                    Some(ValueNode::Bin(&expected_bin)),
                    "bytes: {}",
                    fixture.bytes
                );
            }
        }

        #[test]
        fn test_arr_fixtures() {
            let fixtures = load_fixtures();
            for fixture in &fixtures.arr {
                let bytes = hex_to_bytes(&fixture.bytes);
                let parsed = ValueNode::new(&bytes);
                let p = &fixture.parsed;

                match parsed {
                    Some(ValueNode::Arr(arr)) => match arr {
                        ArrValue::Root(root) => {
                            assert!(p.is_root, "expected root, bytes: {}", fixture.bytes);
                            assert_eq!(root.is_branch, p.is_branch, "bytes: {}", fixture.bytes);
                            assert_eq!(root.node_len, p.node_len, "bytes: {}", fixture.bytes);
                            assert_eq!(root.shift, p.shift, "bytes: {}", fixture.bytes);
                            assert_eq!(root.bitmap, p.bitmap, "bytes: {}", fixture.bytes);
                            assert_eq!(
                                root.length,
                                p.length.expect("root should have length"),
                                "bytes: {}",
                                fixture.bytes
                            );
                            let entries: Vec<u32> = root.entries().collect();
                            assert_eq!(entries, p.entries, "bytes: {}", fixture.bytes);
                        }
                        ArrValue::Child(child) => {
                            assert!(!p.is_root, "expected child, bytes: {}", fixture.bytes);
                            assert_eq!(child.is_branch, p.is_branch, "bytes: {}", fixture.bytes);
                            assert_eq!(child.node_len, p.node_len, "bytes: {}", fixture.bytes);
                            assert_eq!(child.shift, p.shift, "bytes: {}", fixture.bytes);
                            assert_eq!(child.bitmap, p.bitmap, "bytes: {}", fixture.bytes);
                            let entries: Vec<u32> = child.entries().collect();
                            assert_eq!(entries, p.entries, "bytes: {}", fixture.bytes);
                        }
                    },
                    other => panic!("expected Arr, got {:?}, bytes: {}", other, fixture.bytes),
                }
            }
        }

        #[test]
        fn test_map_fixtures() {
            let fixtures = load_fixtures();
            for fixture in &fixtures.map {
                let bytes = hex_to_bytes(&fixture.bytes);
                let parsed = ValueNode::new(&bytes);
                let p = &fixture.parsed;

                match parsed {
                    Some(ValueNode::Map(map)) => {
                        if p.is_branch {
                            match map {
                                MapValue::Branch(branch) => {
                                    assert_eq!(
                                        branch.node_len, p.node_len,
                                        "bytes: {}",
                                        fixture.bytes
                                    );
                                    assert_eq!(
                                        branch.bitmap,
                                        p.bitmap.expect("branch should have bitmap"),
                                        "bytes: {}",
                                        fixture.bytes
                                    );
                                    let entries: Vec<u32> = branch
                                        .entries_buffer
                                        .chunks_exact(4)
                                        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
                                        .collect();
                                    let expected: Vec<u32> = p
                                        .entries
                                        .as_array()
                                        .unwrap()
                                        .iter()
                                        .map(|v| v.as_u64().unwrap() as u32)
                                        .collect();
                                    assert_eq!(entries, expected, "bytes: {}", fixture.bytes);
                                }
                                MapValue::Leaf(_) => {
                                    panic!("expected branch, got leaf, bytes: {}", fixture.bytes)
                                }
                            }
                        } else {
                            match map {
                                MapValue::Leaf(leaf) => {
                                    assert_eq!(
                                        leaf.node_len, p.node_len,
                                        "bytes: {}",
                                        fixture.bytes
                                    );
                                    let pairs: Vec<(u32, u32)> = leaf.pairs().collect();
                                    let expected: Vec<(u32, u32)> = p
                                        .entries
                                        .as_array()
                                        .unwrap()
                                        .iter()
                                        .map(|v| {
                                            let obj = v.as_object().unwrap();
                                            (
                                                obj["key"].as_u64().unwrap() as u32,
                                                obj["value"].as_u64().unwrap() as u32,
                                            )
                                        })
                                        .collect();
                                    assert_eq!(pairs, expected, "bytes: {}", fixture.bytes);
                                }
                                MapValue::Branch(_) => {
                                    panic!("expected leaf, got branch, bytes: {}", fixture.bytes)
                                }
                            }
                        }
                    }
                    other => panic!("expected Map, got {:?}, bytes: {}", other, fixture.bytes),
                }
            }
        }
    }
}
