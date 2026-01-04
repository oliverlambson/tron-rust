//! Trailer.

use crate::document::TREE_MAGIC;

/// Tree document trailer (12 bytes).
#[derive(Debug, PartialEq)]
pub struct Trailer {
    pub root_node_offset: u32,
    pub prev_root_node_offset: u32,
}
impl Trailer {
    pub fn new(data: &[u8; 12]) -> Option<Self> {
        if data.get(8..12)? != TREE_MAGIC {
            return None;
        }
        Some(Self {
            root_node_offset: u32::from_le_bytes(data.get(0..4)?.try_into().ok()?),
            prev_root_node_offset: u32::from_le_bytes(data.get(4..8)?.try_into().ok()?),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_tree_trailer() {
        let data: [u8; 12] = [
            0x20, 0x00, 0x00, 0x00, // root_node_offset: 0x20
            0x10, 0x00, 0x00, 0x00, // prev_root_node_offset: 0x10
            b'T', b'R', b'O', b'N', // magic: TRON
        ];
        let trailer = Trailer::new(&data).unwrap();
        assert_eq!(trailer.root_node_offset, 0x20);
        assert_eq!(trailer.prev_root_node_offset, 0x10);
    }

    #[test]
    fn parse_trailer_rejects_non_tree() {
        let data: [u8; 12] = [0; 12];
        assert_eq!(Trailer::new(&data), None);
    }
}
