//! Tree document.

use std::borrow::Cow;

use crate::node::{
    ArrBranchNodeRef, ArrLeafNodeRef, KeyType, MapBranchNodeRef, MapLeafNodeRef, NodeHeaderRef,
    NodeKind, map_slot,
};
use crate::trailer::Trailer;
use crate::value::ValueType;

/// Parsed tree document containing HAMT/vector trie nodes.
#[derive(Debug, PartialEq)]
pub struct TreeDocument<'a> {
    data: Cow<'a, [u8]>,
    pub root_offset: u32,
    pub prev_root_offset: u32,
}

impl<'a> TreeDocument<'a> {
    /// Parse a tree document from raw bytes.
    pub fn new(data: &'a [u8]) -> Option<Self> {
        // minimum length: 8 (smallest node) + 12 (trailer) = 20 bytes
        if data.len() < 20 {
            return None;
        }

        // parse trailer from last 12 bytes
        let trailer_data: &[u8; 12] = data[data.len() - 12..].try_into().ok()?;
        let trailer = Trailer::new(trailer_data)?;

        // validate root offset is within bounds
        if trailer.root_node_offset as usize >= data.len() - 12 {
            return None;
        }

        Some(Self {
            data: Cow::Borrowed(data),
            root_offset: trailer.root_node_offset,
            prev_root_offset: trailer.prev_root_node_offset,
        })
    }

    /// Get the root node's type (Arr or Map).
    pub fn root_type(&self) -> Option<KeyType> {
        let header = NodeHeaderRef::new(&self.data[self.root_offset as usize..])?;
        Some(header.key_type())
    }

    /// HAMT map lookup: get value by key from a map at given offset.
    pub fn map_get(&'a self, offset: u32, key: &str) -> Option<ValueType<'a>> {
        self.map_get_recursive(offset, key, 0)
    }

    fn map_get_recursive(&'a self, offset: u32, key: &str, depth: u8) -> Option<ValueType<'a>> {
        let node_data = self.data.get(offset as usize..)?;
        let header = NodeHeaderRef::new(node_data)?;

        match header.kind() {
            NodeKind::Leaf => {
                let leaf = MapLeafNodeRef::new(node_data)?;
                leaf.get(key)
            }
            NodeKind::Branch => {
                let branch = MapBranchNodeRef::new(node_data)?;
                let slot = map_slot(key, depth);
                let bitmap = branch.bitmap()?;

                // check if slot is present
                if (bitmap >> slot) & 1 == 0 {
                    return None;
                }

                // find child index via popcount
                let child_idx = (bitmap & ((1 << slot) - 1)).count_ones() as usize;
                let child_offset = branch.child_offset(child_idx)?;

                self.map_get_recursive(child_offset, key, depth + 1)
            }
        }
    }

    /// Vector trie array lookup: get value by index from an array at given offset.
    pub fn arr_get(&'a self, offset: u32, index: u32) -> Option<ValueType<'a>> {
        let node_data = self.data.get(offset as usize..)?;
        let header = NodeHeaderRef::new(node_data)?;

        match header.kind() {
            NodeKind::Leaf => {
                let leaf = ArrLeafNodeRef::new(node_data)?;
                let slot = (index & 0xF) as u8;
                let bitmap = leaf.bitmap()?;

                // check if slot is present
                if (bitmap >> slot) & 1 == 0 {
                    return None;
                }

                // find entry index via popcount
                let entry_idx = (bitmap & ((1 << slot) - 1)).count_ones() as usize;
                leaf.value_at(entry_idx)
            }
            NodeKind::Branch => {
                let branch = ArrBranchNodeRef::new(node_data)?;
                let shift = branch.shift();
                let slot = ((index >> shift) & 0xF) as u8;
                let bitmap = branch.bitmap()?;

                // check if slot is present
                if (bitmap >> slot) & 1 == 0 {
                    return None;
                }

                // find child index via popcount
                let child_idx = (bitmap & ((1 << slot) - 1)).count_ones() as usize;
                let child_offset = branch.child_offset(child_idx)?;

                self.arr_get(child_offset, index)
            }
        }
    }

    /// Get array length from root node at given offset.
    pub fn arr_len(&self, offset: u32) -> Option<u32> {
        let node_data = self.data.get(offset as usize..)?;
        let header = NodeHeaderRef::new(node_data)?;

        match header.kind() {
            NodeKind::Leaf => ArrLeafNodeRef::new(node_data)?.length(),
            NodeKind::Branch => ArrBranchNodeRef::new(node_data)?.length(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper to build simple tree document with map leaf root
    fn make_map_leaf_doc(entries: &[(&str, &[u8])]) -> Vec<u8> {
        let mut buf = Vec::new();

        // build leaf node entries
        let mut entries_buf = Vec::new();
        for (key, value) in entries {
            // txt key: packed if <= 15 chars
            let key_bytes = key.as_bytes();
            if key_bytes.len() <= 15 {
                entries_buf.push((0x0C | key_bytes.len() << 4) as u8);
                entries_buf.extend_from_slice(key_bytes);
            } else {
                if key_bytes.len() >= 256 {
                    panic!("")
                }
                entries_buf.push(0x04);
                entries_buf.push(key_bytes.len() as u8);
                entries_buf.extend_from_slice(key_bytes);
            }
            // value bytes
            entries_buf.extend_from_slice(value);
        }

        // calculate node length: must be multiple of 4
        let content_len = 8 + entries_buf.len(); // header + entries
        let padding = (4 - (content_len % 4)) % 4;
        let node_len = content_len + padding;

        // node header: leaf=1, map=1 -> 0x03 in low bits
        let header_u32 = (node_len as u32) | 0x03;
        buf.extend_from_slice(&header_u32.to_le_bytes());
        buf.extend_from_slice(&(entries.len() as u32).to_le_bytes());
        buf.extend_from_slice(&entries_buf);
        buf.extend(std::iter::repeat_n(0, padding));

        let root_offset = 0u32;

        // trailer
        buf.extend_from_slice(&root_offset.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes()); // prev_root
        buf.extend_from_slice(b"TRON");

        buf
    }

    /// Helper to build simple tree document with array leaf root
    fn make_arr_leaf_doc(values: &[&[u8]]) -> Vec<u8> {
        let mut buf = Vec::new();

        // build leaf node values
        let mut values_buf = Vec::new();
        let mut bitmap: u16 = 0;
        for (i, value) in values.iter().enumerate() {
            bitmap |= 1 << i;
            values_buf.extend_from_slice(value);
        }

        // calculate node length: must be multiple of 4
        // header (8) + shift(1) + reserved(1) + bitmap(2) + length(4) + values
        let content_len = 8 + 8 + values_buf.len();
        let padding = (4 - (content_len % 4)) % 4;
        let node_len = content_len + padding;

        // node header: leaf=1, arr=0 -> 0x01 in low bits
        let header_u32 = (node_len as u32) | 0x01;
        buf.extend_from_slice(&header_u32.to_le_bytes());
        buf.extend_from_slice(&(values.len() as u32).to_le_bytes());

        // array-specific fields: shift, reserved, bitmap, length
        buf.push(0); // shift = 0 (leaf)
        buf.push(0);
        buf.extend_from_slice(&bitmap.to_le_bytes());
        buf.extend_from_slice(&(values.len() as u32).to_le_bytes());

        buf.extend_from_slice(&values_buf);
        buf.extend(std::iter::repeat_n(0, padding));

        let root_offset = 0u32;

        // trailer
        buf.extend_from_slice(&root_offset.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes()); // prev_root
        buf.extend_from_slice(b"TRON");

        buf
    }

    // Basic parsing tests
    #[test]
    fn parse_map_root() {
        let i64_42 = [0x40, 0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        let data = make_map_leaf_doc(&[("a", &i64_42)]);
        let doc = TreeDocument::new(&data).unwrap();
        assert_eq!(doc.root_offset, 0);
        assert_eq!(doc.root_type(), Some(KeyType::Map));
    }

    #[test]
    fn parse_arr_root() {
        let nil = [0x00];
        let data = make_arr_leaf_doc(&[&nil, &nil]);
        let doc = TreeDocument::new(&data).unwrap();
        assert_eq!(doc.root_offset, 0);
        assert_eq!(doc.root_type(), Some(KeyType::Arr));
    }

    #[test]
    fn rejects_too_short() {
        let data = [0u8; 19]; // less than 20 bytes
        assert_eq!(TreeDocument::new(&data), None);
    }

    #[test]
    fn rejects_wrong_magic() {
        let mut data = make_map_leaf_doc(&[]);
        // corrupt magic
        let len = data.len();
        data[len - 4..].copy_from_slice(b"NORT");
        assert_eq!(TreeDocument::new(&data), None);
    }

    #[test]
    fn rejects_invalid_root_offset() {
        let mut data = make_map_leaf_doc(&[]);
        // root offset beyond document
        let len = data.len();
        data[len - 12..len - 8].copy_from_slice(&0xFFFFFFFFu32.to_le_bytes());
        assert_eq!(TreeDocument::new(&data), None);
    }

    // Map operations
    #[test]
    fn map_get_single_leaf() {
        let i64_42 = [0x02, 0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        let i64_99 = [0x02, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        let data = make_map_leaf_doc(&[("a", &i64_42), ("b", &i64_99)]);
        let doc = TreeDocument::new(&data).unwrap();

        assert_eq!(doc.map_get(doc.root_offset, "a"), Some(ValueType::I64(42)));
        assert_eq!(doc.map_get(doc.root_offset, "b"), Some(ValueType::I64(99)));
        assert_eq!(doc.map_get(doc.root_offset, "c"), None);
    }

    #[test]
    fn map_get_missing_key() {
        let nil = [0x00];
        let data = make_map_leaf_doc(&[("exists", &nil)]);
        let doc = TreeDocument::new(&data).unwrap();

        assert_eq!(doc.map_get(doc.root_offset, "exists"), Some(ValueType::Nil));
        assert_eq!(doc.map_get(doc.root_offset, "missing"), None);
    }

    // Array operations
    #[test]
    fn arr_get_single_leaf() {
        let i64_42 = [0x02, 0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        let i64_99 = [0x02, 0x63, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        let data = make_arr_leaf_doc(&[&i64_42, &i64_99]);
        let doc = TreeDocument::new(&data).unwrap();

        assert_eq!(doc.arr_get(doc.root_offset, 0), Some(ValueType::I64(42)));
        assert_eq!(doc.arr_get(doc.root_offset, 1), Some(ValueType::I64(99)));
    }

    #[test]
    fn arr_get_out_of_bounds() {
        let nil = [0x00];
        let data = make_arr_leaf_doc(&[&nil, &nil]);
        let doc = TreeDocument::new(&data).unwrap();

        assert_eq!(doc.arr_get(doc.root_offset, 0), Some(ValueType::Nil));
        assert_eq!(doc.arr_get(doc.root_offset, 1), Some(ValueType::Nil));
        assert_eq!(doc.arr_get(doc.root_offset, 2), None); // out of bounds
    }

    #[test]
    fn arr_len_single_leaf() {
        let nil = [0x00];
        let data = make_arr_leaf_doc(&[&nil, &nil, &nil]);
        let doc = TreeDocument::new(&data).unwrap();

        assert_eq!(doc.arr_len(doc.root_offset), Some(3));
    }

    // Nested structures
    #[test]
    fn nested_map() {
        // Build document: {"outer": {"inner": 42}}
        // inner map at offset 0
        let i64_42 = [0x02, 0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
        let mut buf = Vec::new();

        // inner map leaf: {"inner": 42}
        let inner_entries: Vec<u8> = {
            let mut e = Vec::new();
            e.push(0x5C); // txt "inner" packed len=5
            e.extend_from_slice(b"inner");
            e.extend_from_slice(&i64_42);
            e
        };
        let inner_content_len = 8 + inner_entries.len();
        let inner_padding = (4 - (inner_content_len % 4)) % 4;
        let inner_node_len = inner_content_len + inner_padding;
        let inner_header = (inner_node_len as u32) | 0x03; // leaf + map
        buf.extend_from_slice(&inner_header.to_le_bytes());
        buf.extend_from_slice(&1u32.to_le_bytes()); // entry_count
        buf.extend_from_slice(&inner_entries);
        buf.extend(std::iter::repeat_n(0, inner_padding));

        let outer_offset = buf.len() as u32;

        // outer map leaf: {"outer": map@0}
        let outer_entries: Vec<u8> = {
            let mut e = Vec::new();
            e.push(0x5C); // txt "outer" packed len=5
            e.extend_from_slice(b"outer");
            e.push(0x07); // map packed 1 byte offset
            e.push(0x00); // offset 0
            e
        };
        let outer_content_len = 8 + outer_entries.len();
        let outer_padding = (4 - (outer_content_len % 4)) % 4;
        let outer_node_len = outer_content_len + outer_padding;
        let outer_header = (outer_node_len as u32) | 0x03; // leaf + map
        buf.extend_from_slice(&outer_header.to_le_bytes());
        buf.extend_from_slice(&1u32.to_le_bytes()); // entry_count
        buf.extend_from_slice(&outer_entries);
        buf.extend(std::iter::repeat_n(0, outer_padding));

        // trailer
        buf.extend_from_slice(&outer_offset.to_le_bytes());
        buf.extend_from_slice(&0u32.to_le_bytes());
        buf.extend_from_slice(b"TRON");

        let doc = TreeDocument::new(&buf).unwrap();
        assert_eq!(doc.root_type(), Some(KeyType::Map));

        // get outer.outer -> Map(0)
        let outer_value = doc.map_get(doc.root_offset, "outer").unwrap();
        assert_eq!(outer_value, ValueType::Map(0));

        // get inner.inner -> 42
        if let ValueType::Map(inner_offset) = outer_value {
            assert_eq!(doc.map_get(inner_offset, "inner"), Some(ValueType::I64(42)));
        } else {
            panic!("expected Map");
        }
    }
}
