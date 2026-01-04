//! Document.

pub const TREE_MAGIC: &[u8; 4] = b"TRON";
pub const SCALAR_MAGIC: &[u8; 4] = b"NORT";

#[derive(Debug, PartialEq)]
pub enum DocumentType {
    Scalar,
    Tree,
}

/// Detect document type by checking the last 4 bytes.
pub fn doc_type(tail: &[u8; 4]) -> Option<DocumentType> {
    match tail {
        TREE_MAGIC => Some(DocumentType::Tree),
        SCALAR_MAGIC => Some(DocumentType::Scalar),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detect_tree_document() {
        assert_eq!(doc_type(b"TRON"), Some(DocumentType::Tree));
    }

    #[test]
    fn detect_scalar_document() {
        assert_eq!(doc_type(b"NORT"), Some(DocumentType::Scalar));
    }

    #[test]
    fn detect_invalid_document() {
        assert_eq!(doc_type(b"\0\0\0\0"), None);
    }
}
