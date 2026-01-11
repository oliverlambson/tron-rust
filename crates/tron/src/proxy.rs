//! High-level ergonomic API for reading & writing TRON documents.

use std::fmt;

use crate::document::Tron;
use crate::value::{ArrValue, ValueNode};
use crate::{arr, map};

/// Error type for TronProxy operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProxyError {
    NotAMap,
    NotAnArray,
    KeyNotFound {
        key: String,
    },
    IndexOutOfBounds {
        index: u32,
        length: u32,
    },
    InvalidNode {
        address: u32,
    },
    TypeMismatch {
        expected: &'static str,
        actual: &'static str,
    },
}

impl fmt::Display for ProxyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProxyError::NotAMap => write!(f, "value is not a map"),
            ProxyError::NotAnArray => write!(f, "value is not an array"),
            ProxyError::KeyNotFound { key } => write!(f, "key not found: {}", key),
            ProxyError::IndexOutOfBounds { index, length } => {
                write!(
                    f,
                    "index {} out of bounds for array of length {}",
                    index, length
                )
            }
            ProxyError::InvalidNode { address } => write!(f, "invalid node at address {}", address),
            ProxyError::TypeMismatch { expected, actual } => {
                write!(f, "type mismatch: expected {}, got {}", expected, actual)
            }
        }
    }
}

impl std::error::Error for ProxyError {}

/// A high-level proxy into a TRON document node.
///
/// Provides ergonomic navigation and value extraction without requiring
/// knowledge of TRON internals.
///
/// # Example
///
/// ```ignore
/// let doc = Tron::from_bytes(&data)?;
/// let proxy = TronProxy::from_doc(&doc);
///
/// // Method chaining
/// let name = proxy.get("users")?.index(0)?.get("name")?.as_str()?;
///
/// // Path-based access
/// let elevation = proxy.get_path(&["features", "0", "properties", "elevation"])?;
///
/// // Type coercion
/// let count = proxy.get("count")?.as_i64()?;
/// let flag = proxy.get("enabled")?.as_bool()?;
/// ```
#[derive(Debug, Copy, Clone)]
pub struct TronProxy<'a> {
    buffer: &'a [u8],
    node: ValueNode<'a>,
    node_addr: u32,
    arr_length: Option<u32>,
}

impl<'a> TronProxy<'a> {
    /// Create a proxy from a TRON document.
    pub fn from_doc(doc: &'a Tron<'a>) -> Self {
        let arr_length = match doc.root() {
            ValueNode::Arr(ArrValue::Root(root)) => Some(root.length),
            _ => None,
        };
        TronProxy {
            buffer: doc.buffer(),
            node: *doc.root(),
            node_addr: doc.root_addr(),
            arr_length,
        }
    }

    /// Create a proxy from raw buffer and root info.
    ///
    /// Used internally by TronMut to create proxys of the current state.
    pub fn from_raw(buffer: &'a [u8], root_addr: u32, arr_length: Option<u32>) -> Option<Self> {
        let node_bytes = buffer.get(root_addr as usize..)?;
        let node = ValueNode::new(node_bytes)?;
        Some(TronProxy {
            buffer,
            node,
            node_addr: root_addr,
            arr_length,
        })
    }

    /// Get a map entry by key.
    pub fn get(&self, key: &str) -> Result<TronProxy<'a>, ProxyError> {
        match &self.node {
            ValueNode::Map(_) => {
                let (node, addr) =
                    map::map_get(self.buffer, self.node_addr, key).ok_or_else(|| {
                        ProxyError::KeyNotFound {
                            key: key.to_string(),
                        }
                    })?;

                let arr_length = match &node {
                    ValueNode::Arr(ArrValue::Root(root)) => Some(root.length),
                    _ => None,
                };

                Ok(TronProxy {
                    buffer: self.buffer,
                    node,
                    node_addr: addr,
                    arr_length,
                })
            }
            _ => Err(ProxyError::NotAMap),
        }
    }

    /// Get an array element by index.
    pub fn index(&self, idx: u32) -> Result<TronProxy<'a>, ProxyError> {
        match &self.node {
            ValueNode::Arr(_) => {
                let length = self.arr_length.ok_or(ProxyError::NotAnArray)?;

                if idx >= length {
                    return Err(ProxyError::IndexOutOfBounds { index: idx, length });
                }

                let (node, addr) = arr::arr_get(self.buffer, self.node_addr, idx, length).ok_or(
                    ProxyError::InvalidNode {
                        address: self.node_addr,
                    },
                )?;

                let arr_length = match &node {
                    ValueNode::Arr(ArrValue::Root(root)) => Some(root.length),
                    _ => None,
                };

                Ok(TronProxy {
                    buffer: self.buffer,
                    node,
                    node_addr: addr,
                    arr_length,
                })
            }
            _ => Err(ProxyError::NotAnArray),
        }
    }

    /// Navigate to a nested value using a path.
    ///
    /// Path segments that parse as u32 are treated as array indices,
    /// otherwise they are treated as map keys.
    pub fn get_path(&self, path: &[&str]) -> Result<TronProxy<'a>, ProxyError> {
        let mut current = *self;

        for segment in path {
            current = if let Ok(idx) = segment.parse::<u32>() {
                current.index(idx)?
            } else {
                current.get(segment)?
            };
        }

        Ok(current)
    }

    /// Extract a string value.
    pub fn as_str(&self) -> Result<&'a str, ProxyError> {
        match &self.node {
            ValueNode::Txt(s) => Ok(*s),
            _ => Err(ProxyError::TypeMismatch {
                expected: "txt",
                actual: self.value_type(),
            }),
        }
    }

    /// Extract an i64 value.
    pub fn as_i64(&self) -> Result<i64, ProxyError> {
        match &self.node {
            ValueNode::I64(n) => Ok(*n),
            _ => Err(ProxyError::TypeMismatch {
                expected: "i64",
                actual: self.value_type(),
            }),
        }
    }

    /// Extract an f64 value.
    pub fn as_f64(&self) -> Result<f64, ProxyError> {
        match &self.node {
            ValueNode::F64(n) => Ok(*n),
            _ => Err(ProxyError::TypeMismatch {
                expected: "f64",
                actual: self.value_type(),
            }),
        }
    }

    /// Extract a bool value.
    pub fn as_bool(&self) -> Result<bool, ProxyError> {
        match &self.node {
            ValueNode::Bit(b) => Ok(*b),
            _ => Err(ProxyError::TypeMismatch {
                expected: "bit",
                actual: self.value_type(),
            }),
        }
    }

    /// Extract bytes.
    pub fn as_bytes(&self) -> Result<&'a [u8], ProxyError> {
        match &self.node {
            ValueNode::Bin(b) => Ok(*b),
            _ => Err(ProxyError::TypeMismatch {
                expected: "bin",
                actual: self.value_type(),
            }),
        }
    }

    /// Check if value is nil.
    pub fn is_nil(&self) -> bool {
        matches!(&self.node, ValueNode::Nil)
    }

    /// Get the type name of the current value.
    pub fn value_type(&self) -> &'static str {
        match &self.node {
            ValueNode::Nil => "nil",
            ValueNode::Bit(_) => "bit",
            ValueNode::I64(_) => "i64",
            ValueNode::F64(_) => "f64",
            ValueNode::Txt(_) => "txt",
            ValueNode::Bin(_) => "bin",
            ValueNode::Arr(_) => "arr",
            ValueNode::Map(_) => "map",
        }
    }

    /// Check if value is a map.
    pub fn is_map(&self) -> bool {
        matches!(&self.node, ValueNode::Map(_))
    }

    /// Check if value is an array.
    pub fn is_array(&self) -> bool {
        matches!(&self.node, ValueNode::Arr(_))
    }

    /// Get the underlying node (for advanced use).
    pub fn node(&self) -> &ValueNode<'a> {
        &self.node
    }
}

// ============================================================================
// Mutable API
// ============================================================================

/// Error type for TronMut operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MutError {
    NotAMap,
    NotAnArray,
    KeyNotFound { key: String },
    IndexOutOfBounds { index: u32, length: u32 },
    InvalidNode { address: u32 },
}

impl fmt::Display for MutError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MutError::NotAMap => write!(f, "value is not a map"),
            MutError::NotAnArray => write!(f, "value is not an array"),
            MutError::KeyNotFound { key } => write!(f, "key not found: {}", key),
            MutError::IndexOutOfBounds { index, length } => {
                write!(
                    f,
                    "index {} out of bounds for array of length {}",
                    index, length
                )
            }
            MutError::InvalidNode { address } => {
                write!(f, "invalid node at address 0x{:x}", address)
            }
        }
    }
}

impl std::error::Error for MutError {}

/// Trait for values that can be encoded into TRON format.
pub trait IntoValue {
    fn into_value(self) -> crate::encode::Value<'static>;
}

impl IntoValue for () {
    fn into_value(self) -> crate::encode::Value<'static> {
        crate::encode::Value::Nil
    }
}

impl IntoValue for bool {
    fn into_value(self) -> crate::encode::Value<'static> {
        crate::encode::Value::Bit(self)
    }
}

impl IntoValue for i64 {
    fn into_value(self) -> crate::encode::Value<'static> {
        crate::encode::Value::I64(self)
    }
}

impl IntoValue for f64 {
    fn into_value(self) -> crate::encode::Value<'static> {
        crate::encode::Value::F64(self)
    }
}

impl IntoValue for &'static str {
    fn into_value(self) -> crate::encode::Value<'static> {
        crate::encode::Value::Txt(self)
    }
}

impl IntoValue for &'static [u8] {
    fn into_value(self) -> crate::encode::Value<'static> {
        crate::encode::Value::Bin(self)
    }
}

/// A mutable TRON document that supports in-place modifications.
///
/// Uses copy-on-write semantics internally: mutations append new nodes
/// to the buffer and update the root address. Old roots remain valid.
///
/// # Example
///
/// ```ignore
/// let mut doc = TronMut::from_bytes(&data)?;
///
/// // Direct mutations
/// doc.set("name", "Alice")?;
/// doc.delete("old_field")?;
///
/// // Path-based mutations
/// doc.set_path(&["users", "0", "name"], "Bob")?;
///
/// // Chained navigation
/// doc.cursor().get("users")?.index(0)?.set_key("name", "Charlie")?;
///
/// // Read current state
/// let proxy = doc.proxy()?;
/// let name = proxy.get("name")?.as_str()?;
///
/// // Export
/// let bytes = doc.into_bytes();
/// ```
#[derive(Debug)]
pub struct TronMut {
    buffer: Vec<u8>,
    root_addr: u32,
    arr_length: Option<u32>,
    prev_root: u32, // Previous root address (for footer)
}

impl TronMut {
    /// Create from existing TRON bytes (makes owned copy).
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let footer_start = bytes.len().checked_sub(12)?;
        let footer_bytes = bytes.get(footer_start..)?;
        let root_addr = u32::from_le_bytes(footer_bytes[0..4].try_into().ok()?);
        let prev_root = u32::from_le_bytes(footer_bytes[4..8].try_into().ok()?);

        // Validate magic
        if &footer_bytes[8..12] != b"TRON" {
            return None;
        }

        // Parse root to get arr_length if array
        let node_bytes = bytes.get(root_addr as usize..footer_start)?;
        let node = ValueNode::new(node_bytes)?;
        let arr_length = match node {
            ValueNode::Arr(ArrValue::Root(root)) => Some(root.length),
            _ => None,
        };

        // Copy buffer WITHOUT the footer - footer will be added back in into_bytes()
        let buffer = bytes[..footer_start].to_vec();

        Some(TronMut {
            buffer,
            root_addr,
            arr_length,
            prev_root,
        })
    }

    /// Create from owned buffer.
    pub fn from_vec(mut buffer: Vec<u8>) -> Option<Self> {
        let footer_start = buffer.len().checked_sub(12)?;
        let footer_bytes = buffer.get(footer_start..)?;
        let root_addr = u32::from_le_bytes(footer_bytes[0..4].try_into().ok()?);
        let prev_root = u32::from_le_bytes(footer_bytes[4..8].try_into().ok()?);

        if &footer_bytes[8..12] != b"TRON" {
            return None;
        }

        let node_bytes = buffer.get(root_addr as usize..footer_start)?;
        let node = ValueNode::new(node_bytes)?;
        let arr_length = match node {
            ValueNode::Arr(ArrValue::Root(root)) => Some(root.length),
            _ => None,
        };

        // Remove footer from buffer - it will be added back in into_bytes()
        buffer.truncate(footer_start);

        Some(TronMut {
            buffer,
            root_addr,
            arr_length,
            prev_root,
        })
    }

    /// Get a read-only proxy of the current state.
    pub fn proxy(&self) -> Option<TronProxy<'_>> {
        TronProxy::from_raw(&self.buffer, self.root_addr, self.arr_length)
    }

    /// Get the underlying buffer.
    pub fn buffer(&self) -> &[u8] {
        &self.buffer
    }

    /// Get the current root address.
    pub fn root_addr(&self) -> u32 {
        self.root_addr
    }

    /// Consume and return the buffer with footer.
    pub fn into_bytes(mut self) -> Vec<u8> {
        self.add_footer();
        self.buffer
    }

    fn add_footer(&mut self) {
        // Buffer doesn't have footer - add it now
        crate::encode::encode_footer(&mut self.buffer, self.root_addr, self.prev_root);
    }

    // === Map mutations (when root is a map) ===

    /// Set a key-value pair at the root map.
    pub fn set<V: IntoValue>(&mut self, key: &str, value: V) -> Result<(), MutError> {
        self.root_addr = map::map_set(&mut self.buffer, self.root_addr, key, value.into_value())
            .map_err(|_| MutError::InvalidNode {
                address: self.root_addr,
            })?;
        Ok(())
    }

    /// Delete a key from the root map.
    pub fn delete(&mut self, key: &str) -> Result<(), MutError> {
        self.root_addr = map::map_del(&mut self.buffer, self.root_addr, key).map_err(|_| {
            MutError::InvalidNode {
                address: self.root_addr,
            }
        })?;
        Ok(())
    }

    // === Array mutations (when root is an array) ===

    /// Set an element at the given index in the root array.
    pub fn set_index<V: IntoValue>(&mut self, index: u32, value: V) -> Result<(), MutError> {
        let length = self.arr_length.ok_or(MutError::NotAnArray)?;
        let value_addr = crate::encode::encode_value(&mut self.buffer, value.into_value());
        self.root_addr = arr::arr_set(&mut self.buffer, self.root_addr, index, value_addr, length)
            .map_err(|e| match e {
                arr::ArrError::IndexOutOfBounds { index, length } => {
                    MutError::IndexOutOfBounds { index, length }
                }
                arr::ArrError::InvalidNode { address } => MutError::InvalidNode { address },
            })?;
        Ok(())
    }

    /// Append a value to the root array.
    pub fn push<V: IntoValue>(&mut self, value: V) -> Result<(), MutError> {
        let length = self.arr_length.ok_or(MutError::NotAnArray)?;
        let value_addr = crate::encode::encode_value(&mut self.buffer, value.into_value());
        let (new_root, new_len) =
            arr::arr_append(&mut self.buffer, self.root_addr, &[value_addr], length).map_err(
                |_| MutError::InvalidNode {
                    address: self.root_addr,
                },
            )?;
        self.root_addr = new_root;
        self.arr_length = Some(new_len);
        Ok(())
    }

    /// Extend the root array with multiple values.
    pub fn extend<V: IntoValue>(
        &mut self,
        values: impl IntoIterator<Item = V>,
    ) -> Result<(), MutError> {
        let length = self.arr_length.ok_or(MutError::NotAnArray)?;
        let value_addrs: Vec<u32> = values
            .into_iter()
            .map(|v| crate::encode::encode_value(&mut self.buffer, v.into_value()))
            .collect();
        if value_addrs.is_empty() {
            return Ok(());
        }
        let (new_root, new_len) =
            arr::arr_append(&mut self.buffer, self.root_addr, &value_addrs, length).map_err(
                |_| MutError::InvalidNode {
                    address: self.root_addr,
                },
            )?;
        self.root_addr = new_root;
        self.arr_length = Some(new_len);
        Ok(())
    }

    // === Path-based mutations ===

    /// Set a value at a path (e.g., ["users", "0", "name"]).
    ///
    /// Path segments that parse as u32 are treated as array indices.
    pub fn set_path<V: IntoValue>(&mut self, path: &[&str], value: V) -> Result<(), MutError> {
        if path.is_empty() {
            return Err(MutError::KeyNotFound { key: String::new() });
        }

        let value_enum = value.into_value();
        self.root_addr = self.cow_set_path(self.root_addr, path, value_enum)?;
        Ok(())
    }

    /// Delete a value at a path.
    pub fn delete_path(&mut self, path: &[&str]) -> Result<(), MutError> {
        if path.is_empty() {
            return Err(MutError::KeyNotFound { key: String::new() });
        }

        self.root_addr = self.cow_delete_path(self.root_addr, path)?;
        Ok(())
    }

    fn cow_set_path(
        &mut self,
        node_addr: u32,
        path: &[&str],
        value: crate::encode::Value<'_>,
    ) -> Result<u32, MutError> {
        if path.len() == 1 {
            // At the target level - perform the mutation
            let segment = path[0];
            if let Ok(idx) = segment.parse::<u32>() {
                // Array index at leaf
                let length = self.get_arr_length_at(node_addr)?;
                let value_addr = crate::encode::encode_value(&mut self.buffer, value);
                arr::arr_set(&mut self.buffer, node_addr, idx, value_addr, length).map_err(|e| {
                    match e {
                        arr::ArrError::IndexOutOfBounds { index, length } => {
                            MutError::IndexOutOfBounds { index, length }
                        }
                        arr::ArrError::InvalidNode { address } => MutError::InvalidNode { address },
                    }
                })
            } else {
                // Map key at leaf
                map::map_set(&mut self.buffer, node_addr, segment, value)
                    .map_err(|_| MutError::InvalidNode { address: node_addr })
            }
        } else {
            // Navigate deeper
            let segment = path[0];
            let rest = &path[1..];

            let node_bytes = self
                .buffer
                .get(node_addr as usize..)
                .ok_or(MutError::InvalidNode { address: node_addr })?;
            let node =
                ValueNode::new(node_bytes).ok_or(MutError::InvalidNode { address: node_addr })?;

            match node {
                ValueNode::Map(_) => {
                    let (_, child_addr) = map::map_get(&self.buffer, node_addr, segment).ok_or(
                        MutError::KeyNotFound {
                            key: segment.to_string(),
                        },
                    )?;

                    let new_child_addr = self.cow_set_path(child_addr, rest, value)?;

                    if new_child_addr == child_addr {
                        return Ok(node_addr);
                    }

                    // Rebuild map with new child - encode value at new_child_addr
                    map::map_set_addr(&mut self.buffer, node_addr, segment, new_child_addr)
                        .map_err(|_| MutError::InvalidNode { address: node_addr })
                }
                ValueNode::Arr(arr) => {
                    let idx: u32 = segment.parse().map_err(|_| MutError::NotAnArray)?;
                    let length = match arr {
                        ArrValue::Root(r) => r.length,
                        ArrValue::Child(_) => return Err(MutError::NotAnArray),
                    };

                    let (_, child_addr) = arr::arr_get(&self.buffer, node_addr, idx, length)
                        .ok_or(MutError::IndexOutOfBounds { index: idx, length })?;

                    let new_child_addr = self.cow_set_path(child_addr, rest, value)?;

                    if new_child_addr == child_addr {
                        return Ok(node_addr);
                    }

                    arr::arr_set(&mut self.buffer, node_addr, idx, new_child_addr, length).map_err(
                        |e| match e {
                            arr::ArrError::IndexOutOfBounds { index, length } => {
                                MutError::IndexOutOfBounds { index, length }
                            }
                            arr::ArrError::InvalidNode { address } => {
                                MutError::InvalidNode { address }
                            }
                        },
                    )
                }
                _ => Err(MutError::NotAMap),
            }
        }
    }

    fn cow_delete_path(&mut self, node_addr: u32, path: &[&str]) -> Result<u32, MutError> {
        if path.len() == 1 {
            let segment = path[0];
            // Only maps support delete - arrays don't support removing elements
            map::map_del(&mut self.buffer, node_addr, segment)
                .map_err(|_| MutError::InvalidNode { address: node_addr })
        } else {
            let segment = path[0];
            let rest = &path[1..];

            let node_bytes = self
                .buffer
                .get(node_addr as usize..)
                .ok_or(MutError::InvalidNode { address: node_addr })?;
            let node =
                ValueNode::new(node_bytes).ok_or(MutError::InvalidNode { address: node_addr })?;

            match node {
                ValueNode::Map(_) => {
                    let (_, child_addr) = map::map_get(&self.buffer, node_addr, segment).ok_or(
                        MutError::KeyNotFound {
                            key: segment.to_string(),
                        },
                    )?;

                    let new_child_addr = self.cow_delete_path(child_addr, rest)?;

                    if new_child_addr == child_addr {
                        return Ok(node_addr);
                    }

                    map::map_set_addr(&mut self.buffer, node_addr, segment, new_child_addr)
                        .map_err(|_| MutError::InvalidNode { address: node_addr })
                }
                ValueNode::Arr(arr) => {
                    let idx: u32 = segment.parse().map_err(|_| MutError::NotAnArray)?;
                    let length = match arr {
                        ArrValue::Root(r) => r.length,
                        ArrValue::Child(_) => return Err(MutError::NotAnArray),
                    };

                    let (_, child_addr) = arr::arr_get(&self.buffer, node_addr, idx, length)
                        .ok_or(MutError::IndexOutOfBounds { index: idx, length })?;

                    let new_child_addr = self.cow_delete_path(child_addr, rest)?;

                    if new_child_addr == child_addr {
                        return Ok(node_addr);
                    }

                    arr::arr_set(&mut self.buffer, node_addr, idx, new_child_addr, length).map_err(
                        |e| match e {
                            arr::ArrError::IndexOutOfBounds { index, length } => {
                                MutError::IndexOutOfBounds { index, length }
                            }
                            arr::ArrError::InvalidNode { address } => {
                                MutError::InvalidNode { address }
                            }
                        },
                    )
                }
                _ => Err(MutError::NotAMap),
            }
        }
    }

    fn get_arr_length_at(&self, node_addr: u32) -> Result<u32, MutError> {
        let node_bytes = self
            .buffer
            .get(node_addr as usize..)
            .ok_or(MutError::InvalidNode { address: node_addr })?;
        let node =
            ValueNode::new(node_bytes).ok_or(MutError::InvalidNode { address: node_addr })?;
        match node {
            ValueNode::Arr(ArrValue::Root(r)) => Ok(r.length),
            _ => Err(MutError::NotAnArray),
        }
    }

    /// Get a cursor for chained navigation and mutation.
    pub fn cursor(&mut self) -> TronCursor<'_> {
        TronCursor {
            doc: self,
            path: Vec::new(),
        }
    }
}

/// Path segment for cursor navigation.
#[derive(Clone, Debug)]
enum PathSegment {
    Key(String),
    Index(u32),
}

/// A cursor for navigating and mutating a TRON document.
///
/// The cursor tracks the path taken and performs COW updates
/// when a mutation is requested.
pub struct TronCursor<'a> {
    doc: &'a mut TronMut,
    path: Vec<PathSegment>,
}

impl<'a> TronCursor<'a> {
    /// Navigate into a map key.
    pub fn get(mut self, key: &str) -> Result<Self, MutError> {
        // Validate path exists
        self.validate_path(&PathSegment::Key(key.to_string()))?;
        self.path.push(PathSegment::Key(key.to_string()));
        Ok(self)
    }

    /// Navigate into an array index.
    pub fn index(mut self, idx: u32) -> Result<Self, MutError> {
        self.validate_path(&PathSegment::Index(idx))?;
        self.path.push(PathSegment::Index(idx));
        Ok(self)
    }

    /// Set the value at current cursor position.
    pub fn set<V: IntoValue>(self, value: V) -> Result<(), MutError> {
        let path_strs: Vec<String> = self
            .path
            .iter()
            .map(|s| match s {
                PathSegment::Key(k) => k.clone(),
                PathSegment::Index(i) => i.to_string(),
            })
            .collect();
        let path_refs: Vec<&str> = path_strs.iter().map(|s| s.as_str()).collect();
        self.doc.set_path(&path_refs, value)
    }

    /// Set a nested key-value at current position (for maps).
    pub fn set_key<V: IntoValue>(mut self, key: &str, value: V) -> Result<(), MutError> {
        self.path.push(PathSegment::Key(key.to_string()));
        self.set(value)
    }

    /// Delete the value at current cursor position.
    pub fn delete(self) -> Result<(), MutError> {
        let path_strs: Vec<String> = self
            .path
            .iter()
            .map(|s| match s {
                PathSegment::Key(k) => k.clone(),
                PathSegment::Index(i) => i.to_string(),
            })
            .collect();
        let path_refs: Vec<&str> = path_strs.iter().map(|s| s.as_str()).collect();
        self.doc.delete_path(&path_refs)
    }

    fn validate_path(&self, next: &PathSegment) -> Result<(), MutError> {
        let proxy = self.doc.proxy().ok_or(MutError::InvalidNode {
            address: self.doc.root_addr,
        })?;
        let mut current = proxy;

        for segment in &self.path {
            current = match segment {
                PathSegment::Key(k) => current
                    .get(k)
                    .map_err(|_| MutError::KeyNotFound { key: k.clone() })?,
                PathSegment::Index(i) => current.index(*i).map_err(|e| match e {
                    ProxyError::IndexOutOfBounds { index, length } => {
                        MutError::IndexOutOfBounds { index, length }
                    }
                    _ => MutError::NotAnArray,
                })?,
            };
        }

        // Validate next segment
        match next {
            PathSegment::Key(k) => {
                current
                    .get(k)
                    .map_err(|_| MutError::KeyNotFound { key: k.clone() })?;
            }
            PathSegment::Index(i) => {
                current.index(*i).map_err(|e| match e {
                    ProxyError::IndexOutOfBounds { index, length } => {
                        MutError::IndexOutOfBounds { index, length }
                    }
                    _ => MutError::NotAnArray,
                })?;
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encode::*;

    fn make_simple_map() -> Vec<u8> {
        let mut buffer = Vec::new();

        // Key: "name"
        let key_addr = encode_txt(&mut buffer, "name");
        // Value: "Alice"
        let val_addr = encode_txt(&mut buffer, "Alice");

        // Map leaf with one entry
        let root_addr = encode_map_leaf(&mut buffer, &[(key_addr, val_addr)]);
        encode_footer(&mut buffer, root_addr, 0);

        buffer
    }

    fn make_nested_map() -> Vec<u8> {
        let mut buffer = Vec::new();

        // Inner map: { "city": "NYC" }
        let inner_key = encode_txt(&mut buffer, "city");
        let inner_val = encode_txt(&mut buffer, "NYC");
        let inner_map = encode_map_leaf(&mut buffer, &[(inner_key, inner_val)]);

        // Outer map: { "location": inner_map }
        let outer_key = encode_txt(&mut buffer, "location");
        let root_addr = encode_map_leaf(&mut buffer, &[(outer_key, inner_map)]);
        encode_footer(&mut buffer, root_addr, 0);

        buffer
    }

    fn make_simple_array() -> Vec<u8> {
        let mut buffer = Vec::new();

        let val0 = encode_i64(&mut buffer, 10);
        let val1 = encode_i64(&mut buffer, 20);
        let val2 = encode_i64(&mut buffer, 30);

        let root_addr = encode_arr_root(&mut buffer, false, 0, 0b111, 3, &[val0, val1, val2]);
        encode_footer(&mut buffer, root_addr, 0);

        buffer
    }

    fn make_array_of_maps() -> Vec<u8> {
        let mut buffer = Vec::new();

        // First map: { "name": "Alice" }
        let k0 = encode_txt(&mut buffer, "name");
        let v0 = encode_txt(&mut buffer, "Alice");
        let map0 = encode_map_leaf(&mut buffer, &[(k0, v0)]);

        // Second map: { "name": "Bob" }
        let k1 = encode_txt(&mut buffer, "name");
        let v1 = encode_txt(&mut buffer, "Bob");
        let map1 = encode_map_leaf(&mut buffer, &[(k1, v1)]);

        let root_addr = encode_arr_root(&mut buffer, false, 0, 0b11, 2, &[map0, map1]);
        encode_footer(&mut buffer, root_addr, 0);

        buffer
    }

    #[test]
    fn test_simple_map_get() {
        let buffer = make_simple_map();
        let doc = Tron::from_bytes(&buffer).unwrap();
        let proxy = TronProxy::from_doc(&doc);

        let name = proxy.get("name").unwrap().as_str().unwrap();
        assert_eq!(name, "Alice");
    }

    #[test]
    fn test_map_key_not_found() {
        let buffer = make_simple_map();
        let doc = Tron::from_bytes(&buffer).unwrap();
        let proxy = TronProxy::from_doc(&doc);

        let err = proxy.get("missing").unwrap_err();
        assert_eq!(
            err,
            ProxyError::KeyNotFound {
                key: "missing".to_string()
            }
        );
    }

    #[test]
    fn test_nested_map_navigation() {
        let buffer = make_nested_map();
        let doc = Tron::from_bytes(&buffer).unwrap();
        let proxy = TronProxy::from_doc(&doc);

        let city = proxy
            .get("location")
            .unwrap()
            .get("city")
            .unwrap()
            .as_str()
            .unwrap();
        assert_eq!(city, "NYC");
    }

    #[test]
    fn test_simple_array_index() {
        let buffer = make_simple_array();
        let doc = Tron::from_bytes(&buffer).unwrap();
        let proxy = TronProxy::from_doc(&doc);

        assert_eq!(proxy.index(0).unwrap().as_i64().unwrap(), 10);
        assert_eq!(proxy.index(1).unwrap().as_i64().unwrap(), 20);
        assert_eq!(proxy.index(2).unwrap().as_i64().unwrap(), 30);
    }

    #[test]
    fn test_array_out_of_bounds() {
        let buffer = make_simple_array();
        let doc = Tron::from_bytes(&buffer).unwrap();
        let proxy = TronProxy::from_doc(&doc);

        let err = proxy.index(5).unwrap_err();
        assert_eq!(
            err,
            ProxyError::IndexOutOfBounds {
                index: 5,
                length: 3
            }
        );
    }

    #[test]
    fn test_array_of_maps() {
        let buffer = make_array_of_maps();
        let doc = Tron::from_bytes(&buffer).unwrap();
        let proxy = TronProxy::from_doc(&doc);

        let alice = proxy
            .index(0)
            .unwrap()
            .get("name")
            .unwrap()
            .as_str()
            .unwrap();
        assert_eq!(alice, "Alice");

        let bob = proxy
            .index(1)
            .unwrap()
            .get("name")
            .unwrap()
            .as_str()
            .unwrap();
        assert_eq!(bob, "Bob");
    }

    #[test]
    fn test_get_path_with_map_keys() {
        let buffer = make_nested_map();
        let doc = Tron::from_bytes(&buffer).unwrap();
        let proxy = TronProxy::from_doc(&doc);

        let city = proxy
            .get_path(&["location", "city"])
            .unwrap()
            .as_str()
            .unwrap();
        assert_eq!(city, "NYC");
    }

    #[test]
    fn test_get_path_with_array_indices() {
        let buffer = make_array_of_maps();
        let doc = Tron::from_bytes(&buffer).unwrap();
        let proxy = TronProxy::from_doc(&doc);

        let bob = proxy.get_path(&["1", "name"]).unwrap().as_str().unwrap();
        assert_eq!(bob, "Bob");
    }

    #[test]
    fn test_type_mismatch() {
        let buffer = make_simple_map();
        let doc = Tron::from_bytes(&buffer).unwrap();
        let proxy = TronProxy::from_doc(&doc);

        let name_proxy = proxy.get("name").unwrap();
        let err = name_proxy.as_i64().unwrap_err();
        assert_eq!(
            err,
            ProxyError::TypeMismatch {
                expected: "i64",
                actual: "txt"
            }
        );
    }

    #[test]
    fn test_not_a_map() {
        let buffer = make_simple_array();
        let doc = Tron::from_bytes(&buffer).unwrap();
        let proxy = TronProxy::from_doc(&doc);

        let err = proxy.get("key").unwrap_err();
        assert_eq!(err, ProxyError::NotAMap);
    }

    #[test]
    fn test_not_an_array() {
        let buffer = make_simple_map();
        let doc = Tron::from_bytes(&buffer).unwrap();
        let proxy = TronProxy::from_doc(&doc);

        let err = proxy.index(0).unwrap_err();
        assert_eq!(err, ProxyError::NotAnArray);
    }

    #[test]
    fn test_value_type() {
        let buffer = make_simple_map();
        let doc = Tron::from_bytes(&buffer).unwrap();
        let proxy = TronProxy::from_doc(&doc);

        assert_eq!(proxy.value_type(), "map");
        assert!(proxy.is_map());
        assert!(!proxy.is_array());

        let name_proxy = proxy.get("name").unwrap();
        assert_eq!(name_proxy.value_type(), "txt");
    }

    #[test]
    fn test_introspection() {
        let buffer = make_simple_array();
        let doc = Tron::from_bytes(&buffer).unwrap();
        let proxy = TronProxy::from_doc(&doc);

        assert!(proxy.is_array());
        assert!(!proxy.is_map());
        assert!(!proxy.is_nil());

        let val = proxy.index(0).unwrap();
        assert_eq!(val.value_type(), "i64");
    }

    // ========================================================================
    // TronMut tests
    // ========================================================================

    #[test]
    fn test_tronmut_from_bytes() {
        let buffer = make_simple_map();
        let doc = TronMut::from_bytes(&buffer).unwrap();
        let proxy = doc.proxy().unwrap();
        assert_eq!(proxy.get("name").unwrap().as_str().unwrap(), "Alice");
    }

    #[test]
    fn test_tronmut_set() {
        let buffer = make_simple_map();
        let mut doc = TronMut::from_bytes(&buffer).unwrap();

        // Update existing key
        doc.set("name", "Bob").unwrap();
        let proxy = doc.proxy().unwrap();
        assert_eq!(proxy.get("name").unwrap().as_str().unwrap(), "Bob");
    }

    #[test]
    fn test_tronmut_set_new_key() {
        let buffer = make_simple_map();
        let mut doc = TronMut::from_bytes(&buffer).unwrap();

        // Add new key
        doc.set("age", 30i64).unwrap();
        let proxy = doc.proxy().unwrap();
        assert_eq!(proxy.get("name").unwrap().as_str().unwrap(), "Alice");
        assert_eq!(proxy.get("age").unwrap().as_i64().unwrap(), 30);
    }

    #[test]
    fn test_tronmut_delete() {
        let buffer = make_simple_map();
        let mut doc = TronMut::from_bytes(&buffer).unwrap();

        doc.delete("name").unwrap();
        let proxy = doc.proxy().unwrap();
        assert!(proxy.get("name").is_err());
    }

    #[test]
    fn test_tronmut_array_set_index() {
        let buffer = make_simple_array();
        let mut doc = TronMut::from_bytes(&buffer).unwrap();

        doc.set_index(1, 99i64).unwrap();
        let proxy = doc.proxy().unwrap();
        assert_eq!(proxy.index(0).unwrap().as_i64().unwrap(), 10);
        assert_eq!(proxy.index(1).unwrap().as_i64().unwrap(), 99);
        assert_eq!(proxy.index(2).unwrap().as_i64().unwrap(), 30);
    }

    #[test]
    fn test_tronmut_array_push() {
        let buffer = make_simple_array();
        let mut doc = TronMut::from_bytes(&buffer).unwrap();

        doc.push(40i64).unwrap();
        let proxy = doc.proxy().unwrap();
        assert_eq!(proxy.index(3).unwrap().as_i64().unwrap(), 40);
    }

    #[test]
    fn test_tronmut_set_path() {
        let buffer = make_nested_map();
        let mut doc = TronMut::from_bytes(&buffer).unwrap();

        doc.set_path(&["location", "city"], "LA").unwrap();
        let proxy = doc.proxy().unwrap();
        assert_eq!(
            proxy
                .get("location")
                .unwrap()
                .get("city")
                .unwrap()
                .as_str()
                .unwrap(),
            "LA"
        );
    }

    #[test]
    fn test_tronmut_delete_path() {
        let buffer = make_nested_map();
        let mut doc = TronMut::from_bytes(&buffer).unwrap();

        doc.delete_path(&["location", "city"]).unwrap();
        let proxy = doc.proxy().unwrap();
        // location still exists but city is gone
        assert!(proxy.get("location").unwrap().get("city").is_err());
    }

    #[test]
    fn test_tronmut_set_path_in_array() {
        let buffer = make_array_of_maps();
        let mut doc = TronMut::from_bytes(&buffer).unwrap();

        doc.set_path(&["0", "name"], "Charlie").unwrap();
        let proxy = doc.proxy().unwrap();
        assert_eq!(
            proxy
                .index(0)
                .unwrap()
                .get("name")
                .unwrap()
                .as_str()
                .unwrap(),
            "Charlie"
        );
        // Second element unchanged
        assert_eq!(
            proxy
                .index(1)
                .unwrap()
                .get("name")
                .unwrap()
                .as_str()
                .unwrap(),
            "Bob"
        );
    }

    #[test]
    fn test_tronmut_cursor() {
        let buffer = make_array_of_maps();
        let mut doc = TronMut::from_bytes(&buffer).unwrap();

        doc.cursor()
            .index(1)
            .unwrap()
            .set_key("name", "Dave")
            .unwrap();

        let proxy = doc.proxy().unwrap();
        assert_eq!(
            proxy
                .index(1)
                .unwrap()
                .get("name")
                .unwrap()
                .as_str()
                .unwrap(),
            "Dave"
        );
    }

    #[test]
    fn test_tronmut_into_bytes_roundtrip() {
        let buffer = make_simple_map();
        let mut doc = TronMut::from_bytes(&buffer).unwrap();

        doc.set("name", "Updated").unwrap();
        doc.set("count", 42i64).unwrap();

        let bytes = doc.into_bytes();

        // Parse the new bytes and verify
        let doc2 = TronMut::from_bytes(&bytes).unwrap();
        let proxy = doc2.proxy().unwrap();
        assert_eq!(proxy.get("name").unwrap().as_str().unwrap(), "Updated");
        assert_eq!(proxy.get("count").unwrap().as_i64().unwrap(), 42);
    }

    #[test]
    fn test_tronmut_error_not_array() {
        let buffer = make_simple_map();
        let mut doc = TronMut::from_bytes(&buffer).unwrap();

        let err = doc.push(1i64).unwrap_err();
        assert_eq!(err, MutError::NotAnArray);
    }

    #[test]
    fn test_tronmut_error_index_out_of_bounds() {
        let buffer = make_simple_array();
        let mut doc = TronMut::from_bytes(&buffer).unwrap();

        let err = doc.set_index(10, 1i64).unwrap_err();
        assert_eq!(
            err,
            MutError::IndexOutOfBounds {
                index: 10,
                length: 3
            }
        );
    }
}
