use core::fmt;

use serde_json::Value;

use crate::{ParseIndexError, Pointer};

/// Delete is implemented by types which can internally remove a value based on
/// a JSON Pointer
pub trait Delete {
    /// Error associated with `Delete`
    type Error;
    /// Attempts to internally delete a value based upon a [Pointer].
    fn delete(&mut self, ptr: &Pointer) -> Option<Value>;
}

impl Delete for Value {
    type Error = DeleteError;
    fn delete(&mut self, ptr: &Pointer) -> Option<Value> {
        ptr.delete(self)
    }
}

/// Indicates that a `Value` could not be deleted at the specified `Pointer`.
#[derive(Debug)]
pub enum DeleteError {
    /// `Value` at `Pointer` could not be because a `Token` for an array index
    /// is not a valid integer or dash (`"-"`).
    ///
    /// ## Example
    /// ```rust
    /// # use serde_json::json;
    /// # use jsonptr::Pointer;
    /// let data = json!({ "foo": ["bar"] });
    /// let ptr = Pointer::from_static("/foo/invalid");
    /// assert!(ptr.resolve(&data).unwrap_err().is_failed_to_parse_index());
    /// ```
    FailedToParseIndex {
        /// offset of the partial pointer starting with the token that failed to
        /// parse as an index
        offset: usize,
        /// the source `ParseIndexError`
        source: ParseIndexError,
    },
}

impl fmt::Display for DeleteError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FailedToParseIndex { offset, .. } => {
                write!(f, "failed to parse index at offset {}", offset)
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for DeleteError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::FailedToParseIndex { source, .. } => Some(source),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn test_issue_18() {
        let mut data = json!({
            "Example": 21,
            "test": "test"
        });
        let pointer = Pointer::from_static("/Example");
        pointer.delete(&mut data);
        assert_eq!(json!({"test": "test"}), data);
    }
}
