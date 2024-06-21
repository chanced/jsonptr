use crate::{OutOfBoundsError, ParseIndexError, Pointer};
use serde_json::Value;

/// Resolve is implemented by types which can resolve a reference to a
/// `serde_json::Value` from the path in a JSON Pointer.
pub trait Resolve {
    /// Error associated with `Resolve`
    type Error;
    /// Resolve a reference to a `serde_json::Value` based on the path in a
    /// [Pointer].
    fn resolve(&self, ptr: &Pointer) -> Result<&Value, Self::Error>;
}
impl Resolve for Value {
    type Error = ResolveError;

    fn resolve(&self, mut ptr: &Pointer) -> Result<&Value, Self::Error> {
        let mut offset = 0;
        let mut value = self;
        while let Some((token, rem)) = ptr.split_front() {
            let tok_len = token.encoded().len();
            ptr = rem;
            value = match value {
                Value::Array(v) => {
                    let idx = token
                        .to_index()
                        .map_err(|source| ResolveError::FailedToParseIndex { offset, source })?
                        .for_len(v.len())
                        .map_err(|source| ResolveError::OutOfBounds { offset, source })?;
                    Ok(&v[idx])
                }

                Value::Object(v) => v
                    .get(token.decoded().as_ref())
                    .ok_or_else(|| ResolveError::NotFound { offset }),
                // found a leaf node but the pointer hasn't been exhausted
                _ => Err(ResolveError::Unreachable { offset }),
            }?;
            offset += 1 + tok_len;
        }
        Ok(value)
    }
}

/// ResolveMut is implemented by types which can resolve a mutable reference to
/// a `serde_json::Value` from the path in a JSON Pointer.
pub trait ResolveMut {
    /// Error associated with `ResolveMut`
    type Error;
    /// Resolve a mutable reference to a `serde_json::Value` based on the path
    /// in a JSON Pointer.
    fn resolve_mut(&mut self, ptr: &Pointer) -> Result<&mut Value, Self::Error>;
}
impl ResolveMut for Value {
    type Error = ResolveError;

    fn resolve_mut(&mut self, mut ptr: &Pointer) -> Result<&mut Value, ResolveError> {
        let mut offset = 0;
        let mut value = self;
        while let Some((token, rem)) = ptr.split_front() {
            let tok_len = token.encoded().len();
            ptr = rem;
            value = match value {
                Value::Array(array) => {
                    let idx = token
                        .to_index()
                        .map_err(|source| ResolveError::FailedToParseIndex { offset, source })?
                        .for_len(array.len())
                        .map_err(|source| ResolveError::OutOfBounds { offset, source })?;
                    Ok(&mut array[idx])
                }
                Value::Object(v) => v
                    .get_mut(token.decoded().as_ref())
                    .ok_or_else(|| ResolveError::NotFound { offset }),
                // found a leaf node but the pointer hasn't been exhausted
                _ => Err(ResolveError::Unreachable { offset }),
            }?;
            offset += 1 + tok_len;
        }
        Ok(value)
    }
}

/// Indicates that the `Pointer` could not be resolved.
#[derive(Debug)]
pub enum ResolveError {
    /// `Pointer` could not be resolved because a `Token` for an array index is
    /// not a valid integer or dash (`"-"`).
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
        /// Offset of the partial pointer starting with the invalid index.
        offset: usize,
        /// The source `ParseIndexError`
        source: ParseIndexError,
    },
    /// `Pointer` could not be resolved due to an index being out of bounds
    /// within an array.
    ///
    /// ## Example
    /// ```rust
    /// # use serde_json::json;
    /// # use jsonptr::Pointer;
    /// let data = json!({ "foo": ["bar"] });
    /// let ptr = Pointer::from_static("/foo/1");
    /// assert!(ptr.resolve(&data).unwrap_err().is_out_of_bounds());
    OutOfBounds {
        /// Offset of the partial pointer starting with the invalid index.
        offset: usize,
        /// The source `OutOfBoundsError`
        source: OutOfBoundsError,
    },

    /// `Pointer` could not be resolved as a segment of the path was not found.
    ///
    /// ## Example
    /// ```rust
    /// # use serde_json::json;
    /// # use jsonptr::{Pointer};
    /// let mut data = json!({ "foo": "bar" });
    /// let ptr = Pointer::from_static("/bar");
    /// assert!(ptr.resolve(&data).unwrap_err().is_not_found());
    /// ```
    NotFound {
        /// Offset of the pointer starting with the `Token` which was not found.
        offset: usize,
    },

    /// `Pointer` could not be resolved as the path contains a scalar value
    /// before fully exhausting the path.
    ///
    /// ## Example
    /// ```rust
    /// # use serde_json::json;
    /// # use jsonptr::Pointer;
    /// let mut data = json!({ "foo": "bar" });
    /// let ptr = Pointer::from_static("/foo/unreachable");
    /// assert!(ptr.resolve(&data).unwrap_err(), err.is_unreachable());
    /// ```
    Unreachable {
        /// Offset of the pointer which was unreachable.
        offset: usize,
    },
}
impl ResolveError {
    /// Offset of the partial pointer starting with the token which caused the
    /// error.
    pub fn offset(&self) -> usize {
        match self {
            Self::FailedToParseIndex { offset, .. }
            | Self::OutOfBounds { offset, .. }
            | Self::NotFound { offset, .. }
            | Self::Unreachable { offset, .. } => *offset,
        }
    }
    /// Returns `true` if this error is `FailedToParseIndex`; otherwise returns
    /// `false`.
    pub fn is_unreachable(&self) -> bool {
        matches!(self, Self::Unreachable { .. })
    }
    /// Returns `true` if this error is `FailedToParseIndex`; otherwise returns
    /// `false`.
    pub fn is_not_found(&self) -> bool {
        matches!(self, Self::NotFound { .. })
    }
    /// Returns `true` if this error is `FailedToParseIndex`; otherwise returns
    /// `false`.
    pub fn is_out_of_bounds(&self) -> bool {
        matches!(self, Self::OutOfBounds { .. })
    }
    /// Returns `true` if this error is `FailedToParseIndex`; otherwise returns
    /// `false`.
    pub fn is_failed_to_parse_index(&self) -> bool {
        matches!(self, Self::FailedToParseIndex { .. })
    }
}
impl core::fmt::Display for ResolveError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::FailedToParseIndex { offset, .. } => {
                write!(f, "failed to parse index at offset {}", offset)
            }
            Self::OutOfBounds { offset, .. } => {
                write!(f, "index at offset {} out of bounds", offset)
            }
            Self::NotFound { offset, .. } => {
                write!(f, "pointer starting at offset {} not found", offset)
            }
            Self::Unreachable { offset, .. } => {
                write!(f, "pointer starting at offset {} is unreachable", offset)
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ResolveError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::FailedToParseIndex { source, .. } => Some(source),
            Self::OutOfBounds { source, .. } => Some(source),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Pointer, PointerBuf};
    use serde_json::json;

    fn test_data() -> serde_json::Value {
        json!({
            "foo": {
                "bar": {
                    "baz": {
                        "qux": "quux"
                    }
                },
                "strings": ["zero", "one", "two"],
                "nothing": null,
                "bool": true,
                "objects": [{
                    "field": "zero"
                }, {
                    "field": "one"
                }, {
                    "field": "two"
                }]
            }
        })
    }

    #[test]
    fn test_rfc_examples() {
        let data = json!({
            "foo": ["bar", "baz"],
            "": 0,
            "a/b": 1,
            "c%d": 2,
            "e^f": 3,
            "g|h": 4,
            "i\\j": 5,
            "k\"l": 6,
            " ": 7,
            "m~n": 8
        });

        let val = data.get("").unwrap();
        assert_eq!(val, 0);

        // ""           // the whole document
        let ptr = Pointer::root();
        assert_eq!(data.resolve(ptr).unwrap(), &data);

        // "/foo"       ["bar", "baz"]
        let ptr = Pointer::from_static("/foo");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(["bar", "baz"]));

        // "/foo/0"     "bar"
        let ptr = Pointer::from_static("/foo/0");
        assert_eq!(data.resolve(ptr).unwrap(), &json!("bar"));

        // // "/"          0
        let ptr = Pointer::from_static("/");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(0));

        // "/a~1b"      1
        assert_eq!(data.get("a/b").unwrap(), 1);
        let ptr = Pointer::from_static("/a~1b");
        assert_eq!(ptr.as_str(), "/a~1b");
        assert_eq!(data.get("a/b").unwrap(), 1);
        assert_eq!(&ptr.first().unwrap().decoded(), "a/b");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(1));

        // "/c%d"       2
        let ptr = Pointer::from_static("/c%d");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(2));

        // // "/e^f"       3
        let ptr = Pointer::from_static("/e^f");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(3));

        // // "/g|h"       4
        let ptr = Pointer::from_static("/g|h");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(4));

        // "/i\\j"      5
        let ptr = Pointer::from_static("/i\\j");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(5));

        // // "/k\"l"      6
        let ptr = Pointer::from_static("/k\"l");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(6));

        // // "/ "         7
        let ptr = Pointer::from_static("/ ");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(7));
        // // "/m~0n"      8
        let ptr = Pointer::from_static("/m~0n");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(8));
    }

    #[test]
    fn test_resolve_unresolvable() {
        let mut data = test_data();
        let ptr = Pointer::from_static("/foo/bool/unresolvable");
        let res = ptr.resolve_mut(&mut data);

        assert!(res.is_err());
        let err = res.unwrap_err();
        assert!(err.is_unreachable());
        assert_eq!(err.offset(), 9)
    }

    #[test]
    fn test_resolve_not_found() {
        let mut data = test_data();
        let ptr = PointerBuf::from_tokens(["foo", "not_found", "nope"]);
        let res = ptr.resolve_mut(&mut data);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert!(err.is_not_found());

        match err {
            ResolveError::NotFound { offset, .. } => {
                assert_eq!(offset, 4);
            }
            _ => panic!("expected NotFound"),
        }
    }

    #[test]
    fn test_try_from() {
        let ptr = PointerBuf::from_tokens(["foo", "bar", "~/"]);

        assert_eq!(PointerBuf::try_from("/foo/bar/~0~1").unwrap(), ptr);
        let into: PointerBuf = "/foo/bar/~0~1".try_into().unwrap();
        assert_eq!(ptr, into);
    }

    #[test]
    fn test_resolve_mut_unresolvable_error() {
        let mut data = test_data();
        let ptr = Pointer::from_static("/foo/bool/unresolvable/not-in-token");
        let res = ptr.resolve_mut(&mut data);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert!(err.is_unreachable());
        assert_eq!(err.offset(), 9);

        let ptr = Pointer::from_static("/foo/bool/unresolvable");
        let res = ptr.resolve_mut(&mut data);
        let err = res.unwrap_err();
        assert!(err.is_unreachable());
        assert_eq!(err.offset(), 9);

        let mut data = json!({"foo": "bar"});
        let ptr = PointerBuf::try_from("/foo/unresolvable").unwrap();
        let err = data.resolve_mut(&ptr).unwrap_err();
        assert!(err.is_unreachable());
        assert_eq!(err.offset(), 4);
    }

    #[test]
    fn test_resolve_unresolvable_error() {
        let data = test_data();
        let ptr = Pointer::from_static("/foo/bool/unresolvable/not-in-token");
        let res = ptr.resolve(&data);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert!(err.is_unreachable());
        assert_eq!(err.offset(), 9);
    }
}
