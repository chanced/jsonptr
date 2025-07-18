//! # Assign values based on JSON [`Pointer`]s
//!
//! This module provides the [`Assign`] trait which allows for the assignment of
//! values based on a JSON Pointer.
//!
//! This module is enabled by default with the `"assign"` feature flag.
//!
//! # Expansion
//! The path will automatically be expanded if the [`Pointer`] is not fully
//! exhausted before reaching a non-existent key in the case of objects, index
//! in the case of arrays, or a scalar value (including `null`) based upon a
//! best-guess effort on the meaning of each [`Token`](crate::Token):
//! - If the [`Token`](crate::Token) is equal to `"0"` or `"-"`, the token will
//!   be considered an index of an array.
//! - All tokens not equal to `"0"` or `"-"` will be considered keys of an
//!   object.
//!
//! ## Usage
//! [`Assign`] can be used directly or through the [`assign`](Pointer::assign)
//! method of [`Pointer`].
//!
//! ```rust
//! use jsonptr::Pointer;
//! use serde_json::json;
//! let mut data = json!({"foo": "bar"});
//! let ptr = Pointer::from_static("/foo");
//! let replaced = ptr.assign(&mut data, "baz").unwrap();
//! assert_eq!(replaced, Some(json!("bar")));
//! assert_eq!(data, json!({"foo": "baz"}));
//! ```
//! ## Provided implementations
//!
//! | Lang  |     value type      | feature flag | Default |
//! | ----- |: ----------------- :|: ---------- :| ------- |
//! | JSON  | `serde_json::Value` |   `"json"`   |   ✓     |
//! | TOML  |    `toml::Value`    |   `"toml"`   |         |
//!

use crate::{
    diagnostic::{diagnostic_url, Diagnostic, Label},
    index::{OutOfBoundsError, ParseIndexError},
    Pointer, PointerBuf,
};
use alloc::{boxed::Box, string::ToString};
use core::{
    fmt::{self, Debug},
    iter::once,
};

/// Implemented by types which can internally assign a
/// ([`Value`](`Assign::Value`)) at a path represented by a JSON [`Pointer`].
///
/// ## Expansion
/// For provided implementations (`"json"`, and `"toml"`) path will
/// automatically be expanded the if the [`Pointer`] is not fully exhausted
/// before reaching a non-existent key in the case of objects, index in the case
/// of arrays, or a scalar value (including `null`) based upon a best-guess
/// effort on the meaning of each [`Token`](crate::Token):
///
/// - If the [`Token`](crate::Token) is equal to `"0"` or `"-"`, the token will
///   be considered an index of an array.
/// - All tokens not equal to `"0"` or `"-"` will be considered keys of an
///   object.
///
/// ## Examples
///
/// ### Successful assignment with replacement
/// This example demonstrates a successful assignment with replacement.
/// ```rust
/// use jsonptr::{Pointer, assign::Assign};
/// use serde_json::{json, Value};
///
/// let mut data = json!({"foo": "bar"});
/// let ptr = Pointer::from_static("/foo");
///
/// let replaced = data.assign(&ptr, "baz").unwrap();
/// assert_eq!(replaced, Some(json!("bar")));
/// assert_eq!(data, json!({"foo": "baz"}));
/// ```
///
/// ### Successful assignment with path expansion
/// This example demonstrates path expansion, including an array index (`"0"`)
/// ```rust
/// # use jsonptr::{Pointer, assign::Assign};
/// # use serde_json::{json, Value};
/// let ptr = Pointer::from_static("/foo/bar/0/baz");
/// let mut data = serde_json::json!({"foo": "bar"});
///
/// let replaced = data.assign(ptr, json!("qux")).unwrap();
///
/// assert_eq!(&data, &json!({"foo": {"bar": [{"baz": "qux"}]}}));
/// assert_eq!(replaced, Some(json!("bar")));
/// ```
///
/// ### Successful assignment with `"-"` token
///
/// This example performs path expansion using the special `"-"` token (per RFC
/// 6901) to represent the next element in an array.
///
/// ```rust
/// # use jsonptr::{Pointer, assign::Assign};
/// # use serde_json::{json, Value};
/// let ptr = Pointer::from_static("/foo/bar/-/baz");
/// let mut data = json!({"foo": "bar"});
///
/// let replaced = data.assign(ptr, json!("qux")).unwrap();
/// assert_eq!(&data, &json!({"foo": {"bar": [{"baz": "qux"}]}}));
/// assert_eq!(replaced, Some(json!("bar")));
/// ```
pub trait Assign {
    /// The type of value that this implementation can operate on.
    type Value;

    /// Error associated with `Assign`
    type Error;

    /// Assigns a value of based on the path provided by a JSON Pointer,
    /// returning the replaced value, if any.
    ///
    /// # Errors
    /// Returns [`Self::Error`] if the assignment fails.
    fn assign<V>(&mut self, ptr: &Pointer, value: V) -> Result<Option<Self::Value>, Self::Error>
    where
        V: Into<Self::Value>;
}

/// Alias for [`Error`] - indicates a value assignment failed.
#[deprecated(since = "0.7.0", note = "renamed to `Error`")]
pub type AssignError = Error;

/// Possible error returned from [`Assign`] implementations for
/// [`serde_json::Value`] and
/// [`toml::Value`](https://docs.rs/toml/0.8.14/toml/index.html).
#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    /// A [`Token`](crate::Token) within the [`Pointer`] failed to be parsed as
    /// an array index.
    FailedToParseIndex {
        /// Position (index) of the token which failed to parse as an [`Index`](crate::index::Index)
        position: usize,
        /// Offset of the partial pointer starting with the invalid index.
        offset: usize,
        /// The source [`ParseIndexError`]
        source: ParseIndexError,
    },

    /// A [`Token`](crate::Token) within the [`Pointer`] contains an
    /// [`Index`](crate::index::Index) which is out of bounds.
    ///
    /// The current or resulting array's length is less than the index.
    OutOfBounds {
        /// Position (index) of the token which failed to parse as an [`Index`](crate::index::Index)
        position: usize,
        /// Offset of the partial pointer starting with the invalid index.
        offset: usize,
        /// The source [`OutOfBoundsError`]
        source: OutOfBoundsError,
    },
}

impl Error {
    /// The position (token index) of the [`Token`](crate::Token) which was out of bounds
    pub fn position(&self) -> usize {
        match self {
            Self::OutOfBounds { position, .. } | Self::FailedToParseIndex { position, .. } => {
                *position
            }
        }
    }
    /// Offset (in bytes) of the partial pointer starting with the invalid token.
    pub fn offset(&self) -> usize {
        match self {
            Self::OutOfBounds { offset, .. } | Self::FailedToParseIndex { offset, .. } => *offset,
        }
    }

    /// Returns `true` if the error is [`OutOfBounds`].
    ///
    /// [`OutOfBounds`]: Error::OutOfBounds
    #[must_use]
    pub fn is_out_of_bounds(&self) -> bool {
        matches!(self, Self::OutOfBounds { .. })
    }

    /// Returns `true` if the error is [`FailedToParseIndex`].
    ///
    /// [`FailedToParseIndex`]: Error::FailedToParseIndex
    #[must_use]
    pub fn is_failed_to_parse_index(&self) -> bool {
        matches!(self, Self::FailedToParseIndex { .. })
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FailedToParseIndex { offset, .. } => {
                write!(
                    f,
                    "assign failed: json pointer token at offset {offset} failed to parse as an array index"
                )
            }
            Self::OutOfBounds { offset, .. } => write!(
                f,
                "assign failed: json pointer token at offset {offset} is out of bounds",
            ),
        }
    }
}

impl Diagnostic for Error {
    type Subject = PointerBuf;

    fn url() -> &'static str {
        diagnostic_url!(enum assign::Error)
    }

    fn labels(&self, origin: &Self::Subject) -> Option<Box<dyn Iterator<Item = Label>>> {
        let position = self.position();
        let token = origin.get(position)?;
        let offset = if self.offset() + 1 < origin.as_str().len() {
            self.offset() + 1
        } else {
            self.offset()
        };
        let len = token.encoded().len();
        let text = match self {
            Error::FailedToParseIndex { .. } => "expected array index or '-'".to_string(),
            Error::OutOfBounds { source, .. } => {
                format!("{} is out of bounds (len: {})", source.index, source.length)
            }
        };
        Some(Box::new(once(Label::new(text, offset, len))))
    }
}

#[cfg(feature = "miette")]
impl miette::Diagnostic for Error {
    fn url<'a>(&'a self) -> Option<Box<dyn fmt::Display + 'a>> {
        Some(Box::new(<Self as Diagnostic>::url()))
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::FailedToParseIndex { source, .. } => Some(source),
            Self::OutOfBounds { source, .. } => Some(source),
        }
    }
}

#[cfg(feature = "json")]
mod json {
    use super::{Assign, Assigned, Error};
    use crate::{Pointer, Token};
    use alloc::{
        string::{String, ToString},
        vec::Vec,
    };

    use core::mem;
    use serde_json::{map::Entry, Map, Value};

    fn expand(mut remaining: &Pointer, mut value: Value) -> Value {
        while let Some((ptr, tok)) = remaining.split_back() {
            remaining = ptr;
            match tok.encoded() {
                "0" | "-" => {
                    value = Value::Array(vec![value]);
                }
                _ => {
                    let mut obj = Map::new();
                    obj.insert(tok.to_string(), value);
                    value = Value::Object(obj);
                }
            }
        }
        value
    }
    impl Assign for Value {
        type Value = Value;
        type Error = Error;
        fn assign<V>(&mut self, ptr: &Pointer, value: V) -> Result<Option<Self::Value>, Self::Error>
        where
            V: Into<Self::Value>,
        {
            assign_value(ptr, self, value.into())
        }
    }

    pub(crate) fn assign_value(
        mut ptr: &Pointer,
        mut dest: &mut Value,
        mut value: Value,
    ) -> Result<Option<Value>, Error> {
        let mut offset = 0;

        let mut position = 0;
        while let Some((token, tail)) = ptr.split_front() {
            let tok_len = token.encoded().len();

            let assigned = match dest {
                Value::Array(array) => assign_array(token, tail, array, value, position, offset)?,
                Value::Object(obj) => assign_object(token, tail, obj, value),
                _ => assign_scalar(ptr, dest, value),
            };
            match assigned {
                Assigned::Done(assignment) => {
                    return Ok(assignment);
                }
                Assigned::Continue {
                    next_dest: next_value,
                    same_value: same_src,
                } => {
                    value = same_src;
                    dest = next_value;
                    ptr = tail;
                }
            }
            offset += 1 + tok_len;
            position += 1;
        }

        // Pointer is root, we can replace `dest` directly
        let replaced = Some(core::mem::replace(dest, value));
        Ok(replaced)
    }
    #[allow(clippy::needless_pass_by_value)]
    fn assign_array<'v>(
        token: Token<'_>,
        remaining: &Pointer,
        array: &'v mut Vec<Value>,
        src: Value,
        position: usize,
        offset: usize,
    ) -> Result<Assigned<'v, Value>, Error> {
        // parsing the index
        let idx = token
            .to_index()
            .map_err(|source| Error::FailedToParseIndex {
                position,
                offset,
                source,
            })?
            .for_len_incl(array.len())
            .map_err(|source| Error::OutOfBounds {
                position,
                offset,
                source,
            })?;

        debug_assert!(idx <= array.len());

        if idx < array.len() {
            // element exists in the array, we either need to replace it or continue
            // depending on whether this is the last token or not
            if remaining.is_root() {
                // last token, we replace the value and call it a day
                Ok(Assigned::Done(Some(mem::replace(&mut array[idx], src))))
            } else {
                // not the last token, we continue with a mut ref to the element as
                // the next value
                Ok(Assigned::Continue {
                    next_dest: &mut array[idx],
                    same_value: src,
                })
            }
        } else {
            // element does not exist in the array.
            // we create the path and assign the value
            let src = expand(remaining, src);
            array.push(src);
            Ok(Assigned::Done(None))
        }
    }

    #[allow(clippy::needless_pass_by_value)]
    fn assign_object<'v>(
        token: Token<'_>,
        remaining: &Pointer,
        obj: &'v mut Map<String, Value>,
        src: Value,
    ) -> Assigned<'v, Value> {
        // grabbing the entry of the token
        let entry = obj.entry(token.to_string());
        // adding token to the pointer buf

        match entry {
            Entry::Occupied(entry) => {
                // if the entry exists, we either replace it or continue
                let entry = entry.into_mut();
                if remaining.is_root() {
                    // if this is the last token, we are done
                    // grab the old value and replace it with the new one
                    Assigned::Done(Some(mem::replace(entry, src)))
                } else {
                    // if this is not the last token, we continue with a mutable
                    // reference to the entry as the next value
                    Assigned::Continue {
                        same_value: src,
                        next_dest: entry,
                    }
                }
            }
            Entry::Vacant(entry) => {
                // if the entry does not exist, we create a value based on the
                // remaining path with the src value as a leaf and assign it to the
                // entry
                entry.insert(expand(remaining, src));
                Assigned::Done(None)
            }
        }
    }

    fn assign_scalar<'v>(
        remaining: &Pointer,
        scalar: &'v mut Value,
        value: Value,
    ) -> Assigned<'v, Value> {
        // scalar values are always replaced at the current buf (with its token)
        // build the new src and we replace the value with it.
        let replaced = Some(mem::replace(scalar, expand(remaining, value)));
        Assigned::Done(replaced)
    }
}

#[cfg(feature = "toml")]
mod toml {
    use super::{Assign, Assigned, Error};
    use crate::{Pointer, Token};
    use alloc::{string::String, vec, vec::Vec};
    use core::mem;
    use toml::{map::Entry, map::Map, Value};

    fn expand(mut remaining: &Pointer, mut value: Value) -> Value {
        while let Some((ptr, tok)) = remaining.split_back() {
            remaining = ptr;
            match tok.encoded() {
                "0" | "-" => {
                    value = Value::Array(vec![value]);
                }
                _ => {
                    let mut obj = Map::new();
                    obj.insert(tok.to_string(), value);
                    value = Value::Table(obj);
                }
            }
        }
        value
    }

    impl Assign for Value {
        type Value = Value;
        type Error = Error;
        fn assign<V>(&mut self, ptr: &Pointer, value: V) -> Result<Option<Self::Value>, Self::Error>
        where
            V: Into<Self::Value>,
        {
            assign_value(ptr, self, value.into())
        }
    }

    pub(crate) fn assign_value(
        mut ptr: &Pointer,
        mut dest: &mut Value,
        mut value: Value,
    ) -> Result<Option<Value>, Error> {
        let mut offset = 0;
        let mut position = 0;

        while let Some((token, tail)) = ptr.split_front() {
            let tok_len = token.encoded().len();

            let assigned = match dest {
                Value::Array(array) => assign_array(token, tail, array, value, position, offset)?,
                Value::Table(tbl) => assign_object(token, tail, tbl, value),
                _ => assign_scalar(ptr, dest, value),
            };
            match assigned {
                Assigned::Done(assignment) => {
                    return Ok(assignment);
                }
                Assigned::Continue {
                    next_dest: next_value,
                    same_value: same_src,
                } => {
                    value = same_src;
                    dest = next_value;
                    ptr = tail;
                }
            }
            offset += 1 + tok_len;
            position += 1;
        }

        // Pointer is root, we can replace `dest` directly
        let replaced = Some(mem::replace(dest, value));
        Ok(replaced)
    }

    #[allow(clippy::needless_pass_by_value)]
    fn assign_array<'v>(
        token: Token<'_>,
        remaining: &Pointer,
        array: &'v mut Vec<Value>,
        src: Value,
        position: usize,
        offset: usize,
    ) -> Result<Assigned<'v, Value>, Error> {
        // parsing the index
        let idx = token
            .to_index()
            .map_err(|source| Error::FailedToParseIndex {
                position,
                offset,
                source,
            })?
            .for_len_incl(array.len())
            .map_err(|source| Error::OutOfBounds {
                position,
                offset,
                source,
            })?;

        debug_assert!(idx <= array.len());

        if idx < array.len() {
            // element exists in the array, we either need to replace it or continue
            // depending on whether this is the last token or not
            if remaining.is_root() {
                // last token, we replace the value and call it a day
                Ok(Assigned::Done(Some(mem::replace(&mut array[idx], src))))
            } else {
                // not the last token, we continue with a mut ref to the element as
                // the next value
                Ok(Assigned::Continue {
                    next_dest: &mut array[idx],
                    same_value: src,
                })
            }
        } else {
            // element does not exist in the array.
            // we create the path and assign the value
            let src = expand(remaining, src);
            array.push(src);
            Ok(Assigned::Done(None))
        }
    }

    #[allow(clippy::needless_pass_by_value)]
    fn assign_object<'v>(
        token: Token<'_>,
        remaining: &Pointer,
        obj: &'v mut Map<String, Value>,
        src: Value,
    ) -> Assigned<'v, Value> {
        // grabbing the entry of the token
        match obj.entry(token.to_string()) {
            Entry::Occupied(entry) => {
                // if the entry exists, we either replace it or continue
                let entry = entry.into_mut();
                if remaining.is_root() {
                    // if this is the last token, we are done
                    // grab the old value and replace it with the new one
                    Assigned::Done(Some(mem::replace(entry, src)))
                } else {
                    // if this is not the last token, we continue with a mutable
                    // reference to the entry as the next value
                    Assigned::Continue {
                        same_value: src,
                        next_dest: entry,
                    }
                }
            }
            Entry::Vacant(entry) => {
                // if the entry does not exist, we create a value based on the
                // remaining path with the src value as a leaf and assign it to the
                // entry
                entry.insert(expand(remaining, src));
                Assigned::Done(None)
            }
        }
    }

    fn assign_scalar<'v>(
        remaining: &Pointer,
        scalar: &'v mut Value,
        value: Value,
    ) -> Assigned<'v, Value> {
        // scalar values are always replaced at the current buf (with its token)
        // build the new src and we replace the value with it.
        Assigned::Done(Some(mem::replace(scalar, expand(remaining, value))))
    }
}

enum Assigned<'v, V> {
    Done(Option<V>),
    Continue { next_dest: &'v mut V, same_value: V },
}

#[cfg(test)]
#[allow(clippy::too_many_lines)]
mod tests {
    use super::{Assign, Error};
    use crate::{
        index::{InvalidCharacterError, OutOfBoundsError, ParseIndexError},
        Pointer,
    };
    use core::fmt::{Debug, Display};

    #[derive(Debug)]
    struct Test<V: Assign> {
        data: V,
        ptr: &'static str,
        assign: V,
        expected_data: V,
        expected: Result<Option<V>, V::Error>,
    }

    impl<V> Test<V>
    where
        V: Assign + Clone + PartialEq + Display + Debug,
        V::Value: Debug + PartialEq + From<V>,
        V::Error: Debug + PartialEq,
        Result<Option<V>, V::Error>: PartialEq<Result<Option<V::Value>, V::Error>>,
    {
        fn run(self, i: usize) {
            let Test {
                ptr,
                mut data,
                assign,
                expected_data,
                expected,
                ..
            } = self;
            let ptr = Pointer::from_static(ptr);
            let replaced = ptr.assign(&mut data, assign.clone());
            assert_eq!(
                &expected_data, &data,
                "test #{i}:\n\ndata: \n{data:#?}\n\nexpected_data\n{expected_data:#?}"
            );
            assert_eq!(&expected, &replaced);
        }
    }

    #[test]
    #[cfg(feature = "json")]
    fn assign_json() {
        use serde_json::json;
        [
            Test {
                ptr: "/foo",
                data: json!({}),
                assign: json!("bar"),
                expected_data: json!({"foo": "bar"}),
                expected: Ok(None),
            },
            Test {
                ptr: "",
                data: json!({"foo": "bar"}),
                assign: json!("baz"),
                expected_data: json!("baz"),
                expected: Ok(Some(json!({"foo": "bar"}))),
            },
            Test {
                ptr: "/foo",
                data: json!({"foo": "bar"}),
                assign: json!("baz"),
                expected_data: json!({"foo": "baz"}),
                expected: Ok(Some(json!("bar"))),
            },
            Test {
                ptr: "/foo/bar",
                data: json!({"foo": "bar"}),
                assign: json!("baz"),
                expected_data: json!({"foo": {"bar": "baz"}}),
                expected: Ok(Some(json!("bar"))),
            },
            Test {
                ptr: "/foo/bar",
                data: json!({}),
                assign: json!("baz"),
                expected_data: json!({"foo": {"bar": "baz"}}),
                expected: Ok(None),
            },
            Test {
                ptr: "/",
                data: json!({}),
                assign: json!("foo"),
                expected_data: json!({"": "foo"}),
                expected: Ok(None),
            },
            Test {
                ptr: "/-",
                data: json!({}),
                assign: json!("foo"),
                expected_data: json!({"-": "foo"}),
                expected: Ok(None),
            },
            Test {
                ptr: "/-",
                data: json!(null),
                assign: json!(34),
                expected_data: json!([34]),
                expected: Ok(Some(json!(null))),
            },
            Test {
                ptr: "/foo/-",
                data: json!({"foo": "bar"}),
                assign: json!("baz"),
                expected_data: json!({"foo": ["baz"]}),
                expected: Ok(Some(json!("bar"))),
            },
            Test {
                ptr: "/foo/-/bar",
                assign: "baz".into(),
                data: json!({}),
                expected: Ok(None),
                expected_data: json!({"foo":[{"bar": "baz"}]}),
            },
            Test {
                ptr: "/foo/-/bar",
                assign: "qux".into(),
                data: json!({"foo":[{"bar":"baz" }]}),
                expected: Ok(None),
                expected_data: json!({"foo":[{"bar":"baz"},{"bar":"qux"}]}),
            },
            Test {
                ptr: "/foo/-/bar",
                data: json!({"foo":[{"bar":"baz"},{"bar":"qux"}]}),
                assign: "quux".into(),
                expected: Ok(None),
                expected_data: json!({"foo":[{"bar":"baz"},{"bar":"qux"},{"bar":"quux"}]}),
            },
            Test {
                ptr: "/foo/0/bar",
                data: json!({"foo":[{"bar":"baz"},{"bar":"qux"},{"bar":"quux"}]}),
                assign: "grault".into(),
                expected: Ok(Some("baz".into())),
                expected_data: json!({"foo":[{"bar":"grault"},{"bar":"qux"},{"bar":"quux"}]}),
            },
            Test {
                ptr: "/0",
                data: json!({}),
                assign: json!("foo"),
                expected_data: json!({"0": "foo"}),
                expected: Ok(None),
            },
            Test {
                ptr: "/1",
                data: json!(null),
                assign: json!("foo"),
                expected_data: json!({"1": "foo"}),
                expected: Ok(Some(json!(null))),
            },
            Test {
                ptr: "/0",
                data: json!([]),
                expected_data: json!(["foo"]),
                assign: json!("foo"),
                expected: Ok(None),
            },
            Test {
                ptr: "///bar",
                data: json!({"":{"":{"bar": 42}}}),
                assign: json!(34),
                expected_data: json!({"":{"":{"bar":34}}}),
                expected: Ok(Some(json!(42))),
            },
            Test {
                ptr: "/1",
                data: json!([]),
                assign: json!("foo"),
                expected: Err(Error::OutOfBounds {
                    position: 0,
                    offset: 0,
                    source: OutOfBoundsError {
                        index: 1,
                        length: 0,
                    },
                }),
                expected_data: json!([]),
            },
            Test {
                ptr: "/0",
                data: json!(["foo"]),
                assign: json!("bar"),
                expected: Ok(Some(json!("foo"))),
                expected_data: json!(["bar"]),
            },
            Test {
                ptr: "/12a",
                data: json!([]),
                assign: json!("foo"),
                expected: Err(Error::FailedToParseIndex {
                    position: 0,
                    offset: 0,
                    source: ParseIndexError::InvalidCharacter(InvalidCharacterError { offset: 2 }),
                }),
                expected_data: json!([]),
            },
            Test {
                ptr: "/002",
                data: json!([]),
                assign: json!("foo"),
                expected: Err(Error::FailedToParseIndex {
                    position: 0,
                    offset: 0,
                    source: ParseIndexError::LeadingZeros,
                }),
                expected_data: json!([]),
            },
            Test {
                ptr: "/+23",
                data: json!([]),
                assign: json!("foo"),
                expected: Err(Error::FailedToParseIndex {
                    position: 0,
                    offset: 0,
                    source: ParseIndexError::InvalidCharacter(InvalidCharacterError { offset: 0 }),
                }),
                expected_data: json!([]),
            },
        ]
        .into_iter()
        .enumerate()
        .for_each(|(i, t)| t.run(i));
    }

    #[test]
    #[cfg(feature = "toml")]
    fn assign_toml() {
        use alloc::vec;
        use toml::{toml, Table, Value};
        [
            Test {
                data: Value::Table(toml::Table::new()),
                ptr: "/foo",
                assign: "bar".into(),
                expected_data: toml! { "foo" = "bar" }.into(),
                expected: Ok(None),
            },
            Test {
                data: toml! {foo =  "bar"}.into(),
                ptr: "",
                assign: "baz".into(),
                expected_data: "baz".into(),
                expected: Ok(Some(toml! {foo =  "bar"}.into())),
            },
            Test {
                data: toml! { foo = "bar"}.into(),
                ptr: "/foo",
                assign: "baz".into(),
                expected_data: toml! {foo = "baz"}.into(),
                expected: Ok(Some("bar".into())),
            },
            Test {
                data: toml! { foo = "bar"}.into(),
                ptr: "/foo/bar",
                assign: "baz".into(),
                expected_data: toml! {foo = { bar = "baz"}}.into(),
                expected: Ok(Some("bar".into())),
            },
            Test {
                data: Table::new().into(),
                ptr: "/",
                assign: "foo".into(),
                expected_data: toml! {"" =  "foo"}.into(),
                expected: Ok(None),
            },
            Test {
                data: Table::new().into(),
                ptr: "/-",
                assign: "foo".into(),
                expected_data: toml! {"-" = "foo"}.into(),
                expected: Ok(None),
            },
            Test {
                data: "data".into(),
                ptr: "/-",
                assign: 34.into(),
                expected_data: Value::Array(vec![34.into()]),
                expected: Ok(Some("data".into())),
            },
            Test {
                data: toml! {foo = "bar"}.into(),
                ptr: "/foo/-",
                assign: "baz".into(),
                expected_data: toml! {foo =  ["baz"]}.into(),
                expected: Ok(Some("bar".into())),
            },
            Test {
                data: Table::new().into(),
                ptr: "/0",
                assign: "foo".into(),
                expected_data: toml! {"0" = "foo"}.into(),
                expected: Ok(None),
            },
            Test {
                data: 21.into(),
                ptr: "/1",
                assign: "foo".into(),
                expected_data: toml! {"1" = "foo"}.into(),
                expected: Ok(Some(21.into())),
            },
            Test {
                data: Value::Array(vec![]),
                ptr: "/0",
                expected_data: vec![Value::from("foo")].into(),
                assign: "foo".into(),
                expected: Ok(None),
            },
            Test {
                ptr: "/foo/-/bar",
                assign: "baz".into(),
                data: Table::new().into(),
                expected: Ok(None),
                expected_data: toml! { "foo" = [{"bar" = "baz"}] }.into(),
            },
            Test {
                ptr: "/foo/-/bar",
                assign: "qux".into(),
                data: toml! {"foo" = [{"bar" = "baz"}] }.into(),
                expected: Ok(None),
                expected_data: toml! {"foo" = [{"bar" = "baz"}, {"bar" = "qux"}]}.into(),
            },
            Test {
                ptr: "/foo/-/bar",
                data: toml! {"foo" = [{"bar" = "baz"}, {"bar" = "qux"}]}.into(),
                assign: "quux".into(),
                expected: Ok(None),
                expected_data: toml! {"foo" = [{"bar" = "baz"}, {"bar" = "qux"}, {"bar" = "quux"}]}
                    .into(),
            },
            Test {
                ptr: "/foo/0/bar",
                data: toml! {"foo" = [{"bar" = "baz"}, {"bar" = "qux"}, {"bar" = "quux"}]}.into(),
                assign: "grault".into(),
                expected: Ok(Some("baz".into())),
                expected_data:
                    toml! {"foo" = [{"bar" = "grault"}, {"bar" = "qux"}, {"bar" = "quux"}]}.into(),
            },
            Test {
                data: Value::Array(vec![]),
                ptr: "/-",
                assign: "foo".into(),
                expected: Ok(None),
                expected_data: vec!["foo"].into(),
            },
            Test {
                data: Value::Array(vec![]),
                ptr: "/1",
                assign: "foo".into(),
                expected: Err(Error::OutOfBounds {
                    position: 0,
                    offset: 0,
                    source: OutOfBoundsError {
                        index: 1,
                        length: 0,
                    },
                }),
                expected_data: Value::Array(vec![]),
            },
            Test {
                data: Value::Array(vec![]),
                ptr: "/a",
                assign: "foo".into(),
                expected: Err(Error::FailedToParseIndex {
                    position: 0,
                    offset: 0,
                    source: ParseIndexError::InvalidCharacter(InvalidCharacterError { offset: 0 }),
                }),
                expected_data: Value::Array(vec![]),
            },
        ]
        .into_iter()
        .enumerate()
        .for_each(|(i, t)| t.run(i));
    }
}
