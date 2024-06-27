//! # Assign values based on JSON [`Pointer`]s
//!
//! This module provides the [`Assign`] trait which allows for the assignment of
//! values based on a JSON Pointer.
//!
//! ## Feature Flag
//! This module is enabled by default with the `"assign"` feature flag.
//!
//! # Expansion
//! The path will automatically be expanded if the [`Pointer`] is not fully
//! exhausted before reaching a non-existent key in the case of objects, index
//! in the case of arrays, or a scalar value (including `null`) based upon a
//! best-guess effort on the meaning of each [`Token`](crate::Token):
//! - If the [`Token`](crate::Token) is equal to `"0"` or `"-"`, the token will
//!  be considered an index of an array.
//! - All tokens not equal to `"0"` or `"-"` will be considered keys of an
//!   object.
//!
//!
//! ## Provided implementations
//!
//! | Lang  |     value type      | feature flag | Default |
//! | ----- |: ----------------- :|: ---------- :| ------- |
//! | JSON  | `serde_json::Value` |   `"json"`   |   ✓     |
//! | TOML  |    `toml::Value`    |   `"toml"`   |         |
//!
//! ## Example
//! ```rust
//! # use jsonptr::Pointer;
//! # use serde_json::json;
//! let mut data = json!({"foo": "bar"});
//! let ptr = Pointer::from_static("/foo");
//! let replaced = ptr.assign(&mut data, "baz").unwrap();
//! assert_eq!(replaced, Some(json!("bar")));
//! assert_eq!(data, json!({"foo": "baz"}));
//! ```

use crate::{OutOfBoundsError, ParseIndexError, Pointer};
use core::fmt::{self, Debug};

/// Implemented by types which can internally assign a
/// ([`Value`](`Assign::Value`)) at a path represented by a JSON [`Pointer`].
///
/// ## Expansion
/// For provided implementations (`"json"`, and `"toml"`) path will automatically be expanded the if the [`Pointer`] is not fully
/// exhausted before reaching a non-existent key in the case of objects, index
/// in the case of arrays, or a scalar value (including `null`) based upon a
/// best-guess effort on the meaning of each [`Token`](crate::Token):
///
/// - If the [`Token`](crate::Token) is equal to `"0"` or `"-"`, the token will
///  be considered an index of an array.
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

/// Possible error returned from [`Assign`] implementations for
/// [`serde_json::Value`] and
/// [`toml::Value`](https://docs.rs/toml/latest/toml/enum.Value.html).
#[derive(Debug, PartialEq, Eq)]
pub enum AssignError {
    /// A `Token` within the `Pointer` failed to be parsed as an array index.
    FailedToParseIndex {
        /// Offset of the partial pointer starting with the invalid index.
        offset: usize,
        /// The source [`ParseIndexError`]
        source: ParseIndexError,
    },

    /// target array.
    OutOfBounds {
        /// Offset of the partial pointer starting with the invalid index.
        offset: usize,
        /// The source [`OutOfBoundsError`]
        source: OutOfBoundsError,
    },
}

impl fmt::Display for AssignError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FailedToParseIndex { offset, .. } => {
                write!(
                    f,
                    "assignment failed due to an invalid index at offset {offset}"
                )
            }
            Self::OutOfBounds { offset, .. } => {
                write!(
                    f,
                    "assignment failed due to index at offset {offset} being out of bounds"
                )
            }
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for AssignError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::FailedToParseIndex { source, .. } => Some(source),
            Self::OutOfBounds { source, .. } => Some(source),
        }
    }
}

enum Assigned<'v, V> {
    Done(Option<V>),
    Continue { next_dest: &'v mut V, same_value: V },
}

mod json {
    use super::{Assign, AssignError, Assigned};
    use crate::{Pointer, Token};
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
        type Error = AssignError;
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
    ) -> Result<Option<Value>, AssignError> {
        let mut offset = 0;

        while let Some((token, tail)) = ptr.split_front() {
            let tok_len = token.encoded().len();

            let assigned = match dest {
                Value::Array(array) => assign_array(token, tail, array, value, offset)?,
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
        offset: usize,
    ) -> Result<Assigned<'v, Value>, AssignError> {
        // parsing the index
        let idx = token
            .to_index()
            .map_err(|source| AssignError::FailedToParseIndex { offset, source })?
            .for_len_incl(array.len())
            .map_err(|source| AssignError::OutOfBounds { offset, source })?;

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

    #[cfg(test)]
    #[cfg(feature = "serde")]
    mod tests {
        use crate::{Pointer, PointerBuf};
        use insta::{assert_debug_snapshot, assert_snapshot};
        use serde::Serialize;
        use serde_json::{json, Value};

        #[derive(Serialize, Debug)]
        struct Test {
            data: Value,
            ptr: &'static str,
            assign: Value,
        }

        impl Test {
            fn all(tests: impl IntoIterator<Item = Test>) {
                tests.into_iter().for_each(Test::run);
            }
            fn run(self) {
                let mut data = self.data.clone();

                let ptr = Pointer::from_static(self.ptr);
                let replaced = ptr.assign(&mut data, self.assign.clone());
                let mut s = insta::Settings::new();

                s.set_info(&self);
                insta::with_settings!({
                    info => &self,
                    description => "asserting that the JSON data is as expected after assignment",
                    omit_expression => true // do not include the default expression
                }, {
                    assert_snapshot!(&data);
                });
                insta::with_settings!({
                    info => &self,
                    description => "asserting that the replaced JSON data returned from the assignment is as expected",
                    omit_expression => true // do not include the default expression
                }, {
                    assert_debug_snapshot!(&replaced);
                });
            }
        }

        #[test]
        #[allow(clippy::too_many_lines)]
        fn test_assign() {
            Test::all([
                Test {
                    ptr: "/foo",
                    data: json!({}),
                    assign: json!("bar"),
                },
                Test {
                    ptr: "",
                    data: json!({"foo": "bar"}),
                    assign: json!("baz"),
                },
                Test {
                    ptr: "/foo",
                    data: json!({"foo": "bar"}),
                    assign: json!("baz"),
                },
                Test {
                    ptr: "/foo/bar",
                    data: json!({"foo": "bar"}),
                    assign: json!("baz"),
                },
                Test {
                    ptr: "/",
                    data: json!({}),
                    assign: json!("foo"),
                },
                Test {
                    ptr: "/-",
                    data: json!({}),
                    assign: json!("foo"),
                },
                Test {
                    ptr: "/-",
                    data: json!(null),
                    assign: json!(34),
                },
                Test {
                    ptr: "/foo/-",
                    data: json!({"foo": "bar"}),
                    assign: json!("baz"),
                },
                Test {
                    ptr: "/0",
                    data: json!({}),
                    assign: json!("foo"),
                },
                Test {
                    ptr: "/1",
                    data: json!(null),
                    assign: json!("foo"),
                },
                Test {
                    ptr: "/0",
                    data: json!([]),
                    assign: json!("foo"),
                },
                Test {
                    ptr: "/1",
                    data: json!([]),
                    assign: json!("foo"),
                },
                Test {
                    ptr: "/a",
                    data: json!([]),
                    assign: json!("foo"),
                },
            ]);
        }

        #[test]
        fn test_assign_with_explicit_array_path() {
            let mut data = json!({});
            let ptr = Pointer::from_static("/foo/0/bar");
            let val = json!("baz");

            let replaced = ptr.assign(&mut data, val).unwrap();
            assert_eq!(replaced, None);
            assert_eq!(&data, &json!({"foo": [{"bar": "baz"}]}),);
        }

        #[test]
        fn test_assign_array_with_next_token() {
            Test::all([
                Test {
                    ptr: "/foo/-/bar",
                    assign: "baz".into(),
                    data: json!({}),
                    // expected_result: Ok(None),
                    // expected_data: json!({"foo":[{"bar": "baz"}]})
                },
                Test {
                    ptr: "/foo/-/bar",
                    assign: "qux".into(),
                    data: json!({"foo":[{"bar":"baz" }]}),
                },
                Test {
                    ptr: "/foo/-/bar",
                    data: json!({"foo":[{"bar":"baz"},{"bar":"qux"}]}),
                    assign: "quux".into(),
                },
                Test {
                    ptr: "/foo/0/bar",
                    data: json!({"foo":[{"bar":"baz"},{"bar":"qux"},{"bar":"quux"}]}),
                    assign: "grault".into(),
                },
            ]);
        }

        #[test]
        fn test_assign_with_obj_path() {
            let mut data = json!({});
            let ptr = Pointer::from_static("/foo/bar");
            let val = json!("baz");
            let replaced = ptr.assign(&mut data, val).unwrap();
            assert_eq!(&json!({"foo": {"bar": "baz"}}), &data);
            assert_eq!(replaced, None);
        }

        #[test]
        fn test_assign_with_scalar_replace() {
            let mut data = json!({
                "foo": "bar"
            });

            let ptr = Pointer::from_static("/foo/bar/baz");
            let val = json!("qux");

            ptr.assign(&mut data, val).unwrap();
            assert_eq!(&json!({"foo":{"bar":{"baz": "qux"}}}), &data);
        }

        #[test]
        fn nested_maps_with_empty_keys() {
            let data = json!({
                "": {
                    "": {
                        "bar": 42,
                    }
                }
            });

            {
                let ptr = Pointer::from_static("///bar");
                assert_eq!(ptr.resolve(&data).unwrap(), 42);
            }
            {
                let mut ptr = PointerBuf::new();
                ptr.push_back("".into());
                ptr.push_back("".into());
                ptr.push_back("bar".into());
                assert_eq!(ptr.resolve(&data).unwrap(), 42);
            }
        }
    }
}

#[cfg(feature = "toml")]
mod toml {
    use super::{Assign, AssignError, Assigned};
    use crate::{Pointer, Token};
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
        type Error = AssignError;
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
    ) -> Result<Option<Value>, AssignError> {
        let mut offset = 0;

        while let Some((token, tail)) = ptr.split_front() {
            let tok_len = token.encoded().len();

            let assigned = match dest {
                Value::Array(array) => assign_array(token, tail, array, value, offset)?,
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
        offset: usize,
    ) -> Result<Assigned<'v, Value>, AssignError> {
        // parsing the index
        let idx = token
            .to_index()
            .map_err(|source| AssignError::FailedToParseIndex { offset, source })?
            .for_len_incl(array.len())
            .map_err(|source| AssignError::OutOfBounds { offset, source })?;

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
        Assigned::Done(Some(mem::replace(scalar, expand(remaining, value))))
    }

    #[cfg(test)]
    mod tests {
        use crate::Pointer;
        use ::toml::{toml, Value};
        use insta::{assert_debug_snapshot, assert_snapshot};
        use serde::Serialize;
        use toml::Table;

        #[derive(Serialize, Debug)]
        struct Test {
            data: Value,
            ptr: &'static str,
            assign: Value,
        }

        impl Test {
            fn all(tests: impl IntoIterator<Item = Test>) {
                tests.into_iter().for_each(Test::run);
            }
            fn run(self) {
                let mut data = self.data.clone();

                let ptr = Pointer::from_static(self.ptr);
                let replaced = ptr.assign(&mut data, self.assign.clone());
                let mut s = insta::Settings::new();

                s.set_info(&self);
                insta::with_settings!({
                    info => &self,
                    description => "asserting that the TOML data is as expected after assignment",
                    omit_expression => true // do not include the default expression
                }, {
                    assert_snapshot!(&data);
                });
                insta::with_settings!({
                    info => &self,
                    description => "asserting that the replaced TOML data returned from the assignment is as expected",
                    omit_expression => true // do not include the default expression
                }, {
                    assert_debug_snapshot!(&replaced);
                });
            }
        }

        #[test]
        #[allow(clippy::too_many_lines)]
        fn test_assign() {
            Test::all([
                Test {
                    data: Value::Table(toml::Table::new()),
                    ptr: "/foo",
                    assign: "bar".into(),
                },
                Test {
                    data: toml! {foo =  "bar"}.into(),
                    ptr: "",
                    assign: "baz".into(),
                },
                Test {
                    data: toml! { foo = "bar"}.into(),
                    ptr: "/foo",
                    assign: "baz".into(),
                },
                Test {
                    data: toml! { foo = "bar"}.into(),
                    ptr: "/foo/bar",
                    assign: "baz".into(),
                },
                Test {
                    data: Table::new().into(),
                    ptr: "/",
                    assign: "foo".into(),
                },
                Test {
                    data: Table::new().into(),
                    ptr: "/-",
                    assign: "foo".into(),
                },
                Test {
                    data: "data".into(),
                    ptr: "/-",
                    assign: 34.into(),
                },
                Test {
                    data: toml! {foo = "bar"}.into(),
                    ptr: "/foo/-",
                    assign: "baz".into(),
                },
                Test {
                    data: Table::new().into(),
                    ptr: "/0",
                    assign: "foo".into(),
                },
                Test {
                    data: 21.into(),
                    ptr: "/1",
                    assign: "foo".into(),
                },
                Test {
                    data: Value::Array(vec![]),
                    ptr: "/0",
                    assign: "foo".into(),
                },
                Test {
                    data: Value::Array(vec![]),
                    ptr: "/-",
                    assign: "foo".into(),
                },
                Test {
                    data: Value::Array(vec![]),
                    ptr: "/1",
                    assign: "foo".into(),
                },
                Test {
                    data: Value::Array(vec![]),
                    ptr: "/a",
                    assign: "foo".into(),
                },
            ]);
        }

        #[test]
        fn test_assign_with_explicit_array_path() {
            let mut data: Value = Table::new().into();
            let ptr = Pointer::from_static("/foo/0/bar");
            let val: Value = "baz".into();

            let replaced = ptr.assign(&mut data, val).unwrap();
            assert_eq!(replaced, None);
            assert_eq!(&data, &(toml! {"foo" = [{"bar" = "baz"}]}.into()));
        }

        #[test]
        fn test_assign_array_with_next_token() {
            Test::all([
                Test {
                    ptr: "/foo/-/bar",
                    assign: "baz".into(),
                    data: Table::new().into(),
                },
                Test {
                    ptr: "/foo/-/bar",
                    assign: "qux".into(),
                    data: toml! { "foo" = [{ "bar" = "baz" }] }.into(),
                },
                Test {
                    ptr: "/foo/-/bar",
                    data: toml! {"foo" = [{ "bar" = "baz" }, { "bar" = "qux" }]}.into(),
                    assign: "quux".into(),
                },
                Test {
                    ptr: "/foo/0/bar",
                    data: toml! {"foo" = [{"bar" = "baz"},{"bar" = "qux"},{"bar" = "quux"}]}.into(),
                    assign: "grault".into(),
                },
            ]);
        }

        // #[test]
        // fn test_assign_with_obj_path() {
        //     let mut data = json!({});
        //     let ptr = Pointer::from_static("/foo/bar");
        //     let val = json!("baz");
        //     let replaced = ptr.assign(&mut data, val).unwrap();
        //     assert_eq!(&json!({"foo": {"bar": "baz"}}), &data);
        //     assert_eq!(replaced, None);
        // }

        // #[test]
        // fn test_assign_with_scalar_replace() {
        //     let mut data = json!({
        //         "foo": "bar"
        //     });

        //     let ptr = Pointer::from_static("/foo/bar/baz");
        //     let val = json!("qux");

        //     ptr.assign(&mut data, val).unwrap();
        //     assert_eq!(&json!({"foo":{"bar":{"baz": "qux"}}}), &data);
        // }

        // #[test]
        // fn nested_maps_with_empty_keys() {
        //     let data = json!({
        //         "": {
        //             "": {
        //                 "bar": 42,
        //             }
        //         }
        //     });

        //     {
        //         let ptr = Pointer::from_static("///bar");
        //         assert_eq!(ptr.resolve(&data).unwrap(), 42);
        //     }
        //     {
        //         let mut ptr = PointerBuf::new();
        //         ptr.push_back("".into());
        //         ptr.push_back("".into());
        //         ptr.push_back("bar".into());
        //         assert_eq!(ptr.resolve(&data).unwrap(), 42);
        //     }
        // }
    }
}
