use core::fmt::{self, Debug};

use crate::{OutOfBoundsError, ParseIndexError, Pointer, PointerBuf};

#[cfg(feature = "std")]
type BoxedError = Box<dyn 'static + std::error::Error>;

#[cfg(not(feature = "std"))]
type BoxedError = Box<dyn 'static + core::fmt::Debug + core::fmt::Display>;

/// Assign is implemented by types which can internally assign a
/// [`serde_json::Value`] by a JSON Pointer.
pub trait Assign {
    /// The type of value that is being assigned.
    ///
    /// Provided implementations include:
    ///
    /// | Lang  |     value type      | feature flag |
    /// | ----- | ------------------- |: ---------- :|
    /// | JSON  | `serde_json::Value` |   `"json"`   |
    /// | YAML  | `serde_json::Value` |   `"yaml"`   |
    /// | TOML  | `serde_json::Value` |   `"toml"`   |
    type Value;
    /// Error associated with `Assign`
    type Error: From<AssignError>;
    /// Assign a value of based on the path provided by a JSON Pointer.
    fn assign<'v>(
        &'v mut self,
        ptr: &Pointer,
        value: Self::Value,
        expansion: Expansion<'_, Self::Value>,
    ) -> Result<Assignment<'v, Self::Value>, Self::Error>;
}

pub trait Expand<V> {
    /// - `token`: The current token
    /// - `ptr`: The pointer prior to `tok`
    fn expand(&self, path: &Pointer, src: V) -> Result<V, AssignError>;
}

impl<V> Expand<V> for () {
    fn expand(&self, path: &Pointer, src: V) -> Result<V, AssignError> {
        if path.is_root() {
            Ok(src)
        } else {
            Err(AssignError::FailedToExpand {
                offset: 0,
                source: "Expansion strategy not provided".into(),
            })
        }
    }
}

#[derive(Default)]
pub enum Expansion<'e, V> {
    /// This strategy will automatically expand the path of the [`Pointer`] if a
    /// the `Pointer` is not fully exhausted before reaching a non-existent key
    /// in the case of objects, or scalar value.
    ///
    /// If a scalar or non-existent path is encountered before the [`Pointer`]
    /// is exhausted, the path will automatically be expanded into
    /// [`Assign::Value`] based upon a best-guess effort on the meaning of each
    /// [`Token`]:
    /// - If the [`Token`] is equal to `"0"` or `"-"`, the token will be
    ///  considered an index of an array.
    /// - All tokens not equal to `"0"` or `"-"` will be considered keys of an
    ///   object.
    ///  
    ///  Note: This strategy will not return [`AssignError::NotFound`] or
    ///  [`AssignError::Unreachable`].
    ///
    BestGuess,

    /// This strategy will error if the [`Pointer`] is not fully exhausted before
    /// a scalar or non-existent key or [`Index`](crate::Index) is encountered.
    #[default]
    Never,

    /// This strategy allows for a custom implementation of [`Expand`] to be
    /// provided.
    Custom(&'e dyn Expand<V>),
}

impl<'e, V> Debug for Expansion<'e, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expansion::BestGuess => write!(f, "Expansion::BestGuess"),
            Expansion::Never => write!(f, "Expansion::Never"),
            Expansion::Custom(_) => write!(f, "Expansion::Custom"),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
/// The data structure returned from a successful call to `assign`.
pub struct Assignment<'v, V> {
    /// The value that was assigned.
    ///
    /// In the event a path is created, this will be a mutable reference to the
    /// `serde_json::Value` encompassing the new branch.
    pub assigned: &'v mut V,

    /// The path which was assigned to.
    ///
    /// If some or all of the path must be created, this will be the path to the
    /// top-level value that was assigned. For example, given the json `{ "foo":
    /// { "bar": "baz" } }`, if `"new_value"` is assigned to `"/foo/qux/quux"`,
    /// then `assigned_to` would equal `"/foo/qux"` as `"qux"` is the top-level
    /// value assigned.
    ///
    /// The resulting json would have the following structure:
    /// ```json
    /// {
    ///     "foo": {
    ///        "bar": "baz",
    ///         "qux": {
    ///             "quux": "new_value"
    ///         }
    ///     }
    /// }
    /// ```
    ///
    /// Note: if a portion of the path contains a leaf node that is to be
    /// overridden by an object or an array, then the path will be leaf that is
    /// replaced. For example, given the json `{ "foo:" "bar" }`, if `"new_value"` is
    /// assigned to `"/foo/bar/baz"`, then `assigned_to` would be `/foo/bar"`
    ///
    /// ## Example
    /// ```rust
    /// # use serde_json::json;
    /// # use jsonptr::{Pointer, Assign, Expansion};
    /// let mut data = json!({ "foo": ["zero"] });
    /// let mut ptr = Pointer::from_static("/foo/-");
    /// let assignment = data.assign(&mut ptr, "one", Expansion::Enabled).unwrap();
    /// assert_eq!(assignment.assigned_to, Pointer::from_static("/foo/1"));
    /// ```
    pub assigned_to: PointerBuf,

    /// The value that was replaced, if any.
    pub replaced: Option<V>,
}

///
#[derive(Debug)]
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

    /// An error occurred while expanding the path.
    FailedToExpand {
        /// Offset of the partial pointer which triggered the expansion error.
        offset: usize,
        /// Underlying
        source: BoxedError,
    },
}

impl PartialEq for AssignError {
    fn eq(&self, other: &Self) -> bool {
        match self {
            Self::FailedToParseIndex { offset, source } => {
                let Self::FailedToParseIndex {
                    offset: o,
                    source: s,
                } = other
                else {
                    return false;
                };
                offset == o && source == s
            }
            Self::OutOfBounds { offset, source } => {
                let Self::OutOfBounds {
                    offset: o,
                    source: s,
                } = other
                else {
                    return false;
                };
                offset == o && source == s
            }
            Self::FailedToExpand { offset, source } => {
                let Self::FailedToExpand {
                    offset: o,
                    source: s,
                } = other
                else {
                    return false;
                };
                // not ideal to allocate here but its the only way I can think
                // of to get `PartialEq` on `Box<dyn Error>`
                //
                // I'm guessing this will only be used in tests but it may be
                // worth an error enum specifically for expansion or dumping
                // `PartialEq`
                offset == o && source.to_string() == s.to_string()
            }
        }
    }
}

impl fmt::Display for AssignError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FailedToParseIndex { offset, .. } => {
                write!(f, "failed to parse index at offset {}", offset)
            }
            Self::OutOfBounds { offset, .. } => {
                write!(f, "index at offset {} out of bounds", offset)
            }
            Self::FailedToExpand { source, .. } => {
                write!(f, "{source}")
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
            Self::FailedToExpand { source, .. } => Some(source.as_ref()),
        }
    }
}

enum Assigned<'v, V> {
    Done(Assignment<'v, V>),
    Continue {
        next_buf: PointerBuf,
        next_value: &'v mut V,
        same_src: V,
    },
}

#[cfg(feature = "json")]
mod json {
    use super::*;
    use crate::{Pointer, PointerBuf, Token};
    use core::mem;
    use serde_json::{map::Entry, Map, Value};

    impl Expand<Value> for Expansion<'_, Value> {
        fn expand(&self, path: &Pointer, src: Value) -> Result<Value, AssignError> {
            match self {
                Expansion::BestGuess => expand_auto(path, src),
                Expansion::Never => expand_error(path, src),
                Expansion::Custom(e) => e.expand(path, src),
            }
        }
    }

    fn expand_auto(mut path: &Pointer, mut src: Value) -> Result<Value, AssignError> {
        while let Some((ptr, tok)) = path.split_back() {
            path = ptr;
            match tok.decoded().as_ref() {
                "0" | "-" => {
                    src = Value::Array(vec![src]);
                }
                _ => {
                    let mut obj = Map::new();
                    obj.insert(tok.to_string(), src);
                    src = Value::Object(obj);
                }
            }
        }
        Ok(src)
    }

    fn expand_error(path: &Pointer, src: Value) -> Result<Value, AssignError> {
        todo!()
    }

    impl Assign for Value {
        type Value = Value;
        type Error = AssignError;
        fn assign<'v>(
            &'v mut self,
            ptr: &Pointer,
            value: Self::Value,
            expansion: Expansion<'_, Self::Value>,
        ) -> Result<Assignment<'v, Self::Value>, Self::Error> {
            assign_value(ptr, self, value, expansion)
        }
    }

    pub(crate) fn assign_value<'v>(
        mut ptr: &Pointer,
        mut value: &'v mut Value,
        mut src: Value,
        expansion: Expansion<'_, Value>,
    ) -> Result<Assignment<'v, Value>, AssignError> {
        let mut offset = 0;
        let mut buf = PointerBuf::with_capacity(ptr.as_str().len());

        while let Some((token, tail)) = ptr.split_front() {
            let tok_len = token.encoded().chars().count();

            let assigned = match value {
                Value::Array(array) => {
                    assign_array(token, tail, buf, array, src, offset, &expansion)?
                }
                Value::Object(obj) => assign_object(token, tail, buf, obj, src, &expansion)?,
                _ => assign_scalar(token, ptr, buf, value, src, &expansion)?,
            };
            match assigned {
                Assigned::Done(assignment) => {
                    return Ok(assignment);
                }
                Assigned::Continue {
                    next_buf,
                    next_value,
                    same_src,
                } => {
                    buf = next_buf;
                    src = same_src;
                    value = next_value;
                    ptr = tail;
                }
            }
            offset += 1 + tok_len;
        }

        // Pointer is root, we can replace `dest` directly
        let replaced = Some(core::mem::replace(value, src.into()));
        Ok(Assignment {
            assigned: value,
            replaced,
            assigned_to: buf,
        })
    }

    fn assign_array<'v>(
        token: Token<'_>,
        remaining: &Pointer,
        mut buf: PointerBuf,
        array: &'v mut Vec<Value>,
        src: Value,
        offset: usize,
        expansion: &Expansion<'_, Value>,
    ) -> Result<Assigned<'v, Value>, AssignError> {
        // parsing the index
        let idx = token
            .to_index()
            .map_err(|source| AssignError::FailedToParseIndex { offset, source })?
            .for_len_incl(array.len())
            .map_err(|source| AssignError::OutOfBounds { offset, source })?;
        buf.push_back(idx.into());

        debug_assert!(idx <= array.len());

        if idx < array.len() {
            // element exists in the array, we either need to replace it or continue
            // depending on whether this is the last token or not
            if remaining.is_root() {
                // last token, we replace the value and call it a day
                let assigned = array
                    .last_mut()
                    .expect("non-empty array should have last_mut");
                Ok(Assigned::Done(Assignment {
                    assigned,
                    assigned_to: buf,
                    replaced: None,
                }))
            } else {
                // not the last token, we continue with a mut ref to the element as
                // the next value
                Ok(Assigned::Continue {
                    next_value: &mut array[idx],
                    same_src: src,
                    next_buf: buf,
                })
            }
        } else {
            // element does not exist in the array.
            // we create the path and assign the value
            let src = expansion.expand(remaining, src)?;
            array.push(src);
            let assigned = array.last_mut().expect("just pushed");
            Ok(Assigned::Done(Assignment {
                assigned,
                assigned_to: buf,
                replaced: None,
            }))
        }
    }

    fn assign_object<'v>(
        token: Token<'_>,
        remaining: &Pointer,
        mut buf: PointerBuf,
        obj: &'v mut Map<String, Value>,
        src: Value,
        expansion: &Expansion<'_, Value>,
    ) -> Result<Assigned<'v, Value>, AssignError> {
        // grabbing the entry of the token
        let entry = obj.entry(token.to_string());
        // adding token to the pointer buf
        buf.push_back(token);

        match entry {
            Entry::Occupied(entry) => {
                // if the entry exists, we either replace it or continue
                let entry = entry.into_mut();
                if remaining.is_root() {
                    // if this is the last token, we are done
                    // grab the old value and replace it with the new one
                    let replaced = Some(mem::replace(entry, src));
                    Ok(Assigned::Done(Assignment {
                        assigned: entry,
                        assigned_to: buf,
                        replaced,
                    }))
                } else {
                    // if this is not the last token, we continue with a mutable
                    // reference to the entry as the next value
                    Ok(Assigned::Continue {
                        same_src: src,
                        next_buf: buf,
                        next_value: entry,
                    })
                }
            }
            Entry::Vacant(entry) => {
                // if the entry does not exist, we create a value based on the
                // remaining path with the src value as a leaf and assign it to the
                // entry
                let src = expansion.expand(remaining, src)?;
                let assigned = entry.insert(src);
                Ok(Assigned::Done(Assignment {
                    assigned,
                    assigned_to: buf,
                    replaced: None,
                }))
            }
        }
    }

    fn assign_scalar<'v>(
        token: Token<'_>,
        remaining: &'_ Pointer,
        mut buf: PointerBuf,
        value: &'v mut Value,
        src: Value,
        expansion: &Expansion<'_, Value>,
    ) -> Result<Assigned<'v, Value>, AssignError> {
        // scalar values are always replaced at the current buf (with its token)
        // build the new src and we replace the value with it.

        buf.push_back(token);
        let src = expansion.expand(remaining, src)?;
        let replaced = Some(mem::replace(value, src));

        Ok(Assigned::Done(Assignment {
            assigned: value,
            assigned_to: buf,
            replaced,
        }))
    }

    #[cfg(test)]
    mod tests {
        use core::str::FromStr;

        use serde_json::{json, Value};

        use crate::{assign::Expansion, AssignError, ParseIndexError, Pointer, PointerBuf};

        #[test]
        fn test_assign_error_partial_eq() {
            assert_eq!(
                AssignError::FailedToParseIndex {
                    offset: 0,
                    source: ParseIndexError {
                        source: usize::from_str("invalid").unwrap_err()
                    }
                },
                AssignError::FailedToParseIndex {
                    offset: 0,
                    source: ParseIndexError {
                        source: usize::from_str("invalid").unwrap_err()
                    }
                }
            );
            assert_eq!(
                AssignError::FailedToParseIndex {
                    offset: 0,
                    source: ParseIndexError {
                        source: usize::from_str("invalid").unwrap_err()
                    }
                },
                AssignError::FailedToParseIndex {
                    offset: 0,
                    source: ParseIndexError {
                        source: usize::from_str("different-invalid").unwrap_err()
                    }
                },
            );
            assert_eq!(
                AssignError::OutOfBounds {
                    offset: 0,
                    source: crate::OutOfBoundsError {
                        length: 3,
                        index: 5
                    }
                },
                AssignError::OutOfBounds {
                    offset: 0,
                    source: crate::OutOfBoundsError {
                        length: 3,
                        index: 5
                    }
                },
            );
            assert_eq!(
                AssignError::FailedToExpand {
                    offset: 0,
                    source: "error".into()
                },
                AssignError::FailedToExpand {
                    offset: 0,
                    source: "error".into()
                },
            );
        }

        #[test]
        fn test_assign() {
            let mut data = json!({});

            let ptr = Pointer::from_static("/foo");
            let val = json!("bar");

            let assignment = ptr
                .assign(&mut data, val.clone(), Expansion::BestGuess)
                .unwrap();
            assert_eq!(assignment.replaced, None);
            assert_eq!(assignment.assigned, &val);
            assert_eq!(assignment.assigned_to, "/foo");

            // now testing replacement
            let val2 = json!("baz");
            let assignment = ptr
                .assign(&mut data, val2.clone(), Expansion::BestGuess)
                .unwrap();
            assert_eq!(assignment.replaced, Some(Value::String("bar".to_string())));
            assert_eq!(assignment.assigned, &val2);
            assert_eq!(assignment.assigned_to, "/foo");

            // let tests = [
            //     (
            //         // `pointer` of the assignment
            //         "/foo",
            //         // value to assign
            //         json!("bar"),
            //         // `Expand` strategy
            //         Expansion::BestGuess,
            //         // expected `Result`
            //         Ok(Assignment {
            //             assigned: &mut placeholder,
            //             assigned_to: PointerBuf::from_str("/foo").unwrap(),
            //             replaced: None,
            //         }),
            //         // expected assigned
            //         Some(json!("bar")),
            //         // expected replaced
            //         None,
            //         // expected data
            //         json!({"foo": "bar"}),
            //     ),
            //     (
            //         "/foo/list",
            //         json!([]),
            //         Expansion::BestGuess,
            //         Ok(Assignment {
            //             assigned: &mut placeholder,
            //             assigned_to: PointerBuf::from_str("/foo").unwrap(),
            //             replaced: Some(json!("bar")),
            //         }),
            //         // expected assigned
            //         Some(json!({ "list": [] })),
            //         // expected replaced
            //         Some(json!("bar")),
            //         json!({"foo": { "list": []}}),
            //     ),
            // ];
            // for (
            //     pointer,
            //     value,
            //     expand,
            //     expected_result,
            //     expected_assigned,
            //     expected_replaced,
            //     expected_data,
            // ) in tests
            // {
            //     let ptr = PointerBuf::from_str(pointer).unwrap();
            //     let assignment = ptr.assign(&mut data, value, expand);
            //     assert_eq!(assignment, expected_result);
            //     assert_eq!(data, expected_data);
            // }
        }

        #[test]
        fn test_assign_with_explicit_array_path() {
            let mut data = json!({});
            let ptr = Pointer::from_static("/foo/0/bar");
            let val = json!("baz");

            let assignment = ptr.assign(&mut data, val, Expansion::BestGuess).unwrap();
            assert_eq!(assignment.replaced, None);
            assert_eq!(assignment.assigned_to, "/foo");
            assert_eq!(assignment.replaced, None);
            assert_eq!(
                json!({
                    "foo": [
                        {
                            "bar": "baz"
                        }
                    ]
                }),
                data.clone()
            );
        }

        #[test]
        fn test_assign_array_with_next_token() {
            let mut data = json!({});

            let tests = [
                (
                    "/foo/-/bar",
                    "/foo",
                    json!("baz"),
                    json!({ "foo": [{ "bar": "baz" }] }),
                    None,
                ),
                (
                    "/foo/-/bar",
                    "/foo/1",
                    json!("qux"),
                    json!({"foo": [{ "bar": "baz" }, { "bar": "qux" }]
                    }),
                    None,
                ),
                (
                    "/foo/-/bar",
                    "/foo/2",
                    json!("quux"),
                    json!({
                        "foo": [
                            { "bar": "baz" },
                            { "bar": "qux" },
                            { "bar": "quux" }
                        ]
                    }),
                    None,
                ),
                (
                    "/foo/0/bar",
                    "/foo/0/bar",
                    json!("grault"),
                    json!({
                        "foo": [
                            { "bar": "grault" },
                            { "bar": "qux" },
                            { "bar": "quux" }
                        ]
                    }),
                    Some(json!("baz")),
                ),
            ];

            for (path, assigned_to, val, expected, replaced) in tests {
                println!("{}", serde_json::to_string_pretty(&data).unwrap());
                let ptr = PointerBuf::parse(path).expect(&format!("failed to parse \"{path}\""));
                let assignment = ptr
                    .assign(&mut data, val.clone(), Expansion::BestGuess)
                    .expect(&format!("failed to assign \"{path}\""));
                assert_eq!(
                    assignment.assigned_to, *assigned_to,
                    "assigned_to not equal"
                );
                assert_eq!(assignment.replaced, replaced, "replaced not equal");
                assert_eq!(&expected, &data);
            }
        }

        #[test]
        fn test_assign_with_obj_path() {
            let mut data = json!({});
            let ptr = PointerBuf::try_from("/foo/bar").unwrap();
            let val = json!("baz");

            let assignment = ptr.assign(&mut data, val, Expansion::BestGuess).unwrap();
            assert_eq!(assignment.assigned_to, "/foo");
            assert_eq!(assignment.replaced, None);
            assert_eq!(
                &json!({
                    "foo": {
                        "bar": "baz"
                    }
                }),
                &data
            );
        }

        #[test]
        fn test_assign_with_scalar_replace() {
            let mut data = json!({
                "foo": "bar"
            });

            let ptr = Pointer::from_static("/foo/bar/baz");
            let val = json!("qux");

            ptr.assign(&mut data, val, Expansion::BestGuess).unwrap();
            assert_eq!(
                &json!({
                    "foo": {
                        "bar": {
                            "baz": "qux"
                        }
                    }
                }),
                &data
            );
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
