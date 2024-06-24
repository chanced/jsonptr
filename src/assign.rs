use crate::{OutOfBoundsError, ParseIndexError, Pointer};
use core::fmt::{self, Debug};

/// Implemented by types which can internally assign a
/// ([`Value`](`Assign::Value`)) at a path represented by a JSON [`Pointer`].
///
/// ## Expansion
/// The path will automatically be expanded the if the [`Pointer`] is not fully
/// exhausted before reaching a non-existent key in the case of objects, index
/// in the case of arrays, or a scalar value (including `null`) based upon
/// a best-guess effort on the meaning of each [`Token`](crate::Token):
///
/// - If the [`Token`](crate::Token) is equal to `"0"` or `"-"`, the token will
///  be considered an index of an array.
/// - All tokens not equal to `"0"` or `"-"` will be considered keys of an
///   object.
///
/// ## Examples
///
/// ### Successful assignment with replacement
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

/// This example uses the special `"-"` token (per RFC 6901) to represent the
/// next element in an array.
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
///
///
/// ## Provided implementations
///
/// | Language  | Feature Flag |
/// | --------- | ------------ |
/// |   JSON    |   `"json"`   |
/// |   TOML    |   `"toml"`   |
pub trait Assign {
    /// The type of value that this implementation can operate on.
    ///
    /// Provided implementations include:
    ///
    /// | Lang  |     value type      | feature flag |
    /// | ----- |: ----------------- :|: ---------- :|
    /// | JSON  | `serde_json::Value` |   `"json"`   |
    /// | TOML  |    `toml::Value`    |   `"toml"`   |
    type Value;

    /// Error associated with `Assign`
    type Error;

    /// Assigns a value of based on the path provided by a JSON Pointer,
    /// returning the replaced value, if any.
    fn assign<'v, V>(
        &'v mut self,
        ptr: &Pointer,
        value: V,
    ) -> Result<Option<Self::Value>, Self::Error>
    where
        V: Into<Self::Value>;
}

///
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

#[cfg(feature = "json")]
mod json {
    use super::*;
    use crate::{Pointer, Token};
    use core::mem;
    use serde_json::{map::Entry, Map, Value};

    fn expand(mut remaining: &Pointer, mut value: Value) -> Value {
        while let Some((ptr, tok)) = remaining.split_back() {
            remaining = ptr;
            match tok.encoded().as_ref() {
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
        fn assign<'v, V>(
            &'v mut self,
            ptr: &Pointer,
            value: V,
        ) -> Result<Option<Self::Value>, Self::Error>
        where
            V: Into<Self::Value>,
        {
            assign_value(ptr, self, value.into())
        }
    }

    pub(crate) fn assign_value<'v>(
        mut ptr: &Pointer,
        mut dest: &'v mut Value,
        mut value: Value,
    ) -> Result<Option<Value>, AssignError> {
        let mut offset = 0;

        while let Some((token, tail)) = ptr.split_front() {
            let tok_len = token.encoded().chars().count();

            let assigned = match dest {
                Value::Array(array) => assign_array(token, tail, array, value, offset)?,
                Value::Object(obj) => assign_object(token, tail, obj, value)?,
                _ => assign_scalar(ptr, dest, value)?,
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
        let replaced = Some(core::mem::replace(dest, value.into()));
        Ok(replaced)
    }

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

    fn assign_object<'v>(
        token: Token<'_>,
        remaining: &Pointer,
        obj: &'v mut Map<String, Value>,
        src: Value,
    ) -> Result<Assigned<'v, Value>, AssignError> {
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
                    Ok(Assigned::Done(Some(mem::replace(entry, src))))
                } else {
                    // if this is not the last token, we continue with a mutable
                    // reference to the entry as the next value
                    Ok(Assigned::Continue {
                        same_value: src,
                        next_dest: entry,
                    })
                }
            }
            Entry::Vacant(entry) => {
                // if the entry does not exist, we create a value based on the
                // remaining path with the src value as a leaf and assign it to the
                // entry
                entry.insert(expand(remaining, src));
                Ok(Assigned::Done(None))
            }
        }
    }

    fn assign_scalar<'v>(
        remaining: &Pointer,
        scalar: &'v mut Value,
        value: Value,
    ) -> Result<Assigned<'v, Value>, AssignError> {
        // scalar values are always replaced at the current buf (with its token)
        // build the new src and we replace the value with it.
        let replaced = Some(mem::replace(scalar, expand(remaining, value)));
        Ok(Assigned::Done(replaced))
    }

    #[cfg(test)]
    mod tests {
        use core::str::FromStr;

        use serde_json::{json, Value};

        use crate::{Pointer, PointerBuf};

        #[test]
        fn test_assign() {
            let mut data = json!({});

            let ptr = Pointer::from_static("/foo");
            let replaced = ptr.assign(&mut data, json!("bar")).unwrap();
            assert_eq!(replaced, None);
            assert_eq!(&data, &json!({"foo": "bar"}));

            // now testing replacement
            let replaced = ptr.assign(&mut data, json!("baz")).unwrap();
            assert_eq!(replaced, Some(Value::String("bar".to_string())));
            assert_eq!(&data, &json!({"foo": "baz"}));

            let tests = [(json!({}), "/foo", json!("bar"))];
            for (mut data, ptr, value) in tests {
                let ptr = PointerBuf::from_str(ptr).unwrap();
                let replaced = ptr.assign(&mut data, value);
            }
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
            let mut data = json!({});

            let tests = [
                (
                    "/foo/-/bar",
                    json!("baz"),
                    json!({ "foo": [{ "bar": "baz" }] }),
                    None,
                ),
                (
                    "/foo/-/bar",
                    json!("qux"),
                    json!({"foo": [{ "bar": "baz" }, { "bar": "qux" }]
                    }),
                    None,
                ),
                (
                    "/foo/-/bar",
                    json!("quux"),
                    json!({"foo": [{"bar": "baz"},{"bar": "qux"},{"bar": "quux"}]}),
                    None,
                ),
                (
                    "/foo/0/bar",
                    json!("grault"),
                    json!({"foo": [{"bar": "grault"},{"bar": "qux"},{"bar": "quux"}]}),
                    Some(json!("baz")),
                ),
            ];

            for (path, val, expected, expected_replaced) in tests {
                let ptr = PointerBuf::parse(path).expect(&format!("failed to parse \"{path}\""));
                let replaced = ptr
                    .assign(&mut data, val.clone())
                    .expect(&format!("failed to assign \"{path}\""));
                assert_eq!(&expected, &data);
                assert_eq!(expected_replaced, replaced, "replaced not equal");
            }
        }

        #[test]
        fn test_assign_with_obj_path() {
            let mut data = json!({});
            let ptr = PointerBuf::try_from("/foo/bar").unwrap();
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
