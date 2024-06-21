use core::{mem::replace, ptr};

use serde_json::{map::Entry, Map, Value};

use crate::{AssignError, Pointer, PointerBuf, Token};

/// Assign is implemented by types which can internally assign a
/// `serde_json::Value` by a JSON Pointer.
pub trait Assign {
    /// Error associated with `Assign`
    type Error;
    /// Assign a value of based on the path provided by a JSON Pointer.
    fn assign<'v, V>(&'v mut self, ptr: &Pointer, value: V) -> Result<Assignment<'v>, Self::Error>
    where
        V: Into<Value>;
}

impl Assign for Value {
    type Error = AssignError;
    fn assign<'v, V>(&'v mut self, ptr: &Pointer, value: V) -> Result<Assignment<'v>, Self::Error>
    where
        V: Into<Value>,
    {
        ptr.assign(self, value.into())
    }
}

#[derive(Debug)]
/// The data structure returned from a successful call to `assign`.
pub struct Assignment<'v> {
    /// The value that was assigned.
    ///
    /// In the event a path is created, this will be a mutable reference to the
    /// `serde_json::Value` encompassing the new branch.
    pub assigned: &'v mut Value,

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
    /// # use jsonptr::{Pointer, Assign};
    /// let mut data = json!({ "foo": ["zero"] });
    /// let mut ptr = Pointer::from_static("/foo/-");
    /// let assignment = data.assign(&mut ptr, "one").unwrap();
    /// assert_eq!(assignment.assigned_to, Pointer::from_static("/foo/1"));
    /// ```
    pub assigned_to: PointerBuf,

    /// The value that was replaced, if any.
    pub replaced: Option<Value>,
}

pub(crate) fn assign_value<'v>(
    remaining: &Pointer,
    mut value: &'v mut Value,
    mut src: Value,
) -> Result<Assignment<'v>, AssignError> {
    println!("dest: {}", value.to_string());
    let mut offset = 0;
    let mut buf = PointerBuf::with_capacity(remaining.as_str().len());

    while let Some((token, tail)) = remaining.split_front() {
        let tok_len = token.encoded().len();

        let assigned = match value {
            Value::Array(array) => assign_array(token, tail, buf, array, src, offset)?,
            Value::Object(obj) => assign_object(token, tail, buf, obj, src)?,
            _ => assign_scalar(token, remaining, buf, value, src)?,
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

enum Assigned<'v> {
    // TODO: Change this to return Assignment
    Done(Assignment<'v>),
    Continue {
        next_buf: PointerBuf,
        next_value: &'v mut Value,
        same_src: Value,
    },
}

fn assign_array<'v>(
    token: Token<'_>,
    remaining: &Pointer,
    mut buf: PointerBuf,
    array: &'v mut Vec<Value>,
    src: Value,
    offset: usize,
) -> Result<Assigned<'v>, AssignError> {
    let idx = token
        .to_index()
        .map_err(|source| AssignError::FailedToParseIndex { offset, source })?
        .for_len_incl(array.len())
        .map_err(|source| AssignError::OutOfBounds { offset, source })?;
    buf.push_back(idx.into());

    debug_assert!(idx <= array.len());

    if idx < array.len() {
        // element exists in the array, we either need to replace it or continue
        // depending on whether this is the last elem or not
        if remaining.is_root() {
            let replaced = Some(replace(&mut array[idx], src));
            let assigned = &mut array[idx];
            Ok(Assigned::Done(Assignment {
                assigned,
                assigned_to: buf,
                replaced,
            }))
        } else {
            Ok(Assigned::Continue {
                next_value: &mut array[idx],
                same_src: src,
                next_buf: buf,
            })
        }
    } else {
        // element does not exist in the array.
        // we create the path and assign the value
        let (assigned_to, src) = expand_src_path(buf, remaining, src)?;
        array.push(src);
        // SAFETY: just pushed.
        let assigned = array.last_mut().unwrap();
        Ok(Assigned::Done(Assignment {
            assigned,
            assigned_to,
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
) -> Result<Assigned<'v>, AssignError> {
    let entry = obj.entry(token.to_string());
    buf.push_back(token);

    match entry {
        Entry::Occupied(entry) => {
            let entry = entry.into_mut();
            // if this is the last element, we return the full pointer up to this point
            if remaining.is_root() {
                let replaced = Some(replace(entry, src));
                Ok(Assigned::Done(Assignment {
                    assigned: entry,
                    assigned_to: buf,
                    replaced,
                }))
            } else {
                Ok(Assigned::Continue {
                    same_src: src,
                    next_buf: buf,
                    next_value: entry,
                })
            }
        }
        Entry::Vacant(entry) => {
            let (assigned_to, src) = expand_src_path(buf, remaining, src)?;
            let assigned = entry.insert(src);
            Ok(Assigned::Done(Assignment {
                assigned,
                assigned_to,
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
) -> Result<Assigned<'v>, AssignError> {
    buf.push_back(token);
    let (assigned_to, src) = expand_src_path(buf, remaining, src)?;
    let replaced = Some(replace(value, src));

    Ok(Assigned::Done(Assignment {
        assigned: value,
        assigned_to,
        replaced,
    }))
}

fn expand_src_path(
    mut buf: PointerBuf,
    mut path: &Pointer,
    mut src: Value,
) -> Result<(PointerBuf, Value), AssignError> {
    let mut assigned_buf = PointerBuf::with_capacity(path.to_string().len());
    while let Some((ptr, tok)) = path.split_back() {
        path = ptr;
        match tok.decoded().as_ref() {
            "0" | "-" => {
                src = Value::Array(vec![src]);
                assigned_buf.push_front("0".into())
            }
            _ => {
                let mut obj = Map::new();
                obj.insert(tok.to_string(), src);
                src = Value::Object(obj);
                assigned_buf.push_front(tok)
            }
        }
    }
    buf.append(&assigned_buf);
    Ok((buf, src))
}

#[cfg(test)]
mod tests {
    use serde_json::{json, Value};

    use crate::{Pointer, PointerBuf};

    #[test]
    fn test_assign() {
        let mut data = json!({});
        let ptr = Pointer::from_static("/foo");
        let val = json!("bar");

        let assignment = ptr.assign(&mut data, val.clone()).unwrap();
        assert_eq!(assignment.replaced, None);
        assert_eq!(assignment.assigned, &val);
        assert_eq!(assignment.assigned_to, "/foo");

        // now testing replacement
        let val2 = json!("baz");
        let assignment = ptr.assign(&mut data, val2.clone()).unwrap();
        assert_eq!(assignment.replaced, Some(Value::String("bar".to_string())));
        assert_eq!(assignment.assigned, &val2);
        assert_eq!(assignment.assigned_to, "/foo");
    }

    #[test]
    fn test_assign_with_explicit_array_path() {
        let mut data = json!({});
        let ptr = Pointer::from_static("/foo/0/bar");
        let val = json!("baz");

        let assignment = ptr.assign(&mut data, val).unwrap();
        assert_eq!(assignment.replaced, None);
        assert_eq!(assignment.assigned_to, "/foo/0/bar");
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
        let ptr = PointerBuf::try_from("/foo/-/bar").unwrap();
        let val = json!("baz");
        let assignment = ptr
            .assign(&mut data, val)
            .expect("failed to assign with dash");
        assert_eq!(assignment.replaced, None);
        assert_eq!(assignment.assigned_to, "/foo/0/bar",);
        assert_eq!(assignment.replaced, None);
        assert_eq!(
            &json!({
                "foo": [
                    {
                        "bar": "baz"
                    }
                ]
            }),
            &data
        );
        let val = json!("baz2");
        let assignment = ptr.assign(&mut data, val).unwrap();
        assert_eq!(assignment.replaced, None);
        assert_eq!(assignment.assigned_to, "/foo/1/bar",);
        assert_eq!(assignment.replaced, None);
        assert_eq!(
            json!({
                "foo": [
                    {
                        "bar": "baz"
                    },
                    {
                        "bar": "baz2"
                    }
                ]
            }),
            data.clone()
        );
        let ptr = PointerBuf::try_from("/foo/0/bar").unwrap();
        let val = json!("qux");
        let assignment = ptr.assign(&mut data, val).unwrap();
        // assert_eq!(assignment.assigned_to, "/foo/0/bar");
        assert_eq!(assignment.replaced, Some(Value::String("baz".to_string())));
        assert_eq!(
            json!({
                "foo": [
                    {
                        "bar": "qux"
                    },
                    {
                        "bar": "baz2"
                    }
                ]
            }),
            data.clone()
        );
    }

    #[test]
    fn test_assign_with_obj_path() {
        let mut data = json!({});
        let ptr = PointerBuf::try_from("/foo/bar").unwrap();
        let val = json!("baz");

        let assignment = ptr.assign(&mut data, val).unwrap();
        assert_eq!(assignment.assigned_to, "/foo/bar");
        assert_eq!(assignment.replaced, None);
        assert_eq!(
            json!({
                "foo": {
                    "bar": "baz"
                }
            }),
            data.clone()
        );
    }

    #[test]
    fn test_assign_with_scalar_replace() {
        let mut data = json!({
            "foo": "bar"
        });

        let ptr = Pointer::from_static("/foo/bar/baz");
        let val = json!("qux");

        ptr.assign(&mut data, val).unwrap();
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
