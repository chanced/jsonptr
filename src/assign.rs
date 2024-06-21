use core::mem::replace;

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
    mut remaining: &Pointer,
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
            Value::Object(obj) => assign_object(token, tail, buf, obj, src, offset)?,
            _ => assign_scalar(remaining, buf, value, src)?,
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
    buf: PointerBuf,
    dest: &'v mut Vec<Value>,
    src: Value,
    offset: usize,
) -> Result<Assigned<'v>, AssignError> {
    let idx = token
        .to_index()
        .map_err(|source| AssignError::FailedToParseIndex { offset, source })?
        .for_len_incl(dest.len())
        .map_err(|source| AssignError::OutOfBounds { offset, source })?;
    debug_assert!(idx <= dest.len());

    // if idx < dest.len() {
    //     // element exists in the array, we either need to replace it or continue
    //     // depending on whether this is the last elem or not
    //     if remaining.is_root() {
    //         let replaced = Some(replace(&mut dest[idx], src));
    //         let assigned = &mut dest[idx];
    //         Ok(Assigned::Done {
    //             assigned_to: current,
    //             replaced,
    //             assigned,
    //         })
    //     } else {
    //         Ok(Assigned::Continue {
    //             remaining,
    //             dest: &mut dest[idx],
    //             same_src: src,
    //         })
    //     }
    // } else {
    //     // element does not exist in the array.
    //     // we create the path and assign the value
    //     dest.push(src);
    //     // SAFETY: just pushed.
    //     let assigned_to = dest.last_mut().unwrap();
    //     Ok(Assigned::Done {
    //         assigned_to: current,
    //         replaced: None,
    //         assigned: assigned_to,
    //     })
    // }

    todo!()

    // if idx < dest.len() {
    //     let replaced;
    //     if remaining.is_root() {
    //         replaced = Some(replace(&mut dest[idx], src));
    //         returned_src = Some(dest[idx].clone());
    //     } else {
    //         replaced = None;
    //         returned_src = Some(src);
    //     }
    // } else {
    //     let src = create_value_path(remaining, src)?;
    //     dest.push(src);
    //     Ok(Assigned {
    //         remaining: Pointer::root(),
    //         dest: &mut dest[idx],
    //         replaced: None,
    //         src: None,
    //     })
    // }
}

fn assign_object<'v>(
    token: Token<'_>,
    remaining: &Pointer,
    buf: PointerBuf,
    obj: &'v mut Map<String, Value>,
    src: Value,
    offset: usize,
) -> Result<Assigned<'v>, AssignError> {
    // let entry = obj.entry(token.to_string());
    // match entry {
    //     Entry::Occupied(entry) => {
    //         let entry = entry.into_mut();
    //         // if this is the last element, we return the full pointer up to this point
    //         if remaining.is_root() {
    //             let replaced = Some(replace(entry, src));
    //             Ok(Assigned::Done {
    //                 assigned_to: current,
    //                 replaced,
    //                 assigned: entry,
    //             })
    //         } else {
    //             Ok(Assigned::Continue {
    //                 remaining: remaining,
    //                 dest: entry,
    //                 same_src: src,
    //             })
    //         }
    //     }
    //     Entry::Vacant(entry) => {
    //         let src = expand_src_path(remaining, src)?;
    //         let assigned = entry.insert(src);
    //         Ok(Assigned::Done {
    //             assigned_to: current,
    //             assigned,
    //             replaced: None,
    //         })
    //     }
    // }
    todo!()
}

fn assign_scalar<'v>(
    remaining: &'_ Pointer,
    buf: PointerBuf,
    value: &'v mut Value,
    src: Value,
) -> Result<Assigned<'v>, AssignError> {
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
    while let Some((ptr, tok)) = path.split_back() {
        path = ptr;
        match tok.decoded().as_ref() {
            "0" | "-" => {
                src = Value::Array(vec![src]);
                buf.push_back("0".into())
            }
            _ => {
                let mut obj = Map::new();
                obj.insert(tok.to_string(), src);
                src = Value::Object(obj);
                buf.push_back(tok)
            }
        }
    }
    Ok((buf, src))
}
