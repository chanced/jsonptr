use core::mem::replace;

use serde_json::{map::Entry, Map, Value};
use snafu::ResultExt;

use crate::{assign_error, AssignError, Pointer, Token};

/// Assign is implemented by types which can internally assign a
/// `serde_json::Value` by a JSON Pointer.
pub trait Assign {
    /// Error associated with `Assign`
    type Error;
    /// Assign a value of based on the path provided by a JSON Pointer.
    fn assign<'p, 'd, V>(
        &'d mut self,
        ptr: &'p Pointer,
        value: V,
    ) -> Result<Assignment<'p, 'd>, Self::Error>
    where
        V: Into<Value>;
}

impl Assign for Value {
    type Error = AssignError;
    fn assign<'p, 'd, V>(
        &'d mut self,
        ptr: &'p Pointer,
        value: V,
    ) -> Result<Assignment<'p, 'd>, Self::Error>
    where
        V: Into<Value>,
    {
        ptr.assign(self, value.into())
    }
}

#[derive(Debug)]
/// The data structure returned from a successful call to `assign`.
pub struct Assignment<'p, 'd> {
    /// The value that was assigned.
    ///
    /// In the event a path is created, this will be a mutable reference to the
    /// `serde_json::Value` encompassing the new branch.
    pub assigned: &'d mut Value,

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
    pub assigned_to: &'p Pointer,

    /// The value that was replaced, if any.
    pub replaced: Option<Value>,
}

pub(crate) fn assign_value<'p, 'd>(
    mut remaining: &'p Pointer,
    mut dest: &'d mut Value,
    mut src: Value,
) -> Result<Assignment<'p, 'd>, AssignError> {
    let mut offset = 0;
    let full_ptr = remaining;
    let mut replaced;
    let mut returned_src;
    while let Some((token, tail)) = remaining.split_front() {
        offset = offset + 1;
        let tok_len = token.encoded().len();
        let (assigned_to, _) = full_ptr
            .split_at(offset)
            .unwrap_or((Pointer::root(), Pointer::root()));
        Assigned {
            dest,
            remaining,
            replaced,
            src: returned_src,
        } = match dest {
            Value::Array(array) => assign_to_array(token, tail, array, src, offset)?,
            Value::Object(obj) => assign_to_object(token, tail, obj, src)?,
            _ => assign_to_scalar(remaining, dest, src)?,
        };
        if remaining.is_root() {
            return Ok(Assignment {
                assigned: dest,
                assigned_to,
                replaced,
            });
        }
        offset += tok_len;
        src = returned_src.unwrap();
    }
    // Pointer is root, we can replace `dest` directly
    let replaced = Some(core::mem::replace(dest, src.into()));
    Ok(Assignment {
        assigned: dest,
        replaced,
        assigned_to: remaining,
    })
}
fn create_value_path(mut path: &Pointer, mut src: Value) -> Result<Value, AssignError> {
    while let Some((token, tail)) = path.split_front() {
        path = tail;
        match path.as_str() {
            "0" | "-" => {
                src = Value::Array(vec![src]);
            }
            _ => {
                let mut obj = Map::new();
                obj.insert(token.to_string(), src);
                src = Value::Object(obj);
            }
        }
    }
    Ok(src)
}

struct Assigned<'p, 'd> {
    remaining: &'p Pointer,
    dest: &'d mut Value,
    replaced: Option<Value>,
    src: Option<Value>,
}

fn assign_to_array<'p, 'd>(
    token: Token<'_>,
    remaining: &'p Pointer,
    dest: &'d mut Vec<Value>,
    src: Value,
    offset: usize,
) -> Result<Assigned<'p, 'd>, AssignError> {
    let idx = token
        .to_index()
        .with_context(|_| assign_error::FailedToParseIndexSnafu { offset })?
        .for_len_incl(dest.len())
        .with_context(|_| assign_error::OutOfBoundsSnafu { offset })?;
    debug_assert!(idx <= dest.len());
    if idx < dest.len() {
        let returned_src;
        let replaced;
        if remaining.is_root() {
            replaced = Some(replace(&mut dest[idx], src));
            returned_src = Some(dest[idx].clone());
        } else {
            replaced = None;
            returned_src = Some(src);
        }
        Ok(Assigned {
            remaining,
            dest: &mut dest[idx],
            replaced,
            src: returned_src,
        })
    } else {
        let src = create_value_path(remaining, src)?;
        dest.push(src);
        Ok(Assigned {
            remaining: Pointer::root(),
            dest: &mut dest[idx],
            replaced: None,
            src: None,
        })
    }
}

fn assign_to_object<'p, 'd>(
    token: Token<'_>,
    remaining: &'p Pointer,
    dest: &'d mut Map<String, Value>,
    src: Value,
) -> Result<Assigned<'p, 'd>, AssignError> {
    let mut returned_src = None;
    match dest.entry(token.to_string()) {
        Entry::Occupied(entry) => {
            let entry = entry.into_mut();
            let replaced = if remaining.is_root() {
                Some(replace(entry, src))
            } else {
                returned_src = Some(src);
                None
            };
            Ok(Assigned {
                remaining,
                dest: entry,
                replaced,
                src: returned_src,
            })
        }
        Entry::Vacant(entry) => {
            let src = create_value_path(remaining, src)?;
            Ok(Assigned {
                remaining: Pointer::root(),
                dest: entry.insert(src),
                replaced: None,
                src: None,
            })
        }
    }
}

fn assign_to_scalar<'p, 'd>(
    remaining: &'p Pointer,
    dest: &'d mut Value,
    src: Value,
) -> Result<Assigned<'p, 'd>, AssignError> {
    let src = create_value_path(remaining, src)?;
    let replaced = Some(replace(dest, src));
    Ok(Assigned {
        remaining: &Pointer::root(),
        dest,
        replaced,
        src: None,
    })
}
