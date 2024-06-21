use core::mem::replace;

use serde_json::{
    map::{Entry, OccupiedEntry, VacantEntry},
    Map, Value,
};

use crate::{AssignError, Pointer, Token};

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
    let dest_str = dest.to_string();
    println!("dest: {}", dest_str);

    let mut offset = 0;
    let full_ptr = remaining;
    while let Some((token, tail)) = remaining.split_front() {
        let tok_len = token.encoded().len();
        let (assigned_to, rest) = full_ptr
            .split_at(offset)
            .unwrap_or((Pointer::root(), Pointer::root()));
        println!("splitting pointer {full_ptr} at {offset} into \"{assigned_to}\" and \"{rest}\"");
        let assigned = match dest {
            Value::Array(array) => AssignArray {
                token,
                remaining,
                current: assigned_to,
                dest: array,
                src,
                offset,
            }
            .assign()?,
            Value::Object(obj) => AssignObject {
                token,
                remaining,
                current: assigned_to,
                dest: obj,
                src,
                offset,
            }
            .assign()?,
            _ => AssignToScalar {
                remaining,
                current: assigned_to,
                dest,
                src,
                offset,
            }
            .assign()?,
        };
        match assigned {
            Assigned::Done {
                assigned_to,
                replaced,
                assigned,
            } => todo!(),
            Assigned::Continue {
                remaining,
                dest,
                src,
            } => todo!(),
        }
        offset += 1 + tok_len;
    }
    // Pointer is root, we can replace `dest` directly
    let replaced = Some(core::mem::replace(dest, src.into()));
    Ok(Assignment {
        assigned: dest,
        replaced,
        assigned_to: remaining,
    })
}
fn expand_src_path(mut path: &Pointer, mut src: Value) -> Result<Value, AssignError> {
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

enum Assigned<'p, 'd> {
    // TODO: Change this to return Assignment
    Done {
        assigned_to: &'p Pointer,
        replaced: Option<Value>,
        assigned: &'d mut Value,
    },
    Continue {
        remaining: &'p Pointer,
        dest: &'d mut Value,
        src: Value,
    },
}

struct AssignArray<'p, 'd> {
    token: Token<'p>,
    remaining: &'p Pointer,
    current: &'p Pointer,
    dest: &'d mut Vec<Value>,
    src: Value,
    offset: usize,
}
impl<'p, 'd> AssignArray<'p, 'd> {
    fn assign(self) -> Result<Assigned<'p, 'd>, AssignError> {
        let AssignArray {
            token,
            remaining,
            dest,
            src,
            offset,
            current,
        } = self;
        let idx = token
            .to_index()
            .map_err(|source| AssignError::FailedToParseIndex { offset, source })?
            .for_len_incl(dest.len())
            .map_err(|source| AssignError::OutOfBounds { offset, source })?;
        debug_assert!(idx <= dest.len());

        if idx < dest.len() {
            // element exists in the array, we either need to replace it or continue
            // depending on whether this is the last elem or not
            if remaining.is_root() {
                let replaced = Some(replace(&mut dest[idx], src));
                let assigned = &mut dest[idx];
                Ok(Assigned::Done {
                    assigned_to: current,
                    replaced,
                    assigned,
                })
            } else {
                Ok(Assigned::Continue {
                    remaining,
                    dest: &mut dest[idx],
                    src,
                })
            }
        } else {
            // element does not exist in the array.
            // we create the path and assign the value
            dest.push(src);
            // SAFETY: just pushed.
            let assigned_to = dest.last_mut().unwrap();
            Ok(Assigned::Done {
                assigned_to: current,
                replaced: None,
                assigned: assigned_to,
            })
        }

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
}
struct AssignObject<'p, 'd> {
    token: Token<'p>,
    remaining: &'p Pointer,
    current: &'p Pointer,
    dest: &'d mut Map<String, Value>,
    src: Value,
    offset: usize,
}
impl<'p, 'd> AssignObject<'p, 'd> {
    fn assign(self) -> Result<Assigned<'p, 'd>, AssignError> {
        let entry = self.dest.entry(self.token.to_string());
        match entry {
            Entry::Occupied(entry) => {
                let entry = entry.into_mut();
                // if this is the last element, we return the full pointer up to this point
                if self.remaining.is_root() {
                    let replaced = Some(replace(entry, self.src));
                    Ok(Assigned::Done {
                        assigned_to: self.current,
                        replaced,
                        assigned: entry,
                    })
                } else {
                    Ok(Assigned::Continue {
                        remaining: self.remaining,
                        dest: entry,
                        src: self.src,
                    })
                }
            }
            Entry::Vacant(entry) => {
                let src = expand_src_path(self.remaining, self.src)?;
                let assigned = entry.insert(src);
                Ok(Assigned::Done {
                    assigned_to: self.current,
                    assigned,
                    replaced: None,
                })
            }
        }
    }
}

struct AssignToScalar<'p, 'd> {
    remaining: &'p Pointer,
    current: &'p Pointer,
    dest: &'d mut Value,
    src: Value,
    offset: usize,
}
impl<'p, 'd> AssignToScalar<'p, 'd> {
    fn assign(self) -> Result<Assigned<'p, 'd>, AssignError> {
        let src = expand_src_path(self.remaining, self.src)?;
        let replaced = Some(replace(self.dest, src));
        Ok(Assigned::Done {
            assigned_to: self.current,
            replaced,
            assigned: self.dest,
        })
    }
}
