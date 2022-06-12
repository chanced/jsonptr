#[cfg(test)]
mod pointer_test;

use serde::{Deserialize, Serialize};
use serde_json::Value;
use url::Url;

use crate::{
    Assignment, Error, MalformedPointerError, NotFoundError, OutOfBoundsError, ReplaceTokenError,
    Token, Tokens, UnresolvableError,
};
use std::{
    borrow::{Borrow, Cow},
    cmp::Ordering,
    fmt::{Debug, Display},
    hash::{Hash, Hasher},
    mem,
    ops::{ControlFlow, Deref},
    str::{FromStr, Split},
};

#[derive(Clone)]
/// A JSON Pointer is a string containing a sequence of zero or more reference
/// tokens, each prefixed by a '/' character.
///
/// See [RFC 6901 for more
/// information](https://datatracker.ietf.org/doc/html/rfc6901).
///
/// ## Example
/// ```rust
/// use jsonptr::{Pointer, Resolve};
/// use serde_json::{json, Value};
/// use url::Url; // for the `try_from` example below.
///
/// let data = json!({ "foo": { "bar": "baz" } });
/// let ptr = Pointer::new(&["foo", "bar"]);
/// let bar = data.resolve(&ptr).unwrap();
/// assert_eq!(bar, "baz");
///
/// // you can also use `try_from`, which expects a properly formatted JSON Pointer:
/// assert_eq!(ptr, Pointer::try_from("/foo/bar").unwrap());
///
/// let url = Url::parse("https://example.com#/foo/bar").unwrap();
/// assert_eq!(ptr, Pointer::try_from(url).unwrap())
/// ```
pub struct Pointer {
    inner: String,
    count: usize,
    err: Option<Box<MalformedPointerError>>,
}

impl Pointer {
    /// Creates a root json pointer.
    ///
    /// alias for `default`
    pub fn root() -> Self {
        Self::default()
    }
    pub fn new(tokens: &[impl AsRef<str>]) -> Self {
        let mut inner = String::new();
        for t in tokens.iter().map(Token::new) {
            inner.push('/');
            inner.push_str(t.encoded());
        }
        Pointer {
            inner,
            err: None,
            count: tokens.len(),
        }
    }
    /// Extracts a string slice containing the entire encoded `Pointer`.
    pub fn as_str(&self) -> &str {
        &self.inner
    }

    /// Returns `true` if the `Pointer` is valid. The only way an invalid
    /// `Pointer` can occur is through deserialization.
    ///
    /// The JSON Pointer specification
    pub fn is_valid(&self) -> bool {
        self.err.is_none()
    }

    /// Pushes a `Token` onto the front of this `Pointer`.
    pub fn push_front(&mut self, token: Token) {
        self.count += 1;
        self.inner.insert(0, '/');
        self.inner.insert_str(1, token.encoded());
    }
    /// Pushes a `Token` onto the back of this `Pointer`.
    pub fn push_back(&mut self, token: Token) {
        self.count += 1;
        if !self.inner.ends_with('/') {
            self.inner.push('/');
        }
        self.inner.push_str(token.encoded());
    }

    /// Removes and returns the last `Token` in the `Pointer` if it exists.
    pub fn pop_back(&mut self) -> Option<Token> {
        if self.is_root() {
            return None;
        }
        if self.count > 0 {
            self.count -= 1;
        }
        self.inner[1..]
            .rsplit_once('/')
            .map_or(Some((&self.inner[1..], "")), Option::Some)
            .map(|(f, b)| (f.to_owned(), b.to_owned()))
            .map(|(front, back)| {
                if !front.is_empty() {
                    self.inner = String::from("/") + &front;
                } else {
                    self.inner = "".to_owned();
                }
                Token::from_encoded(back)
            })

        // self.rsplit_once().map(|(front, back)| {
        //     self.inner = maybe_prepend_slash(&front);

        // })
    }
    /// Removes and returns the first `Token` in the `Pointer` if it exists.
    pub fn pop_front(&mut self) -> Option<Token> {
        if self.inner.is_empty() {
            return None;
        }
        if self.count > 0 {
            self.count -= 1;
        }

        self.inner[1..]
            .split_once('/')
            .map_or(Some((&self.inner[1..], "")), Option::Some)
            .map(|(f, b)| (f.to_owned(), b.to_owned()))
            .map(|(front, back)| {
                if !back.is_empty() {
                    self.inner = String::from("/") + &back;
                } else {
                    self.inner = String::new()
                }
                front.into()
            })
    }
    /// Returns the number of tokens in the `Pointer`.
    pub fn count(&self) -> usize {
        self.count
    }
    /// Returns `true` if the JSON Pointer equals `""`.
    pub fn is_root(&self) -> bool {
        self.inner.is_empty()
    }

    /// Returns the last `Token` in the `Pointer`.
    pub fn back(&self) -> Option<Token> {
        self.inner[1..]
            .rsplit_once('/')
            .map_or(Some((&self.inner[1..], "")), Option::Some)
            .map(|(front, back)| {
                if !back.is_empty() {
                    Token::from_encoded(back)
                } else {
                    Token::from_encoded(front)
                }
            })
    }
    /// Returns the last token in the `Pointer`.
    ///
    /// alias for `back`
    pub fn last(&self) -> Option<Token> {
        self.back()
    }
    /// Returns the first `Token` in the `Pointer`.
    pub fn front(&self) -> Option<Token> {
        if self.is_root() {
            return None;
        }
        self.inner[1..]
            .split_once('/')
            .map_or(Some((&self.inner[1..], "")), Option::Some)
            .map(|(front, _)| Token::from_encoded(front))
    }
    /// Returns the first `Token` in the `Pointer`.
    ///
    /// alias for `front`
    pub fn first(&self) -> Option<Token> {
        self.front()
    }
    /// Merges two `Pointer`s by appending `other` onto `self`.
    pub fn append(&mut self, other: &Pointer) -> &Pointer {
        self.count += other.count;
        if self.err.is_none() && other.err.is_some() {
            self.err = other.err.clone();
        }
        if self.is_root() {
            self.inner = other.inner.clone();
        } else if !other.is_root() {
            self.inner.push_str(&other.inner);
        }
        self
    }
    /// Attempts to get a `Token` by the index. Returns `None` if the index is
    /// out of bounds.
    ///
    /// ## Example
    /// ```rust
    /// use jsonptr::{Pointer, Token};
    ///
    /// let ptr = Pointer::new(&["foo", "bar"]);
    /// assert_eq!(ptr.get(0), Some("foo".into()));
    /// assert_eq!(ptr.get(1), Some("bar".into()));
    /// assert_eq!(ptr.get(2), None);
    ///
    /// let ptr = Pointer::default();
    /// assert_eq!(ptr.get(0), None);
    /// ```
    pub fn get(&self, index: usize) -> Option<Token> {
        if self.is_root() {
            return None;
        }
        let tokens = self.tokens().collect::<Vec<_>>();
        tokens.get(index).cloned()
    }

    pub fn replace_token(
        &mut self,
        index: usize,
        token: Token,
    ) -> Result<Option<Token>, ReplaceTokenError> {
        if self.is_root() {
            return Err(ReplaceTokenError {
                count: self.count,
                index,
                pointer: self.clone(),
            });
        }
        let mut tokens = self.tokens().collect::<Vec<_>>();
        if index > tokens.len() {
            return Err(ReplaceTokenError {
                count: tokens.len(),
                index,
                pointer: self.clone(),
            });
        }
        let old = tokens.get(index).cloned();
        tokens[index] = token;

        self.inner = String::from("/")
            + &tokens
                .iter()
                .map(Token::encoded)
                .collect::<Vec<_>>()
                .join("/");
        Ok(old)
    }

    /// Clears the `Pointer`, setting it to root (`"/"`).
    pub fn clear(&mut self) {
        self.count = 0;
        self.inner = String::from("");
    }

    /// Returns an iterator of `Token`s in the `Pointer`.
    pub fn tokens(&self) -> Tokens {
        Tokens::new(self.split())
    }

    /// Returns the validation error which occurred during deserialization.
    pub fn validate(&self) -> Result<(), MalformedPointerError> {
        if let Some(err) = self.err.as_deref() {
            Err(err.clone())
        } else {
            Ok(())
        }
    }
    /// Attempts to resolve a `Value` based on the path in this `Pointer`.
    pub fn resolve<'v>(&self, value: &'v Value) -> Result<&'v Value, Error> {
        let Resolved {
            value,
            remaining,
            mut resolved,
        } = self.try_resolve(value)?;

        if remaining.is_root() {
            Ok(value)
        } else {
            match value {
                Value::Object(_) => {
                    if !remaining.is_root() {
                        resolved.push_back(remaining.front().unwrap());
                    }
                    Err(NotFoundError::new(resolved).into())
                }
                Value::Array(_) => {
                    if !remaining.is_root() {
                        resolved.push_back(remaining.front().unwrap());
                    }
                    Err(NotFoundError::new(resolved).into())
                }
                Value::Null => {
                    if !remaining.is_root() {
                        resolved.push_back(remaining.front().unwrap());
                    }
                    Err(NotFoundError::new(resolved).into())
                }
                _ => {
                    if let Some(t) = remaining.front() {
                        resolved.push_back(t);
                    }
                    Err(UnresolvableError::new(resolved).into())
                }
            }
        }
    }
    /// Attempts to resolve a mutable `Value` based on the path in this `Pointer`.
    pub fn resolve_mut<'v>(&self, value: &'v mut Value) -> Result<&'v mut Value, Error> {
        let ResolvedMut {
            value,
            remaining,
            mut resolved,
        } = self.try_resolve_mut(value)?;

        if remaining.is_root() {
            Ok(value)
        } else {
            match value {
                Value::Object(_) => {
                    if !remaining.is_root() {
                        resolved.push_back(remaining.front().unwrap());
                    }
                    Err(NotFoundError::new(resolved).into())
                }
                Value::Array(_) => {
                    if !remaining.is_root() {
                        resolved.push_back(remaining.front().unwrap());
                    }
                    Err(NotFoundError::new(resolved).into())
                }
                Value::Null => {
                    if !remaining.is_root() {
                        resolved.push_back(remaining.front().unwrap());
                    }
                    Err(NotFoundError::new(resolved).into())
                }
                _ => {
                    if let Some(t) = remaining.front() {
                        resolved.push_back(t);
                    }
                    Err(UnresolvableError::new(resolved).into())
                }
            }
        }
    }
    /// Finds the commonality between this and another `Pointer`.
    pub fn union(&self, other: &Pointer) -> Pointer {
        let mut res = Pointer::default();
        for (i, token) in self.tokens().enumerate() {
            if let Some(t) = other.get(i) {
                if t == token {
                    res.push_back(t);
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        res
    }
    /// Attempts to delete a `serde_json::Value` based upon the path in this
    /// `Pointer`.
    ///
    /// - If the `Pointer` can be resolved, the `Value` is deleted and returned.
    /// - If the `Pointer` can not be resolved, Ok(None) is returned.
    /// - If the `Pointer` is malformed, an error is returned.
    /// - If the `Pointer` is root, then `value` is replaced with `Value::Null`.
    ///
    /// ## Examples
    /// ### Deleting a resolved pointer:
    /// ```rust
    /// use jsonptr::{Pointer, Delete};
    /// use serde_json::json;
    ///
    /// let mut data = json!({ "foo": { "bar": { "baz": "qux" } } });
    /// let ptr = Pointer::new(&["foo", "bar", "baz"]);
    /// assert_eq!(data.delete(&ptr), Ok(Some("qux".into())));
    /// assert_eq!(data, json!({ "foo": { "bar": {} } }));
    /// ```
    /// ### Deleting a non-existent Pointer returns `None`:
    /// ```rust
    /// use jsonptr::{Pointer};
    /// use serde_json::json;
    ///
    /// let mut data = json!({});
    /// let ptr = Pointer::new(&["foo", "bar", "baz"]);
    /// assert_eq!(ptr.delete(&mut data), Ok(None));
    /// assert_eq!(data, json!({}));
    /// ```
    /// ### Deleting a root pointer replaces the value with `Value::Null`:
    /// ```rust
    /// use jsonptr::{Pointer, Delete};
    /// use serde_json::json;
    ///
    /// let mut data = json!({ "foo": { "bar": "baz" } });
    /// let ptr = Pointer::default();
    /// assert_eq!(data.delete(&ptr), Ok(Some(json!({ "foo": { "bar": "baz" } }))));
    /// assert!(data.is_null());
    /// ```
    pub fn delete(&self, value: &mut Value) -> Result<Option<Value>, MalformedPointerError> {
        self.validate()?;
        if self.is_root() {
            return Ok(Some(mem::replace(value, Value::Null)));
        }
        let mut ptr = self.clone();
        let last_token = ptr.pop_back().unwrap();

        match ptr.try_resolve_mut(value) {
            Ok(ResolvedMut {
                remaining,
                resolved: _resolved,
                value,
            }) => {
                if remaining.is_root() {
                    match value {
                        Value::Array(arr) => match last_token.as_index(arr.len()) {
                            Ok(idx) => Ok(Some(arr.remove(idx))),
                            Err(_) => Ok(None),
                        },
                        Value::Object(obj) => Ok(obj.remove(last_token.as_key())),
                        _ => Ok(None),
                    }
                } else {
                    Ok(None)
                }
            }
            Err(_) => Ok(None),
        }
    }

    /// Attempts to assign `src` to `dest` based on the path in this `Pointer`.
    ///
    /// If the path is
    /// partially available, the missing portions will be created. If the path contains an index,
    /// such as `"/0"` or `"/1"` then an array will be created. Otherwise, objects will be utilized
    /// to create the missing path.
    ///
    /// ## Example
    /// ```rust
    /// use jsonptr::{Pointer};
    /// use jsonptr::prelude::*; // <-- for Assign trait
    /// use serde_json::{json, Value};
    /// let mut data = json!([]);
    ///
    /// let mut ptr = Pointer::new(&["0", "foo"]);
    /// let src = json!("bar");
    /// let assignment = data.assign(&ptr, src).unwrap();
    /// assert_eq!(data, json!([{ "foo": "bar" } ]));
    /// ```
    pub fn assign<'d>(&self, dest: &'d mut Value, src: Value) -> Result<Assignment<'d>, Error> {
        match self.try_resolve_mut(dest) {
            Ok(ResolvedMut {
                value: dest,
                mut remaining,
                mut resolved,
            }) => {
                if remaining.is_root() {
                    let replaced = mem::replace(dest, src);
                    Ok(Assignment {
                        replaced,
                        assigned: Cow::Borrowed(dest),
                        created_or_mutated: self.clone(),
                        assigned_to: self.clone(),
                    })
                } else {
                    let Assigned {
                        assigned,
                        replaced,
                        to,
                    } = remaining.assign_value(dest, src)?;
                    resolved.append(&to);
                    Ok(Assignment {
                        replaced,
                        assigned: Cow::Borrowed(assigned),
                        created_or_mutated: remaining,
                        assigned_to: resolved,
                    })
                }
            }
            Err(err) => Err(err),
        }
    }

    fn assign_value<'a>(&mut self, dest: &'a mut Value, src: Value) -> Result<Assigned<'a>, Error> {
        if self.is_root() {
            let replaced = mem::replace(dest, src);
            return Ok(Assigned {
                assigned: dest,
                replaced,
                to: Pointer::default(),
            });
        }
        let mut replaced = Value::Null;
        // this is safe as we know that this pointer is not root and has tokens.
        let token = self.pop_front().unwrap();
        // if dest is either a scalar or null value, we replace it with either
        // an object or an array, based upon the token.
        if dest.is_boolean() || dest.is_null() || dest.is_string() || dest.is_number() {
            let new_dest = if token.as_index(0).is_ok() {
                Value::Array(vec![])
            } else {
                Value::Object(serde_json::Map::new())
            };
            replaced = mem::replace(dest, new_dest);
        }
        let mut idx: Option<usize> = None;
        // if the value is an array, attempt to parse the token as an index and
        // insert at that index.
        if dest.is_array() {
            let len = dest.as_array().unwrap().len();
            let i = token.as_index(len)?;
            idx = Some(i);
            // if the token is equal to the length of the array, we push a new
            // value onto the array.
            if self.is_root() {
                if i == len {
                    dest.as_array_mut().unwrap().push(src);
                } else {
                    replaced = dest.as_array_mut().unwrap().get(i).cloned().unwrap();
                    dest.as_array_mut().unwrap()[i] = src;
                }
                let assigned = dest.as_array_mut().unwrap().get_mut(i).unwrap();

                return Ok(Assigned {
                    assigned,
                    replaced,
                    to: i.into(),
                });
            } else if let Some(repl) = self.create_next(dest, &token, Some(i))? {
                replaced = repl;
            }
        // if not an array, the value is an object (due to the assignment above)
        // if root, replace the value
        } else if self.is_root() {
            if let Some(old_val) = dest.as_object_mut().unwrap().insert(token.to_string(), src) {
                replaced = old_val;
            }
            let assigned = dest
                .as_object_mut()
                .unwrap()
                .get_mut(token.as_key())
                .unwrap();

            return Ok(Assigned {
                assigned,
                replaced,
                to: token.into(),
            });
        // otherwise, create a new value based on the next token
        } else if let Some(repl) = self.create_next(dest, &token, None)? {
            replaced = repl;
        }

        let assigned = if dest.is_array() {
            let idx = idx.unwrap();
            dest.as_array_mut().unwrap().get_mut(idx).unwrap()
        } else {
            dest.as_object_mut()
                .unwrap()
                .get_mut(token.as_key())
                .unwrap()
        };
        let Assigned {
            assigned: _assigned,
            replaced: _replaced,
            mut to,
        } = self.assign_value(assigned, src)?;
        let last_token = if let Some(i) = idx { i.into() } else { token };
        to.push_front(last_token);
        Ok(Assigned {
            assigned,
            replaced,
            to,
        })
    }
    fn create_next(
        &self,
        dest: &mut Value,
        token: &Token,
        idx: Option<usize>,
    ) -> Result<Option<Value>, Error> {
        // we need to peak ahead to the next token to see if it is an object or an array
        let next_token = self.front().unwrap();
        // if the next token is an index, we push a new array onto the array.
        let next = if next_token.as_index(0).is_ok() {
            Value::Array(vec![])
        } else {
            Value::Object(serde_json::Map::new())
        };
        if let Some(idx) = idx {
            let len = dest.as_array().unwrap().len();
            if idx == len {
                dest.as_array_mut().unwrap().push(next);
                Ok(None)
            } else {
                let prev = dest.as_array_mut().unwrap().get_mut(idx).unwrap().clone();
                dest.as_array_mut().unwrap()[idx] = next;
                Ok(Some(prev))
            }
        } else {
            let prev = dest
                .as_object_mut()
                .unwrap()
                .insert(token.to_string(), next);
            Ok(prev)
        }
    }
    /// Resolves a `Pointer` as far as possible. If it encounters an an
    /// array without the given index, an object without the given key, or a null
    /// value then the pointer is returned at the last resolved location along with
    /// the last resolved value.
    ///
    /// If a leaf node is found (`String`, `Number`, `Boolean`) and the pointer is
    /// not at the root, an error is returned.
    ///
    /// If the resolution is successful, the pointer will be empty.
    fn try_resolve_mut<'v, 'p>(&'p self, value: &'v mut Value) -> Result<ResolvedMut<'v>, Error> {
        self.validate()?;
        let mut tokens = self.tokens();
        let mut resolved = Pointer::default();
        let res = tokens.try_fold((value, self.clone()), |(v, mut p), token| match v {
            Value::Null => ControlFlow::Break((v, p)),
            Value::Number(_) | Value::String(_) | Value::Bool(_) => ControlFlow::Break((v, p)),
            Value::Array(_) => match token.as_index(v.as_array_mut().unwrap().len()) {
                Ok(idx) => {
                    if idx < v.as_array_mut().unwrap().len() {
                        let t = p.pop_front();
                        if let Some(t) = t {
                            resolved.push_back(t);
                        }
                        ControlFlow::Continue((v.as_array_mut().unwrap().get_mut(idx).unwrap(), p))
                    } else {
                        ControlFlow::Break((v, p))
                    }
                }
                Err(_) => ControlFlow::Break((v, p)),
            },
            Value::Object(_) => {
                if v.as_object_mut().unwrap().contains_key(&*token) {
                    let t = p.pop_front();
                    if let Some(t) = t {
                        resolved.push_back(t);
                    }
                    ControlFlow::Continue((
                        v.as_object_mut().unwrap().get_mut(token.as_key()).unwrap(),
                        p,
                    ))
                } else {
                    ControlFlow::Break((v, p))
                }
            }
        });
        match res {
            ControlFlow::Continue((v, remaining)) => Ok(ResolvedMut {
                value: v,
                remaining,
                resolved,
            }),
            ControlFlow::Break((value, remaining)) => match value {
                Value::Null | Value::Object(_) => Ok(ResolvedMut {
                    value,
                    remaining,
                    resolved,
                }),
                Value::Array(_) => match remaining.first() {
                    Some(token) => {
                        let len = value.as_array().unwrap().len();
                        let idx = token.as_index(len)?;
                        if idx <= len {
                            Ok(ResolvedMut {
                                value,
                                remaining,
                                resolved,
                            })
                        } else {
                            Err(OutOfBoundsError {
                                index: idx,
                                len,
                                token,
                            }
                            .into())
                        }
                    }
                    None => Ok(ResolvedMut {
                        value,
                        remaining,
                        resolved,
                    }),
                },
                // this should return `UnresovableError` but currently makes
                // `assign` impossible without unsafe code.
                Value::Bool(_) | Value::Number(_) | Value::String(_) => Ok(ResolvedMut {
                    value,
                    remaining,
                    resolved,
                }),
            },
        }
    }

    /// Resolves a `Pointer` as far as possible. If it encounters an an
    /// array without the given index, an object without the given key, or a null
    /// value then the pointer is returned at the last resolved location along with
    /// the last resolved value.
    ///
    /// If a leaf node is found (`String`, `Number`, `Boolean`) and the pointer is
    /// not at the root, an error is returned.
    ///
    /// If the resolution is successful, the pointer will be empty.
    fn try_resolve<'v, 'p>(&'p self, value: &'v Value) -> Result<Resolved<'v>, Error> {
        let mut tokens = self.tokens();
        let mut resolved = Pointer::default();
        let res = tokens.try_fold((value, self.clone()), |(v, mut p), token| match v {
            Value::Null => ControlFlow::Break((v, p)),
            Value::Number(_) | Value::String(_) | Value::Bool(_) => ControlFlow::Break((v, p)),
            Value::Array(_) => match token.as_index(v.as_array().unwrap().len()) {
                Ok(idx) => {
                    if idx < v.as_array().unwrap().len() {
                        let t = p.pop_front();
                        if let Some(t) = t {
                            resolved.push_back(t);
                        }
                        ControlFlow::Continue((v.as_array().unwrap().get(idx).unwrap(), p))
                    } else {
                        ControlFlow::Break((v, p))
                    }
                }
                Err(_) => ControlFlow::Break((v, p)),
            },
            Value::Object(_) => {
                if v.as_object().unwrap().contains_key(&*token) {
                    let t = p.pop_front();
                    if let Some(t) = t {
                        resolved.push_back(t);
                    }
                    ControlFlow::Continue((v.as_object().unwrap().get(&*token).unwrap(), p))
                } else {
                    ControlFlow::Break((v, p))
                }
            }
        });
        match res {
            ControlFlow::Continue((v, remaining)) => Ok(Resolved {
                value: v,
                remaining,
                resolved,
            }),
            ControlFlow::Break((value, remaining)) => match value {
                Value::Null | Value::Object(_) => Ok(Resolved {
                    value,
                    remaining,
                    resolved,
                }),
                Value::Array(_) => match remaining.first() {
                    Some(token) => {
                        let len = value.as_array().unwrap().len();
                        let idx = token.as_index(len)?;
                        if idx <= len {
                            Ok(Resolved {
                                value,
                                remaining,
                                resolved,
                            })
                        } else {
                            Err(OutOfBoundsError {
                                index: idx,
                                len,
                                token,
                            }
                            .into())
                        }
                    }
                    None => Ok(Resolved {
                        value,
                        remaining,
                        resolved,
                    }),
                },
                // this should return `UnresovableError` but currently makes
                // `assign` impossible without unsafe code.
                Value::Bool(_) | Value::Number(_) | Value::String(_) => Ok(Resolved {
                    value,
                    remaining,
                    resolved,
                }),
            },
        }
    }

    fn split(&self) -> Split<'_, char> {
        let mut s = self.inner.split('/');
        // skipping the first '/'
        s.next();
        s
    }
}

impl Default for Pointer {
    fn default() -> Self {
        Self {
            inner: "".to_string(),
            err: None,
            count: 0,
        }
    }
}

impl Eq for Pointer {}
impl Deref for Pointer {
    type Target = str;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl Serialize for Pointer {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        String::serialize(&self.inner, serializer)
    }
}

impl<'de> Deserialize<'de> for Pointer {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        match Pointer::try_from(s.as_str()) {
            Ok(p) => Ok(p),
            Err(err) => Ok(Pointer {
                inner: s,
                count: 0,
                err: Some(Box::new(err)),
            }),
        }
    }
}

impl AsRef<str> for Pointer {
    fn as_ref(&self) -> &str {
        &self.inner
    }
}
impl Borrow<str> for Pointer {
    fn borrow(&self) -> &str {
        &self.inner
    }
}
impl From<Token> for Pointer {
    fn from(t: Token) -> Self {
        Pointer::new(&[t])
    }
}

impl PartialEq<&str> for Pointer {
    fn eq(&self, other: &&str) -> bool {
        &self.inner == other
    }
}
impl PartialEq<str> for Pointer {
    fn eq(&self, other: &str) -> bool {
        self.inner == other
    }
}

impl PartialEq<Pointer> for Pointer {
    fn eq(&self, other: &Pointer) -> bool {
        self.inner == other.inner
    }
}

impl PartialEq<Pointer> for str {
    fn eq(&self, other: &Pointer) -> bool {
        self == other.inner
    }
}
impl PartialEq<String> for Pointer {
    fn eq(&self, other: &String) -> bool {
        &self.inner == other
    }
}

impl TryFrom<String> for Pointer {
    type Error = MalformedPointerError;
    fn try_from(value: String) -> Result<Self, Self::Error> {
        Self::try_from(value.as_str())
    }
}

impl TryFrom<Url> for Pointer {
    type Error = MalformedPointerError;
    fn try_from(url: Url) -> Result<Self, Self::Error> {
        match url.fragment() {
            Some(f) => Self::try_from(f),
            None => Ok(Pointer::default()),
        }
    }
}
impl From<usize> for Pointer {
    fn from(value: usize) -> Self {
        Pointer::new(&[value.to_string()])
    }
}
impl TryFrom<&str> for Pointer {
    type Error = MalformedPointerError;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let (count, inner) = validate_and_format(value)?;
        Ok(Pointer {
            err: None,
            count,
            inner,
        })
    }
}

fn validate_and_format(value: &str) -> Result<(usize, String), MalformedPointerError> {
    let mut chars = value.chars();

    match chars.next() {
        Some('#') => {
            let next = chars.next();
            if next.is_none() {
                return Ok((0, "".to_string()));
            }
            if next != Some('/') {
                return Err(MalformedPointerError::NoLeadingSlash(value.into()));
            }
        }
        Some('/') => {}
        Some(_) => {
            return Err(MalformedPointerError::NoLeadingSlash(value.into()));
        }
        None => {
            return Ok((0, "".to_string()));
        }
    }
    let mut res = String::with_capacity(value.len());
    res.push('/');
    let mut count = 1; // accounting for the first slash

    while let Some(c) = chars.next() {
        res.push(c);
        match c {
            '~' => match chars.next() {
                Some('0') => res.push('0'),
                Some('1') => res.push('1'),
                _ => {
                    return Err(MalformedPointerError::InvalidEncoding(value.to_string()));
                }
            },
            '/' => {
                count += 1;
            }
            _ => {}
        }
    }
    Ok((count, res))
}

impl PartialOrd<&str> for Pointer {
    fn partial_cmp(&self, other: &&str) -> Option<Ordering> {
        PartialOrd::partial_cmp(&self.inner[..], &other[..])
    }
}
impl PartialOrd<String> for Pointer {
    fn partial_cmp(&self, other: &String) -> Option<Ordering> {
        self.inner.partial_cmp(other)
    }
}
impl PartialOrd<Pointer> for Pointer {
    fn partial_cmp(&self, other: &Pointer) -> Option<Ordering> {
        self.inner.partial_cmp(&other.inner)
    }
}
impl PartialEq<Pointer> for String {
    fn eq(&self, other: &Pointer) -> bool {
        PartialEq::eq(&self[..], &other.inner[..])
    }
}

impl PartialOrd<Pointer> for String {
    fn partial_cmp(&self, other: &Pointer) -> Option<Ordering> {
        self.partial_cmp(&other.inner)
    }
}
impl Hash for Pointer {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.inner.hash(state)
    }
}

impl Debug for Pointer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner)
    }
}
impl Display for Pointer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner)
    }
}
impl FromStr for Pointer {
    type Err = MalformedPointerError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from(s)
    }
}

fn prepend_slash(s: &str) -> String {
    if !s.starts_with('/') {
        "/".to_string() + s
    } else {
        s.to_owned()
    }
}

#[derive(Debug)]
struct Assigned<'a> {
    assigned: &'a mut Value,
    replaced: Value,
    to: Pointer,
}

/// Used internally as a response from `try_resolve`
#[derive(Debug)]
struct ResolvedMut<'a> {
    value: &'a mut Value,
    remaining: Pointer,
    resolved: Pointer,
}

/// Used internally as a response from `try_resolve`
#[derive(Debug)]
struct Resolved<'a> {
    value: &'a Value,
    remaining: Pointer,
    resolved: Pointer,
}
