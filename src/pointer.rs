use core::{
    borrow::Borrow,
    cmp::Ordering,
    mem,
    ops::{ControlFlow, Deref},
    str::{FromStr, Split},
};

use crate::{
    Assignment, Error, MalformedPointerError, NotFoundError, OutOfBoundsError, ReplaceTokenError,
    Token, Tokens, UnresolvableError,
};
use alloc::{
    borrow::{Cow, ToOwned},
    string::{String, ToString},
    vec,
    vec::Vec,
};
use serde::{Deserialize, Serialize};
use serde_json::Value;

/// Helper type for deserialization. Either a valid [`Pointer`] or a string and
/// the parsing error
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MaybePointer {
    /// A valid [`Pointer`].
    Pointer(Pointer),
    /// An invalid [`Pointer`] and the error that caused it.
    Malformed(String, MalformedPointerError),
}
impl Deref for MaybePointer {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        match self {
            MaybePointer::Pointer(p) => p.as_str(),
            MaybePointer::Malformed(s, _) => s,
        }
    }
}
impl<'de> Deserialize<'de> for MaybePointer {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        String::deserialize(deserializer).map(|s| match Pointer::from_str(&s) {
            Ok(ptr) => MaybePointer::Pointer(ptr),
            Err(e) => MaybePointer::Malformed(s, e),
        })
    }
}
impl Serialize for MaybePointer {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            MaybePointer::Pointer(ptr) => serializer.serialize_str(ptr.as_str()),
            MaybePointer::Malformed(s, _) => serializer.serialize_str(s),
        }
    }
}

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
///
/// let data = json!({ "foo": { "bar": "baz" } });
/// let ptr = Pointer::new(&["foo", "bar"]);
/// let bar = data.resolve(&ptr).unwrap();
/// assert_eq!(bar, "baz");
/// ```
#[cfg_attr(
    feature = "url",
    doc = r##"
```rust
use jsonptr::Pointer;
let expected = Pointer::new(&["foo", "bar"]);
let url = url::Url::parse("https://example.com#/foo/bar").unwrap();
assert_eq!(expected, Pointer::try_from(url).unwrap())
```
"##
)]
#[derive(Clone, Default)]
pub struct Pointer {
    inner: String,
    count: usize,
}

impl Pointer {
    /// Creates a root json pointer.
    ///
    /// alias for `default`
    pub fn root() -> Self {
        Self::default()
    }
    /// Creates a new `Pointer` from a slice of non-encoded strings.
    pub fn new<V, T>(tokens: V) -> Self
    where
        V: AsRef<[T]>,
        Token: for<'a> From<&'a T>,
    {
        let mut inner = String::new();
        let tokens = tokens.as_ref();

        for t in tokens.iter().map(Into::<Token>::into) {
            inner.push('/');
            inner.push_str(t.encoded());
        }
        Pointer {
            inner,
            count: tokens.len(),
        }
    }
    /// Parses `value` as a JSON Pointer.
    ///
    /// # Errors
    /// returns `MalformedPointerError` if `value` is not able to be parsed as a
    /// valid JSON Pointer.
    pub fn parse(value: &str) -> Result<Self, MalformedPointerError> {
        Self::from_str(value)
    }
    /// Extracts a string slice containing the entire encoded `Pointer`.
    pub fn as_str(&self) -> &str {
        &self.inner
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
        self.inner.push('/');
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
        let (front, back) = self.inner.rsplit_once('/').expect("`self.count` was > 0");
        let back = Token::from_encoded(back);

        self.inner = front.to_owned();

        Some(back)
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

    /// Returns a `serde_json::Value` representation of this `Pointer`
    pub fn to_value(&self) -> Value {
        Value::String(self.to_string())
    }
    /// Returns the last `Token` in the `Pointer`.
    pub fn back(&self) -> Option<Token> {
        if self.is_root() {
            return None;
        }

        let (_, back) = self
            .inner
            .rsplit_once('/')
            .expect("`self.is_root()` is false, thus pointer starts with `/`");
        Some(Token::from_encoded(back))
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
    /// Attempts to replace a `Token` by the index, returning the replaced
    /// `Token` if it already exists. Returns `None` otherwise.
    ///
    /// A `ReplaceTokenError` is returned if the index is out of bounds.
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

    /// Clears the `Pointer`, setting it to root (`""`).
    pub fn clear(&mut self) {
        self.count = 0;
        self.inner = String::from("");
    }

    /// Returns an iterator of `Token`s in the `Pointer`.
    pub fn tokens(&self) -> Tokens {
        Tokens::new(self.split())
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
    /// assert_eq!(data.delete(&ptr), Some("qux".into()));
    /// assert_eq!(data, json!({ "foo": { "bar": {} } }));
    /// ```
    /// ### Deleting a non-existent Pointer returns `None`:
    /// ```rust
    /// use jsonptr::{Pointer};
    /// use serde_json::json;
    ///
    /// let mut data = json!({});
    /// let ptr = Pointer::new(&["foo", "bar", "baz"]);
    /// assert_eq!(ptr.delete(&mut data), None);
    /// assert_eq!(data, json!({}));
    /// ```
    /// ### Deleting a root pointer replaces the value with `Value::Null`:
    /// ```rust
    /// use jsonptr::{Pointer, Delete};
    /// use serde_json::json;
    ///
    /// let mut data = json!({ "foo": { "bar": "baz" } });
    /// let ptr = Pointer::default();
    /// assert_eq!(data.delete(&ptr), Some(json!({ "foo": { "bar": "baz" } })));
    /// assert!(data.is_null());
    /// ```
    pub fn delete(&self, value: &mut Value) -> Option<Value> {
        if self.is_root() {
            return Some(mem::replace(value, Value::Null));
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
                            Ok(idx) => Some(arr.remove(idx)),
                            Err(_) => None,
                        },
                        Value::Object(obj) => obj.remove(last_token.as_key()),
                        _ => None,
                    }
                } else {
                    None
                }
            }
            Err(_) => None,
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
    pub fn assign<'d, V>(&self, dest: &'d mut Value, src: V) -> Result<Assignment<'d>, Error>
    where
        V: Into<Value>,
    {
        match self.try_resolve_mut(dest) {
            Ok(ResolvedMut {
                value: dest,
                mut remaining,
                mut resolved,
            }) => {
                if remaining.is_root() {
                    let replaced = mem::replace(dest, src.into());
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
                    } = remaining.assign_value(dest, src.into())?;
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

    fn assign_value<'a, V>(&mut self, dest: &'a mut Value, src: V) -> Result<Assigned<'a>, Error>
    where
        V: Into<Value>,
    {
        if self.is_root() {
            let replaced = mem::replace(dest, src.into());
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
                    dest.as_array_mut().unwrap().push(src.into());
                } else {
                    replaced = dest.as_array_mut().unwrap().get(i).cloned().unwrap();
                    dest.as_array_mut().unwrap()[i] = src.into();
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
            if let Some(old_val) = dest
                .as_object_mut()
                .unwrap()
                .insert(token.to_string(), src.into())
            {
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
    fn try_resolve_mut<'v>(&self, value: &'v mut Value) -> Result<ResolvedMut<'v>, Error> {
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
    fn try_resolve<'v>(&self, value: &'v Value) -> Result<Resolved<'v>, Error> {
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
        use serde::de::Error;
        let s = String::deserialize(deserializer)?;
        match Pointer::try_from(s.as_str()) {
            Ok(p) => Ok(p),
            Err(err) => Err(D::Error::custom(err)),
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
        Pointer::new([t])
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
impl AsRef<[u8]> for Pointer {
    fn as_ref(&self) -> &[u8] {
        self.inner.as_bytes()
    }
}

impl Borrow<[u8]> for Pointer {
    fn borrow(&self) -> &[u8] {
        self.inner.as_bytes()
    }
}

#[cfg(feature = "uniresid")]
impl TryFrom<&uniresid::Uri> for Pointer {
    type Error = MalformedPointerError;

    fn try_from(uri: &uniresid::Uri) -> Result<Self, Self::Error> {
        match uri.fragment_to_string() {
            Ok(Some(_)) => todo!(),
            Ok(None) => todo!(),
            Err(err) => Err(err.into()),
        }
    }
}
#[cfg(feature = "uniresid")]
impl TryFrom<uniresid::Uri> for Pointer {
    type Error = MalformedPointerError;

    fn try_from(uri: uniresid::Uri) -> Result<Self, Self::Error> {
        Self::try_from(&uri)
    }
}
#[cfg(feature = "uniresid")]
impl TryFrom<&uniresid::AbsoluteUri> for Pointer {
    type Error = MalformedPointerError;

    fn try_from(uri: &uniresid::AbsoluteUri) -> Result<Self, Self::Error> {
        match uri.fragment_to_string() {
            Ok(Some(_)) => todo!(),
            Ok(None) => todo!(),
            Err(err) => Err(err.into()),
        }
    }
}
#[cfg(feature = "uniresid")]
impl TryFrom<uniresid::AbsoluteUri> for Pointer {
    type Error = MalformedPointerError;

    fn try_from(uri: uniresid::AbsoluteUri) -> Result<Self, Self::Error> {
        Self::try_from(&uri)
    }
}
#[cfg(feature = "url")]
impl TryFrom<&url::Url> for Pointer {
    type Error = MalformedPointerError;
    fn try_from(url: &url::Url) -> Result<Self, Self::Error> {
        match url.fragment() {
            Some(f) => Self::try_from(f),
            None => Ok(Pointer::default()),
        }
    }
}
#[cfg(feature = "url")]
impl TryFrom<url::Url> for Pointer {
    type Error = MalformedPointerError;
    fn try_from(url: url::Url) -> Result<Self, Self::Error> {
        match url.fragment() {
            Some(f) => Self::try_from(f),
            None => Ok(Pointer::default()),
        }
    }
}

#[cfg(feature = "fluent-uri")]
impl TryFrom<&fluent_uri::Uri<&str>> for Pointer {
    type Error = MalformedPointerError;
    fn try_from(uri: &fluent_uri::Uri<&str>) -> Result<Self, Self::Error> {
        match uri.fragment() {
            Some(f) => Self::try_from(f.as_str()),
            None => Ok(Pointer::default()),
        }
    }
}

#[cfg(feature = "fluent-uri")]
impl TryFrom<&fluent_uri::Uri<String>> for Pointer {
    type Error = MalformedPointerError;
    fn try_from(uri: &fluent_uri::Uri<String>) -> Result<Self, Self::Error> {
        match uri.fragment() {
            Some(f) => Self::try_from(f.as_str()),
            None => Ok(Pointer::default()),
        }
    }
}

#[cfg(feature = "fluent-uri")]
impl TryFrom<&fluent_uri::Uri<&mut [u8]>> for Pointer {
    type Error = MalformedPointerError;
    fn try_from(uri: &fluent_uri::Uri<&mut [u8]>) -> Result<Self, Self::Error> {
        match uri.fragment() {
            Some(f) => Self::try_from(f.as_str()),
            None => Ok(Pointer::default()),
        }
    }
}

impl From<Pointer> for Value {
    fn from(ptr: Pointer) -> Self {
        ptr.to_value()
    }
}

impl From<&Pointer> for Value {
    fn from(ptr: &Pointer) -> Self {
        ptr.to_value()
    }
}

impl From<usize> for Pointer {
    fn from(value: usize) -> Self {
        Pointer::new([value])
    }
}

impl<'a> IntoIterator for &'a Pointer {
    type Item = Token;
    type IntoIter = Tokens<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.tokens()
    }
}

impl TryFrom<&str> for Pointer {
    type Error = MalformedPointerError;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let (count, inner) = validate_and_format(value)?;
        Ok(Pointer { count, inner })
    }
}

fn validate_and_format(value: &str) -> Result<(usize, String), MalformedPointerError> {
    let mut chars = value.chars();

    match chars.next() {
        Some('#') => {
            let next = chars.next();
            if next.is_none() {
                return Ok((0, String::default()));
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
            return Ok((0, String::default()));
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
impl core::hash::Hash for Pointer {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.inner.hash(state)
    }
}

impl core::fmt::Debug for Pointer {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "\"{}\"", self.inner)
    }
}
impl core::fmt::Display for Pointer {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.inner)
    }
}
impl FromStr for Pointer {
    type Err = MalformedPointerError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from(s)
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

#[cfg(test)]
mod tests {
    use serde_json::json;

    use crate::{Resolve, ResolveMut};

    use super::*;

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
        let ptr = Pointer::default();
        assert_eq!(data.resolve(&ptr).unwrap(), &data);

        // "/foo"       ["bar", "baz"]
        let ptr = Pointer::try_from("/foo").unwrap();

        assert_eq!(data.resolve(&ptr).unwrap(), &json!(["bar", "baz"]));

        // "/foo/0"     "bar"
        let ptr = Pointer::try_from("/foo/0").unwrap();
        assert_eq!(data.resolve(&ptr).unwrap(), &json!("bar"));

        // // "/"          0
        let ptr = Pointer::try_from("/").unwrap();
        assert_eq!(data.resolve(&ptr).unwrap(), &json!(0));

        // "/a~1b"      1
        assert_eq!(data.get("a/b").unwrap(), 1);
        let ptr = Pointer::try_from("/a~1b").unwrap();
        assert_eq!(ptr.as_str(), "/a~1b");
        assert_eq!(data.get("a/b").unwrap(), 1);
        assert_eq!(&ptr.first().unwrap(), "a/b");
        assert_eq!(data.resolve(&ptr).unwrap(), &json!(1));

        // "/c%d"       2
        let ptr = Pointer::try_from("/c%d").unwrap();
        assert_eq!(data.resolve(&ptr).unwrap(), &json!(2));

        // // "/e^f"       3
        let ptr = Pointer::try_from("/e^f").unwrap();
        assert_eq!(data.resolve(&ptr).unwrap(), &json!(3));

        // // "/g|h"       4
        let ptr = Pointer::try_from("/g|h").unwrap();
        assert_eq!(data.resolve(&ptr).unwrap(), &json!(4));

        // "/i\\j"      5
        let ptr = Pointer::try_from("/i\\j").unwrap();
        assert_eq!(data.resolve(&ptr).unwrap(), &json!(5));

        // // "/k\"l"      6
        let ptr = Pointer::try_from("/k\"l").unwrap();
        assert_eq!(data.resolve(&ptr).unwrap(), &json!(6));

        // // "/ "         7
        let ptr = Pointer::try_from("/ ").unwrap();
        assert_eq!(data.resolve(&ptr).unwrap(), &json!(7));
        // // "/m~0n"      8
        let ptr = Pointer::try_from("/m~0n").unwrap();
        assert_eq!(data.resolve(&ptr).unwrap(), &json!(8));
    }

    #[test]
    fn test_try_from_validation() {
        assert!(Pointer::try_from("").is_ok());
        assert!(Pointer::try_from("/").is_ok());
        assert!(Pointer::try_from("/foo").is_ok());

        let res = Pointer::try_from("/foo~");
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(
            err,
            MalformedPointerError::InvalidEncoding("/foo~".to_string())
        );

        let res = Pointer::try_from("foo");
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert_eq!(
            err,
            MalformedPointerError::NoLeadingSlash("foo".to_string())
        );

        assert!(Pointer::try_from("/foo/bar/baz/~1/~0").is_ok());

        assert_eq!(
            &Pointer::try_from("/foo/bar/baz/~1/~0").unwrap(),
            "/foo/bar/baz/~1/~0"
        );
    }

    #[test]
    fn test_push_pop_back() {
        let mut ptr = Pointer::default();
        assert_eq!(ptr, "", "default, root pointer should equal \"\"");
        assert_eq!(ptr.count(), 0, "default pointer should have 0 tokens");

        ptr.push_back("foo".into());
        assert_eq!(ptr, "/foo", "pointer should equal \"/foo\" after push_back");

        ptr.push_back("bar".into());
        assert_eq!(
            ptr, "/foo/bar",
            "pointer should equal \"/foo/bar\" after push_back"
        );
        ptr.push_back("/baz".into());
        assert_eq!(
            ptr, "/foo/bar/~1baz",
            "pointer should equal \"/foo/bar/~1baz\" after push_back"
        );

        let mut ptr = Pointer::new(["foo", "bar"]);
        assert_eq!(ptr.pop_back(), Some("bar".into()));
        assert_eq!(ptr, "/foo", "pointer should equal \"/foo\" after pop_back");
        assert_eq!(
            ptr.pop_back(),
            Some("foo".into()),
            "\"foo\" should have been popped from the back"
        );
        assert_eq!(ptr, "", "pointer should equal \"\" after pop_back");
    }

    #[test]
    fn test_replace_token() {
        let mut ptr = Pointer::try_from("/test/token").unwrap();

        let res = ptr.replace_token(0, "new".into());
        assert!(res.is_ok());
        assert_eq!(
            ptr, "/new/token",
            "pointer should equal \"/new/token\" after replace_token"
        );

        let res = ptr.replace_token(3, "invalid".into());

        assert!(res.is_err());
    }

    #[test]
    fn test_push_pop_front() {
        let mut ptr = Pointer::default();
        assert_eq!(ptr, "");
        assert_eq!(ptr.count(), 0);
        ptr.push_front("bar".into());
        assert_eq!(ptr, "/bar");
        assert_eq!(ptr.count(), 1);

        ptr.push_front("foo".into());
        assert_eq!(ptr, "/foo/bar");
        assert_eq!(ptr.count(), 2);

        ptr.push_front("too".into());
        assert_eq!(ptr, "/too/foo/bar");
        assert_eq!(ptr.count(), 3);

        assert_eq!(ptr.pop_front(), Some("too".into()));
        assert_eq!(ptr, "/foo/bar");
        assert_eq!(ptr.count(), 2);

        assert_eq!(ptr.pop_back(), Some("bar".into()));
        assert_eq!(ptr, "/foo");
        assert_eq!(ptr.count(), 1);
        assert_eq!(ptr.pop_front(), Some("foo".into()));
        assert_eq!(ptr, "");
    }

    #[test]
    fn test_formatting() {
        assert_eq!(Pointer::new(["foo", "bar"]), "/foo/bar");
        assert_eq!(
            Pointer::new(["~/foo", "~bar", "/baz"]),
            "/~0~1foo/~0bar/~1baz"
        );
        assert_eq!(Pointer::new(["field", "", "baz"]), "/field//baz");
        assert_eq!(Pointer::default(), "");
    }

    #[test]
    fn test_last() {
        let ptr = Pointer::try_from("/foo/bar").unwrap();

        assert_eq!(ptr.last(), Some("bar".into()));

        let ptr = Pointer::try_from("/foo/bar/-").unwrap();
        assert_eq!(ptr.last(), Some("-".into()));

        let ptr = Pointer::try_from("/-").unwrap();
        assert_eq!(ptr.last(), Some("-".into()));

        let ptr = Pointer::default();
        assert_eq!(ptr.last(), None);

        let ptr = Pointer::try_from("/bar").unwrap();
        assert_eq!(ptr.last(), Some("bar".into()));
    }

    #[test]
    fn test_first() {
        let ptr = Pointer::try_from("/foo/bar").unwrap();
        assert_eq!(ptr.first(), Some("foo".into()));

        let ptr = Pointer::try_from("/foo/bar/-").unwrap();
        assert_eq!(ptr.first(), Some("foo".into()));

        let ptr = Pointer::default();
        assert_eq!(ptr.first(), None);
    }

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
    fn test_try_resolve_mut() {
        let mut data = test_data();
        let ptr = Pointer::try_from("/foo/bar/baz/qux").unwrap();
        let ResolvedMut {
            value,
            remaining,
            resolved: _resolved,
        } = ptr.try_resolve_mut(&mut data).unwrap();
        assert_eq!(&remaining, "");
        assert_eq!(value, &mut json!("quux"));

        let ptr = Pointer::try_from("/foo/bar/does_not_exist/derp").unwrap();
        let ResolvedMut {
            value,
            remaining,
            resolved: _resolved,
        } = ptr.try_resolve_mut(&mut data).unwrap();
        assert_eq!(remaining, "/does_not_exist/derp");

        assert_eq!(
            value,
            &mut json!({
                "baz": {
                    "qux": "quux"
                }
            })
        );

        let ptr = Pointer::try_from("/foo/strings/0").unwrap();
        let res = ptr.try_resolve_mut(&mut data).unwrap();
        assert_eq!(res.remaining, "");
        assert_eq!(res.value, &mut json!("zero"));

        let ptr = Pointer::try_from("/foo/strings/1").unwrap();
        let res = ptr.try_resolve_mut(&mut data).unwrap();
        assert_eq!(res.remaining, "");
        assert_eq!(res.value, &mut json!("one"));

        let ptr = Pointer::try_from("/foo/strings/2").unwrap();
        let res = ptr.try_resolve_mut(&mut data).unwrap();
        assert_eq!(res.remaining, "");
        assert_eq!(res.value, &mut json!("two"));

        let ptr = Pointer::try_from("/foo/strings/-").unwrap();
        let res = ptr.try_resolve_mut(&mut data).unwrap();
        assert_eq!(res.remaining, "/-");
        assert_eq!(res.value, &mut json!(["zero", "one", "two"]));

        let ptr = Pointer::try_from("/foo/strings/0").unwrap();
        let res = ptr.try_resolve_mut(&mut data).unwrap();
        assert_eq!(res.remaining, "");
        assert_eq!(res.value, &mut json!("zero"));
    }

    #[test]
    fn test_try_resolve_mut_overflow_error() {
        let mut data = test_data();
        let ptr = Pointer::try_from("/foo/strings/7").unwrap();
        let res = ptr.try_resolve_mut(&mut data);
        assert!(res.is_err());
    }
    #[test]
    fn test_resolve_unresolvable() {
        let mut data = test_data();
        let ptr = Pointer::try_from("/foo/bool/unresolvable").unwrap();
        let res = ptr.resolve_mut(&mut data);

        assert!(res.is_err());
        let err = res.unwrap_err();
        assert!(err.is_unresolvable());
    }
    #[test]
    fn test_resolve_not_found() {
        let mut data = test_data();
        let ptr = Pointer::new(["foo", "not_found", "nope"]);
        let res = ptr.resolve_mut(&mut data);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert!(err.is_not_found());
        match err {
            Error::NotFound(err) => {
                assert_eq!(err.pointer, "/foo/not_found");
            }
            _ => panic!("expected NotFound"),
        }
    }

    #[test]
    fn test_try_resolve_mut_unresolvable() {
        let mut data = test_data();
        let ptr = Pointer::try_from("/foo/bool/unresolvable").unwrap();
        let res = ptr.try_resolve_mut(&mut data).unwrap();

        assert_eq!(res.remaining, "/unresolvable");
        assert_eq!(res.resolved, "/foo/bool");
        assert!(res.value.is_boolean());
    }
    #[test]
    fn test_try_from() {
        let ptr = Pointer::new(["foo", "bar", "~/"]);

        assert_eq!(Pointer::try_from("/foo/bar/~0~1").unwrap(), ptr);
        let into: Pointer = "/foo/bar/~0~1".try_into().unwrap();
        assert_eq!(ptr, into);
    }

    #[test]
    fn test_try_resolve() {
        let data = test_data();
        let ptr = Pointer::try_from("/foo/bar/baz/qux").unwrap();
        let res = ptr.try_resolve(&data).unwrap();
        assert_eq!(&res.remaining, "");
        assert_eq!(res.value, &mut json!("quux"));

        let ptr = Pointer::try_from("/foo/bar/does_not_exist/derp").unwrap();
        let res = ptr.try_resolve(&data).unwrap();
        assert_eq!(res.remaining, "/does_not_exist/derp");

        assert_eq!(
            res.value,
            &mut json!({
                "baz": {
                    "qux": "quux"
                }
            })
        );

        let ptr = Pointer::try_from("/foo/strings/0").unwrap();
        let res = ptr.try_resolve(&data).unwrap();
        assert_eq!(res.remaining, "");
        assert_eq!(res.value, &mut json!("zero"));

        let ptr = Pointer::try_from("/foo/strings/1").unwrap();
        let res = ptr.try_resolve(&data).unwrap();
        assert_eq!(res.remaining, "");
        assert_eq!(res.value, &mut json!("one"));

        let ptr = Pointer::try_from("/foo/strings/2").unwrap();
        let res = ptr.try_resolve(&data).unwrap();
        assert_eq!(res.remaining, "");
        assert_eq!(res.value, &mut json!("two"));

        let ptr = Pointer::try_from("/foo/strings/-").unwrap();
        let res = ptr.try_resolve(&data).unwrap();
        assert_eq!(res.remaining, "/-");
        assert_eq!(res.value, &mut json!(["zero", "one", "two"]));

        let ptr = Pointer::try_from("/foo/strings/0").unwrap();
        let res = ptr.try_resolve(&data).unwrap();
        assert_eq!(res.remaining, "");
        assert_eq!(res.value, &mut json!("zero"));
    }

    #[test]
    fn test_try_resolve_overflow_error() {
        let data = test_data();
        let ptr = Pointer::try_from("/foo/strings/7").unwrap();
        let res = ptr.try_resolve(&data);
        assert!(res.is_err());
    }
    #[test]
    fn test_try_resolve_unresolvable_error() {
        let data = test_data();
        let ptr = Pointer::try_from("/foo/bool/unresolvable/not-in-token").unwrap();
        let res = ptr.try_resolve(&data).unwrap();
        assert_eq!(
            res.remaining,
            Pointer::try_from("/unresolvable/not-in-token").unwrap()
        );
    }

    #[test]
    fn test_resolve_mut_unresolvable_error() {
        let mut data = test_data();
        let ptr = Pointer::try_from("/foo/bool/unresolvable/not-in-token").unwrap();
        let res = ptr.resolve_mut(&mut data);
        assert!(res.is_err());
        let unresolvable = "/foo/bool/unresolvable".try_into().unwrap();
        assert_eq!(
            res.err().unwrap(),
            UnresolvableError::new(unresolvable).into()
        );

        let mut data = json!({"foo": "bar"});
        let ptr = Pointer::try_from("/foo/unresolvable").unwrap();
        let err = data.resolve_mut(&ptr).unwrap_err();
        assert_eq!(err, UnresolvableError::new(ptr.clone()).into());
    }

    #[test]
    fn test_resolve_unresolvable_error() {
        let data = test_data();
        let ptr = Pointer::try_from("/foo/bool/unresolvable/not-in-token").unwrap();
        let res = ptr.resolve(&data);

        assert!(res.is_err());
        let unresolvable = "/foo/bool/unresolvable".try_into().unwrap();
        assert_eq!(
            res.err().unwrap(),
            UnresolvableError::new(unresolvable).into()
        )
    }

    #[test]
    fn test_assign() {
        let mut data = json!({});
        let ptr = Pointer::try_from("/foo").unwrap();
        let val = json!("bar");
        let assignment = ptr.assign(&mut data, val.clone()).unwrap();
        assert_eq!(assignment.replaced, Value::Null);
        assert_eq!(assignment.assigned.clone().into_owned(), val);
        assert_eq!(assignment.assigned_to, "/foo");

        // now testing replacement
        let val2 = json!("baz");
        let assignment = ptr.assign(&mut data, val2.clone()).unwrap();
        assert_eq!(assignment.replaced, Value::String("bar".to_string()));
        assert_eq!(assignment.assigned.clone().into_owned(), val2);
        assert_eq!(assignment.assigned_to, "/foo");
    }
    #[test]
    fn test_assign_with_explicit_array_path() {
        let mut data = json!({});
        let ptr = Pointer::try_from("/foo/0/bar").unwrap();
        let val = json!("baz");

        let assignment = ptr.assign(&mut data, val).unwrap();
        assert_eq!(assignment.replaced, Value::Null);
        assert_eq!(assignment.assigned_to, "/foo/0/bar");
        assert_eq!(assignment.replaced, Value::Null);
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
        let ptr = Pointer::try_from("/foo/-/bar").unwrap();
        let val = json!("baz");
        let assignment = ptr.assign(&mut data, val).unwrap();
        assert_eq!(assignment.replaced, Value::Null);
        assert_eq!(
            assignment.assigned_to, "/foo/0/bar",
            "`assigned_to` should equal \"/foo/0/bar\""
        );
        assert_eq!(assignment.replaced, Value::Null);
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
        let val = json!("baz2");
        let assignment = ptr.assign(&mut data, val).unwrap();
        assert_eq!(assignment.replaced, Value::Null);
        assert_eq!(
            assignment.assigned_to, "/foo/1/bar",
            "`assigned_to` should equal \"/foo/1/bar\""
        );
        assert_eq!(assignment.replaced, Value::Null);
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
        let ptr = Pointer::try_from("/foo/0/bar").unwrap();
        let val = json!("qux");
        let assignment = ptr.assign(&mut data, val).unwrap();
        // assert_eq!(assignment.assigned_to, "/foo/0/bar");
        assert_eq!(assignment.replaced, Value::String("baz".to_string()));
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
        let ptr = Pointer::try_from("/foo/bar").unwrap();
        let val = json!("baz");

        let assignment = ptr.assign(&mut data, val).unwrap();
        assert_eq!(assignment.assigned_to, "/foo/bar");
        assert_eq!(assignment.replaced, Value::Null);
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

        let ptr = Pointer::try_from("/foo/bar/baz").unwrap();
        let val = json!("qux");

        ptr.assign(&mut data, val).unwrap();
        assert_eq!(
            json!({
                "foo": {
                    "bar": {
                        "baz": "qux"
                    }
                }
            }),
            data.clone()
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
            let ptr = Pointer::try_from("///bar").unwrap();
            assert_eq!(ptr.resolve(&data).unwrap(), 42);
        }
        {
            let mut ptr = Pointer::root();
            ptr.push_back("".into());
            ptr.push_back("".into());
            ptr.push_back("bar".into());
            assert_eq!(ptr.resolve(&data).unwrap(), 42);
        }
    }

    #[test]
    fn pop_back_works_with_empty_strings() {
        {
            let mut ptr = Pointer::root();
            ptr.push_back("".into());
            ptr.push_back("".into());
            ptr.push_back("bar".into());

            assert_eq!(ptr.tokens().count(), 3);
            ptr.pop_back();
            assert_eq!(ptr.tokens().count(), 2);
            ptr.pop_back();
            assert_eq!(ptr.tokens().count(), 1);
            ptr.pop_back();
            assert_eq!(ptr.tokens().count(), 0);
            assert_eq!(ptr, Pointer::root());
        }
        {
            let mut ptr = Pointer::root();
            assert_eq!(ptr.tokens().count(), 0);
            ptr.push_back("".into());
            assert_eq!(ptr.tokens().count(), 1);
            ptr.pop_back();
            assert_eq!(ptr.tokens().count(), 0);
        }
        {
            let mut ptr = Pointer::root();
            let input = ["", "", "", "foo", "", "bar", "baz", ""];
            for (idx, s) in input.iter().enumerate() {
                assert_eq!(ptr.tokens().count(), idx);
                ptr.push_back(s.into());
            }
            assert_eq!(ptr.tokens().count(), input.len());
            for (idx, s) in input.iter().enumerate().rev() {
                assert_eq!(ptr.tokens().count(), idx + 1);
                assert_eq!(ptr.back().unwrap().as_str(), *s);
                assert_eq!(ptr.pop_back().unwrap().as_str(), *s);
            }
            assert_eq!(ptr.tokens().count(), 0);
            assert!(ptr.back().is_none());
            assert!(ptr.pop_back().is_none());
        }
    }

    #[test]
    #[cfg(feature = "fluent-uri")]
    fn test_try_from_fluent_uri() {
        let uri = fluent_uri::Uri::parse("#/foo/bar").unwrap();
        let ptr = Pointer::try_from(&uri).unwrap();
        assert_eq!(ptr, "/foo/bar");
    }
}
