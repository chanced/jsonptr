use serde::{Deserialize, Serialize};
use serde_json::Value;
use url::Url;

use crate::{Assignment, Error, MalformedError, NotFoundError, Token, Tokens, UnresolvableError};
use std::{
    borrow::{Borrow, Cow},
    cmp::Ordering,
    fmt::{Debug, Display},
    hash::{Hash, Hasher},
    mem,
    ops::{ControlFlow, Deref},
    str::Split,
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
    valid: bool,
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
            Err(_) => Ok(Pointer {
                inner: s,
                valid: false,
            }),
        }
    }
}

impl Pointer {
    pub fn new(tokens: &[impl AsRef<str>]) -> Self {
        let mut inner = String::new();
        for t in tokens.iter().map(Token::new) {
            inner.push_str(&prepend(t.encoded()));
        }
        if inner.is_empty() {
            inner.push('/');
        }
        Pointer { inner, valid: true }
    }

    /// Returns `true` if the `Pointer` is valid. The only way an invalid
    /// `Pointer` can occur is through deserialization.
    ///
    /// The JSON Pointer specification
    pub fn is_valid(&self) -> bool {
        self.valid
    }

    /// Pushes a `Token` onto the front of this `Pointer`.
    pub fn push_front(&mut self, token: Token) {
        if self.inner == "/" {
            self.inner.push_str(token.encoded());
            return;
        }
        self.inner.insert(0, '/');
        self.inner.insert_str(1, token.encoded());
    }
    /// Pushes a `Token` onto the back of this `Pointer`.
    pub fn push_back(&mut self, token: Token) {
        if !self.inner.ends_with('/') {
            self.inner.push('/');
        }
        self.inner.push_str(token.encoded());
    }

    /// Removes and returns the last `Token` in the `Pointer` if it exists.
    pub fn pop_back(&mut self) -> Option<Token> {
        if self.inner.len() == 1 {
            return None;
        }
        self.rsplit_once().map(|(front, back)| {
            self.inner = prepend(&front);
            Token::from_encoded(back)
        })
    }
    /// Removes and returns the first `Token` in the `Pointer` if it exists.
    pub fn pop_front(&mut self) -> Option<Token> {
        self.split_once().map(|(front, rest)| {
            self.inner = prepend(&rest);
            front.into()
        })
    }
    /// Returns the number of tokens in the `Pointer`.
    pub fn count(&self) -> usize {
        if self.inner == "/" {
            return 0;
        }
        self.inner.matches('/').count()
    }
    /// Returns `true` if the JSON Pointer equals `"/"`.
    pub fn is_root(&self) -> bool {
        self.inner == "/"
    }

    /// Returns the last `Token` in the `Pointer`.
    pub fn back(&self) -> Option<Token> {
        self.rsplit_once().map(|(front, last)| {
            if last.is_empty() {
                Token::from_encoded(front)
            } else {
                Token::from_encoded(last)
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
        self.split_once().map(|(front, _)| front.into())
    }
    /// Returns the first `Token` in the `Pointer`.
    ///
    /// alias for `front`
    pub fn first(&self) -> Option<Token> {
        self.front()
    }
    /// Merges two `Pointer`s by appending `other` onto `self`.
    pub fn append(&mut self, other: &Pointer) -> &Pointer {
        if !other.is_root() {
            self.inner.push_str(other);
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

    /// Clears the `Pointer`, setting it to root (`"/"`).
    pub fn clear(&mut self) {
        self.inner = prepend("")
    }

    /// Returns an iterator of `Token`s in the `Pointer`.
    pub fn tokens(&self) -> Tokens {
        Tokens::new(self.split())
    }
    /// Attempts to resolve a `Value` based on the path in this `Pointer`.
    pub fn resolve<'v>(&self, value: &'v Value) -> Result<&'v Value, Error> {
        let (res, ptr) = self.try_resolve(value)?;
        if ptr.is_root() {
            Ok(res)
        } else {
            Err(NotFoundError::new(ptr).into())
        }
    }

    /// Attempts to resolve a mutable `Value` based on the path in this `Pointer`.
    pub fn resolve_mut<'v>(&self, value: &'v mut Value) -> Result<&'v mut Value, Error> {
        let (res, ptr, _) = self.try_resolve_mut(value)?;
        if ptr.is_root() {
            Ok(res)
        } else {
            Err(NotFoundError::new(ptr).into())
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

    pub fn assign<'d>(&self, dest: &'d mut Value, src: Value) -> Result<Assignment<'d>, Error> {
        match self.try_resolve_mut(dest) {
            Ok((dest, mut remaining, mut resolved)) => {
                if remaining.is_root() {
                    let replaced = mem::replace(dest, src);
                    Ok(Assignment {
                        replaced,
                        assigned: Cow::Borrowed(dest),
                        created_or_mutated: self.clone(),
                        assigned_to: self.clone(),
                    })
                } else {
                    let assigned = remaining.assign_value(dest, src)?;
                    let replaced = assigned.replaced;
                    let assigned = assigned.assigned;
                    if !remaining.is_root() {
                        resolved.push_back(remaining.first().unwrap());
                    }
                    Ok(Assignment {
                        replaced,
                        assigned: Cow::Borrowed(assigned),
                        created_or_mutated: remaining,
                        assigned_to: self.clone(),
                    })
                }
            }
            Err(Error::Unresolvable(err)) => {
                if err.unresolvable.is_root() {
                    let replaced = mem::replace(dest, src);
                    Ok(Assignment {
                        replaced,
                        assigned: Cow::Borrowed(dest),
                        created_or_mutated: self.clone(),
                        assigned_to: self.clone(),
                    })
                } else {
                    let mut ptr = err.unresolvable.clone();
                    let last_token = ptr.pop_back();
                    let (new_dest, _, mut resolved) = ptr.try_resolve_mut(dest).unwrap();
                    todo!()
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
                return Ok(Assigned { assigned, replaced });
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

            return Ok(Assigned { assigned, replaced });
        // otherwise, create a new value based on the next token
        } else if let Some(repl) = self.create_next(dest, &token, None)? {
            replaced = repl;
        }

        let assigned = if dest.is_array() {
            let idx = idx.unwrap();
            dbg!(idx);
            dest.as_array_mut().unwrap().get_mut(idx).unwrap()
        } else {
            dest.as_object_mut()
                .unwrap()
                .get_mut(token.as_key())
                .unwrap()
        };
        // hmmm
        self.assign_value(assigned, src)?;
        Ok(Assigned { assigned, replaced })
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
    pub(crate) fn try_resolve_mut<'v, 'p>(
        &'p self,
        value: &'v mut Value,
    ) -> Result<(&'v mut Value, Pointer, Pointer), Error> {
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
            ControlFlow::Continue((v, p)) => Ok((v, p, resolved)),
            ControlFlow::Break((v, p)) => match v {
                Value::Null | Value::Object(_) => Ok((v, p, resolved)),
                Value::Array(_) => match p.first() {
                    Some(i) => {
                        let len = v.as_array().unwrap().len();
                        let idx = i.as_index(len)?;
                        if idx <= len {
                            Ok((v, p, resolved))
                        } else {
                            Err(UnresolvableError::new(resolved).into())
                        }
                    }
                    None => Ok((v, p, resolved)),
                },
                Value::Bool(_) | Value::Number(_) | Value::String(_) => {
                    Err(UnresolvableError::new(resolved).into())
                }
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
    pub(crate) fn try_resolve<'v, 'p>(
        &'p self,
        value: &'v Value,
    ) -> Result<(&'v Value, Pointer), Error> {
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
            ControlFlow::Continue((v, p)) => Ok((v, p)),
            ControlFlow::Break((v, p)) => match v {
                Value::Null | Value::Object(_) => Ok((v, p)),
                Value::Array(_) => match p.first() {
                    Some(i) => {
                        let len = v.as_array().unwrap().len();
                        let idx = i.as_index(len)?;
                        if idx <= len {
                            Ok((v, p))
                        } else {
                            Err(UnresolvableError::new(resolved).into())
                        }
                    }
                    None => Ok((v, p)),
                },
                Value::Bool(_) | Value::Number(_) | Value::String(_) => {
                    Err(UnresolvableError::new(resolved).into())
                }
            },
        }
    }

    fn split(&self) -> Split<'_, char> {
        let mut s = self.inner.split('/');
        // skipping the first '/'
        s.next();
        s
    }
    fn split_once(&self) -> Option<(String, String)> {
        if self.is_root() {
            None
        } else {
            self.inner[1..]
                .split_once('/')
                .map_or(Some((&self.inner[1..], "")), Option::Some)
                .map(|(f, b)| (f.to_owned(), b.to_owned()))
        }
    }

    fn rsplit_once(&self) -> Option<(String, String)> {
        if self.is_root() {
            None
        } else {
            self.inner[1..]
                .rsplit_once('/')
                .map_or(Some((&self.inner[1..], "")), Option::Some)
                .map(|(f, b)| (f.to_owned(), b.to_owned()))
        }
    }
}

impl Default for Pointer {
    fn default() -> Self {
        Self {
            inner: "/".to_owned(),
            valid: true,
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
    type Error = MalformedError;
    fn try_from(value: String) -> Result<Self, Self::Error> {
        Self::try_from(value.as_str())
    }
}

impl TryFrom<Url> for Pointer {
    type Error = MalformedError;
    fn try_from(url: Url) -> Result<Self, Self::Error> {
        match url.fragment() {
            Some(f) => Self::try_from(f),
            None => Ok(Pointer::default()),
        }
    }
}

impl TryFrom<&str> for Pointer {
    type Error = MalformedError;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        if value.is_empty() {
            Ok(Pointer::default())
        } else {
            Ok(Pointer {
                valid: true,
                inner: value.to_owned(),
            })
        }
    }
}

fn validate_and_format(value: &str) -> Result<String, MalformedError> {
    let mut value = value;
    let mut res = String::with_capacity(value.len());
    let mut chars = value.chars();
    let mut had_hash = false;
    if value.starts_with('#') {
        had_hash = true;
        value = &value[1..];
    }
    if value.is_empty() {
        return Ok("/".to_string());
    }
    if !value.starts_with('/') {
        if had_hash {
            return Err(MalformedError::NoLeadingSlash("#".to_string() + value));
        } else {
            return Err(MalformedError::NoLeadingSlash(value.to_string()));
        }
    }
    while let Some(c) = chars.next() {
        res.push(c);
        if c == '~' {
            match chars.next() {
                Some('0') => res.push('0'),
                Some('1') => res.push('1'),
                _ => {
                    if had_hash {
                        return Err(MalformedError::InvalidEncoding(String::from("#") + value));
                    } else {
                        return Err(MalformedError::InvalidEncoding(value.to_string()));
                    }
                }
            }
        }
    }
    Ok(res)
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

fn prepend(s: &str) -> String {
    if !s.starts_with('/') {
        "/".to_string() + s
    } else {
        s.to_owned()
    }
}

struct Assigned<'a> {
    assigned: &'a mut Value,
    replaced: Value,
}

// ================================================================================================== //
// ================================================================================================== //
//                                                Tests                                               //
// ================================================================================================== //
// ================================================================================================== //

#[cfg(test)]
mod test {
    use serde_json::{json, Value};

    use crate::{Pointer, UnresolvableError};

    #[test]
    fn test_push_pop_back() {
        let mut ptr = Pointer::default();
        assert_eq!(ptr, "/", "default pointer should equal \"/\"");
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
    }

    #[test]
    fn test_push_pop_front() {
        let mut ptr = Pointer::default();
        assert_eq!(ptr, "/");
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

        ptr.pop_front();
    }

    #[test]
    fn test_formatting() {
        assert_eq!(Pointer::new(&["foo", "bar"]), "/foo/bar");
        assert_eq!(
            Pointer::new(&["~/foo", "~bar", "/baz"]),
            "/~0~1foo/~0bar/~1baz"
        );
        assert_eq!(Pointer::new(&["field", "", "baz"]), "/field//baz");
        assert_eq!(Pointer::default(), "/");
    }

    #[test]
    fn test_last() {
        let ptr = Pointer::try_from("/foo/bar").unwrap();

        assert_eq!(ptr.last(), Some("bar".into()));

        let ptr = Pointer::try_from("/foo/bar/-").unwrap();
        assert_eq!(ptr.last(), Some("-".into()));

        let ptr = Pointer::try_from("/-").unwrap();
        assert_eq!(ptr.last(), Some("-".into()));
    }
    #[test]
    fn test_first() {
        let ptr = Pointer::try_from("/foo/bar").unwrap();

        assert_eq!(ptr.first(), Some("foo".into()));

        let ptr = Pointer::try_from("/foo/bar/-").unwrap();
        assert_eq!(ptr.first(), Some("foo".into()));

        let ptr = Pointer::try_from("/").unwrap();
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
        let (val_res, ptr_res, _) = ptr.try_resolve_mut(&mut data).unwrap();
        assert_eq!(&ptr_res, "/");
        assert_eq!(val_res, &mut json!("quux"));

        let ptr = Pointer::try_from("/foo/bar/does_not_exist/derp").unwrap();
        let (val_res, ptr_res, _) = ptr.try_resolve_mut(&mut data).unwrap();
        assert_eq!(ptr_res, "/does_not_exist/derp");

        assert_eq!(
            val_res,
            &mut json!({
                "baz": {
                    "qux": "quux"
                }
            })
        );

        let ptr = Pointer::try_from("/foo/strings/0").unwrap();
        let (val_res, ptr_res, _) = ptr.try_resolve_mut(&mut data).unwrap();
        assert_eq!(ptr_res, "/");
        assert_eq!(val_res, &mut json!("zero"));

        let ptr = Pointer::try_from("/foo/strings/1").unwrap();
        let (val_res, ptr_res, _) = ptr.try_resolve_mut(&mut data).unwrap();
        assert_eq!(ptr_res, "/");
        assert_eq!(val_res, &mut json!("one"));

        let ptr = Pointer::try_from("/foo/strings/2").unwrap();
        let (val_res, ptr_res, _) = ptr.try_resolve_mut(&mut data).unwrap();
        assert_eq!(ptr_res, "/");
        assert_eq!(val_res, &mut json!("two"));

        let ptr = Pointer::try_from("/foo/strings/-").unwrap();
        let (val_res, ptr_res, _) = ptr.try_resolve_mut(&mut data).unwrap();
        assert_eq!(ptr_res, "/-");
        assert_eq!(val_res, &mut json!(["zero", "one", "two"]));

        let ptr = Pointer::try_from("/foo/strings/0").unwrap();
        let (val_res, ptr_res, _) = ptr.try_resolve_mut(&mut data).unwrap();
        assert_eq!(ptr_res, "/");
        assert_eq!(val_res, &mut json!("zero"));
    }

    #[test]
    fn test_try_resolve_mut_overflow_error() {
        let mut data = test_data();
        let ptr = Pointer::try_from("/foo/strings/7").unwrap();
        let res = ptr.try_resolve_mut(&mut data);
        assert!(res.is_err());
    }
    #[test]
    fn test_try_resolve_mut_unreachable_error() {
        let mut data = test_data();
        let ptr = Pointer::try_from("/foo/bool/unreachable").unwrap();
        let res = ptr.try_resolve_mut(&mut data);
        assert!(res.is_err());

        assert_eq!(
            res.err().unwrap(),
            UnresolvableError::new("/foo/bool".try_into().unwrap()).into()
        )
    }
    #[test]
    fn test_try_from() {
        let ptr = Pointer::new(&["foo", "bar", "~/"]);

        assert_eq!(Pointer::try_from("/foo/bar/~0~1").unwrap(), ptr);
        let into: Pointer = "/foo/bar/~0~1".try_into().unwrap();
        assert_eq!(ptr, into);
    }

    #[test]
    fn test_try_resolve() {
        let data = test_data();
        let ptr = Pointer::try_from("/foo/bar/baz/qux").unwrap();
        let (val_res, ptr_res) = ptr.try_resolve(&data).unwrap();
        assert_eq!(&ptr_res, "/");
        assert_eq!(val_res, &mut json!("quux"));

        let ptr = Pointer::try_from("/foo/bar/does_not_exist/derp").unwrap();
        let (val_res, ptr_res) = ptr.try_resolve(&data).unwrap();
        assert_eq!(ptr_res, "/does_not_exist/derp");

        assert_eq!(
            val_res,
            &mut json!({
                "baz": {
                    "qux": "quux"
                }
            })
        );

        let ptr = Pointer::try_from("/foo/strings/0").unwrap();
        let (val_res, ptr_res) = ptr.try_resolve(&data).unwrap();
        assert_eq!(ptr_res, "/");
        assert_eq!(val_res, &mut json!("zero"));

        let ptr = Pointer::try_from("/foo/strings/1").unwrap();
        let (val_res, ptr_res) = ptr.try_resolve(&data).unwrap();
        assert_eq!(ptr_res, "/");
        assert_eq!(val_res, &mut json!("one"));

        let ptr = Pointer::try_from("/foo/strings/2").unwrap();
        let (val_res, ptr_res) = ptr.try_resolve(&data).unwrap();
        assert_eq!(ptr_res, "/");
        assert_eq!(val_res, &mut json!("two"));

        let ptr = Pointer::try_from("/foo/strings/-").unwrap();
        let (val_res, ptr_res) = ptr.try_resolve(&data).unwrap();
        assert_eq!(ptr_res, "/-");
        assert_eq!(val_res, &mut json!(["zero", "one", "two"]));

        let ptr = Pointer::try_from("/foo/strings/0").unwrap();
        let (val_res, ptr_res) = ptr.try_resolve(&data).unwrap();
        assert_eq!(ptr_res, "/");
        assert_eq!(val_res, &mut json!("zero"));
    }

    #[test]
    fn test_try_resolve_overflow_error() {
        let data = test_data();
        let ptr = Pointer::try_from("/foo/strings/7").unwrap();
        let res = ptr.try_resolve(&data);
        assert!(res.is_err());
    }
    #[test]
    fn test_try_resolve_unreachable_error() {
        let data = test_data();
        let ptr = Pointer::try_from("/foo/bool/unreachable").unwrap();
        let res = ptr.try_resolve(&data);
        assert!(res.is_err());

        assert_eq!(
            res.err().unwrap(),
            UnresolvableError::new("/foo/bool".try_into().unwrap()).into()
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
        dbg!(&assignment);
        assert_eq!(assignment.replaced, Value::String("bar".to_string()));
        assert_eq!(assignment.assigned.clone().into_owned(), val2);
        assert_eq!(assignment.assigned_to, "/foo");
    }
    #[test]
    fn test_assign_with_array_path() {
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
        let mut data = json!({});
        let ptr = Pointer::try_from("/foo/-/bar").unwrap();
        let val = json!("baz");
        let assignment = ptr.assign(&mut data, val).unwrap();
        assert_eq!(assignment.replaced, Value::Null);
        assert_eq!(assignment.assigned_to, "/foo/-/bar"); // i think this should actually be /foo/0/bar
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
        assert_eq!(assignment.assigned_to, "/foo/-/bar"); // i think this should actually be /foo/0/bar
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
        let val = json!("qux");
        let assignment = ptr.assign(&mut data, val).unwrap();
        assert_eq!(assignment.replaced, Value::Null);
        assert_eq!(assignment.assigned_to, "/foo/0/bar");
        assert_eq!(assignment.replaced, Value::Null);
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
}
