use crate::{
    assign::assign_value, AssignError, Assignment, InvalidEncodingError, ParseError,
    ReplaceTokenError, Resolve, ResolveMut, Token, Tokens,
};
use alloc::{
    borrow::ToOwned,
    string::{String, ToString},
    vec::Vec,
};
use core::{borrow::Borrow, cmp::Ordering, mem, ops::Deref, slice, str::FromStr};
use serde::{Deserialize, Serialize};
use serde_json::Value;

fn validate(value: &str) -> Result<&str, ParseError> {
    let mut chars = value.char_indices();
    match chars.next().map(|(_, c)| c) {
        Some('/') => {}                                        // expected
        Some(_) => return Err(ParseError::NoLeadingBackslash), // invalid pointer - missing leading slash
        None => return Ok(value),                              // done
    }
    let mut tok_idx = 0;

    while let Some((offset, c)) = chars.next() {
        if c == '/' {
            tok_idx = 0;
            continue;
        }
        if c == '~' && !matches!(chars.next().map(|(_, c)| c), Some('0') | Some('1')) {
            // '~' must be followed by '0' or '1' in order to be properly encoded
            return Err(ParseError::InvalidEncoding {
                offset,
                source: InvalidEncodingError { offset: tok_idx },
            });
        }
        tok_idx += 1;
    }
    Ok(value)
}

unsafe fn extend_one_before(s: &str) -> &str {
    let ptr = s.as_ptr().offset(-1);
    let len = s.len() + 1;
    let slice = slice::from_raw_parts(ptr, len);
    core::str::from_utf8_unchecked(slice)
}

const fn is_valid_ptr(value: &str) -> bool {
    let bytes = value.as_bytes();

    if bytes.is_empty() {
        // root pointer
        return true;
    }

    match bytes[0] {
        b'#' => {
            if bytes.len() == 1 {
                // also root pointer
                return true;
            }
            if bytes[1] != b'/' {
                return false;
            }
        }
        b'/' => {}
        _ => return false,
    }

    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'~' {
            if i + 1 >= bytes.len() {
                return false;
            }
            if bytes[i + 1] != b'0' && bytes[i + 1] != b'1' {
                return false;
            }
        }
        i += 1;
    }

    true
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
/// let ptr = Pointer::from_static("/foo/bar");
/// let bar = data.resolve(&ptr).unwrap();
/// assert_eq!(bar, "baz");
/// ```
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Pointer(str);

impl core::fmt::Display for Pointer {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.fmt(f)
    }
}

impl Pointer {
    /// Private constructor for strings that are known to be correctly encoded
    ///
    /// This is a zero-copy constructor
    fn new<S: AsRef<str> + ?Sized>(s: &S) -> &Self {
        unsafe { &*(s.as_ref() as *const str as *const Self) }
    }

    /// Constant reference to a root pointer
    pub const fn root() -> &'static Self {
        unsafe { &*("" as *const str as *const Self) }
    }

    /// Attempts to parse a string into a `Pointer`.
    ///
    /// If successful, this does not allocate.
    pub fn parse<S: AsRef<str> + ?Sized>(s: &S) -> Result<&Self, ParseError> {
        validate(s.as_ref()).map(Self::new)
    }

    /// Creates a static `Pointer` from a string.
    ///
    /// # Panics
    ///
    /// Will panic if the string does not represent a valid pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use jsonptr::{Pointer, Resolve};
    /// use serde_json::{json, Value};
    ///
    /// const POINTER: &Pointer = Pointer::from_static("/foo/bar");
    /// let data = json!({ "foo": { "bar": "baz" } });
    /// let bar = data.resolve(POINTER).unwrap();
    /// assert_eq!(bar, "baz");
    /// ````
    pub const fn from_static(s: &'static str) -> &'static Self {
        assert!(is_valid_ptr(s), "invalid JSON Pointer");
        unsafe { &*(s as *const str as *const Self) }
    }

    /// The encoded string representation of this `Pointer`
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Converts into an owned PointerBuf
    pub fn to_buf(&self) -> PointerBuf {
        PointerBuf(self.0.to_string())
    }

    /// Returns an iterator of `Token`s in the `Pointer`.
    pub fn tokens(&self) -> Tokens {
        let mut s = self.0.split('/');
        // skipping the first '/'
        s.next();
        Tokens::new(s)
    }

    /// Returns the number of tokens in the `Pointer`.
    pub fn count(&self) -> usize {
        self.tokens().count()
    }

    /// Returns `true` if the JSON Pointer equals `""`.
    pub fn is_root(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns a `serde_json::Value` representation of this `Pointer`
    pub fn to_value(&self) -> Value {
        Value::String(self.0.to_string())
    }

    /// Returns the last `Token` in the `Pointer`.
    pub fn back(&self) -> Option<Token> {
        self.0
            .rsplit_once('/')
            .map(|(_, back)| Token::from_encoded_unchecked(back))
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
        self.0[1..]
            .split_once('/')
            .map_or_else(
                || Token::from_encoded_unchecked(&self.0[1..]),
                |(front, _)| Token::from_encoded_unchecked(front),
            )
            .into()
    }

    /// Returns the first `Token` in the `Pointer`.
    ///
    /// alias for `front`
    pub fn first(&self) -> Option<Token> {
        self.front()
    }

    /// Splits the `Pointer` into the first `Token` and a remainder `Pointer`.
    pub fn split_front(&self) -> Option<(Token, &Self)> {
        if self.is_root() {
            return None;
        }
        self.0[1..]
            .split_once('/')
            .map_or_else(
                || (Token::from_encoded_unchecked(&self.0[1..]), Self::root()),
                |(front, back)| {
                    // We want to include the delimiter character too!
                    // SAFETY: if split was successful, then the delimiter
                    // character exists before the start of the second `str`.
                    let back = unsafe { extend_one_before(back) };
                    (Token::from_encoded_unchecked(front), Self::new(back))
                },
            )
            .into()
    }
    /// Splits the `Pointer` at the given index if the character at the index is
    /// a seperator backslash (`'/'`), returning `Some((head, tail))`. Otherwise,
    /// returns `None`.
    ///
    /// For the following JSON Pointer, the following splits are possible (0, 4, 8):
    /// ```text
    /// /foo/bar/baz
    /// ↑   ↑   ↑
    /// 0   4   8
    /// ```
    /// All other indices will return `None`.
    ///
    /// ## Example
    ///
    /// ```rust
    /// # use jsonptr::Pointer;
    /// let ptr = Pointer::from_static("/foo/bar/baz");
    /// let (head, tail) = ptr.split_at(4).unwrap();
    /// assert_eq!(head, Pointer::from_static("/foo"));
    /// assert_eq!(tail, Pointer::from_static("/bar/baz"));
    ///
    /// assert_eq!(ptr.split_at(3), None);
    /// ```
    pub fn split_at(&self, idx: usize) -> Option<(&Self, &Self)> {
        if self.0.get(idx..idx + 1) != Some("/") {
            return None;
        }
        let (head, tail) = self.0.split_at(idx);
        Some((Self::new(head), Self::new(tail)))
    }

    /// Splits the `Pointer` into the parent path and the last `Token`.
    pub fn split_back(&self) -> Option<(&Self, Token)> {
        self.0
            .rsplit_once('/')
            .map(|(front, back)| (Self::new(front), Token::from_encoded_unchecked(back)))
    }

    /// A pointer to the parent of the current path.
    pub fn parent(&self) -> Option<&Self> {
        self.0.rsplit_once('/').map(|(front, _)| Self::new(front))
    }

    /// Returns the pointer stripped of the given suffix.
    pub fn strip_suffix<'a>(&'a self, suffix: &Self) -> Option<&'a Self> {
        self.0.strip_suffix(&suffix.0).map(Self::new)
    }

    /// Attempts to get a `Token` by the index. Returns `None` if the index is
    /// out of bounds.
    ///
    /// ## Example
    /// ```rust
    /// use jsonptr::{Pointer, Token};
    ///
    /// let ptr = Pointer::from_static("/foo/bar");
    /// assert_eq!(ptr.get(0), Some("foo".into()));
    /// assert_eq!(ptr.get(1), Some("bar".into()));
    /// assert_eq!(ptr.get(2), None);
    ///
    /// let ptr = Pointer::root();
    /// assert_eq!(ptr.get(0), None);
    /// ```
    pub fn get(&self, index: usize) -> Option<Token> {
        self.tokens().nth(index).to_owned()
    }

    /// Attempts to resolve a `Value` based on the path in this `Pointer`.
    pub fn resolve<'v, R: Resolve>(&self, value: &'v R) -> Result<&'v Value, R::Error> {
        value.resolve(self)
    }

    /// Attempts to resolve a mutable `Value` based on the path in this `Pointer`.
    ///
    pub fn resolve_mut<'v, R: ResolveMut>(
        &self,
        value: &'v mut R,
    ) -> Result<&'v mut Value, R::Error> {
        value.resolve_mut(self)
    }

    fn partial_path(&self, suffix: &Self) -> &Self {
        self.strip_suffix(suffix).expect("suffix came from self")
    }

    /// Finds the commonality between this and another `Pointer`.
    pub fn intersection<'a>(&'a self, other: &Self) -> &'a Self {
        let mut last_slash = 0;
        let mut idx = 0;
        for (a, b) in self.0.bytes().zip(other.0.bytes()) {
            if a != b {
                return Self::new(&self.0[..last_slash]);
            }
            if a == b'/' {
                last_slash = idx;
            }
            idx += 1;
        }
        if idx == self.0.len() || self.0.as_bytes()[idx] == b'/' {
            Self::new(&self.0[..idx])
        } else {
            Self::new(&self.0[..last_slash])
        }
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
    /// let ptr = Pointer::from_static("/foo/bar/baz");
    /// assert_eq!(data.delete(&ptr), Some("qux".into()));
    /// assert_eq!(data, json!({ "foo": { "bar": {} } }));
    /// ```
    /// ### Deleting a non-existent Pointer returns `None`:
    /// ```rust
    /// use jsonptr::Pointer;
    /// use serde_json::json;
    ///
    /// let mut data = json!({});
    /// let ptr = Pointer::from_static("/foo/bar/baz");
    /// assert_eq!(ptr.delete(&mut data), None);
    /// assert_eq!(data, json!({}));
    /// ```
    /// ### Deleting a root pointer replaces the value with `Value::Null`:
    /// ```rust
    /// use jsonptr::{Pointer, Delete};
    /// use serde_json::json;
    ///
    /// let mut data = json!({ "foo": { "bar": "baz" } });
    /// let ptr = Pointer::root();
    /// assert_eq!(data.delete(&ptr), Some(json!({ "foo": { "bar": "baz" } })));
    /// assert!(data.is_null());
    /// ```
    pub fn delete(&self, value: &mut Value) -> Option<Value> {
        let Some((parent_ptr, last)) = self.split_back() else {
            // deleting at root
            return Some(mem::replace(value, Value::Null));
        };

        parent_ptr
            .resolve_mut(value)
            .ok()
            .and_then(|parent| match parent {
                Value::Array(children) => {
                    let idx = last.to_index().ok()?.for_len_incl(children.len()).ok()?;
                    children.remove(idx).into()
                }
                Value::Object(children) => children.remove(last.decoded().as_ref()),
                _ => None,
            })
    }

    /// Attempts to assign `src` to `dest` based on the path in this `Pointer`.
    ///
    /// If the path is partially available, the missing portions will be created. If the path
    /// contains a zero index, such as `"/0"`, then an array will be created. Otherwise, objects
    /// will be utilized to create the missing path.
    ///
    /// ## Example
    /// ```rust
    /// use jsonptr::Pointer;
    /// use jsonptr::prelude::*; // <-- for Assign trait
    /// use serde_json::{json, Value};
    /// let mut data = json!([]);
    ///
    /// let mut ptr = Pointer::from_static("/0/foo");
    /// let src = json!("bar");
    /// let assignment = data.assign(&ptr, src).unwrap();
    /// assert_eq!(data, json!([{ "foo": "bar" } ]));
    /// ```
    pub fn assign<'d, V>(&self, dest: &'d mut Value, src: V) -> Result<Assignment<'d>, AssignError>
    where
        V: Into<Value>,
    {
        assign_value(self, dest, src.into())
    }
}

impl Serialize for Pointer {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        <str>::serialize(&self.0, serializer)
    }
}

impl ToOwned for Pointer {
    type Owned = PointerBuf;

    fn to_owned(&self) -> Self::Owned {
        self.to_buf()
    }
}

impl PartialEq<&str> for Pointer {
    fn eq(&self, other: &&str) -> bool {
        &&self.0 == other
    }
}

impl PartialEq<str> for Pointer {
    fn eq(&self, other: &str) -> bool {
        &self.0 == other
    }
}

impl PartialEq<Pointer> for str {
    fn eq(&self, other: &Pointer) -> bool {
        self == &other.0
    }
}

impl PartialEq<String> for Pointer {
    fn eq(&self, other: &String) -> bool {
        &self.0 == other
    }
}

impl PartialEq<PointerBuf> for Pointer {
    fn eq(&self, other: &PointerBuf) -> bool {
        self.0 == other.0
    }
}

impl PartialEq<Pointer> for PointerBuf {
    fn eq(&self, other: &Pointer) -> bool {
        self.0 == other.0
    }
}

impl PartialEq<PointerBuf> for &Pointer {
    fn eq(&self, other: &PointerBuf) -> bool {
        self.0 == other.0
    }
}

impl PartialEq<&Pointer> for PointerBuf {
    fn eq(&self, other: &&Pointer) -> bool {
        self.0 == other.0
    }
}

impl From<&Pointer> for Value {
    fn from(ptr: &Pointer) -> Self {
        ptr.to_value()
    }
}

impl AsRef<str> for Pointer {
    fn as_ref(&self) -> &str {
        &self.0
    }
}

impl Borrow<str> for Pointer {
    fn borrow(&self) -> &str {
        &self.0
    }
}

impl AsRef<[u8]> for Pointer {
    fn as_ref(&self) -> &[u8] {
        self.0.as_bytes()
    }
}

impl PartialOrd<&str> for &Pointer {
    fn partial_cmp(&self, other: &&str) -> Option<Ordering> {
        PartialOrd::partial_cmp(&self.0[..], &other[..])
    }
}

impl PartialOrd<String> for Pointer {
    fn partial_cmp(&self, other: &String) -> Option<Ordering> {
        self.0.partial_cmp(other)
    }
}

impl<'a> IntoIterator for &'a Pointer {
    type Item = Token<'a>;
    type IntoIter = Tokens<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.tokens()
    }
}

/// An owned, mutable Pointer (akin to String).
///
/// This type provides methods like [`PointerBuf::push_back`] and [`PointerBuf::replace_token`] that
/// mutate the pointer in place. It also implements [`core::ops::Deref`] to [`Pointer`], meaning that
/// all methods on [`Pointer`] slices are available on `PointerBuf` values as well.
#[cfg_attr(
    feature = "url",
    doc = r##"
```rust
use jsonptr::PointerBuf;
let expected = PointerBuf::from_tokens(&["foo", "bar"]);
let url = url::Url::parse("https://example.com#/foo/bar").unwrap();
assert_eq!(expected, PointerBuf::try_from(url).unwrap())
```
"##
)]
#[derive(Clone, Default, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PointerBuf(String);

impl PointerBuf {
    /// Creates a new `PointerBuf` pointing to a document root.
    pub fn new() -> Self {
        Self(String::new())
    }

    /// Attempts to parse a string into a `PointerBuf`.
    pub fn parse(s: &str) -> Result<Self, ParseError> {
        Pointer::parse(s).map(Pointer::to_buf)
    }

    /// Creates a new `PointerBuf` with the given capacity.
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        Self(String::with_capacity(capacity))
    }
    /// Creates a new `PointerBuf` from a slice of non-encoded strings.
    pub fn from_tokens<'a, T>(tokens: impl IntoIterator<Item = T>) -> Self
    where
        T: Into<Token<'a>>,
    {
        let mut inner = String::new();
        for t in tokens.into_iter().map(|v| v.into()) {
            inner.push('/');
            inner.push_str(t.encoded());
        }
        PointerBuf(inner)
    }

    /// Coerces to a Pointer slice.
    pub fn as_ptr(&self) -> &Pointer {
        self
    }

    /// Pushes a `Token` onto the front of this `Pointer`.
    pub fn push_front(&mut self, token: Token) {
        self.0.insert(0, '/');
        self.0.insert_str(1, token.encoded());
    }

    /// Pushes a `Token` onto the back of this `Pointer`.
    pub fn push_back(&mut self, token: Token) {
        self.0.push('/');
        self.0.push_str(token.encoded());
    }

    /// Removes and returns the last `Token` in the `Pointer` if it exists.
    pub fn pop_back(&mut self) -> Option<Token<'static>> {
        if let Some(idx) = self.0.rfind('/') {
            let back = Token::from_encoded_unchecked(self.0.split_off(idx + 1));
            self.0.pop(); // remove trailing `/`
            Some(back)
        } else {
            None
        }
    }

    /// Removes and returns the first `Token` in the `Pointer` if it exists.
    pub fn pop_front(&mut self) -> Option<Token<'static>> {
        (!self.is_root()).then(|| {
            // if not root, must contain at least one `/`
            let mut token = if let Some(idx) = self.0[1..].find('/') {
                let token = self.0.split_off(idx + 1);
                core::mem::replace(&mut self.0, token)
            } else {
                core::mem::take(&mut self.0)
            };
            token.remove(0); // remove leading `/`
            Token::from_encoded_unchecked(token)
        })
    }

    /// Merges two `Pointer`s by appending `other` onto `self`.
    pub fn append(&mut self, other: &PointerBuf) -> &PointerBuf {
        if self.is_root() {
            self.0.clone_from(&other.0);
        } else if !other.is_root() {
            self.0.push_str(&other.0);
        }
        self
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
                count: self.count(),
                index,
            });
        }
        let mut tokens = self.tokens().collect::<Vec<_>>();
        if index > tokens.len() {
            return Err(ReplaceTokenError {
                count: tokens.len(),
                index,
            });
        }
        let old = tokens.get(index).map(|t| t.to_owned());
        tokens[index] = token;

        let mut buf = String::new();
        for token in tokens {
            buf.push('/');
            buf.push_str(token.encoded());
        }
        self.0 = buf;

        Ok(old)
    }

    /// Clears the `Pointer`, setting it to root (`""`).
    pub fn clear(&mut self) {
        self.0.clear();
    }
}

impl FromStr for PointerBuf {
    type Err = ParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from(s)
    }
}

impl Borrow<Pointer> for PointerBuf {
    fn borrow(&self) -> &Pointer {
        self.as_ptr()
    }
}

impl Deref for PointerBuf {
    type Target = Pointer;
    fn deref(&self) -> &Self::Target {
        Pointer::new(&self.0)
    }
}

impl<'de> Deserialize<'de> for PointerBuf {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::de::Error;
        let s = String::deserialize(deserializer)?;
        PointerBuf::try_from(s).map_err(D::Error::custom)
    }
}

impl Serialize for PointerBuf {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        String::serialize(&self.0, serializer)
    }
}

impl From<Token<'_>> for PointerBuf {
    fn from(t: Token) -> Self {
        PointerBuf::from_tokens([t])
    }
}

impl TryFrom<String> for PointerBuf {
    type Error = ParseError;
    fn try_from(value: String) -> Result<Self, Self::Error> {
        let _ = validate(&value)?;
        Ok(Self(value))
    }
}

impl From<usize> for PointerBuf {
    fn from(value: usize) -> Self {
        PointerBuf::from_tokens([value])
    }
}

impl<'a> IntoIterator for &'a PointerBuf {
    type Item = Token<'a>;
    type IntoIter = Tokens<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.tokens()
    }
}

impl TryFrom<&str> for PointerBuf {
    type Error = ParseError;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Pointer::parse(value).map(Pointer::to_buf)
    }
}

impl PartialEq<&str> for PointerBuf {
    fn eq(&self, other: &&str) -> bool {
        &self.0 == other
    }
}

impl PartialEq<str> for PointerBuf {
    fn eq(&self, other: &str) -> bool {
        self.0 == other
    }
}

impl core::fmt::Display for PointerBuf {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.0.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Resolve, ResolveError, ResolveMut};
    use alloc::vec;
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;
    use serde_json::json;

    #[test]
    #[should_panic]
    fn from_const_validates() {
        Pointer::from_static("foo/bar");
    }

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
        let ptr = Pointer::root();
        assert_eq!(data.resolve(ptr).unwrap(), &data);

        // "/foo"       ["bar", "baz"]
        let ptr = Pointer::from_static("/foo");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(["bar", "baz"]));

        // "/foo/0"     "bar"
        let ptr = Pointer::from_static("/foo/0");
        assert_eq!(data.resolve(ptr).unwrap(), &json!("bar"));

        // // "/"          0
        let ptr = Pointer::from_static("/");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(0));

        // "/a~1b"      1
        assert_eq!(data.get("a/b").unwrap(), 1);
        let ptr = Pointer::from_static("/a~1b");
        assert_eq!(ptr.as_str(), "/a~1b");
        assert_eq!(data.get("a/b").unwrap(), 1);
        assert_eq!(&ptr.first().unwrap().decoded(), "a/b");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(1));

        // "/c%d"       2
        let ptr = Pointer::from_static("/c%d");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(2));

        // // "/e^f"       3
        let ptr = Pointer::from_static("/e^f");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(3));

        // // "/g|h"       4
        let ptr = Pointer::from_static("/g|h");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(4));

        // "/i\\j"      5
        let ptr = Pointer::from_static("/i\\j");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(5));

        // // "/k\"l"      6
        let ptr = Pointer::from_static("/k\"l");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(6));

        // // "/ "         7
        let ptr = Pointer::from_static("/ ");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(7));
        // // "/m~0n"      8
        let ptr = Pointer::from_static("/m~0n");
        assert_eq!(data.resolve(ptr).unwrap(), &json!(8));
    }

    #[test]
    fn test_try_from_validation() {
        assert!(PointerBuf::try_from("").is_ok());
        assert!(PointerBuf::try_from("/").is_ok());
        assert!(PointerBuf::try_from("/foo").is_ok());

        let res = PointerBuf::try_from("/foo~");
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert!(err.is_invalid_encoding());
        assert_eq!(err.offset(), 4);
        let res = PointerBuf::try_from("foo");
        assert!(res.is_err());
        let err = res.unwrap_err();

        assert!(err.is_no_leading_backslash());
        assert_eq!(err.offset(), 0);
        assert!(PointerBuf::try_from("/foo/bar/baz/~1/~0").is_ok());
        assert_eq!(
            &PointerBuf::try_from("/foo/bar/baz/~1/~0").unwrap(),
            "/foo/bar/baz/~1/~0"
        );
    }

    #[test]
    fn test_push_pop_back() {
        let mut ptr = PointerBuf::default();
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

        let mut ptr = PointerBuf::from_tokens(["foo", "bar"]);
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
        let mut ptr = PointerBuf::try_from("/test/token").unwrap();

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
        let mut ptr = PointerBuf::default();
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
    fn pop_front_works_with_empty_strings() {
        {
            let mut ptr = PointerBuf::from_tokens(["bar", "", ""]);

            assert_eq!(ptr.tokens().count(), 3);
            let mut token = ptr.pop_front();
            assert_eq!(token, Some(Token::from_encoded_unchecked("bar")));
            assert_eq!(ptr.tokens().count(), 2);
            token = ptr.pop_front();
            assert_eq!(token, Some(Token::from_encoded_unchecked("")));
            assert_eq!(ptr.tokens().count(), 1);
            token = ptr.pop_front();
            assert_eq!(token, Some(Token::from_encoded_unchecked("")));
            assert_eq!(ptr.tokens().count(), 0);
            assert_eq!(ptr, Pointer::root());
        }
        {
            let mut ptr = PointerBuf::new();
            assert_eq!(ptr.tokens().count(), 0);
            ptr.push_back("".into());
            assert_eq!(ptr.tokens().count(), 1);
            ptr.pop_back();
            assert_eq!(ptr.tokens().count(), 0);
        }
        {
            let mut ptr = PointerBuf::new();
            let input = ["", "", "", "foo", "", "bar", "baz", ""];
            for (idx, s) in input.iter().enumerate() {
                assert_eq!(ptr.tokens().count(), idx);
                ptr.push_back((*s).into());
            }
            assert_eq!(ptr.tokens().count(), input.len());
            for (idx, s) in input.iter().enumerate() {
                assert_eq!(ptr.tokens().count(), 8 - idx);
                assert_eq!(ptr.front().unwrap().decoded(), *s);
                assert_eq!(ptr.pop_front().unwrap().decoded(), *s);
            }
            assert_eq!(ptr.tokens().count(), 0);
            assert!(ptr.front().is_none());
            assert!(ptr.pop_front().is_none());
        }
    }

    #[test]
    fn test_formatting() {
        assert_eq!(PointerBuf::from_tokens(["foo", "bar"]), "/foo/bar");
        assert_eq!(
            PointerBuf::from_tokens(["~/foo", "~bar", "/baz"]),
            "/~0~1foo/~0bar/~1baz"
        );
        assert_eq!(PointerBuf::from_tokens(["field", "", "baz"]), "/field//baz");
        assert_eq!(PointerBuf::default(), "");
    }

    #[test]
    fn test_last() {
        let ptr = Pointer::from_static("/foo/bar");

        assert_eq!(ptr.last(), Some("bar".into()));

        let ptr = Pointer::from_static("/foo/bar/-");
        assert_eq!(ptr.last(), Some("-".into()));

        let ptr = Pointer::from_static("/-");
        assert_eq!(ptr.last(), Some("-".into()));

        let ptr = Pointer::root();
        assert_eq!(ptr.last(), None);

        let ptr = Pointer::from_static("/bar");
        assert_eq!(ptr.last(), Some("bar".into()));
    }

    #[test]
    fn test_first() {
        let ptr = Pointer::from_static("/foo/bar");
        assert_eq!(ptr.first(), Some("foo".into()));

        let ptr = Pointer::from_static("/foo/bar/-");
        assert_eq!(ptr.first(), Some("foo".into()));

        let ptr = Pointer::root();
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
    fn test_resolve_unresolvable() {
        let mut data = test_data();
        let ptr = Pointer::from_static("/foo/bool/unresolvable");
        let res = ptr.resolve_mut(&mut data);

        assert!(res.is_err());
        let err = res.unwrap_err();
        assert!(err.is_unreachable());
        assert_eq!(err.offset(), 9)
    }

    #[test]
    fn test_resolve_not_found() {
        let mut data = test_data();
        let ptr = PointerBuf::from_tokens(["foo", "not_found", "nope"]);
        let res = ptr.resolve_mut(&mut data);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert!(err.is_not_found());

        match err {
            ResolveError::NotFound { offset, .. } => {
                assert_eq!(offset, 4);
            }
            _ => panic!("expected NotFound"),
        }
    }

    #[test]
    fn test_try_from() {
        let ptr = PointerBuf::from_tokens(["foo", "bar", "~/"]);

        assert_eq!(PointerBuf::try_from("/foo/bar/~0~1").unwrap(), ptr);
        let into: PointerBuf = "/foo/bar/~0~1".try_into().unwrap();
        assert_eq!(ptr, into);
    }

    #[test]
    fn test_resolve_mut_unresolvable_error() {
        let mut data = test_data();
        let ptr = Pointer::from_static("/foo/bool/unresolvable/not-in-token");
        let res = ptr.resolve_mut(&mut data);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert!(err.is_unreachable());
        assert_eq!(err.offset(), 9);

        let ptr = Pointer::from_static("/foo/bool/unresolvable");
        let res = ptr.resolve_mut(&mut data);
        let err = res.unwrap_err();
        assert!(err.is_unreachable());
        assert_eq!(err.offset(), 9);

        let mut data = json!({"foo": "bar"});
        let ptr = PointerBuf::try_from("/foo/unresolvable").unwrap();
        let err = data.resolve_mut(&ptr).unwrap_err();
        assert!(err.is_unreachable());
        assert_eq!(err.offset(), 4);
    }

    #[test]
    fn test_resolve_unresolvable_error() {
        let data = test_data();
        let ptr = Pointer::from_static("/foo/bool/unresolvable/not-in-token");
        let res = ptr.resolve(&data);
        assert!(res.is_err());
        let err = res.unwrap_err();
        assert!(err.is_unreachable());
        assert_eq!(err.offset(), 9);
    }

    #[test]
    fn pop_back_works_with_empty_strings() {
        {
            let mut ptr = PointerBuf::new();
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
            assert_eq!(ptr, PointerBuf::new());
        }
        {
            let mut ptr = PointerBuf::new();
            assert_eq!(ptr.tokens().count(), 0);
            ptr.push_back("".into());
            assert_eq!(ptr.tokens().count(), 1);
            ptr.pop_back();
            assert_eq!(ptr.tokens().count(), 0);
        }
        {
            let mut ptr = PointerBuf::new();
            let input = ["", "", "", "foo", "", "bar", "baz", ""];
            for (idx, s) in input.iter().enumerate() {
                assert_eq!(ptr.tokens().count(), idx);
                ptr.push_back((*s).into());
            }
            assert_eq!(ptr.tokens().count(), input.len());
            for (idx, s) in input.iter().enumerate().rev() {
                assert_eq!(ptr.tokens().count(), idx + 1);
                assert_eq!(ptr.back().unwrap().decoded(), *s);
                assert_eq!(ptr.pop_back().unwrap().decoded(), *s);
            }
            assert_eq!(ptr.tokens().count(), 0);
            assert!(ptr.back().is_none());
            assert!(ptr.pop_back().is_none());
        }
    }

    #[test]
    fn intersect() {
        let base = Pointer::from_static("/foo/bar");
        let a = Pointer::from_static("/foo/bar/qux");
        let b = Pointer::from_static("/foo/bar");
        assert_eq!(a.intersection(b), base);

        let base = Pointer::from_static("");
        let a = Pointer::from_static("/foo");
        let b = Pointer::from_static("/");
        assert_eq!(a.intersection(b), base);

        let base = Pointer::from_static("");
        let a = Pointer::from_static("/fooqux");
        let b = Pointer::from_static("/foobar");
        assert_eq!(a.intersection(b), base);
    }

    #[test]
    #[cfg(feature = "fluent-uri")]
    fn test_try_from_fluent_uri() {
        let uri = fluent_uri::Uri::parse("#/foo/bar").unwrap();
        let ptr = PointerBuf::try_from(&uri).unwrap();
        assert_eq!(ptr, "/foo/bar");
    }

    #[quickcheck]
    fn qc_pop_and_push(mut ptr: PointerBuf) -> bool {
        let original_ptr = ptr.clone();
        let mut tokens = Vec::with_capacity(ptr.count());
        while let Some(token) = ptr.pop_back() {
            tokens.push(token);
        }
        if ptr.count() != 0 || !ptr.is_root() || ptr.last().is_some() || ptr.first().is_some() {
            return false;
        }
        for token in tokens.drain(..) {
            ptr.push_front(token);
        }
        if ptr != original_ptr {
            return false;
        }
        while let Some(token) = ptr.pop_front() {
            tokens.push(token);
        }
        if ptr.count() != 0 || !ptr.is_root() || ptr.last().is_some() || ptr.first().is_some() {
            return false;
        }
        for token in tokens {
            ptr.push_back(token);
        }
        ptr == original_ptr
    }

    #[quickcheck]
    fn qc_split(ptr: PointerBuf) -> bool {
        if let Some((head, tail)) = ptr.split_front() {
            {
                let Some(first) = ptr.first() else {
                    return false;
                };
                if first != head {
                    return false;
                }
            }
            {
                let mut copy = ptr.clone();
                copy.pop_front();
                if copy != tail {
                    return false;
                }
            }
            {
                let mut buf = tail.to_buf();
                buf.push_front(head.clone());
                if buf != ptr {
                    return false;
                }
            }
            {
                let fmt = alloc::format!("/{}{tail}", head.encoded());
                if Pointer::parse(&fmt).unwrap() != ptr {
                    return false;
                }
            }
        } else {
            return ptr.is_root()
                && ptr.count() == 0
                && ptr.last().is_none()
                && ptr.first().is_none();
        }
        if let Some((head, tail)) = ptr.split_back() {
            {
                let Some(last) = ptr.last() else {
                    return false;
                };
                if last != tail {
                    return false;
                }
            }
            {
                let mut copy = ptr.clone();
                copy.pop_back();
                if copy != head {
                    return false;
                }
            }
            {
                let mut buf = head.to_buf();
                buf.push_back(tail.clone());
                if buf != ptr {
                    return false;
                }
            }
            {
                let fmt = alloc::format!("{head}/{}", tail.encoded());
                if Pointer::parse(&fmt).unwrap() != ptr {
                    return false;
                }
            }
            if Some(head) != ptr.parent() {
                return false;
            }
        } else {
            return ptr.is_root()
                && ptr.count() == 0
                && ptr.last().is_none()
                && ptr.first().is_none();
        }
        true
    }

    #[quickcheck]
    fn qc_from_tokens(tokens: Vec<String>) -> bool {
        let buf = PointerBuf::from_tokens(&tokens);
        let reconstructed: Vec<_> = buf.tokens().collect();
        reconstructed
            .into_iter()
            .zip(tokens)
            .all(|(a, b)| a.decoded() == b)
    }

    #[quickcheck]
    fn qc_intersection(base: PointerBuf, suffix_0: PointerBuf, suffix_1: PointerBuf) -> TestResult {
        if suffix_0.first() == suffix_1.first() {
            // base must be the true intersection
            return TestResult::discard();
        }
        let mut a = base.clone();
        a.append(&suffix_0);
        let mut b = base.clone();
        b.append(&suffix_1);
        let isect = a.intersection(&b);
        TestResult::from_bool(isect == base)
    }
}
