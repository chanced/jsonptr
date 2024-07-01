use crate::{InvalidEncodingError, ParseError, ReplaceTokenError, Token, Tokens};
use alloc::{
    borrow::ToOwned,
    string::{String, ToString},
    vec::Vec,
};
use core::{borrow::Borrow, cmp::Ordering, ops::Deref, str::FromStr};

/*
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║                                   Pointer                                    ║
║                                  ¯¯¯¯¯¯¯¯¯                                   ║
╚══════════════════════════════════════════════════════════════════════════════╝
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
*/

/// A JSON Pointer is a string containing a sequence of zero or more reference
/// tokens, each prefixed by a '/' character.
///
/// See [RFC 6901 for more
/// information](https://datatracker.ietf.org/doc/html/rfc6901).
///
/// ## Example
/// ```rust
/// use jsonptr::{Pointer, resolve::Resolve};
/// use serde_json::{json, Value};
///
/// let data = json!({ "foo": { "bar": "baz" } });
/// let ptr = Pointer::from_static("/foo/bar");
/// let bar = data.resolve(&ptr).unwrap();
/// assert_eq!(bar, "baz");
/// ```
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
// See https://doc.rust-lang.org/src/std/path.rs.html#1985
#[cfg_attr(not(doc), repr(transparent))]
pub struct Pointer(str);

impl Default for &'static Pointer {
    fn default() -> Self {
        Pointer::root()
    }
}
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
        unsafe { &*(core::ptr::from_ref::<str>(s.as_ref()) as *const Self) }
    }

    /// Constant reference to a root pointer
    pub const fn root() -> &'static Self {
        // unsafe { &*(core::ptr::from_ref::<str>("") as *const Self) }
        #[allow(clippy::ref_as_ptr)]
        unsafe {
            &*("" as *const str as *const Self)
        }
    }

    /// Attempts to parse a string into a `Pointer`.
    ///
    /// If successful, this does not allocate.
    ///
    /// ## Errors
    /// Returns a `ParseError` if the string is not a valid JSON Pointer.
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
    /// use jsonptr::{Pointer, resolve::Resolve};
    /// use serde_json::{json, Value};
    ///
    /// const POINTER: &Pointer = Pointer::from_static("/foo/bar");
    /// let data = json!({ "foo": { "bar": "baz" } });
    /// let bar = data.resolve(POINTER).unwrap();
    /// assert_eq!(bar, "baz");
    /// ````
    pub const fn from_static(s: &'static str) -> &'static Self {
        assert!(validate(s).is_ok(), "invalid json pointer");
        unsafe { &*(core::ptr::from_ref::<str>(s) as *const Self) }
    }

    /// The encoded string representation of this `Pointer`
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Converts into an owned [`PointerBuf`]
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
    #[cfg(feature = "json")]
    pub fn to_json_value(&self) -> serde_json::Value {
        serde_json::Value::String(self.0.to_string())
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
            .find('/')
            .map_or_else(
                || (Token::from_encoded_unchecked(&self.0[1..]), Self::root()),
                |idx| {
                    let (front, back) = self.0[1..].split_at(idx);
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
    /// assert_eq!(ptr.split_at(3), None);
    /// ```
    pub fn split_at(&self, idx: usize) -> Option<(&Self, &Self)> {
        if self.0.as_bytes().get(idx).copied() != Some(b'/') {
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
        self.tokens().nth(index).clone()
    }

    /// Attempts to resolve a `Value` based on the path in this `Pointer`.
    ///
    /// ## Errors
    /// Returns [`R::Error`](`Resolve::Error`) if an error occurs while
    /// resolving.
    ///
    /// The rules of such are determined by the `R`'s implementation of
    /// [`Resolve`] but provided implementations return
    /// [`ResolveError`](crate::resolve::ResolveError) if:
    /// - The path is unreachable (e.g. a scalar is encountered prior to the end
    ///   of the path)
    /// - The path is not found (e.g. a key in an object or an index in an array
    ///   does not exist)
    /// - An [`Token`] cannot be parsed as an array
    ///   [`Index`](crate::index::Index)
    /// - An array [`Index`](crate::index::Index) is out of bounds
    #[cfg(feature = "resolve")]
    pub fn resolve<'v, R: crate::Resolve>(&self, value: &'v R) -> Result<&'v R::Value, R::Error> {
        value.resolve(self)
    }

    /// Attempts to resolve a mutable `Value` based on the path in this `Pointer`.
    ///
    /// ## Errors
    /// Returns [`R::Error`](`ResolveMut::Error`) if an error occurs while
    /// resolving.
    ///
    /// The rules of such are determined by the `R`'s implementation of
    /// [`ResolveMut`] but provided implementations return
    /// [`ResolveError`](crate::resolve::ResolveError) if:
    /// - The path is unreachable (e.g. a scalar is encountered prior to the end
    ///   of the path)
    /// - The path is not found (e.g. a key in an object or an index in an array
    ///   does not exist)
    /// - An [`Token`] cannot be parsed as an array
    ///   [`Index`](crate::index::Index)
    /// - An array [`Index`](crate::index::Index) is out of bounds
    #[cfg(feature = "resolve")]
    pub fn resolve_mut<'v, R: crate::ResolveMut>(
        &self,
        value: &'v mut R,
    ) -> Result<&'v mut R::Value, R::Error> {
        value.resolve_mut(self)
    }

    /// Finds the commonality between this and another `Pointer`.
    pub fn intersection<'a>(&'a self, other: &Self) -> &'a Self {
        if self.is_root() || other.is_root() {
            return Self::root();
        }
        let mut idx = 0;
        for (a, b) in self.tokens().zip(other.tokens()) {
            if a != b {
                break;
            }
            idx += a.encoded().len() + 1;
        }
        self.split_at(idx).map_or(self, |(head, _)| head)
    }

    /// Attempts to delete a `serde_json::Value` based upon the path in this
    /// `Pointer`.
    ///
    /// The rules of deletion are determined by the `D`'s implementation of
    /// [`Delete`]. The supplied implementations (`"json"` & `"toml"`) operate
    /// as follows:
    /// - If the `Pointer` can be resolved, the `Value` is deleted and returned.
    /// - If the `Pointer` fails to resolve for any reason, `Ok(None)` is returned.
    /// - If the `Pointer` is root, `value` is replaced:
    ///     - `"json"`: `serde_json::Value::Null`
    ///     - `"toml"`: `toml::Value::Table::Default`
    ///
    ///
    /// ## Examples
    /// ### Deleting a resolved pointer:
    /// ```rust
    /// use jsonptr::{Pointer, delete::Delete};
    /// use serde_json::json;
    ///
    /// let mut data = json!({ "foo": { "bar": { "baz": "qux" } } });
    /// let ptr = Pointer::from_static("/foo/bar/baz");
    /// assert_eq!(data.delete(&ptr), Some("qux".into()));
    /// assert_eq!(data, json!({ "foo": { "bar": {} } }));
    /// ```
    /// ### Deleting a non-existent Pointer returns `None`:
    /// ```rust
    /// use jsonptr::{ Pointer, delete::Delete };
    /// use serde_json::json;
    ///
    /// let mut data = json!({});
    /// let ptr = Pointer::from_static("/foo/bar/baz");
    /// assert_eq!(ptr.delete(&mut data), None);
    /// assert_eq!(data, json!({}));
    /// ```
    /// ### Deleting a root pointer replaces the value with `Value::Null`:
    /// ```rust
    /// use jsonptr::{Pointer, delete::Delete};
    /// use serde_json::json;
    ///
    /// let mut data = json!({ "foo": { "bar": "baz" } });
    /// let ptr = Pointer::root();
    /// assert_eq!(data.delete(&ptr), Some(json!({ "foo": { "bar": "baz" } })));
    /// assert!(data.is_null());
    /// ```
    #[cfg(feature = "delete")]
    pub fn delete<D: crate::Delete>(&self, value: &mut D) -> Option<D::Value> {
        value.delete(self)
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
    /// use serde_json::{json, Value};
    ///
    /// let mut data = json!([]);
    /// let mut ptr = Pointer::from_static("/0/foo");
    /// let replaced = ptr.assign(&mut data, json!("bar")).unwrap();
    /// assert_eq!(data, json!([{"foo": "bar"}]));
    /// assert_eq!(replaced, None);
    /// ```
    ///
    /// ## Errors
    /// Returns [`Assign::Error`] if the path is invalid or if the value cannot be assigned.
    ///
    #[cfg(feature = "assign")]
    pub fn assign<D, V>(&self, dest: &mut D, src: V) -> Result<Option<D::Value>, D::Error>
    where
        D: crate::Assign,
        V: Into<D::Value>,
    {
        dest.assign(self, src)
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for Pointer {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        <str>::serialize(&self.0, serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de: 'p, 'p> serde::Deserialize<'de> for &'p Pointer {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::de::{Error, Visitor};

        struct PointerVisitor;

        impl<'a> Visitor<'a> for PointerVisitor {
            type Value = &'a Pointer;

            fn expecting(&self, formatter: &mut core::fmt::Formatter) -> core::fmt::Result {
                formatter.write_str("a borrowed Pointer")
            }

            fn visit_borrowed_str<E>(self, v: &'a str) -> Result<Self::Value, E>
            where
                E: Error,
            {
                Pointer::parse(v).map_err(|err| {
                    Error::custom(format!("failed to parse json pointer\n\ncaused by:\n{err}"))
                })
            }
        }

        deserializer.deserialize_str(PointerVisitor)
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
impl PartialEq<PointerBuf> for String {
    fn eq(&self, other: &PointerBuf) -> bool {
        self == &other.0
    }
}
impl PartialEq<String> for PointerBuf {
    fn eq(&self, other: &String) -> bool {
        &self.0 == other
    }
}
impl AsRef<Pointer> for Pointer {
    fn as_ref(&self) -> &Pointer {
        self
    }
}
impl AsRef<Pointer> for PointerBuf {
    fn as_ref(&self) -> &Pointer {
        self
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

#[cfg(feature = "json")]
impl From<&Pointer> for serde_json::Value {
    fn from(ptr: &Pointer) -> Self {
        ptr.to_json_value()
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
        self.0.partial_cmp(other.as_str())
    }
}

impl<'a> IntoIterator for &'a Pointer {
    type Item = Token<'a>;
    type IntoIter = Tokens<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.tokens()
    }
}

/*
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║                                  PointerBuf                                  ║
║                                 ¯¯¯¯¯¯¯¯¯¯¯¯                                 ║
╚══════════════════════════════════════════════════════════════════════════════╝
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
*/

/// An owned, mutable Pointer (akin to String).
///
/// This type provides methods like [`PointerBuf::push_back`] and
/// [`PointerBuf::replace_token`] that mutate the pointer in place. It also
/// implements [`core::ops::Deref`] to [`Pointer`], meaning that all methods on
/// [`Pointer`] slices are available on `PointerBuf` values as well.
#[derive(Clone, Default, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PointerBuf(String);

impl PointerBuf {
    /// Creates a new `PointerBuf` pointing to a document root.
    pub fn new() -> Self {
        Self(String::new())
    }

    /// Attempts to parse a string into a `PointerBuf`.
    ///
    /// ## Errors
    /// Returns a `ParseError` if the string is not a valid JSON Pointer.
    pub fn parse<S: AsRef<str> + ?Sized>(s: &S) -> Result<Self, ParseError> {
        Pointer::parse(&s).map(Pointer::to_buf)
    }

    /// Creates a new `PointerBuf` from a slice of non-encoded strings.
    pub fn from_tokens<'a, T>(tokens: impl IntoIterator<Item = T>) -> Self
    where
        T: Into<Token<'a>>,
    {
        let mut inner = String::new();
        for t in tokens.into_iter().map(Into::into) {
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
    pub fn append<P: AsRef<Pointer>>(&mut self, other: P) -> &PointerBuf {
        let other = other.as_ref();
        if self.is_root() {
            self.0 = other.0.to_string();
        } else if !other.is_root() {
            self.0.push_str(&other.0);
        }
        self
    }

    /// Attempts to replace a `Token` by the index, returning the replaced
    /// `Token` if it already exists. Returns `None` otherwise.
    ///
    /// ## Errors
    /// A [`ReplaceTokenError`] is returned if the index is out of bounds.
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
        let old = tokens.get(index).map(super::token::Token::to_owned);
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

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for PointerBuf {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::de::Error;
        let s = String::deserialize(deserializer)?;
        PointerBuf::try_from(s).map_err(D::Error::custom)
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for PointerBuf {
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

const fn validate(value: &str) -> Result<&str, ParseError> {
    if value.is_empty() {
        return Ok(value);
    }
    let bytes = value.as_bytes();
    if bytes[0] != b'/' {
        return Err(ParseError::NoLeadingBackslash);
    }
    let mut ptr_offset = 0; // offset within the pointer of the most recent '/' seperator
    let mut tok_offset = 0; // offset within the current token

    let bytes = value.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'/' => {
                // backslashes ('/') seperate tokens
                // we increment the ptr_offset to point to this character
                ptr_offset = i;
                // and reset the token offset
                tok_offset = 0;
            }
            b'~' => {
                // if the character is a '~', then the next character must be '0' or '1'
                // otherwise the encoding is invalid and `InvalidEncodingError` is returned
                if i + 1 >= bytes.len() || (bytes[i + 1] != b'0' && bytes[i + 1] != b'1') {
                    // the pointer is not properly encoded
                    //
                    // we use the pointer offset, which points to the last
                    // encountered seperator, as the offset of the error.
                    // The source `InvalidEncodingError` then uses the token
                    // offset.
                    //
                    // "/foo/invalid~encoding"
                    //      ^       ^
                    //      |       |
                    //  ptr_offset  |
                    //          tok_offset
                    //
                    return Err(ParseError::InvalidEncoding {
                        offset: ptr_offset,
                        source: InvalidEncodingError { offset: tok_offset },
                    });
                }
                // already checked the next character, so we skip it
                i += 1;
                // incrementing the pointer offset since the next byte has
                // already been checked
                tok_offset += 1;
            }
            _ => {}
        }
        i += 1;
        // not a seperator so we increment the token offset
        tok_offset += 1;
    }
    Ok(value)
}

/*
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║                                    Tests                                     ║
║                                   ¯¯¯¯¯¯¯                                    ║
╚══════════════════════════════════════════════════════════════════════════════╝
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
*/

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;

    #[test]
    #[should_panic = "invalid json pointer"]
    fn from_const_validates() {
        let _ = Pointer::from_static("foo/bar");
    }

    #[test]
    fn test_parse() {
        let tests = [
            ("", Ok("")),
            ("/", Ok("/")),
            ("/foo", Ok("/foo")),
            ("/foo/bar", Ok("/foo/bar")),
            ("/foo/bar/baz", Ok("/foo/bar/baz")),
            ("/foo/bar/baz/~0", Ok("/foo/bar/baz/~0")),
            ("/foo/bar/baz/~1", Ok("/foo/bar/baz/~1")),
            ("/foo/bar/baz/~01", Ok("/foo/bar/baz/~01")),
            ("/foo/bar/baz/~10", Ok("/foo/bar/baz/~10")),
            ("/foo/bar/baz/~11", Ok("/foo/bar/baz/~11")),
            ("/foo/bar/baz/~1/~0", Ok("/foo/bar/baz/~1/~0")),
            ("missing-slash", Err(ParseError::NoLeadingBackslash)),
            (
                "/~",
                Err(ParseError::InvalidEncoding {
                    offset: 0,
                    source: InvalidEncodingError { offset: 1 },
                }),
            ),
            (
                "/~2",
                Err(ParseError::InvalidEncoding {
                    offset: 0,
                    source: InvalidEncodingError { offset: 1 },
                }),
            ),
            (
                "/~a",
                Err(ParseError::InvalidEncoding {
                    offset: 0,
                    source: InvalidEncodingError { offset: 1 },
                }),
            ),
        ];
        for (input, expected) in tests {
            let actual = Pointer::parse(input).map(Pointer::as_str);
            assert_eq!(
                actual, expected,
                "pointer parsing failed to meet expectations
                \ninput: {input}
                \nexpected:\n{expected:#?}
                \nactual:\n{actual:#?}",
            );
        }
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

    #[test]
    fn test_pointerbuf_try_from() {
        let ptr = PointerBuf::from_tokens(["foo", "bar", "~/"]);

        assert_eq!(PointerBuf::try_from("/foo/bar/~0~1").unwrap(), ptr);
        let into: PointerBuf = "/foo/bar/~0~1".try_into().unwrap();
        assert_eq!(ptr, into);
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
        if isect != base {
            println!("\nintersection failed\nbase: {base:?}\nisect: {isect:?}\nsuffix_0: {suffix_0:?}\nsuffix_1: {suffix_1:?}\n");
        }
        TestResult::from_bool(isect == base)
    }

    #[test]
    fn test_intersection() {
        struct Test {
            base: &'static str,
            a_suffix: &'static str,
            b_suffix: &'static str,
        }

        let tests = [
            Test {
                base: "",
                a_suffix: "/",
                b_suffix: "/a/b/c",
            },
            Test {
                base: "/a",
                a_suffix: "/",
                b_suffix: "/suffix",
            },
            Test {
                base: "/a",
                a_suffix: "/suffix",
                b_suffix: "",
            },
            Test {
                base: "/¦\\>‶“lv\u{eedd}\u{8a}Y\n\u{99}𘐷vT\n\u{4}Hª\\ 嗱\\Yl6Y`\"1\u{6dd}\u{17}\0\u{10}ዄ8\"Z닍6i)V;\u{6be4c}\u{b}\u{59836}`\u{1e}㑍§~05\u{1d}\u{8a}[뵔\u{437c3}j\u{f326}\";*\u{c}*U\u{1b}\u{8a}I\u{4}묁",
                a_suffix: "/Y\u{2064}",
                b_suffix: "",
            }
        ];

        for Test {
            base,
            a_suffix,
            b_suffix,
        } in tests
        {
            let base = PointerBuf::parse(base).expect(&format!("failed to parse ${base}"));
            let mut a = base.clone();
            let mut b = base.clone();
            a.append(&PointerBuf::parse(a_suffix).unwrap());
            b.append(&PointerBuf::parse(b_suffix).unwrap());
            let intersection = a.intersection(&b);
            assert_eq!(
                intersection, base,
                "\nintersection failed\n\nbase:{base}\na_suffix:{a_suffix}\nb_suffix:{b_suffix} expected: \"{base}\"\n   actual: \"{intersection}\"\n"
            );
        }
    }
}
