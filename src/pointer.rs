use url::Url;

use crate::{MalformedPointerError, Token, Tokens};
use std::{
    borrow::Borrow,
    cmp::Ordering,
    fmt::{Debug, Display},
    hash::{Hash, Hasher},
    ops::Deref,
    str::Split,
};

#[derive(Clone)]
pub struct Pointer {
    inner: String,
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
        Pointer { inner }
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
    /// Merges the `Pointer` `other` into `self` by appending `other` onto `self`.
    pub fn append(&mut self, other: &Pointer) -> &Pointer {
        if !other.is_root() {
            self.inner.push_str(other);
        }
        self
    }

    pub fn get(&mut self, index: usize) -> Option<Token> {
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

    pub fn tokens(&self) -> Tokens {
        Tokens::new(self.split())
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

impl TryFrom<&str> for Pointer {
    type Error = MalformedPointerError;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let mut value = value;
        if value.starts_with('#') {
            value = &value[1..];
        }
        if !value.starts_with('/') {
            Err(MalformedPointerError::new(value.to_owned()))
        } else {
            Ok(Pointer {
                inner: value.to_owned(),
            })
        }
    }
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

// impl Deref for JsonPointer {
//     type Target = str;
//     fn deref(&self) -> &Self::Target {
//         self.in
//     }
// }
// impl Hash for JsonPointer {
//     #[inline]
//     fn hash<H: Hasher>(&self, hasher: &mut H) {
//         (**self).hash(hasher)
//     }
// }

#[cfg(test)]
mod test {
    use crate::Pointer;

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
}
