use crate::{Token, MALFORMED_TOKEN_ERR};
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
            inner.push('/');
            inner.push_str(t.encoded());
        }
        if inner.is_empty() {
            inner.push('/');
        }
        Pointer { inner }
    }

    pub fn default() -> Self {
        Pointer {
            inner: String::from("/"),
        }
    }

    pub fn push_front(&mut self, token: impl AsRef<str>) {
        if self.inner == "/" {
            self.inner.push_str(token.as_ref());
            return;
        }
        self.inner.insert(0, '/');
        self.inner.insert_str(1, token.as_ref());
    }
    pub fn push_back(&mut self, token: impl Into<Token>) {
        if !self.inner.ends_with('/') {
            self.inner.push('/');
        }
        self.inner.push_str(token.into().encoded());
    }
    pub fn pop_back(&mut self) -> Option<Token> {
        self.rsplit_once().map(|(rest, last)| {
            self.inner = rest;
            last.into()
        })
    }
    pub fn pop_front(&mut self) -> Option<Token> {
        self.split_once().map(|(front, rest)| {
            self.inner = "/".to_string() + &rest;
            front.into()
        })
    }

    /// Returns the number of tokens in the Json Pointer.
    pub fn count(&self) -> usize {
        if self.inner == "/" {
            return 0;
        }
        self.inner.matches('/').count()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 1
    }
    pub fn is_root(&self) -> bool {
        self.inner.len() == 1
    }
    pub fn back(&self) -> Option<Token> {
        self.rsplit_once().map(|(_, last)| last.into())
    }
    pub fn front(&self) -> Option<Token> {
        self.split_once().map(|(front, _)| front.into())
    }
    pub fn append(&mut self, other: &Pointer) {
        if !other.is_root() {
            self.inner.push_str(other)
        }
    }

    pub fn clear(&mut self) {
        self.inner = "/".to_string()
    }

    pub fn tokens(&self) -> Tokens {
        Tokens {
            inner: self.split(),
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
            let (front, back) = self.inner[1..].split_once('/').expect(MALFORMED_TOKEN_ERR);
            Some((front.to_owned(), back.to_owned()))
        }
    }

    fn rsplit_once(&self) -> Option<(String, String)> {
        if self.is_root() {
            None
        } else {
            let (front, back) = self.inner.rsplit_once('/').expect(MALFORMED_TOKEN_ERR);
            Some((front.to_owned(), back.to_owned()))
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

/// An iterator over the tokens in a Pointer.
pub struct Tokens<'a> {
    inner: Split<'a, char>,
}

impl<'a> Iterator for Tokens<'a> {
    type Item = Token;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(Into::into)
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
    fn test_mutation() {
        let mut ptr = Pointer::default();
        assert_eq!(ptr, "/");

        assert_eq!(ptr.count(), 0);

        ptr.push_front("foo");
        assert_eq!(ptr, "/foo");
        assert_eq!(ptr.count(), 1);

        ptr.push_back("bar");
        assert_eq!(ptr, "/foo/bar");
        assert_eq!(ptr.count(), 2);
        ptr.push_front("too");
        assert_eq!(ptr, "/too/foo/bar");
        assert_eq!(ptr.count(), 3);

        let token = ptr.pop_front();
        assert_eq!(token, Some("too".into()));
        assert_eq!(ptr, "/foo/bar");
        assert_eq!(ptr.count(), 2);

        let token = ptr.pop_back();
        assert_eq!(token, Some("bar".into()));
        assert_eq!(ptr, "/foo");
        assert_eq!(ptr.count(), 1);
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
}
