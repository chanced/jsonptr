use crate::Token;
use std::{
    borrow::Borrow,
    cmp::Ordering,
    fmt::{Debug, Display},
    hash::{Hash, Hasher},
    ops::Deref,
};

const MALFORMED_TOKEN_ERR:&str = "the Json Pointer was empty which should never happen.\nPlease report this bug: https://github.com/chanced/jsonptr/issues/new.";

#[derive(Clone)]
pub struct JsonPointer {
    inner: String,
}

impl JsonPointer {
    pub fn new(tokens: &[impl AsRef<str>]) -> Self {
        let mut inner = String::new();
        for t in tokens.iter().map(Token::new) {
            inner.push('/');
            inner.push_str(t.encoded());
        }
        if inner.is_empty() {
            inner.push('/');
        }
        JsonPointer { inner }
    }

    pub fn default() -> Self {
        JsonPointer {
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
        let split = || {
            let (front, back) = self.inner.rsplit_once('/').expect(MALFORMED_TOKEN_ERR);
            (front.to_owned(), back.to_owned())
        };
        if self.inner == "/" {
            return None;
        }
        let (rest, last) = split();
        self.inner = rest;
        Some(last.into())
    }
    pub fn pop_front(&mut self) -> Option<Token> {
        if self.inner == "/" {
            return None;
        }
        let split = |s: &str| {
            let (front, back) = s.split_once('/').expect(MALFORMED_TOKEN_ERR);
            (front.to_owned(), back.to_owned())
        };

        let (front, rest) = split(&self.inner[1..]);
        self.inner = "/".to_string() + &rest;
        Some(front.into())
    }
    /// Returns the number of tokens in the Json Pointer.
    pub fn count(&self) -> usize {
        if self.inner == "/" {
            return 0;
        }
        self.inner.matches('/').count()
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn is_root(&self) -> bool {
        // self.tokens.is_empty()
        todo!()
    }
    pub fn back(&self) -> Option<&Token> {
        // self.tokens.back()
        todo!()
    }
    pub fn front(&self) -> Option<&Token> {
        // self.tokens.front()
        todo!()
    }
    pub fn append(&mut self, other: &mut JsonPointer) {
        todo!()
    }
    pub fn clear(&mut self) {
        self.inner = "/".to_string()
    }
}

impl Eq for JsonPointer {}
impl Deref for JsonPointer {
    type Target = str;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl AsRef<str> for JsonPointer {
    fn as_ref(&self) -> &str {
        &self.inner
    }
}
impl Borrow<str> for JsonPointer {
    fn borrow(&self) -> &str {
        &self.inner
    }
}
impl From<Token> for JsonPointer {
    fn from(t: Token) -> Self {
        JsonPointer::new(&[t])
    }
}

impl PartialEq<&str> for JsonPointer {
    fn eq(&self, other: &&str) -> bool {
        &self.inner == other
    }
}

impl PartialEq<JsonPointer> for JsonPointer {
    fn eq(&self, other: &JsonPointer) -> bool {
        self.inner == other.inner
    }
}

impl PartialEq<JsonPointer> for str {
    fn eq(&self, other: &JsonPointer) -> bool {
        self == other.inner
    }
}
impl PartialEq<String> for JsonPointer {
    fn eq(&self, other: &String) -> bool {
        &self.inner == other
    }
}
impl PartialOrd<&str> for JsonPointer {
    fn partial_cmp(&self, other: &&str) -> Option<Ordering> {
        PartialOrd::partial_cmp(&self.inner[..], &other[..])
    }
}
impl PartialOrd<String> for JsonPointer {
    fn partial_cmp(&self, other: &String) -> Option<Ordering> {
        self.inner.partial_cmp(other)
    }
}
impl PartialOrd<JsonPointer> for JsonPointer {
    fn partial_cmp(&self, other: &JsonPointer) -> Option<Ordering> {
        self.inner.partial_cmp(&other.inner)
    }
}
impl PartialEq<JsonPointer> for String {
    fn eq(&self, other: &JsonPointer) -> bool {
        PartialEq::eq(&self[..], &other.inner[..])
    }
}

impl PartialOrd<JsonPointer> for String {
    fn partial_cmp(&self, other: &JsonPointer) -> Option<Ordering> {
        self.partial_cmp(&other.inner)
    }
}
impl Hash for JsonPointer {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.inner.hash(state)
    }
}

impl Debug for JsonPointer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner)
    }
}
impl Display for JsonPointer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner)
    }
}

pub struct Iter {
    inner: std::str::Split<'static, char>,
}

impl Iterator for Iter {
    type Item = Token;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|s| s.into())
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
    use crate::JsonPointer;

    #[test]
    fn test_mutation() {
        let mut ptr = JsonPointer::default();
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
        assert_eq!(JsonPointer::new(&["foo", "bar"]), "/foo/bar");
        assert_eq!(
            JsonPointer::new(&["~/foo", "~bar", "/baz"]),
            "/~0~1foo/~0bar/~1baz"
        );
        assert_eq!(JsonPointer::new(&["field", "", "baz"]), "/field//baz");
        assert_eq!(JsonPointer::default(), "/");
    }
}
