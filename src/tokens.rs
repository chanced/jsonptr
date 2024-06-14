use core::str::Split;

use crate::Token;

/// An iterator over the tokens in a Pointer.
#[derive(Debug)]
pub struct Tokens<'a> {
    inner: Split<'a, char>,
}

impl<'a> Iterator for Tokens<'a> {
    type Item = Token<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(Token::from_encoded)
    }
}
impl<'t> Tokens<'t> {
    pub(crate) fn new(inner: Split<'t, char>) -> Self {
        Self { inner }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_from() {
        assert_eq!(Token::from("/").encoded(), "~1");
        assert_eq!(Token::from("~/").encoded(), "~0~1");
    }
    #[test]
    fn test_from_encoded() {
        assert_eq!(Token::from_encoded("~1").encoded(), "~1");
        assert_eq!(Token::from_encoded("~0~1").encoded(), "~0~1");
        let t = Token::from_encoded("a~1b");
        assert_eq!(t.decoded(), "a/b");
    }
}
