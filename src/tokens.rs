use std::str::Split;

use crate::Token;

/// An iterator over the tokens in a Pointer.
#[derive(Debug)]
pub struct Tokens<'a> {
    inner: Split<'a, char>,
}

impl<'a> Iterator for Tokens<'a> {
    type Item = Token;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(Token::from_encoded)
    }
}
impl<'t> Tokens<'t> {
    pub(crate) fn new(split: Split<char>) -> Tokens {
        Tokens { inner: split }
    }
}
