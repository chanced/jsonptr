use core::str::Split;

use crate::Token;

/*
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║                                    Tokens                                    ║
║                                   ¯¯¯¯¯¯¯¯                                   ║
╚══════════════════════════════════════════════════════════════════════════════╝
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
*/

/// An iterator over the tokens in a Pointer.
#[derive(Debug)]
pub struct Tokens<'a> {
    inner: Split<'a, char>,
}

impl<'a> Iterator for Tokens<'a> {
    type Item = Token<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(Token::from_encoded_unchecked)
    }
}
impl<'t> Tokens<'t> {
    pub(crate) fn new(inner: Split<'t, char>) -> Self {
        Self { inner }
    }
}
