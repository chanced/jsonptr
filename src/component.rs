use crate::{Pointer, Token, Tokens};

pub enum Component<'t> {
    /// The document root
    Root,
    /// A segment of a JSON Pointer
    Token(Token<'t>),
}
impl<'t> From<Token<'t>> for Component<'t> {
    fn from(token: Token<'t>) -> Self {
        Self::Token(token)
    }
}

pub struct Components<'t> {
    tokens: Tokens<'t>,
}
impl<'t> Components<'t> {
    pub(crate) fn new(tokens: Tokens<'t>) -> Self {
        Self { tokens }
    }
}

impl<'t> Iterator for Components<'t> {
    type Item = Component<'t>;
    fn next(&mut self) -> Option<Self::Item> {
        if !self.tokens.has_sent {
            self.tokens.has_sent = true;
            return Some(Component::Root);
        }
        self.tokens.next().map(Component::Token)
    }
}

impl<'t> From<&'t Pointer> for Components<'t> {
    fn from(pointer: &'t Pointer) -> Self {
        Self {
            tokens: pointer.tokens(),
        }
    }
}
