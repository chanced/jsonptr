use crate::{Pointer, Token, Tokens};

/// A single [`Token`] or the root of a JSON Pointer
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Component<'p> {
    /// The document root
    Root,
    /// A token of a [`Pointer`]
    Token {
        /// the [`Token`]
        token: Token<'p>,
        /// The full location of this `Token`, including the `Token` itself
        pointer: &'p Pointer,
        /// index of the token in the pointer
        index: usize,
        /// offset of the [`Token`] in the pointer
        offset: usize,
    },
}

/// An iterator over the [`Component`]s of a JSON Pointer
#[derive(Debug)]
pub struct Components<'p> {
    pointer: &'p Pointer,
    tokens: Tokens<'p>,
    sent: usize,
    offset: usize,
}

impl<'p> Iterator for Components<'p> {
    type Item = Component<'p>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.sent == 0 {
            self.sent += 1;
            return Some(Component::Root);
        }
        let token = self.tokens.next()?;
        let offset = self.offset;
        let index = self.sent - 1;

        self.offset += 1 + token.encoded().len();
        self.sent += 1;
        Some(Component::Token {
            token,
            offset,
            index,
            pointer: self.pointer.partial(index).unwrap(),
        })
    }
}

impl<'t> From<&'t Pointer> for Components<'t> {
    fn from(pointer: &'t Pointer) -> Self {
        Self {
            pointer,
            offset: 0,
            sent: 0,
            tokens: pointer.tokens(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn components() {
        let ptr = Pointer::from_static("");
        let components: Vec<_> = Components::from(ptr).collect();
        assert_eq!(components, vec![Component::Root]);

        let ptr = Pointer::from_static("/foo");
        let components = ptr.components().collect::<Vec<_>>();
        assert_eq!(
            components,
            vec![
                Component::Root,
                Component::Token {
                    token: "foo".into(),
                    index: 0,
                    offset: 0,
                    pointer: Pointer::from_static("/foo")
                }
            ]
        );

        let ptr = Pointer::from_static("/foo/bar/-/0/baz");
        let components = ptr.components().collect::<Vec<_>>();
        assert_eq!(
            components,
            vec![
                Component::Root,
                Component::Token {
                    token: "foo".into(),
                    offset: 0,
                    index: 0,
                    pointer: Pointer::from_static("/foo"),
                },
                Component::Token {
                    token: "bar".into(),
                    index: 1,
                    offset: 4,
                    pointer: Pointer::from_static("/foo/bar")
                },
                Component::Token {
                    token: "-".into(),
                    index: 2,
                    offset: 8,
                    pointer: Pointer::from_static("/foo/bar/-")
                },
                Component::Token {
                    token: "0".into(),
                    index: 3,
                    offset: 10,
                    pointer: Pointer::from_static("/foo/bar/-/0")
                },
                Component::Token {
                    token: "baz".into(),
                    index: 4,
                    offset: 12,
                    pointer: Pointer::from_static("/foo/bar/-/0/baz")
                }
            ]
        );
    }
}
