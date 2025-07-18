use core::{iter::once, str::Split};

use crate::{
    diagnostic::{diagnostic_url, Diagnostic, Label},
    index::{Index, ParseIndexError},
};
use alloc::{
    borrow::Cow,
    boxed::Box,
    fmt,
    string::{String, ToString},
    vec::Vec,
};

const ENCODED_TILDE: &[u8] = b"~0";
const ENCODED_SLASH: &[u8] = b"~1";

const ENC_PREFIX: u8 = b'~';
const TILDE_ENC: u8 = b'0';
const SLASH_ENC: u8 = b'1';

/*
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║                                    Token                                     ║
║                                   ¯¯¯¯¯¯¯                                    ║
╚══════════════════════════════════════════════════════════════════════════════╝
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
*/

/// A `Token` is a segment of a JSON [`Pointer`](crate::Token), preceded by `'/'` (`%x2F`).
///
/// `Token`s can represent a key in a JSON object or an index in an array.
///
/// - Indexes should not contain leading zeros.
/// - When dealing with arrays or path expansion for assignment, `"-"` represent
///   the next, non-existent index in a JSON array.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Token<'a> {
    inner: Cow<'a, str>,
}

impl<'a> Token<'a> {
    /// Constructs a `Token` from an RFC 6901 encoded string.
    ///
    /// This is like [`Self::from_encoded`], except that no validation is
    /// performed on the input string.
    ///
    /// ## Safety
    /// Input string must be RFC 6901 encoded.
    pub(crate) unsafe fn from_encoded_unchecked(inner: impl Into<Cow<'a, str>>) -> Self {
        Self {
            inner: inner.into(),
        }
    }

    /// Constructs a `Token` from an RFC 6901 encoded string.
    ///
    /// To be valid, the string must not contain any `/` characters, and any `~`
    /// characters must be followed by either `0` or `1`.
    ///
    /// This function does not allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jsonptr::Token;
    /// assert_eq!(Token::from_encoded("~1foo~1~0bar").unwrap().decoded(), "/foo/~bar");
    /// let err = Token::from_encoded("foo/oops~bar").unwrap_err();
    /// assert_eq!(err.offset, 3);
    /// ```
    ///
    /// ## Errors
    /// Returns `InvalidEncodingError` if the input string is not a valid RFC
    /// 6901 (`~` must be followed by `0` or `1`)
    pub fn from_encoded(s: impl Into<Cow<'a, str>>) -> Result<Self, EncodingError> {
        let inner = s.into();
        let mut escaped = false;
        for (offset, b) in inner.bytes().enumerate() {
            match b {
                b'/' => {
                    return Err(EncodingError {
                        offset,
                        source: InvalidEncoding::Slash,
                    })
                }
                ENC_PREFIX => {
                    escaped = true;
                }
                TILDE_ENC | SLASH_ENC if escaped => {
                    escaped = false;
                }
                _ => {
                    if escaped {
                        return Err(EncodingError {
                            offset,
                            source: InvalidEncoding::Tilde,
                        });
                    }
                }
            }
        }
        if escaped {
            return Err(EncodingError {
                offset: inner.len(),
                source: InvalidEncoding::Tilde,
            });
        }
        Ok(Self { inner })
    }

    /// Constructs a `Token` from an arbitrary string.
    ///
    /// If the string contains a `/` or a `~`, then it will be assumed not
    /// encoded, in which case this function will encode it, allocating a new
    /// string.
    ///
    /// If the string is already encoded per RFC 6901, use
    /// [`Self::from_encoded`] instead, otherwise it will end up double-encoded.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jsonptr::Token;
    /// assert_eq!(Token::new("/foo/~bar").encoded(), "~1foo~1~0bar");
    /// ```
    pub fn new(s: impl Into<Cow<'a, str>>) -> Self {
        let s = s.into();

        if let Some(i) = s.bytes().position(|b| b == b'/' || b == b'~') {
            let input = s.as_bytes();
            // we could take advantage of [`Cow::into_owned`] here, but it would
            // mean copying over the entire string, only to overwrite a portion
            // of it... so instead we explicitly allocate a new buffer and copy
            // only the prefix until the first encoded character
            // NOTE: the output is at least as large as the input + 1, so we
            // allocate that much capacity ahead of time
            let mut bytes = Vec::with_capacity(input.len() + 1);
            bytes.extend_from_slice(&input[..i]);
            for &b in &input[i..] {
                match b {
                    b'/' => {
                        bytes.extend_from_slice(ENCODED_SLASH);
                    }
                    b'~' => {
                        bytes.extend_from_slice(ENCODED_TILDE);
                    }
                    other => {
                        bytes.push(other);
                    }
                }
            }
            Self {
                // SAFETY: we started from a valid UTF-8 sequence of bytes,
                // and only replaced some ASCII characters with other two ASCII
                // characters, so the output is guaranteed valid UTF-8.
                inner: Cow::Owned(unsafe { String::from_utf8_unchecked(bytes) }),
            }
        } else {
            Self { inner: s }
        }
    }

    /// Converts into an owned copy of this token.
    ///
    /// If the token is not already owned, this will clone the referenced string
    /// slice.
    pub fn into_owned(self) -> Token<'static> {
        Token {
            inner: Cow::Owned(self.inner.into_owned()),
        }
    }

    /// Extracts an owned copy of this token.
    ///
    /// If the token is not already owned, this will clone the referenced string
    /// slice.
    ///
    /// This method is like [`Self::into_owned`], except it doesn't take
    /// ownership of the original `Token`.
    pub fn to_owned(&self) -> Token<'static> {
        Token {
            inner: Cow::Owned(self.inner.clone().into_owned()),
        }
    }

    /// Returns the encoded string representation of the `Token`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jsonptr::Token;
    /// assert_eq!(Token::new("~bar").encoded(), "~0bar");
    /// ```
    pub fn encoded(&self) -> &str {
        &self.inner
    }

    /// Returns the decoded string representation of the `Token`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jsonptr::Token;
    /// assert_eq!(Token::new("~bar").decoded(), "~bar");
    /// ```
    pub fn decoded(&self) -> Cow<'_, str> {
        if let Some(i) = self.inner.bytes().position(|b| b == ENC_PREFIX) {
            let input = self.inner.as_bytes();
            // we could take advantage of [`Cow::into_owned`] here, but it would
            // mean copying over the entire string, only to overwrite a portion
            // of it... so instead we explicitly allocate a new buffer and copy
            // only the prefix until the first encoded character
            // NOTE: the output is at least as large as the input + 1, so we
            // allocate that much capacity ahead of time
            let mut bytes = Vec::with_capacity(input.len() + 1);
            bytes.extend_from_slice(&input[..i]);
            // we start from the first escaped character
            let mut escaped = true;
            for &b in &input[i + 1..] {
                match b {
                    ENC_PREFIX => {
                        escaped = true;
                    }
                    TILDE_ENC if escaped => {
                        bytes.push(b'~');
                        escaped = false;
                    }
                    SLASH_ENC if escaped => {
                        bytes.push(b'/');
                        escaped = false;
                    }
                    other => {
                        bytes.push(other);
                    }
                }
            }
            // SAFETY: we start from a valid String, and only write valid UTF-8
            // byte sequences into it.
            Cow::Owned(unsafe { String::from_utf8_unchecked(bytes) })
        } else {
            // if there are no encoded characters, we don't need to allocate!
            self.inner.clone()
        }
    }

    /// Attempts to parse the given `Token` as an array index.
    ///
    /// Per [RFC 6901](https://datatracker.ietf.org/doc/html/rfc6901#section-4),
    /// the acceptable values are non-negative integers and the `-` character,
    /// which stands for the next, non-existent member after the last array
    /// element.
    ///
    /// ## Examples
    ///
    /// ```
    /// # use jsonptr::{index::Index, Token};
    /// assert_eq!(Token::new("-").to_index(), Ok(Index::Next));
    /// assert_eq!(Token::new("0").to_index(), Ok(Index::Num(0)));
    /// assert_eq!(Token::new("2").to_index(), Ok(Index::Num(2)));
    /// assert!(Token::new("a").to_index().is_err());
    /// assert!(Token::new("-1").to_index().is_err());
    /// ```
    /// ## Errors
    /// Returns [`ParseIndexError`] if the token is not a valid array index.
    pub fn to_index(&self) -> Result<Index, ParseIndexError> {
        self.try_into()
    }

    /// Returns if the `Token` is `-`, which stands for the next array index.
    ///
    /// See also [`Self::to_index`].
    pub fn is_next(&self) -> bool {
        matches!(self.to_index(), Ok(Index::Next))
    }
}

macro_rules! impl_from_num {
    ($($ty:ty),*) => {
        $(
            impl From<$ty> for Token<'static> {
                fn from(v: $ty) -> Self {
                    // SAFETY: only used for integer types, which are always valid
                    unsafe { Token::from_encoded_unchecked(v.to_string()) }
                }
            }
        )*
    };
}
impl_from_num!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);

impl<'a> From<&'a str> for Token<'a> {
    fn from(value: &'a str) -> Self {
        Token::new(value)
    }
}

impl<'a> From<&'a String> for Token<'a> {
    fn from(value: &'a String) -> Self {
        Token::new(value)
    }
}

impl From<String> for Token<'static> {
    fn from(value: String) -> Self {
        Token::new(value)
    }
}

impl<'a> From<&Token<'a>> for Token<'a> {
    fn from(value: &Token<'a>) -> Self {
        value.clone()
    }
}

impl alloc::fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut alloc::fmt::Formatter<'_>) -> alloc::fmt::Result {
        write!(f, "{}", self.decoded())
    }
}

/*
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║                                    Tokens                                    ║
║                                   ¯¯¯¯¯¯¯¯                                   ║
╚══════════════════════════════════════════════════════════════════════════════╝
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
*/

/// An iterator over the [`Token`]s of a [`Pointer`](crate::Pointer).
#[derive(Debug)]
pub struct Tokens<'a> {
    inner: Split<'a, char>,
}

impl<'a> Iterator for Tokens<'a> {
    type Item = Token<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
            // SAFETY: source pointer is encoded
            .map(|s| unsafe { Token::from_encoded_unchecked(s) })
    }
}
impl<'t> Tokens<'t> {
    pub(crate) fn new(inner: Split<'t, char>) -> Self {
        Self { inner }
    }
}

/*
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║                             InvalidEncodingError                             ║
║                            ¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯                            ║
╚══════════════════════════════════════════════════════════════════════════════╝
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
*/

#[deprecated(since = "0.7.0", note = "renamed to `EncodingError`")]
/// Deprecated alias for [`EncodingError`].
pub type InvalidEncodingError = EncodingError;

/*
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║                                EncodingError                                 ║
║                               ¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯                                ║
╚══════════════════════════════════════════════════════════════════════════════╝
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
*/

/// A token within a json pointer contained invalid encoding (`~` not followed
/// by `0` or `1`).
///
#[derive(Debug, PartialEq, Eq)]
pub struct EncodingError {
    /// offset of the erroneous `~` from within the `Token`
    pub offset: usize,
    /// the specific encoding error
    pub source: InvalidEncoding,
}

impl fmt::Display for EncodingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "token contains invalid encoding at offset {}",
            self.offset
        )
    }
}

impl Diagnostic for EncodingError {
    type Subject = String;

    fn url() -> &'static str {
        diagnostic_url!(struct EncodingError)
    }

    fn labels(&self, subject: &Self::Subject) -> Option<Box<dyn Iterator<Item = Label>>> {
        let (text, offset) = match self.source {
            InvalidEncoding::Tilde => {
                if self.offset == subject.len() {
                    ("incomplete escape sequence", self.offset - 1)
                } else {
                    ("must be 0 or 1", self.offset)
                }
            }
            InvalidEncoding::Slash => ("invalid character", self.offset),
        };
        Some(Box::new(once(Label::new(text.to_string(), offset, 1))))
    }
}

#[cfg(feature = "miette")]
impl miette::Diagnostic for EncodingError {}

#[cfg(feature = "std")]
impl std::error::Error for EncodingError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.source)
    }
}

/*
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║                               InvalidEncoding                                ║
║                              ¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯                               ║
╚══════════════════════════════════════════════════════════════════════════════╝
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
*/

/// Represents the specific type of invalid encoding error.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum InvalidEncoding {
    /// `~` not followed by `0` or `1`
    Tilde,
    /// non-encoded `/` found in token
    Slash,
}

impl fmt::Display for InvalidEncoding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InvalidEncoding::Tilde => write!(f, "tilde (~) not followed by 0 or 1"),
            InvalidEncoding::Slash => write!(f, "slash (/) found in token"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for InvalidEncoding {}

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
    use crate::Pointer;

    use super::*;
    use quickcheck_macros::quickcheck;

    #[test]
    fn from() {
        assert_eq!(Token::from("/").encoded(), "~1");
        assert_eq!(Token::from("~/").encoded(), "~0~1");
        assert_eq!(Token::from(34u32).encoded(), "34");
        assert_eq!(Token::from(34u64).encoded(), "34");
        assert_eq!(Token::from(String::from("foo")).encoded(), "foo");
        assert_eq!(Token::from(&Token::new("foo")).encoded(), "foo");
    }

    #[test]
    fn to_index() {
        assert_eq!(Token::new("-").to_index(), Ok(Index::Next));
        assert_eq!(Token::new("0").to_index(), Ok(Index::Num(0)));
        assert_eq!(Token::new("2").to_index(), Ok(Index::Num(2)));
        assert!(Token::new("a").to_index().is_err());
        assert!(Token::new("-1").to_index().is_err());
    }

    #[test]
    fn new() {
        assert_eq!(Token::new("~1").encoded(), "~01");
        assert_eq!(Token::new("a/b").encoded(), "a~1b");
    }

    #[test]
    fn from_encoded() {
        assert_eq!(Token::from_encoded("~1").unwrap().encoded(), "~1");
        assert_eq!(Token::from_encoded("~0~1").unwrap().encoded(), "~0~1");
        let t = Token::from_encoded("a~1b").unwrap();
        assert_eq!(t.decoded(), "a/b");

        let sub = String::from("a/b");
        let err = Token::from_encoded(&sub).unwrap_err();
        let labels: Vec<_> = err.labels(&sub).unwrap().into_iter().collect();
        assert_eq!(labels, vec![Label::new("invalid character".into(), 1, 1)]);
        let err = err.into_report(sub);
        #[cfg(feature = "miette")]
        {
            let labels: Vec<_> = miette::Diagnostic::labels(&err)
                .unwrap()
                .into_iter()
                .collect();
            assert_eq!(
                labels,
                vec![miette::LabeledSpan::new(
                    Some("invalid character".into()),
                    1,
                    1
                )]
            );
        }
        let (err, _) = err.decompose();
        assert_eq!(
            err,
            EncodingError {
                offset: 1,
                source: InvalidEncoding::Slash
            }
        );

        let sub = String::from("a~a");
        let err = Token::from_encoded(&sub).unwrap_err();
        let labels: Vec<_> = err.labels(&sub).unwrap().into_iter().collect();
        assert_eq!(labels, vec![Label::new("must be 0 or 1".into(), 2, 1)]);
        let err = err.into_report(sub);
        #[cfg(feature = "miette")]
        {
            let labels: Vec<_> = miette::Diagnostic::labels(&err)
                .unwrap()
                .into_iter()
                .collect();
            assert_eq!(
                labels,
                vec![miette::LabeledSpan::new(
                    Some("must be 0 or 1".into()),
                    2,
                    1
                )]
            );
        }
        let (err, _) = err.decompose();
        assert_eq!(
            err,
            EncodingError {
                offset: 2,
                source: InvalidEncoding::Tilde
            }
        );
        let sub = String::from("a~");
        let err = Token::from_encoded(&sub).unwrap_err();
        let labels: Vec<_> = err.labels(&sub).unwrap().into_iter().collect();
        assert_eq!(
            labels,
            vec![Label::new("incomplete escape sequence".into(), 1, 1)]
        );
        let err = err.into_report(sub);
        #[cfg(feature = "miette")]
        {
            let labels: Vec<_> = miette::Diagnostic::labels(&err)
                .unwrap()
                .into_iter()
                .collect();
            assert_eq!(
                labels,
                vec![miette::LabeledSpan::new(
                    Some("incomplete escape sequence".into()),
                    1,
                    1
                )]
            );
        }
        let (err, _) = err.decompose();
        assert_eq!(
            err,
            EncodingError {
                offset: 2,
                source: InvalidEncoding::Tilde
            }
        );
    }

    #[test]
    fn into_owned() {
        let token = Token::from_encoded("foo~0").unwrap().into_owned();
        assert_eq!(token.encoded(), "foo~0");
    }

    #[quickcheck]
    fn encode_decode(s: String) -> bool {
        let token = Token::new(s);
        let decoded = Token::from_encoded(token.encoded()).unwrap();
        token == decoded
    }

    #[test]
    fn tokens() {
        let pointer = Pointer::from_static("/a/b/c");
        let tokens: Vec<Token> = pointer.tokens().collect();
        assert_eq!(tokens, unsafe {
            vec![
                Token::from_encoded_unchecked("a"),
                Token::from_encoded_unchecked("b"),
                Token::from_encoded_unchecked("c"),
            ]
        });
    }

    #[test]
    fn is_next() {
        let token = Token::new("-");
        assert!(token.is_next());
        let token = Token::new("0");
        assert!(!token.is_next());
        let token = Token::new("a");
        assert!(!token.is_next());
        let token = Token::new("");
        assert!(!token.is_next());
    }
}
