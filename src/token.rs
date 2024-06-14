use crate::{IndexError, InvalidEncodingError, OutOfBoundsError, ParseError};
use alloc::{
    borrow::Cow,
    string::{String, ToString},
};
use serde::{Deserialize, Serialize};

const ENCODED_TILDE: &[u8] = b"~0";
const ENCODED_SLASH: &[u8] = b"~1";

const ENC_PREFIX: u8 = b'~';
const TILDE_ENC: u8 = b'0';
const SLASH_ENC: u8 = b'1';

/// A `Token` is a segment of a JSON Pointer, seperated by '/' (%x2F). It can
/// represent a key in a JSON object or an index in a JSON array.
///
/// - Indexes should not contain leading zeros.
/// - `"-"` represents the next, non-existent index in a JSON array.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Token<'a> {
    inner: Cow<'a, str>,
}

impl<'a> Token<'a> {
    /// Constructs a `Token` from an RFC 6901 encoded string.
    ///
    /// This is like [`Self::from_encoded`], except that no validation is
    /// performed on the input string.
    pub(crate) fn from_encoded_unchecked(inner: impl Into<Cow<'a, str>>) -> Self {
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
    /// assert_eq!(err.offset(), 3);
    /// ```
    pub fn from_encoded(s: &'a str) -> Result<Self, InvalidEncodingError> {
        let err_at = |i| Err(InvalidEncodingError::new(i));
        let mut escaped = false;
        for (i, b) in s.bytes().enumerate() {
            match b {
                b'/' => return err_at(i),
                ENC_PREFIX => {
                    escaped = true;
                }
                TILDE_ENC | SLASH_ENC if escaped => {
                    escaped = false;
                }
                _ => {
                    if escaped {
                        return err_at(i);
                    }
                }
            }
        }
        if escaped {
            err_at(s.len())
        } else {
            Ok(Self { inner: s.into() })
        }
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

    /// Attempts to parse the given `Token` as an array index (`usize`).
    ///
    /// The argument represents the length of the array and is used to check the
    /// bounds as well as produce the correct index from a `-` token. Per [RFC
    /// 6901](https://datatracker.ietf.org/doc/html/rfc6901#section-4), the `-`
    /// token will stand for the next, non-existent member after the last array
    /// element.
    ///
    /// # Errors
    /// - `IndexError::Parse` - if the token is not a valid index.
    /// - `IndexError::OutOfBounds` - if the token is a valid index but exceeds
    ///   `len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use jsonptr::Token;
    /// assert_eq!(Token::new("-").as_index(1).unwrap(), 1);
    /// assert_eq!(Token::new("1").as_index(1).unwrap(), 1);
    /// assert_eq!(Token::new("2").as_index(2).unwrap(), 2);
    /// ```
    pub fn as_index(&self, len: usize) -> Result<usize, IndexError> {
        if self.decoded() == "-" {
            Ok(len)
        } else {
            match self.decoded().parse().map_err(Into::into) {
                Ok(idx) => {
                    if idx > len {
                        Err(IndexError::OutOfBounds(OutOfBoundsError {
                            len,
                            index: idx,
                        }))
                    } else {
                        Ok(idx)
                    }
                }
                Err(err) => Err(IndexError::Parse(ParseError::new(err))),
            }
        }
    }
}

impl Serialize for Token<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.decoded().as_ref())
    }
}

impl<'de> Deserialize<'de> for Token<'de> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = <&'de str>::deserialize(deserializer)?;
        Ok(Token::new(s))
    }
}

impl From<usize> for Token<'static> {
    fn from(v: usize) -> Self {
        Token::from_encoded_unchecked(v.to_string())
    }
}

impl From<u32> for Token<'static> {
    fn from(v: u32) -> Self {
        Token::from_encoded_unchecked(v.to_string())
    }
}

impl From<u64> for Token<'static> {
    fn from(v: u64) -> Self {
        Token::from_encoded_unchecked(v.to_string())
    }
}

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

impl core::fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.decoded())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck_macros::quickcheck;

    #[test]
    fn test_from() {
        assert_eq!(Token::from("/").encoded(), "~1");
        assert_eq!(Token::from("~/").encoded(), "~0~1");
    }

    #[test]
    fn test_from_encoded() {
        assert_eq!(Token::from_encoded("~1").unwrap().encoded(), "~1");
        assert_eq!(Token::from_encoded("~0~1").unwrap().encoded(), "~0~1");
        let t = Token::from_encoded("a~1b").unwrap();
        assert_eq!(t.decoded(), "a/b");
        let _ = Token::from_encoded("a/b").unwrap_err();
    }

    #[quickcheck]
    fn encode_decode(s: String) -> bool {
        let token = Token::new(s);
        let decoded = Token::from_encoded(token.encoded()).unwrap();
        token == decoded
    }
}
