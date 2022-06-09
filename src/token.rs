#[cfg(test)]
mod token_test;

use std::{
    borrow::Borrow,
    fmt::{Debug, Display},
    hash::{Hash, Hasher},
    ops::Deref,
};

use crate::{IndexError, OutOfBoundsError, ParseError};
use serde::{Deserialize, Serialize};

const ENCODED_TILDE: &str = "~0";
const ENCODED_SLASH: &str = "~1";

const ENC_PREFIX: char = '~';
const TILDE_ENC: char = '0';
const SLASH_ENC: char = '1';

/// A `Token` is a segment of a JSON Pointer, seperated by '/' (%x2F). It can
/// represent a key in a JSON object or an index in a JSON array.
///
/// - Indexes should not contain leading zeros.
/// - `"-"` represents the next, non-existent index in a JSON array.
#[derive(Clone)]
pub struct Token {
    value: Value,
}
impl Token {
    /// Create a new token from `val`. The token is encoded per [RFC
    /// 6901](https://datatracker.ietf.org/doc/html/rfc6901):
    /// - `'~'` is encoded as `"~0"`
    /// - `'/'` is encoded as `"~1"`
    pub fn new(val: impl AsRef<str>) -> Self {
        Token {
            value: Value::parse(val.as_ref()),
        }
    }
    /// Create a new token from `encoded`. The token should be encoded per
    /// [RFC 6901](https://datatracker.ietf.org/doc/html/rfc6901)
    pub fn from_encoded(val: impl AsRef<str>) -> Self {
        Token {
            value: Value::from_encoded(val.as_ref()),
        }
    }

    /// Returns the decoded `&str` representation of the `Token`.
    ///
    /// ```
    /// use jsonptr::Token;
    /// assert_eq!(Token::new("/foo/~bar").decoded(), "/foo/~bar");
    pub fn decoded(&self) -> &str {
        self.value.decoded()
    }
    /// Returns the encoded `&str` representation of the `Token`.
    ///
    /// ```
    /// use jsonptr::Token;
    /// assert_eq!(Token::new("/foo/~bar").encoded(), "~1foo~1~0bar");
    /// ```
    pub fn encoded(&self) -> &str {
        self.value.encoded()
    }

    /// Attempts to parse the given `Token` as an array index (`usize`).
    ///
    /// Per [RFC 6901](https://datatracker.ietf.org/doc/html/rfc6901#section-4),
    /// the token `"-"` will attempt to index the next, non-existent collection
    /// index. In order to accomodate that, the following parameters are
    /// utilized to determine the next index and whether the token falls within
    /// those bounds:
    ///
    /// ## Parameters
    /// - `len` - current length of the array / vector.
    /// - `max_size` - a optional maximum allowed size for the array / vector.
    ///
    /// ## Errors
    /// - `IndexError::Parse` - if the token is not a valid index.
    /// - `IndexError::OutOfBounds` - if the token is a valid index but exceeds
    ///   `max_size` or `len`.
    ///
    /// ## Examples
    ///```
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
                            token: self.clone(),
                        }))
                    } else {
                        Ok(idx)
                    }
                }
                Err(err) => Err(IndexError::Parse(ParseError {
                    source: err,
                    token: self.clone(),
                })),
            }
        }
    }
    /// Returns `&String` for usage as a key for `serde_json::Map`
    pub fn as_key(&self) -> &String {
        self.value.as_key()
    }

    pub fn as_str(&self) -> &str {
        self.value.decoded()
    }
}

impl Serialize for Token {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.decoded())
    }
}
impl<'de> Deserialize<'de> for Token {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        Ok(Token::new(s))
    }
}
impl Eq for Token {}
impl Deref for Token {
    type Target = str;
    fn deref(&self) -> &Self::Target {
        self.decoded()
    }
}
impl From<usize> for Token {
    fn from(v: usize) -> Self {
        Token::new(v.to_string())
    }
}
impl From<&str> for Token {
    fn from(s: &str) -> Self {
        Token::new(s)
    }
}
impl From<String> for Token {
    fn from(value: String) -> Self {
        Token::new(value)
    }
}
impl AsRef<str> for Token {
    fn as_ref(&self) -> &str {
        self.decoded()
    }
}
impl Borrow<str> for Token {
    fn borrow(&self) -> &str {
        self.decoded()
    }
}

impl Borrow<String> for Token {
    fn borrow(&self) -> &String {
        match &self.value {
            Value::Uncoded(u) => u,
            Value::Encoded(e) => &e.decoded,
        }
    }
}

impl From<&Token> for Token {
    fn from(t: &Token) -> Self {
        t.clone()
    }
}

impl PartialEq<str> for Token {
    fn eq(&self, other: &str) -> bool {
        self.decoded() == other
    }
}

impl PartialEq<Token> for Token {
    fn eq(&self, other: &Token) -> bool {
        self == other.decoded()
    }
}

impl PartialEq<Token> for str {
    fn eq(&self, other: &Token) -> bool {
        self == other.decoded()
    }
}
impl PartialEq<String> for Token {
    fn eq(&self, other: &String) -> bool {
        self == other
    }
}

impl PartialEq<&str> for Token {
    fn eq(&self, other: &&str) -> bool {
        &self.value.decoded() == other
    }
}
impl PartialEq<&String> for Token {
    fn eq(&self, other: &&String) -> bool {
        &self.value.decoded() == other
    }
}
impl PartialEq<Token> for &str {
    fn eq(&self, other: &Token) -> bool {
        self == &other.value.decoded()
    }
}
impl PartialEq<&Token> for String {
    fn eq(&self, other: &&Token) -> bool {
        self == other.value.decoded()
    }
}

impl PartialOrd<str> for Token {
    fn partial_cmp(&self, other: &str) -> Option<std::cmp::Ordering> {
        self.decoded().partial_cmp(other)
    }
}
impl PartialOrd<String> for Token {
    fn partial_cmp(&self, other: &String) -> Option<std::cmp::Ordering> {
        self.decoded().partial_cmp(other)
    }
}
impl PartialOrd<Token> for Token {
    fn partial_cmp(&self, other: &Token) -> Option<std::cmp::Ordering> {
        self.decoded().partial_cmp(other.decoded())
    }
}
impl PartialEq<Token> for String {
    fn eq(&self, other: &Token) -> bool {
        self == other.decoded()
    }
}

impl PartialOrd<Token> for String {
    fn partial_cmp(&self, other: &Token) -> Option<std::cmp::Ordering> {
        self.as_str().partial_cmp(other.decoded())
    }
}

impl Hash for Token {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.decoded().hash(state)
    }
}

impl Debug for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.decoded())
    }
}
impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.decoded())
    }
}

impl std::cmp::Ord for Token {
    fn cmp(&self, other: &Token) -> std::cmp::Ordering {
        self.decoded().cmp(other.decoded())
    }
}

#[derive(Clone, Debug)]
enum Value {
    Uncoded(String),
    Encoded(Encoded),
}

impl Value {
    fn decoded(&self) -> &str {
        match self {
            Value::Uncoded(u) => u,
            Value::Encoded(e) => &e.decoded,
        }
    }
    fn encoded(&self) -> &str {
        match self {
            Value::Uncoded(u) => u,
            Value::Encoded(e) => &e.encoded,
        }
    }
    fn as_key(&self) -> &String {
        match self {
            Value::Uncoded(u) => u,
            Value::Encoded(e) => &e.decoded,
        }
    }
    fn from_encoded(s: &str) -> Self {
        let mut uncoded = String::with_capacity(s.len());
        let mut encoded = String::with_capacity(s.len());

        let mut is_encoded = false;
        let mut chars = s.chars();
        while let Some(c) = chars.next() {
            encoded.push(c);
            if c == ENC_PREFIX {
                let next = chars.next();
                if next.is_none() {
                    uncoded.push(c);
                    break;
                }
                let next = next.unwrap();
                encoded.push(next);
                match next {
                    SLASH_ENC => {
                        is_encoded = true;
                        uncoded.push('/');
                    }
                    TILDE_ENC => {
                        is_encoded = true;
                        uncoded.push('~');
                    }
                    _ => {
                        uncoded.push(next);
                    }
                }
            } else {
                uncoded.push(c);
            }
        }
        if is_encoded {
            Value::Encoded(Encoded {
                encoded,
                decoded: uncoded,
            })
        } else {
            Value::Uncoded(uncoded)
        }
    }

    /// parses a string with the expectation that it is not encoded.
    fn parse(s: &str) -> Self {
        let mut uncoded = String::with_capacity(s.len());
        let mut encoded = String::with_capacity(s.len());
        let mut was_encoded = false;
        for c in s.chars() {
            uncoded.push(c);
            match Char::from(c) {
                Char::Char(c) => encoded.push(c),
                Char::Escaped(e) => {
                    was_encoded = true;
                    encoded.push_str(e.into());
                }
            };
        }
        if was_encoded {
            Value::Encoded(Encoded {
                encoded,
                decoded: uncoded,
            })
        } else {
            Value::Uncoded(uncoded)
        }
    }
}

#[derive(Clone, Debug)]
struct Encoded {
    encoded: String,
    decoded: String,
}

enum Char {
    Char(char),
    Escaped(Escaped),
}

impl From<char> for Char {
    fn from(c: char) -> Self {
        match c {
            '/' => Char::Escaped(Escaped::Slash),
            '~' => Char::Escaped(Escaped::Tilde),
            _ => Char::Char(c),
        }
    }
}

enum Escaped {
    Tilde,
    Slash,
}
#[allow(clippy::from_over_into)]
impl Into<&str> for Escaped {
    fn into(self) -> &'static str {
        match self {
            Escaped::Tilde => ENCODED_TILDE,
            Escaped::Slash => ENCODED_SLASH,
        }
    }
}
