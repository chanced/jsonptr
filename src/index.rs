//! Abstract index representation for RFC 6901.
//!
//! [RFC 6901](https://datatracker.ietf.org/doc/html/rfc6901) defines two valid
//! ways to represent array indices as Pointer tokens: non-negative integers,
//! and the character `-`, which stands for the index after the last existing
//! array member. While attempting to use `-` to access an array is an error,
//! the token can be useful when paired with [RFC
//! 6902](https://datatracker.ietf.org/∑doc/html/rfc6902) as a way to express
//! where to put the new element when extending an array.
//!
//! While this crate doesn't implement RFC 6902, it still must consider
//! non-numerical indices as valid, and provide a mechanism for manipulating
//! them. This is what this module provides.
//!
//! The main use of the `Index` type is when resolving a [`Token`] instance as a
//! concrete index for a given array length:
//!
//! ```
//! # use jsonptr::{Index, Token};
//! assert_eq!(Token::new("1").to_index(), Ok(Index::Num(1)));
//! assert_eq!(Token::new("-").to_index(), Ok(Index::Next));
//! assert!(Token::new("a").to_index().is_err());
//!
//! assert_eq!(Index::Num(0).for_len(1), Ok(0));
//! assert!(Index::Num(1).for_len(1).is_err());
//! assert!(Index::Next.for_len(1).is_err());
//!
//! assert_eq!(Index::Num(1).for_len_incl(1), Ok(1));
//! assert_eq!(Index::Next.for_len_incl(1), Ok(1));
//! assert!(Index::Num(2).for_len_incl(1).is_err());
//!
//! assert_eq!(Index::Num(42).for_len_unchecked(30), 42);
//! assert_eq!(Index::Next.for_len_unchecked(30), 30);
//! ````

use crate::Token;
use alloc::string::String;
use core::{
    fmt::{self, Display},
    num::ParseIntError,
    str::FromStr,
};

/// Represents an abstract index into an array.
///
/// If provided an upper bound with [`Self::for_len`] or [`Self::for_len_incl`],
/// will produce a concrete numerical index.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Index {
    /// A non-negative integer value
    Num(usize),
    /// The `-` token, the position of the next would-be item in the array
    Next,
}

impl Index {
    /// Bounds the index for a given array length (exclusive).
    ///
    /// The upper range is exclusive, so only indices that are less than
    /// the given length will be accepted as valid. This ensures that
    /// the resolved numerical index can be used to access an existing array
    /// element.
    ///
    /// [`Self::Next`], by consequence, is always considered *invalid*, since
    /// it resolves to the array length itself.
    ///
    /// See also [`Self::for_len_incl`] for an alternative if you wish to accept
    /// [`Self::Next`] (or its numerical equivalent) as valid.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jsonptr::Index;
    /// assert_eq!(Index::Num(0).for_len(1), Ok(0));
    /// assert!(Index::Num(1).for_len(1).is_err());
    /// assert!(Index::Next.for_len(1).is_err());
    /// ```
    /// # Errors
    /// Returns [`OutOfBoundsError`] if the index is out of bounds.
    pub fn for_len(&self, length: usize) -> Result<usize, OutOfBoundsError> {
        match *self {
            Self::Num(index) if index < length => Ok(index),
            Self::Num(index) => Err(OutOfBoundsError { length, index }),
            Self::Next => Err(OutOfBoundsError {
                length,
                index: length,
            }),
        }
    }

    /// Bounds the index for a given array length (inclusive).
    ///
    /// The upper range is inclusive, so an index pointing to the position
    /// _after_ the last element will be considered valid. Be careful when using
    /// the resulting numerical index for accessing an array.
    ///
    /// [`Self::Next`] is always considered valid.
    ///
    /// See also [`Self::for_len`] for an alternative if you wish to ensure that
    /// the resolved index can be used to access an existing array element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jsonptr::Index;
    /// assert_eq!(Index::Num(1).for_len_incl(1), Ok(1));
    /// assert_eq!(Index::Next.for_len_incl(1), Ok(1));
    /// assert!(Index::Num(2).for_len_incl(1).is_err());
    /// ```
    ///
    /// # Errors
    /// Returns [`OutOfBoundsError`] if the index is out of bounds.
    pub fn for_len_incl(&self, length: usize) -> Result<usize, OutOfBoundsError> {
        match *self {
            Self::Num(index) if index <= length => Ok(index),
            Self::Num(index) => Err(OutOfBoundsError { length, index }),
            Self::Next => Ok(length),
        }
    }

    /// Resolves the index for a given array length.
    ///
    /// No bound checking will take place. If you wish to ensure the index can
    /// be used to access an existing element in the array, use [`Self::for_len`]
    /// - or use [`Self::for_len_incl`] if you wish to accept [`Self::Next`] as
    /// valid as well.
    ///
    /// # Examples
    ///
    /// ```
    /// # use jsonptr::Index;
    /// assert_eq!(Index::Num(42).for_len_unchecked(30), 42);
    /// assert_eq!(Index::Next.for_len_unchecked(30), 30);
    ///
    /// // no bounds checks
    /// assert_eq!(Index::Num(40).for_len_unchecked(34), 40);
    /// assert_eq!(Index::Next.for_len_unchecked(34), 34);
    /// ````
    pub fn for_len_unchecked(&self, length: usize) -> usize {
        match *self {
            Self::Num(idx) => idx,
            Self::Next => length,
        }
    }
}

impl FromStr for Index {
    type Err = ParseIndexError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s == "-" {
            Ok(Index::Next)
        } else {
            Ok(s.parse::<usize>().map(Index::Num)?)
        }
    }
}

impl Display for Index {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Self::Num(index) => write!(f, "{index}"),
            Self::Next => f.write_str("-"),
        }
    }
}

impl From<usize> for Index {
    fn from(value: usize) -> Self {
        Self::Num(value)
    }
}

impl TryFrom<&Token<'_>> for Index {
    type Error = ParseIndexError;

    fn try_from(value: &Token) -> Result<Self, Self::Error> {
        // we don't need to decode because it's a single char
        if value.encoded() == "-" {
            Ok(Index::Next)
        } else {
            Ok(value.decoded().parse::<usize>().map(Index::Num)?)
        }
    }
}

impl TryFrom<&str> for Index {
    type Error = ParseIndexError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Index::from_str(value)
    }
}

macro_rules! derive_try_from {
    ($($t:ty),+ $(,)?) => {
        $(
            impl TryFrom<$t> for Index {
                type Error = ParseIndexError;

                fn try_from(value: $t) -> Result<Self, Self::Error> {
                    Index::from_str(&value)
                }
            }
        )*
    }
}

impl TryFrom<Token<'_>> for Index {
    type Error = ParseIndexError;

    fn try_from(tok: Token) -> Result<Self, Self::Error> {
        Index::from_str(tok.encoded())
    }
}
derive_try_from!(String, &String);

/*
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║                               OutOfBoundsError                               ║
║                              ¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
*/

/// Indicates that an `Index` is not within the given bounds.
#[derive(Debug, PartialEq, Eq)]
pub struct OutOfBoundsError {
    /// The provided array length.
    ///
    /// If the range is inclusive, the resolved numerical index will be strictly
    /// less than this value, otherwise it could be equal to it.
    pub length: usize,

    /// The resolved numerical index.
    ///
    /// Note that [`Index::Next`] always resolves to the given array length,
    /// so it is only valid when the range is inclusive.
    pub index: usize,
}

impl fmt::Display for OutOfBoundsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "index {} out of bounds (limit: {})",
            self.index, self.length
        )
    }
}

#[cfg(feature = "std")]
impl std::error::Error for OutOfBoundsError {}

/*
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║                               ParseIndexError                                ║
║                              ¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯¯                               ║
╚══════════════════════════════════════════════════════════════════════════════╝
░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░
*/

/// Indicates that the `Token` could not be parsed as valid RFC 6901 index.
#[derive(Debug, PartialEq, Eq)]
pub struct ParseIndexError {
    /// The source `ParseIntError`
    pub source: ParseIntError,
}

impl From<ParseIntError> for ParseIndexError {
    fn from(source: ParseIntError) -> Self {
        Self { source }
    }
}

impl fmt::Display for ParseIndexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "failed to parse token as an integer")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for ParseIndexError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.source)
    }
}

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
    use super::*;
    use crate::Token;

    #[test]
    fn index_from_usize() {
        let index = Index::from(5usize);
        assert_eq!(index, Index::Num(5));
    }

    #[test]
    fn index_try_from_token_num() {
        let token = Token::new("3");
        let index = Index::try_from(&token).unwrap();
        assert_eq!(index, Index::Num(3));
    }

    #[test]
    fn index_try_from_token_next() {
        let token = Token::new("-");
        let index = Index::try_from(&token).unwrap();
        assert_eq!(index, Index::Next);
    }

    #[test]
    fn index_try_from_str_num() {
        let index = Index::try_from("42").unwrap();
        assert_eq!(index, Index::Num(42));
    }

    #[test]
    fn index_try_from_str_next() {
        let index = Index::try_from("-").unwrap();
        assert_eq!(index, Index::Next);
    }

    #[test]
    fn index_try_from_string_num() {
        let index = Index::try_from(String::from("7")).unwrap();
        assert_eq!(index, Index::Num(7));
    }

    #[test]
    fn testindex_try_from_string_next() {
        let index = Index::try_from(String::from("-")).unwrap();
        assert_eq!(index, Index::Next);
    }

    #[test]
    fn index_for_len_incl_valid() {
        assert_eq!(Index::Num(0).for_len_incl(1), Ok(0));
        assert_eq!(Index::Next.for_len_incl(2), Ok(2));
    }

    #[test]
    fn index_for_len_incl_out_of_bounds() {
        assert!(Index::Num(2).for_len_incl(1).is_err());
    }

    #[test]
    fn index_for_len_unchecked() {
        assert_eq!(Index::Num(10).for_len_unchecked(5), 10);
        assert_eq!(Index::Next.for_len_unchecked(3), 3);
    }

    #[test]
    fn display_index_num() {
        let index = Index::Num(5);
        assert_eq!(index.to_string(), "5");
    }

    #[test]
    fn display_index_next() {
        assert_eq!(Index::Next.to_string(), "-");
    }

    #[test]
    fn for_len() {
        assert_eq!(Index::Num(0).for_len(1), Ok(0));
        assert!(Index::Num(1).for_len(1).is_err());
        assert!(Index::Next.for_len(1).is_err());
    }

    #[test]
    fn out_of_bounds_error_display() {
        let err = OutOfBoundsError {
            length: 5,
            index: 10,
        };
        assert_eq!(err.to_string(), "index 10 out of bounds (limit: 5)");
    }

    #[test]
    fn parse_index_error_display() {
        let err = ParseIndexError {
            source: "not a number".parse::<usize>().unwrap_err(),
        };
        assert_eq!(err.to_string(), "failed to parse token as an integer");
    }

    #[test]
    #[cfg(feature = "std")]
    fn parse_index_error_source() {
        use std::error::Error;
        let source = "not a number".parse::<usize>().unwrap_err();
        let err = ParseIndexError { source };
        assert_eq!(
            err.source().unwrap().to_string(),
            "not a number".parse::<usize>().unwrap_err().to_string()
        );
    }

    #[test]
    fn try_from_token() {
        let token = Token::new("3");
        let index = <Index as TryFrom<Token>>::try_from(token).unwrap();
        assert_eq!(index, Index::Num(3));
        let token = Token::new("-");
        let index = Index::try_from(&token).unwrap();
        assert_eq!(index, Index::Next);
    }
}
