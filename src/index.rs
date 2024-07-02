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

use crate::{OutOfBoundsError, ParseIndexError, Token};
use alloc::string::String;
use core::fmt::Display;

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
    /// assert_eq!(Index::Num(34).for_len_unchecked(40), 40);
    /// assert_eq!(Index::Next.for_len_unchecked(34), 34);
    /// ````
    pub fn for_len_unchecked(&self, length: usize) -> usize {
        match *self {
            Self::Num(idx) => idx,
            Self::Next => length,
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
        if value == "-" {
            Ok(Index::Next)
        } else {
            Ok(value.parse::<usize>().map(Index::Num)?)
        }
    }
}

macro_rules! derive_try_from {
    ($($t:ty),+ $(,)?) => {
        $(
            impl TryFrom<$t> for Index {
                type Error = ParseIndexError;

                fn try_from(value: $t) -> Result<Self, Self::Error> {
                    value.try_into()
                }
            }
        )*
    }
}

derive_try_from!(Token<'_>, String, &String);
