#![doc = include_str!("../README.md")]
#![warn(missing_docs)]
#![deny(clippy::all, clippy::pedantic)]
#![cfg_attr(not(feature = "std"), no_std)]
#![allow(
    clippy::module_name_repetitions,
    clippy::into_iter_without_iter,
    clippy::needless_pass_by_value,
    clippy::expect_fun_call,
    clippy::must_use_candidate,
    clippy::similar_names
)]

#[cfg_attr(not(feature = "std"), macro_use)]
extern crate alloc;

#[cfg(feature = "assign")]
pub mod assign;
#[cfg(feature = "assign")]
pub use assign::Assign;

#[cfg(feature = "delete")]
pub mod delete;
#[cfg(feature = "delete")]
pub use delete::Delete;

#[cfg(feature = "resolve")]
pub mod resolve;
#[cfg(feature = "resolve")]
pub use resolve::{Resolve, ResolveMut};

mod pointer;
pub use pointer::{ParseError, Pointer, PointerBuf, ReplaceTokenError};

mod token;
pub use token::{InvalidEncodingError, Token, Tokens};

mod index;
pub use index::{Index, OutOfBoundsError, ParseIndexError};

mod component;
pub use component::{Component, Components};

#[cfg(test)]
mod arbitrary;
