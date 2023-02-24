#![doc = include_str!("../README.md")]
#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]
extern crate alloc;

mod pointer;
pub use pointer::*;
mod token;
pub use token::*;

mod error;
pub use error::*;

mod assign;
pub use assign::*;
mod delete;
pub use delete::*;
mod resolve;
pub use resolve::*;

pub mod prelude;

mod tokens;
pub use tokens::*;
