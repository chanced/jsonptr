//! # jsonptr - JSON Pointers (RFC 6901)
//! [<img alt="github"
//! src="https://img.shields.io/badge/github-chanced/jsonptr-62D1FC?style=for-the-badge&labelColor=777&logo=github"
//! height="24">](https://github.com/chanced/jsonptr) [<img alt="docs.rs"
//! src="https://img.shields.io/badge/docs.rs-jsonptr-f0f0f0?style=for-the-badge&labelColor=777&logo=docs.rs"
//! height="24">](https://docs.rs/jsonptr) [<img alt="crates.io"
//! src="https://img.shields.io/crates/v/jsonptr.svg?style=for-the-badge&color=fc8d62&logo=rust"
//! height="24">](https://crates.io/crates/jsonptr) [<img alt="build status"
//! src="https://img.shields.io/github/actions/workflow/status/chanced/jsonptr/test.yml?branch=main&style=for-the-badge"
//! height="24">](https://github.com/chanced/jsonptr/actions?query=branch%3Amain)
//! [<img alt="code coverage"
//! src="https://img.shields.io/codecov/c/github/chanced/jsonptr?style=for-the-badge&color=CBB88D"
//! height="24">](https://codecov.io/gh/chanced/jsonptr)
//!
//! JSON Pointers are a lightly encoded strings that provide a syntax for
//! identifying a specific value within a JSON document. A properly formatted
//! JSON Pointer is composed of either an empty string, indicating the root
//! document, or a series of tokens, each with a leading backslash (`'/'`) and
//! encoded with the following rules:
//! - `'~'` is encoded as `'~0'`
//! - `'/'` is encoded as `'~1'`
//!
//! This module provides data structures and logic for resolving, assigning, and
//! deleting by JSON Pointers ([RFC
//! 6901](https://datatracker.ietf.org/doc/html/rfc6901)). Two types,
//! [`PointerBuf`] and [`Pointer`] (akin to [`String`] and [`str`]), are
//! available for representing JSON Pointers while the operations ([`Resolve`],
//! [`ResolveMut`], [`Assign`], [`Delete`]) are exposed as traits and
//! implemented for [`serde_json::Value`] and [`toml::Value`] if the respective
//! features are enabled.
//!
//! ## Feature Flags
//!
//! | Flag | Description                                                                                                                                                              | Enables                            | Default |
//! | :------------: | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ---------------------------------- | :-----: |
//! | `"std"`      | Implements `std::error::Error` for error types                                                                                                                           | `"serde/std"`, `"serde_json?/std"` |    ✓    |
//! | `"json"`     | Implements [`Resolve`], [`Assign`], [`Delete`] for [`serde_json::Value`]                                                                 | `serde_json`                       |    ✓    |
//! | `"toml"`     | Implements [`Resolve`], [`Assign`], [`Delete`] for [`toml::Value`]                                                                                                       | `"std"`, `toml`                    |         |
//! | `"assign"`   | Enables the [`Assign`] trait and [`Pointer::assign`] for assigning values based on the location specified by a JSON Pointer                                              |                                    |    ✓    |
//! | `"resolve"`  | Enables the [`Resolve`] & [`ResolveMut`] trait and [`Pointer::resolve`], [`Pointer::resolve_mut`] for resolving values based on the location specified by a JSON Pointer |                                    |    ✓    |
//! | `"delete"`   | Enables the [`Delete`] trait and [`Pointer::delete`] for deleting values based on the location specified by a JSON Pointer                                               | `"resolve"`                        |    ✓    |
//!
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

pub mod prelude;

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

mod tokens;
pub use tokens::*;

mod pointer;
pub use pointer::*;

mod token;
pub use token::*;

pub mod index;
pub use index::Index;

#[cfg(test)]
mod arbitrary;
