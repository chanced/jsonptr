// rustdoc + README hack: https://linebender.org/blog/doc-include
//! <style>.rustdoc-hidden { display: none; }</style>
//! <style>.rustdoc-hidden { display: none; }</style>
//! [`Pointer`]: `crate::Pointer`
//! [`PointerBuf`]: `crate::PointerBuf`
//! [`Token`]: `crate::Token`
//! [`Tokens`]: `crate::Tokens`
//! [`Component`]: `crate::Component`
//! [`from_tokens`]: crate::PointerBuf::from_tokens
// ! [`Components`]: crate::Components
// ! [`Resolve`]: crate::resolve::Resolve
// ! [`ResolveMut`]: crate::resolve::ResolveMut
// ! [`resolve`]: crate::resolve
// ! [`assign`]: crate::assign
// ! [`delete`]: crate::delete
// ! [`index`]: crate::index
// ! [`Root`]: crate::Component::Root
// ! [`str`]: str
// ! [`String`]: String
// ! [`serde_json::Value`]: serde_json::Value
// ! [`Pointer::resolve`]: crate::Pointer::resolve
// ! [`Pointer::resolve_mut`]: crate::Pointer::resolve_mut
// ! [`Pointer::assign`]: crate::Pointer::assign
// ! [`Pointer::delete`]: crate::Pointer::delete
// ! [`Pointer::parse`]: crate::Pointer::parse
// ! [`PointerBuf::parse`]: crate::PointerBuf::parse
// ! [`PointerBuf::from_tokens`]: crate::PointerBuf::from_tokens
// ! [`toml::Value`]: https://docs.rs/toml/0.8/toml/enum.Value.html
//! [`from_tokens`]: crate::PointerBuf::from_tokens
// ! [`Components`]: crate::Components
// ! [`Resolve`]: crate::resolve::Resolve
// ! [`ResolveMut`]: crate::resolve::ResolveMut
// ! [`resolve`]: crate::resolve
// ! [`assign`]: crate::assign
// ! [`delete`]: crate::delete
// ! [`index`]: crate::index
// ! [`Root`]: crate::Component::Root
// ! [`str`]: str
// ! [`String`]: String
// ! [`serde_json::Value`]: serde_json::Value
// ! [`Pointer::resolve`]: crate::Pointer::resolve
// ! [`Pointer::resolve_mut`]: crate::Pointer::resolve_mut
// ! [`Pointer::assign`]: crate::Pointer::assign
// ! [`Pointer::delete`]: crate::Pointer::delete
// ! [`Pointer::parse`]: crate::Pointer::parse
// ! [`PointerBuf::parse`]: crate::PointerBuf::parse
// ! [`PointerBuf::from_tokens`]: crate::PointerBuf::from_tokens
// ! [`toml::Value`]: https://docs.rs/toml/0.8/toml/enum.Value.html
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
pub use pointer::{ParseError, Pointer, PointerBuf, ReplaceError};

mod token;
pub use token::{InvalidEncodingError, Token, Tokens};

pub mod index;

mod component;
pub use component::{Component, Components};

#[cfg(test)]
mod arbitrary;
