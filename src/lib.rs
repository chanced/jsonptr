mod pointer;
pub use pointer::*;
mod token;
pub use token::*;

pub mod error;
pub use error::*;

pub mod assign;
pub use assign::*;
pub mod delete;
pub use delete::*;
pub mod resolve;
pub use resolve::*;

pub mod prelude;

pub(crate) const MALFORMED_TOKEN_ERR:&str = "the Json Pointer was empty which should never happen.\nPlease report this bug: https://github.com/chanced/jsonptr/issues/new.";
