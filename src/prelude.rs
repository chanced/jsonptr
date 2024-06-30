//! Exposes the traits `Assign`, `Delete`, `Resolve`, `ResolveMut` if enabled.
#[cfg(feature = "assign")]
pub use crate::assign::Assign;
#[cfg(feature = "delete")]
pub use crate::delete::Delete;
#[cfg(feature = "resolve")]
pub use crate::resolve::{Resolve, ResolveMut};
