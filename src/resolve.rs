use crate::{Error, Pointer};
use serde_json::Value;
/// Resolve is implemented by types which can resolve a reference to a
/// `serde_json::Value` from the path in a JSON Pointer.
pub trait Resolve {
    type Error: std::error::Error + Send + Sync + 'static;
    /// Resolve a reference to a `serde_json::Value` based on the path in a JSON
    /// Pointer.
    fn resolve(&self, ptr: &Pointer) -> Result<&Value, Error>;
}
impl Resolve for Value {
    type Error = Error;
    fn resolve(&self, ptr: &Pointer) -> Result<&Value, Self::Error> {
        ptr.resolve(self)
    }
}

/// ResolveMut is implemented by types which can resolve a mutable reference to
/// a `serde_json::Value` from the path in a JSON Pointer.
pub trait ResolveMut {
    /// Resolve a mutable reference to a `serde_json::Value` based on the path
    /// in a JSON Pointer.
    fn resolve_mut(&mut self, ptr: &Pointer) -> Result<&mut Value, Error>;
}
impl ResolveMut for Value {
    fn resolve_mut(&mut self, ptr: &Pointer) -> Result<&mut Value, Error> {
        ptr.resolve_mut(self)
    }
}
