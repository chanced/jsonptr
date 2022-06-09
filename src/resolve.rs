use crate::{Error, Pointer};
use serde_json::Value;
/// Resolve is implemented by types
pub trait Resolve {
    type Error: std::error::Error + Send + Sync + 'static;
    fn resolve(&self, ptr: &Pointer) -> Result<&Value, Error>;
}
impl Resolve for Value {
    type Error = Error;
    /// Resolve a value based on the path provided by a JSON Pointer.
    fn resolve(&self, ptr: &Pointer) -> Result<&Value, Self::Error> {
        ptr.resolve(self)
    }
}

pub trait ResolveMut {
    fn resolve_mut(&mut self, ptr: &Pointer) -> Result<&mut Value, Error>;
}
impl ResolveMut for Value {
    /// Resolve a mutable value based on the path provided by a JSON Pointer.
    fn resolve_mut(&mut self, ptr: &Pointer) -> Result<&mut Value, Error> {
        ptr.resolve_mut(self)
    }
}
