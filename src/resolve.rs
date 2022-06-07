use crate::{Error, Pointer};
use serde_json::Value;

pub trait Resolve {
    type Error: std::error::Error + Send + Sync + 'static;
    fn resolve(&self, ptr: &Pointer) -> Result<&Value, Error>;
}
impl Resolve for Value {
    type Error = Error;
    fn resolve(&self, ptr: &Pointer) -> Result<&Value, Self::Error> {
        ptr.resolve(self)
    }
}

pub trait ResolveMut {
    fn resolve_mut(&mut self, ptr: &Pointer) -> Result<&mut Value, Error>;
}
impl ResolveMut for Value {
    fn resolve_mut(&mut self, ptr: &Pointer) -> Result<&mut Value, Error> {
        ptr.resolve_mut(self)
    }
}
