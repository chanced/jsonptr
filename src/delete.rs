use serde_json::Value;

use crate::{MalformedPointerError, Pointer};
/// Delete is implemented by types which can internally remove a value based on
/// a JSON Pointer
pub trait Delete {
    /// Error associated with `Delete`
    type Error;
    /// Attempts to internally delete a value based upon a [Pointer].
    fn delete(&mut self, ptr: &Pointer) -> Result<Option<Value>, Self::Error>;
}

impl Delete for Value {
    type Error = MalformedPointerError;
    fn delete(&mut self, ptr: &Pointer) -> Result<Option<Value>, Self::Error> {
        ptr.delete(self)
    }
}
