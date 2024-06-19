use serde_json::Value;

use crate::{DeleteError, Pointer};
/// Delete is implemented by types which can internally remove a value based on
/// a JSON Pointer
pub trait Delete {
    /// Error associated with `Delete`
    type Error;
    /// Attempts to internally delete a value based upon a [Pointer].
    fn delete(&mut self, ptr: &Pointer) -> Option<Value>;
}

impl Delete for Value {
    type Error = DeleteError;
    fn delete(&mut self, ptr: &Pointer) -> Option<Value> {
        ptr.delete(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn test_issue_18() {
        let mut data = json!({
            "Example": 21,
            "test": "test"
        });
        let pointer = Pointer::from_static("/Example");
        pointer.delete(&mut data);
        assert_eq!(json!({"test": "test"}), data);
    }
}
