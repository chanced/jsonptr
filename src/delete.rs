use serde_json::Value;

use crate::{MalformedPointerError, Pointer};
/// Delete is implemented by types which can internally remove a value based on
/// a JSON Pointer
pub trait Delete {
    /// Error associated with `Delete`
    type Error;
    /// Attempts to internally delete a value based upon a [Pointer].
    fn delete(&mut self, ptr: &Pointer) -> Option<Value>;
}

impl Delete for Value {
    type Error = MalformedPointerError;
    fn delete(&mut self, ptr: &Pointer) -> Option<Value> {
        ptr.delete(self)
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn test_issue_18() {
        let mut data = json!(
            {
                "Example": 21,
                "test": "test"
              }
        );
        let pointer = Pointer::new(["Example"]);
        println!("{}", pointer);
        pointer.delete(&mut data);
        assert_eq!(json!({"test": "test"}), data);
    }
}
