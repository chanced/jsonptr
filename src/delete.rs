use serde_json::Value;

use crate::{MalformedPointerError, PointerBuf};
/// Delete is implemented by types which can internally remove a value based on
/// a JSON Pointer
pub trait Delete {
    /// Error associated with `Delete`
    type Error;
    /// Attempts to internally delete a value based upon a [Pointer].
    fn delete(&mut self, ptr: &PointerBuf) -> Option<Value>;
}

impl Delete for Value {
    type Error = MalformedPointerError;
    fn delete(&mut self, ptr: &PointerBuf) -> Option<Value> {
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
        let pointer = PointerBuf::from_tokens(["Example"]);
        println!("{}", pointer);
        pointer.delete(&mut data);
        assert_eq!(json!({"test": "test"}), data);
    }
}
