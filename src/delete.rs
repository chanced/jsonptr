// use serde::Serialize;
// use serde_json::value::{Serializer, Value};

// use crate::{resolve_mut, Error, JsonPointer};

// pub trait Delete {
//     fn delete(&mut self, ptr: &JsonPointer) -> Result<Deletion, Error>;
// }

// pub struct Deletion {
//     pub value: Value,
//     pub deleted: Option<Value>,
// }

// impl<T> Delete for T
// where
//     T: Serialize,
// {
//     fn delete(&mut self, pointer: &JsonPointer) -> Result<Deletion, Error> {
//         let mut value = self.serialize(Serializer).map_err(Into::into)?;
//         let mut ptr = pointer.clone();
//         let last = pointer.pop_back();
//         let res = resolve_mut(&mut value, &mut ptr)?;
//     }
// }

// #[cfg(feature="has_specialization")]
// impl<T> Delete
