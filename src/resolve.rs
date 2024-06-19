use crate::{resolve_error, Pointer, ResolveError};
use serde_json::Value;
use snafu::ResultExt;

/// Resolve is implemented by types which can resolve a reference to a
/// `serde_json::Value` from the path in a JSON Pointer.
pub trait Resolve {
    /// Error associated with `Resolve`
    type Error;
    /// Resolve a reference to a `serde_json::Value` based on the path in a
    /// [Pointer].
    fn resolve(&self, ptr: &Pointer) -> Result<&Value, Self::Error>;
}
impl Resolve for Value {
    type Error = ResolveError;

    fn resolve(&self, mut ptr: &Pointer) -> Result<&Value, Self::Error> {
        let mut offset = 0;
        let mut value = self;
        while let Some((token, rem)) = ptr.split_front() {
            offset += 1 + token.encoded().len();
            ptr = rem;
            value = match value {
                Value::Array(v) => {
                    let idx = token
                        .to_index()
                        .with_context(|_| resolve_error::FailedToParseIndexSnafu { offset })?
                        .for_len(v.len())
                        .with_context(|_| resolve_error::OutOfBoundsSnafu { offset })?;
                    Ok(&v[idx])
                }

                Value::Object(v) => v
                    .get(token.decoded().as_ref())
                    .ok_or_else(|| resolve_error::NotFoundSnafu { offset }.build()),
                // found a leaf node but the pointer hasn't been exhausted
                _ => resolve_error::UnreachableSnafu { offset }.fail(),
            }?;
        }
        Ok(value)
    }
}

/// ResolveMut is implemented by types which can resolve a mutable reference to
/// a `serde_json::Value` from the path in a JSON Pointer.
pub trait ResolveMut {
    type Error;
    /// Resolve a mutable reference to a `serde_json::Value` based on the path
    /// in a JSON Pointer.
    fn resolve_mut(&mut self, ptr: &Pointer) -> Result<&mut Value, Self::Error>;
}
impl ResolveMut for Value {
    type Error = ResolveError;

    fn resolve_mut(&mut self, mut ptr: &Pointer) -> Result<&mut Value, ResolveError> {
        let mut offset = 0;
        let mut value = self;
        while let Some((token, rem)) = ptr.split_front() {
            offset += 1 + token.encoded().len();
            ptr = rem;
            value = match value {
                Value::Array(array) => {
                    let idx = token
                        .to_index()
                        .with_context(|_| resolve_error::FailedToParseIndexSnafu { offset })?
                        .for_len(array.len())
                        .with_context(|_| resolve_error::OutOfBoundsSnafu { offset })?;
                    Ok(&mut array[idx])
                }
                Value::Object(v) => v
                    .get_mut(token.decoded().as_ref())
                    .ok_or_else(|| resolve_error::NotFoundSnafu { offset }.build()),
                // found a leaf node but the pointer hasn't been exhausted
                _ => resolve_error::UnreachableSnafu { offset }.fail(),
            }?;
        }
        Ok(value)
    }
}
