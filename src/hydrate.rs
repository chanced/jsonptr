#[cfg(feature = "has_specialization")]
pub trait Hydrate {
    fn hydrate<T: Deserialize>(&self, state: T) -> Result<T, Error>;
}
