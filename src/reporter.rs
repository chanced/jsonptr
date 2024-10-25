use core::marker::PhantomData;

use polonius_the_crab::polonius;

use crate::{error::Report, pointer::ReplaceError, PointerBuf, Token};

#[derive(Debug)]
pub struct Mutable<'p, E> {
    ptr: &'p mut PointerBuf,
    marker: PhantomData<fn() -> E>,
}

impl<'p> Mutable<'p, ReplaceError> {
    /// Attempts to replace a `Token` by the index, returning the replaced
    /// `Token` if it already exists. Returns `None` otherwise.
    ///
    /// ## Errors
    /// A [`ReplaceError`] is returned if the index is out of bounds.
    #[allow(clippy::missing_panics_doc)]
    pub fn replace<'t>(
        self,
        index: usize,
        token: impl Into<Token<'t>>,
    ) -> Result<Option<Token<'t>>, Report<ReplaceError>>
    where
        'p: 't,
    {
        use polonius_the_crab::{polonius, ForLt, Placeholder, PoloniusResult};
        type TokenRef = ForLt!(<'a> = Result<Option<Token<'a>>, ReplaceError>);
        let ptr = self.ptr;
        match polonius::<_, _, TokenRef>(ptr, |ptr| match ptr.replace(index, token) {
            Ok(res) => PoloniusResult::Borrowing(Ok(res)),
            Err(err) => PoloniusResult::Owned {
                value: Err::<TokenRef, ReplaceError>(err),
                input_borrow: Placeholder,
            },
        }) {
            PoloniusResult::Borrowing(ok) => Ok(unsafe { ok.unwrap_unchecked() }),
            PoloniusResult::Owned {
                value,
                input_borrow,
            } => Err(Report::new(
                unsafe { value.unwrap_err_unchecked() },
                input_borrow.clone(),
            )),
        }
    }
}
