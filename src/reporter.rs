use crate::{
    error::{Report, ReportErr, ReportErrMut},
    pointer::ReplaceError,
    resolve, Pointer, PointerBuf, Token,
};
use core::marker::PhantomData;
use polonius_the_crab::{polonius, ForLt, Placeholder, PoloniusResult};

pub struct Immutable<'p, E> {
    ptr: &'p Pointer,
    marker: PhantomData<fn() -> E>,
}

#[cfg(feature = "resolve")]
impl<'p> Immutable<'p, resolve::Error> {
    /// Attempts to resolve a [`R::Value`] based on the path in this [`Pointer`].
    ///
    /// ## Errors
    /// Returns [`ResolveError`] if:
    /// - The path is unreachable (e.g. a scalar is encountered prior to the end
    ///   of the path)
    /// - The path is not found (e.g. a key in an object or an index in an array
    ///   does not exist)
    /// - A [`Token`] cannot be parsed as an array [`Index`]
    /// - An array [`Index`] is out of bounds
    ///
    /// [`R::Value`]: `crate::resolve::Resolve::Value`
    /// [`R::Error`]: `crate::resolve::Resolve::Error`
    /// [`Resolve`]: `crate::resolve::Resolve`
    /// [`ResolveError`]: `crate::resolve::ResolveError`
    /// [`Token`]: `crate::Token`
    /// [`Index`]: `crate::index::Index`
    pub fn resolve<R: crate::Resolve<Error = resolve::Error>>(
        self,
        value: &'_ R,
    ) -> Result<&'_ R::Value, Report<resolve::Error>> {
        value
            .resolve(self.ptr)
            .map_err(|err| Report::new(err, self.ptr))
    }
}

impl ReportErr<resolve::Error> for &'_ Pointer {
    type Reporter<'e, E> = Immutable<'e, resolve::Error> where Self: 'e;

    fn report_err(&'_ self) -> Self::Reporter<'_, resolve::Error> {
        Immutable {
            ptr: self,
            marker: PhantomData,
        }
    }
}

#[derive(Debug)]
pub struct Mutable<'p, E> {
    ptr: &'p mut PointerBuf,
    marker: PhantomData<fn() -> E>,
}

impl ReportErrMut<ReplaceError> for PointerBuf {
    type Reporter<'e, E> = Mutable<'e, ReplaceError>;

    fn report_err(&'_ mut self) -> Self::Reporter<'_, ReplaceError> {
        Mutable {
            ptr: self,
            marker: PhantomData,
        }
    }
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
        type ReplaceTokenResult = ForLt!(<'a> = Result<Option<Token<'a>>, ReplaceError>);
        let Self { ptr, .. } = self;
        match polonius::<_, _, ReplaceTokenResult>(ptr, |ptr| match ptr.replace(index, token) {
            Ok(res) => PoloniusResult::Borrowing(Ok(res)),
            Err(err) => PoloniusResult::Owned {
                value: Err::<ReplaceTokenResult, ReplaceError>(err),
                input_borrow: Placeholder,
            },
        }) {
            PoloniusResult::Borrowing(ok) => Ok(unsafe { ok.unwrap_unchecked() }),
            PoloniusResult::Owned {
                value,
                input_borrow,
            } => Err(Report::new(
                unsafe { value.unwrap_err_unchecked() }, // unchecked required due to lack of fmt::Debug impl for FtLt<dyn WithLifetime<'_>>
                input_borrow.clone(),
            )),
        }
    }
}
