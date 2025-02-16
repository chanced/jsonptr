use alloc::borrow::Cow;

pub trait StrCow: private::Sealed {
    fn as_ref(&self) -> &str;
    fn into_owned(self) -> String;
}

impl StrCow for &str {
    fn as_ref(&self) -> &str {
        self
    }

    fn into_owned(self) -> String {
        self.to_owned()
    }
}

impl StrCow for String {
    fn as_ref(&self) -> &str {
        self.as_str()
    }

    fn into_owned(self) -> String {
        self
    }
}

impl StrCow for Cow<'_, str> {
    fn as_ref(&self) -> &str {
        AsRef::as_ref(self)
    }

    fn into_owned(self) -> String {
        self.into_owned()
    }
}

mod private {
    use alloc::borrow::Cow;

    pub trait Sealed {}
    impl Sealed for &str {}
    impl Sealed for String {}
    impl Sealed for Cow<'_, str> {}
}
