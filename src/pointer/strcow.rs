use alloc::{
    borrow::{Cow, ToOwned},
    string::String,
};

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
    use alloc::{borrow::Cow, string::String};

    pub trait Sealed {}
    impl Sealed for &str {}
    impl Sealed for String {}
    impl Sealed for Cow<'_, str> {}
}

#[cfg(test)]
mod tests {
    use super::StrCow;
    use alloc::{borrow::Cow, string::String};

    #[test]
    fn sanity() {
        let str_ref = "apple";
        let str_own = String::from("apple");
        let cow_ref = Cow::Borrowed("apple");
        let cow_own = Cow::<'static, str>::Owned(String::from("apple"));
        assert_eq!(StrCow::as_ref(&str_ref), StrCow::as_ref(&str_own));
        assert_eq!(StrCow::as_ref(&str_ref), StrCow::as_ref(&cow_ref));
        assert_eq!(StrCow::as_ref(&str_ref), StrCow::as_ref(&cow_own));
        assert_eq!(StrCow::as_ref(&str_own), StrCow::as_ref(&cow_ref));
        assert_eq!(StrCow::as_ref(&str_own), StrCow::as_ref(&cow_own));
        assert_eq!(StrCow::as_ref(&cow_ref), StrCow::as_ref(&cow_own));
        assert_eq!(
            StrCow::into_owned(str_ref),
            StrCow::into_owned(str_own.clone())
        );
        assert_eq!(
            StrCow::into_owned(str_ref),
            StrCow::into_owned(cow_ref.clone())
        );
        assert_eq!(
            StrCow::into_owned(str_ref),
            StrCow::into_owned(cow_own.clone())
        );
        assert_eq!(
            StrCow::into_owned(str_own.clone()),
            StrCow::into_owned(cow_ref.clone())
        );
        assert_eq!(
            StrCow::into_owned(str_own.clone()),
            StrCow::into_owned(cow_own.clone())
        );
        assert_eq!(
            StrCow::into_owned(cow_ref.clone()),
            StrCow::into_owned(cow_own.clone())
        );
    }
}
