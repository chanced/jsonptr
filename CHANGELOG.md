# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## Unreleased

### Deprecated

-   Deprecated `ResolveError` name.

### Fixed

-   `EncodingError` and `ParseIndexError` now implement `Diagnostic`, which
    unifies the API for errors originating from parse-like operations.
-   Fixes returning an incorrect error type when parsing a `Token` that
    terminates with `~`. This now correctly classifies the error as a `Tilde`
    error.
-   Disabled default features for the `serde` dependency, which enables using
    this library in no-std environments even with the `serde` feature enabled.

### Removed

-   Some methods were removed from `InvalidCharacterError`, as that type no
    longer holds a copy of the input string internally. This is a breaking
    change. To access equivalent functionality, use the `Diagnostic` API
    integration.

### Changed
-   `Token::from_encoded` now accepts owned or borrowed strings (any type that
    implements `Into<Cow<'_, str>>`).
-   Sealed the `Diagnose` trait.
-   Implementation of the `Default` trait for `Pointer` now doesn't constrain the lifetime.

## [0.7.1] 2025-02-16

### Changed

-   Removes accidentally enabled default features `"miette"` and `"toml"`

## [0.7.0] 2025-02-13

### Added

-   Adds method `into_buf` for `Box<Pointer>` and `impl From<PathBuf> for Box<Pointer>`.
-   Adds unsafe associated methods `Pointer::new_unchecked` and `PointerBuf::new_unchecked` for
    external zero-cost construction.
-   Adds `Pointer::starts_with` and `Pointer::ends_with` for prefix and suffix matching.
-   Adds new `ParseIndexError` variant to express the presence non-digit characters in the token.
-   Adds `Token::is_next` for checking if a token represents the `-` character.
-   Adds `InvalidEncoding` to represent the two possible encoding errors when decoding a token.
-   Adds `diagnotic::Diagnostic` trait to facilitate error reporting and
    `miette` integration. All errors intended for usage with `assign::Assign` or
    `resolve::Resolve` must implement this trait.
-   Adds `diagnostic::Report<T>` to capture the input for `PointerBuf::parse`
    and to facilitate `miette` integration for all errors.
-   Adds `"miette"` feature flag to enable `miette` integration for error reporting.

### Changed

-   `Pointer::get` now accepts ranges and can produce `Pointer` segments as output (similar to
    `slice::get`).
-   Bumps minimum Rust version to 1.79.
-   `PointerBuf::parse` now returns `RichParseError`, an alias to
    `Report<ParseError>` which contains the allocated string as well as the
    error. Use `Report::original` for matches or `Report::
-   Renames `ParseError::NoLeadingBackslash` to `ParseError::NoLeadingSlash`
    (sorry for the churn, I spaced hard - @chanced).
-   Adds field `position` to variants of `resolve::Error` and `assign::Error` to indicate the
    token index of where the error occurred.
-   Renames `ParseError::is_no_leading_backslash` to `ParseError::is_no_leading_slash`.
-   Renames `assign::AssignError` to `assign::Error`
-   Renames `resolve::ResolveError` to `resolve::Error`
-   Renames `InvalidEncodingError` to `EncodingError`

### Fixed

-   Make validation of array indices conform to RFC 6901 in the presence of non-digit characters.

### Deprecated

-   `ParseError::is_no_leading_backslash` renamed to `ParseError::is_no_leading_slash`.
-   `assign::AssignError` renamed to `assign::Error`
-   `resolve::ResolveError` renamed to `resolve::Error`
-   `InvalidEncodingError` renamed to `EncodingError`

## [0.6.2] 2024-09-30

### Added

-   Adds methods `len` and `is_empty` to `Pointer`

## [0.6.1] 2024-09-26

## Added

-   Adds fluid methods `with_trailing_token`, `with_leading_token`, `concat` to `Pointer`.

## [0.6.0] - 2024-08-06

### Fixed

-   `Token::to_index` now fails if the token contains leading zeros, as mandated by the RFC.

### Changed

-   `ParseIndexError` is now an enum to reflect the new failure mode when parsing indices.

## [0.5.1]

### Changed

-   README tweak.

## [0.5.0]

This is a breaking release including:

-   [#30](https://github.com/chanced/jsonptr/pull/30) and [#37](https://github.com/chanced/jsonptr/pull/37) by [@asmello](https://github.com/asmello)
-   [#41](https://github.com/chanced/jsonptr/pull/41) by [@chanced](https://github.com/chanced) & [@asmello](https://github.com/asmello)

### Added

-   New slice type `Pointer` that enables zero-copy usage patterns
-   New const constructor `const fn Pointer::from_static` for compile-time allocated `Pointer`s
-   Zero-allocation `Pointer::root` singleton pointer
-   [Quickcheck](https://docs.rs/quickcheck/latest/quickcheck/index.html)-based testing
-   New methods: `Pointer::split_front`, `Pointer::split_back`, `Pointer::parent`, `Pointer::strip_suffix`
-   Implemented `Display` and `Debug` for `ParseError`
-   Adds `Pointer::split_at` which utilizes character offsets to split a pointer at a separator
-   Adds specific error types `ParseError`, `ResolveError`, `AssignError`

### Changed

-   JSON Pointers with leading `"#"` are no longer accepted. Previously, the erroneous leading hashtag was allowed during parsing but discarded.
-   `Assign`, `Resolve`, `ResolveMut`, `Delete` all now use associated types `Value` and `Error`, allowing for more impls other than JSON
-   Debug implementation now preserves type information (e.g. prints `PathBuf("/foo/bar")` instead of `"/foo/bar"`) - `Display` remains the same
-   Original `Pointer` type renamed to `PointerBuf`
-   Error types now use character `offset` indexing instead of owned copies of `Pointer` and `Token`.
-   `Pointer::root` is now `PointerBuf::new`
-   `Pointer::new` is now `PointerBuf::from_tokens` (and takes an `IntoIterator` argument - arrays still work)
-   `Pointer::union` is now `PointerBuf::intersection`
-   `Token` type has been simplified and is now by default a borrowed type (use `Token::to_owned` or `Token::into_owned` to make it owned)
-   `Assign::assign` now returns `Result<Option<Assign::Value>, AssignError>`, where `Option<Assign::Value>` is the replaced value

### Fixed

-   Fixes [#28](https://github.com/chanced/jsonptr/pull/28): `Pointer::union` is misleadingly named

### Removed

-   Removes `Assignment`
-   Removes `MaybePointer`
-   Removes `Error`
-   Removes `impl Deref<Target=&str>` from `Pointer`
-   Removes optional dependencies of `url`, `fluent-uri` and `uniresid` as well as the `TryFrom` implementations for their respective types
-   Removed `Token::as_key` and `Token::as_str` - use `Token::decoded().as_ref()` to achieve the same effect
-   Several redundant or error-prone trait implementations were removed from `Token`

## [0.4.7] 2024-03-18

-   Fixes issue with `pop_front` on a token with an empty string leaving the pointer in an invalid state. #25 by [@wngr](https://github.com/wngr)
-   Fixes issue with `pop_back` on a token with an empty string. #26 by [@asmello](https://github.com/asmello)

## [0.4.6] 2024-03-24

-   Fixes `Pointer::last` panicking for empty/root pointers #23 by [@wngr](https://github.com/wngr)

## [0.4.5] 2024-02-23

### Fixed

-   Fixes issue with `Pointer::push_back` that does not allow for empty strings
    to be appended as tokens. #21 fixed by [@wngr](https://github.com/wngr)

## [0.4.3] 2023-08-20

### Added

-   Adds `parse` method to `Pointer` which calls the currently existing `FromStr`
    impl

## [0.4.2] 2023-06-23

### Added

-   implements `IntoIterator` for `&Pointer`

## [0.4.1] 2023-06-21

### Added

-   implements `Borrow<[u8]>` and `AsRef<[u8]>` for `Pointer`

## [0.4.0] 2023-05-31

### Added

-   Adds `CHANGELOG.md` which will be better upkept moving forward.
-   Adds `MaybePointer` to assist with deserialization which should not fail fast.

### Changed

-   `Pointer::new` now accepts a generic list, so `&["example"]` can be replaced by `["example"]`. For untyped, empty slices (i.e. `Pointer::new(&[])`), use `Pointer::default()`.
-   `std` is now enabled by default.

### Removed

-   Removes optional `MalformedPointerError` from `Pointer`.

## [0.3.6] 2023-05-23

### Changed

-   Adds quotes around `Pointer` debug output (#11)

### Fixed

-   Adds missing `impl std::error::Error` for `Error`, `NotFoundError`, `MalformedError`
-   Fixes build for `std` feature flag

## [0.3.4] 2023-05-11

### Added

-   Adds feature flag `fluent-uri` for `From<fluent_uri::Uri<_>` impl (#3)

## [0.2.0] 2023-02-24

### Changed

-   `std` is now optional
-   Adds feature flags `"uniresid"`, `"url"` to enable implementing `From<Uri>`, `From<Url>` (respectively).

### Removed

-   Removes `Cargo.lock`
-   Makes `uniresid` and `uri` optional

## [0.1.0] - 2022-06-12

### Fixed

-   Fixes root pointer representation `""` rather than the erroneous `"/"`
-   Fixes an issue where encoded tokens were not being resolved properly
