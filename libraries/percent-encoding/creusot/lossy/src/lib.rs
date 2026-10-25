// Gate 1, decode_utf8_lossy (percent-encoding 2.3.2), for builds with debug assertions off
// (Cargo.toml: [profile.dev] debug-assertions = false; every release build). The original body
// (mod orig) and the patched body (mod patched, which drops the debug-only
// `debug_assert!(core::ptr::eq(..))`) meet the same exact spec `lossy_spec`.
// With debug assertions ON the original also evaluates `ptr::eq(utf8.as_bytes(), &*bytes)` and
// panics if it is false. Creusot 0.14 models `&x as *const _` as a fresh pointer unrelated to
// `x`, so that assertion cannot be proved here: see README.md (open for debug builds).
#![allow(unused)]
use creusot_std::prelude::*;
use std::borrow::Cow;
use creusot_std::std::string::injective_to_bytes;
use creusot_std::std::ptr::PointerExt;

// String::from_utf8_lossy, seen through its view (owned or not, and the text): a deterministic
// function of the input bytes; when it borrows, the input was valid UTF-8 and the text is the
// input (std docs: it returns Cow::Borrowed exactly when no replacement is needed).
#[logic(opaque)]
pub fn lossy_v(v: Seq<u8>) -> (bool, Seq<char>) {
    dead
}

extern_spec! {
    impl String {
        #[ensures(cow_view(result) == lossy_v(v@))]
        #[ensures(match result { Cow::Borrowed(s) => s@.to_bytes() == v@, Cow::Owned(_) => true })]
        fn from_utf8_lossy(v: &[u8]) -> Cow<'_, str>;
    }
    impl str {
        #[check(ghost)]
        #[ensures(result@ == self@.to_bytes())]
        fn as_bytes(&self) -> &[u8];
    }
    mod core { mod ptr {
        #[check(ghost)]
        #[ensures(result == (a.addr_logic() == b.addr_logic()))]
        fn eq<T: ?Sized>(a: *const T, b: *const T) -> bool;
    } }
}

// Owned or borrowed, and the text.
#[logic(open)]
pub fn cow_view(c: Cow<'_, str>) -> (bool, Seq<char>) {
    pearlite! { match c { Cow::Borrowed(s) => (false, s@), Cow::Owned(s) => (true, s@) } }
}

#[logic(open)]
pub fn lossy_spec(input: Cow<'_, [u8]>) -> (bool, Seq<char>) {
    pearlite! {
        match input {
            Cow::Borrowed(b) => lossy_v(b@),
            Cow::Owned(v) => (true, lossy_v(v@).1),
        }
    }
}

pub mod orig {
    use super::*;

    #[allow(ambiguous_wide_pointer_comparisons)]
    #[ensures(cow_view(result) == lossy_spec(input))]
    #[ensures({ let _ = injective_to_bytes(); true })]
    // verbatim: upstream src/lib.rs fn decode_utf8_lossy(input: Cow<'_, [u8]>) -> Cow<'_, str> {
    fn decode_utf8_lossy(input: Cow<'_, [u8]>) -> Cow<'_, str> {
        // Note: This function is duplicated in `form_urlencoded/src/query_encoding.rs`.
        match input {
            Cow::Borrowed(bytes) => String::from_utf8_lossy(bytes),
            Cow::Owned(bytes) => {
                match String::from_utf8_lossy(&bytes) {
                    Cow::Borrowed(utf8) => {
                        // If from_utf8_lossy returns a Cow::Borrowed, then we can
                        // be sure our original bytes were valid UTF-8. This is because
                        // if the bytes were invalid UTF-8 from_utf8_lossy would have
                        // to allocate a new owned string to back the Cow so it could
                        // replace invalid bytes with a placeholder.

                        // First we do a debug_assert to confirm our description above.
                        let raw_utf8: *const [u8] = utf8.as_bytes();
                        debug_assert!(core::ptr::eq(raw_utf8, &*bytes));

                        // Given we know the original input bytes are valid UTF-8,
                        // and we have ownership of those bytes, we re-use them and
                        // return a Cow::Owned here.
                        Cow::Owned(unsafe { String::from_utf8_unchecked(bytes) })
                    }
                    Cow::Owned(s) => Cow::Owned(s),
                }
            }
        }
    }
}

pub mod patched {
    use super::*;

    #[allow(ambiguous_wide_pointer_comparisons)]
    #[ensures(cow_view(result) == lossy_spec(input))]
    #[ensures({ let _ = injective_to_bytes(); true })]
    // verbatim: patched src/lib.rs fn decode_utf8_lossy(input: Cow<'_, [u8]>) -> Cow<'_, str> {
    fn decode_utf8_lossy(input: Cow<'_, [u8]>) -> Cow<'_, str> {
        // Note: This function is duplicated in `form_urlencoded/src/query_encoding.rs`.
        match input {
            Cow::Borrowed(bytes) => String::from_utf8_lossy(bytes),
            Cow::Owned(bytes) => {
                match String::from_utf8_lossy(&bytes) {
                    Cow::Borrowed(utf8) => {
                        // If from_utf8_lossy returns a Cow::Borrowed, then we can
                        // be sure our original bytes were valid UTF-8. This is because
                        // if the bytes were invalid UTF-8 from_utf8_lossy would have
                        // to allocate a new owned string to back the Cow so it could
                        // replace invalid bytes with a placeholder.

                        // AENEAS PATCH: the debug-only pointer-equality assertion
                        // `debug_assert!(core::ptr::eq(utf8.as_bytes(), &*bytes))`
                        // is removed; Aeneas has no raw pointers. It never changes
                        // the result in release builds.
                        let _ = utf8;

                        // Given we know the original input bytes are valid UTF-8,
                        // and we have ownership of those bytes, we re-use them and
                        // return a Cow::Owned here.
                        Cow::Owned(unsafe { String::from_utf8_unchecked(bytes) })
                    }
                    Cow::Owned(s) => Cow::Owned(s),
                }
            }
        }
    }
}
