//! This module contains all options to convert an integer of type
//! [`Zq`] into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::Zq;
use core::fmt;
use flint_sys::fmpz::fmpz_get_str;
use std::{ffi::CStr, ptr::null_mut};

impl fmt::Display for Zq {
    /// Allows to convert an integer of type [`Zq`] into a [`String`].
    ///
    /// # Examples
    /// ```
    /// use math::integer_mod_q::Zq;
    /// use std::str::FromStr;
    /// use core::fmt;
    ///
    /// let integer = Zq::from_str("42 mod 3").unwrap();
    /// println!("{}", integer);
    /// ```
    ///
    /// ```rust
    /// use math::integer_mod_q::Zq;
    /// use std::str::FromStr;
    /// use core::fmt;
    ///
    /// let integer = Zq::from_str("42 mod 3").unwrap();
    /// let integer_string = integer.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let modulus_string = self.modulus.to_string();

        let c_str_ptr = unsafe { fmpz_get_str(null_mut(), 10, &self.value.value) };

        // we expect c_str_ptr to be reference a real value, hence get_str returns an
        // actual value, hence a simple unwrap should be sufficient and we do not have
        // to consider an exception
        //
        // c_string should not be null either, since we call this method on an
        // instantiated object
        let msg = "We expect the pointer to point to a real value and the c_string 
        not to be null. This error occurs if the provided string does not have UTF-8 format.";
        let integer_string = unsafe { CStr::from_ptr(c_str_ptr).to_str().expect(msg).to_owned() };

        unsafe { libc::free(c_str_ptr as *mut libc::c_void) };

        write!(f, "{} mod {}", integer_string, modulus_string)
    }
}

#[cfg(test)]
mod test_to_string {

    use crate::integer_mod_q::Zq;
    use std::str::FromStr;

    /// tests whether a large integer works in a roundtrip
    #[test]
    fn working_large_positive() {
        let cmp = Zq::from_str(&format!("{} mod {}", u64::MAX, u128::MAX)).unwrap();

        assert_eq!(format!("{} mod {}", u64::MAX, u128::MAX), cmp.to_string())
    }

    /// tests whether a large integer works in a roundtrip
    #[test]
    fn working_large_negative() {
        let cmp = Zq::from_str(&format!("-{} mod {}", u64::MAX, u128::MAX)).unwrap();
        let diff = u128::MAX - u64::MAX as u128;

        assert_eq!(format!("{} mod {}", diff, u128::MAX), cmp.to_string())
    }

    /// tests whether a positive integer works in a roundtrip
    #[test]
    fn working_positive() {
        let cmp = Zq::from_str("42 mod 60").unwrap();

        assert_eq!("42 mod 60", cmp.to_string())
    }

    /// tests whether a negative integer works in a roundtrip
    #[test]
    fn working_negative() {
        let cmp = Zq::from_str("-40 mod 3").unwrap();

        assert_eq!("2 mod 3", cmp.to_string())
    }

    /// tests whether a integer that is created using a string, returns a
    /// string that can be used to create a [`Zq`]
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp = Zq::from_str("42 mod 10").unwrap();

        let cmp_string = cmp.to_string();

        assert!(Zq::from_str(&cmp_string).is_ok())
    }
}
