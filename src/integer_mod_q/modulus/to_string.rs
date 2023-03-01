//! This module contains all options to convert a modulus of type
//! [`Modulus`](crate::integer_mod_q::Modulus) into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use flint_sys::fmpz::fmpz_get_str;

use super::Modulus;
use core::fmt;
use std::{ffi::CStr, ptr::null_mut};

impl fmt::Display for Modulus {
    /// Allows to convert a modulus of type [`Modulus`] into a [`String`].
    ///
    /// # Example 1
    /// ```rust
    /// use math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    /// use core::fmt;
    ///
    /// let modulus = Modulus::from_str("42").unwrap();
    /// println!("{}", modulus);
    /// ```
    ///
    /// # Example 2
    /// ```rust
    /// use math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    ///
    /// let modulus = Modulus::from_str("42").unwrap();
    /// let modulus_string = modulus.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // we have to access modulus.n[0] manually because there is no dedicated
        // method in FLINT
        let c_str_ptr = unsafe { fmpz_get_str(null_mut(), 10, &self.modulus.n[0]) };

        // we expect c_str_ptr to be reference a real value, hence get_str returns an
        // actual value, hence a simple unwrap should be sufficient and we do not have
        // to consider an exception
        //
        // c_string should not be null either, since we call this method on an
        // instantiated object
        let return_str = unsafe { CStr::from_ptr(c_str_ptr).to_str().unwrap().to_owned() };
        unsafe { libc::free(c_str_ptr as *mut libc::c_void) };

        write!(f, "{}", return_str)
    }
}

#[cfg(test)]
mod test_to_string {
    use std::str::FromStr;

    use crate::integer_mod_q::Modulus;

    // tests whether a large modulus works in a roundtrip
    #[test]
    fn working_large() {
        let cmp_string = "1".repeat(65);
        let cmp = Modulus::from_str(&cmp_string).unwrap();

        assert_eq!(cmp_string, cmp.to_string())
    }

    // tests whether a positive modulus works in a roundtrip
    #[test]
    fn working_positive() {
        let cmp_string = "42";
        let cmp = Modulus::from_str(cmp_string).unwrap();

        assert_eq!(cmp_string, cmp.to_string())
    }

    // tests whether a modulus that is created using a string, returns a
    // string that can be used to create a [`Modulus`]
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp_string = "42";
        let cmp = Modulus::from_str(cmp_string).unwrap();

        let cmp_string2 = cmp.to_string();

        assert!(Modulus::from_str(&cmp_string2).is_ok())
    }
}
