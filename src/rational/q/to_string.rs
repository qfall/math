//! This module contains all options to convert a rational of type
//! [`Q`] into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::Q;
use core::fmt;
use flint_sys::fmpq::fmpq_get_str;
use std::{ffi::CStr, ptr::null_mut};

impl fmt::Display for Q {
    /// Allows to convert an integer of type [`Q`] into a [`String`].
    ///
    /// # Examples
    /// ```rust
    /// use std::str::FromStr;
    /// use math::rational::Q;
    /// use core::fmt;
    ///
    /// let rational = Q::from_str("-1/235").unwrap();
    /// println!("{}", rational);
    /// ```
    ///
    /// ```rust
    /// use std::str::FromStr;
    /// use math::rational::Q;
    /// use core::fmt;
    ///
    /// let rational = Q::from_str("-1/235").unwrap();
    /// let integer_string = rational.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let c_str_ptr = unsafe { fmpq_get_str(null_mut(), 10, &self.value) };

        // we expect c_str_ptr to be reference a real value, hence get_str returns an
        // actual value, hence a simple unwrap should be sufficient and we do not have
        // to consider an exception
        //
        // c_string should not be null either, since we call this method on an
        // instantiated object
        let msg = "We expect the pointer to point to a real value and the c_string 
        not to be null. This error occurs if the provided string does not have UTF-8 format.";
        let return_str = unsafe { CStr::from_ptr(c_str_ptr).to_str().expect(msg).to_owned() };

        unsafe { libc::free(c_str_ptr as *mut libc::c_void) };

        write!(f, "{}", return_str)
    }
}

#[cfg(test)]
mod test_to_string {

    use crate::rational::Q;
    use std::str::FromStr;

    /// tests whether a large rational works in a roundtrip
    #[test]
    fn working_large_positive_nom() {
        let cmp = Q::from_str(&u64::MAX.to_string()).unwrap();

        assert_eq!(u64::MAX.to_string(), cmp.to_string())
    }

    /// tests whether a large rational works in a roundtrip
    #[test]
    fn working_large_negative_nom() {
        let cmp = Q::from_str(&format!("-{}", u64::MAX)).unwrap();

        assert_eq!(format!("-{}", u64::MAX), cmp.to_string())
    }

    /// tests whether a large rational works in a roundtrip
    #[test]
    fn working_large_positive_den() {
        let cmp = Q::from_str(&format!("1/{}", u64::MAX)).unwrap();

        assert_eq!(format!("1/{}", u64::MAX), cmp.to_string())
    }

    /// tests whether a large rational works in a roundtrip
    #[test]
    fn working_large_negative_den() {
        let cmp = Q::from_str(&format!("1/-{}", u64::MAX)).unwrap();

        assert_eq!(format!("-1/{}", u64::MAX), cmp.to_string())
    }

    /// tests whether a positive rational works in a roundtrip
    #[test]
    fn working_positive() {
        let cmp = Q::from_str("42/235").unwrap();

        assert_eq!("42/235", cmp.to_string())
    }

    /// tests whether a positive rational works in a roundtrip
    #[test]
    fn working_negative() {
        let cmp = Q::from_str("-42/235").unwrap();

        assert_eq!("-42/235", cmp.to_string())
    }

    /// tests whether a rational that is created using a string, returns a
    /// string that can be used to create a [`Q`]
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp = Q::from_str("42/235").unwrap();

        let cmp_string2 = cmp.to_string();

        assert!(Q::from_str(&cmp_string2).is_ok())
    }
}
