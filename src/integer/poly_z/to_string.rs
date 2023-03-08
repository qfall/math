//! This module contains all options to convert a polynomial of type
//! [`PolyZ`] into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::PolyZ;
use core::fmt;
use flint_sys::fmpz_poly::fmpz_poly_get_str;
use std::ffi::CStr;

impl fmt::Display for PolyZ {
    /// Allows to convert a polynomial of type [`PolyZ`] into a [`String`].
    ///
    /// # Examples
    /// ```rust
    /// use math::integer::PolyZ;
    /// use std::str::FromStr;
    /// use core::fmt;
    ///
    /// let poly = PolyZ::from_str("4  0 1 2 3").unwrap();
    /// println!("{}", poly);
    /// ```
    ///
    /// ```rust
    /// use math::integer::PolyZ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyZ::from_str("4  0 1 2 3").unwrap();
    /// let poly_string = poly.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let c_str_ptr = unsafe { fmpz_poly_get_str(&self.poly) };
        let return_str = unsafe { CStr::from_ptr(c_str_ptr).to_str().unwrap().to_owned() };
        // free the space allocated by the pointer
        unsafe { libc::free(c_str_ptr as *mut libc::c_void) };
        write!(f, "{}", return_str)
    }
}

#[cfg(test)]
mod test_to_string {

    use super::PolyZ;
    use std::str::FromStr;

    /// tests whether a polynomial that is created using a string, returns the
    /// same string, when it is converted back to a string
    #[test]
    fn working_keeps_same_string() {
        let cmp_string = "3  1 2 -3";
        let cmp = PolyZ::from_str(cmp_string).unwrap();

        assert_eq!(cmp_string, cmp.to_string())
    }

    /// tests whether a polynomial that is created using a string, returns a
    /// string that can be used to create a polynomial
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let cmp_string = "3  1 2 -3";
        let cmp = PolyZ::from_str(cmp_string).unwrap();

        let cmp_string2 = cmp.to_string();

        assert!(PolyZ::from_str(&cmp_string2).is_ok())
    }

    /// tests whether large entries are correctly converted using to_string
    #[test]
    fn large_entries() {
        let cmp_string = format!("3  1 {} -{}", u64::MAX, u64::MAX);
        let cmp = PolyZ::from_str(&cmp_string).unwrap();

        let cmp_string2 = cmp.to_string();

        assert!(PolyZ::from_str(&cmp_string2).is_ok())
    }
}
