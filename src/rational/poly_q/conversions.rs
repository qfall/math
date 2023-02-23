//! Implementations of conversions from and to type [PolyQ].
//!
//! This module contains all options convert a polynomial of type [PolyQ]. This includes the 'Display' trait.

use core::fmt;
use std::ffi::CStr;

use flint_sys::fmpq_poly::fmpq_poly_get_str;

use super::PolyQ;

impl fmt::Display for PolyQ {
    /// Allows to convert a polynomial of type [PolyQ] into a String.
    ///
    /// # Example 1
    /// ```rust
    /// use math::rational::PolyQ;
    /// use std::str::FromStr;
    /// use core::fmt;
    ///
    /// let poly = PolyQ::from_str("4  0 1 2 3").unwrap();
    /// println!("{}", poly);
    /// ```
    ///
    /// # Example 2
    /// ```rust
    /// use math::rational::poly_q::PolyQ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyQ::from_str("4  0 1 2 3").unwrap();
    /// let poly_string = poly.to_string();
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let c_str_ptr = unsafe { fmpq_poly_get_str(&self.poly) };
        let return_str = unsafe { CStr::from_ptr(c_str_ptr).to_str().unwrap().to_owned() };
        // free the space allocated by the pointer
        unsafe { libc::free(c_str_ptr as *mut libc::c_void) };
        write!(f, "{}", return_str)
    }
}

#[cfg(test)]
mod test {
    use std::str::FromStr;

    use crate::rational::poly_q::PolyQ;

    // tests whether a polynomial that is created using a string, returns the same string, when it is converted back to a string
    #[test]
    fn to_string_working_keeps_same_string() {
        let cmp_string = "3  1 2 -3";
        let cmp = PolyQ::from_str(cmp_string).unwrap();

        assert_eq!(cmp_string, cmp.to_string())
    }

    // tests whether a polynomial that is created using a string, returns a string that can be used to create a polynomial
    #[test]
    fn to_string_working_use_result_of_to_string_as_input() {
        let cmp_string = "3  1 2 -3";
        let cmp = PolyQ::from_str(cmp_string).unwrap();

        let cmp_string2 = cmp.to_string();

        assert!(PolyQ::from_str(&cmp_string2).is_ok())
    }
}
