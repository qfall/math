//! This module contains implementations of functions
//! important for ownership such as the [`Clone`] and [`Drop`] trait.
//!
//! The explicit functions contain the documentation.

use super::PolyOverZq;
use crate::integer::PolyOverZ;
use flint_sys::fmpz_mod_poly::{fmpz_mod_poly_init, fmpz_mod_poly_set_fmpz_poly};
use std::{mem::MaybeUninit, str::FromStr};

impl Clone for PolyOverZq {
    /// Clones the given element and returns another cloned reference
    /// to the [`Modulus`](crate::integer_mod_q::Modulus) element.
    ///
    /// # Example
    /// ```
    /// use math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let a = PolyOverZq::from_str("4  0 1 -2 3 mod 13").unwrap();
    /// let b = a.clone();
    /// ```
    fn clone(&self) -> Self {
        let string = self.to_string();
        let poly_over_z = PolyOverZ::from_str(&string).unwrap();

        let mut poly_zq = MaybeUninit::uninit();
        unsafe {
            // init new fmpz_mod_poly_struct
            fmpz_mod_poly_init(poly_zq.as_mut_ptr(), self.modulus.get_fmpz_mod_ctx_struct());

            // set fmpz_mod_poly_struct to actual value
            let mut poly_zq = poly_zq.assume_init();
            fmpz_mod_poly_set_fmpz_poly(
                &mut poly_zq,
                &poly_over_z.poly,
                self.modulus.get_fmpz_mod_ctx_struct(),
            );

            // return clone
            Self {
                poly: poly_zq,
                modulus: self.modulus.clone(),
            }
        }
    }
}

/// Test that the [`Clone`] trait is correctly implemented.
#[cfg(test)]
mod test_clone {

    use super::PolyOverZq;
    use std::str::FromStr;

    /// Check if clone points to same point in memory
    #[test]
    fn same_reference() {
        let a = PolyOverZq::from_str(&format!("4  {} 1 -2 3 mod {}", i64::MAX, u64::MAX)).unwrap();

        let b = a.clone();

        // check that Modulus isn't stored twice
        assert_eq!(
            a.modulus.get_fmpz_mod_ctx_struct().n[0].0,
            b.modulus.get_fmpz_mod_ctx_struct().n[0].0
        );

        // check that values on heap are stored separately
        assert_ne!(
            unsafe { *a.poly.coeffs.offset(0) }.0,
            unsafe { *b.poly.coeffs.offset(0) }.0
        ); // heap
        assert_eq!(
            unsafe { *a.poly.coeffs.offset(1) }.0,
            unsafe { *b.poly.coeffs.offset(1) }.0
        ); // stack
        assert_ne!(
            unsafe { *a.poly.coeffs.offset(2) }.0,
            unsafe { *b.poly.coeffs.offset(2) }.0
        ); // heap
        assert_eq!(
            unsafe { *a.poly.coeffs.offset(3) }.0,
            unsafe { *b.poly.coeffs.offset(3) }.0
        ); // stack
    }
}
