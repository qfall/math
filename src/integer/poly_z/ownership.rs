//! This module contains implementations of functions
//! important for ownership such as the [`Clone`] and [`Drop`] trait.
//!
//! The explicit functions contain the documentation.
//!
//! # Example
//! ```
//! use math::integer::PolyZ;
//! use std::str::FromStr;
//!
//! let a = PolyZ::from_str("3  0 1 2").unwrap();
//! let b = a.clone();
//! drop(a);
//! ```

use super::PolyZ;
use flint_sys::fmpz_poly::{fmpz_poly_clear, fmpz_poly_set};

impl Clone for PolyZ {
    /// Clones the given element and returns a deep clone of the [`PolyZ`] element.
    ///
    /// # Example
    /// ```
    /// use math::integer::PolyZ;
    /// use std::str::FromStr;
    ///
    /// let a = PolyZ::from_str("3  0 1 2").unwrap();
    /// let b = a.clone();
    /// ```
    fn clone(&self) -> Self {
        let mut value = PolyZ::init();

        unsafe { fmpz_poly_set(&mut value.poly, &self.poly) }

        value
    }
}

impl Drop for PolyZ {
    /// Drops the given [`PolyZ`] value and frees the allocated memory.
    ///
    /// # Examples
    /// ```
    /// use math::integer::PolyZ;
    /// use std::str::FromStr;
    /// {
    ///     let a = PolyZ::from_str("3  0 1 2").unwrap();
    /// } // as a's scope ends here, it get's dropped
    /// ```
    ///
    /// ```
    /// use math::integer::PolyZ;
    /// use std::str::FromStr;
    ///
    /// let a = PolyZ::from_str("3  0 1 2").unwrap();
    /// drop(a); // explicitly drops a's value
    /// ```
    fn drop(&mut self) {
        // According to FLINT's documentation:
        // "Clears the given polynomial, releasing any memory used. It must be reinitialized in order to be used again."

        unsafe { fmpz_poly_clear(&mut self.poly) }
    }
}

/// Test that the [`Clone`] trait is correctly implemented.
#[cfg(test)]
mod test_clone {
    use crate::integer::PolyZ;
    use std::str::FromStr;

    /// check if a clone of a PolyZ with an entry larger than 64 bits
    /// works
    #[test]
    fn large_entries() {
        let u64_string = u64::MAX.to_string();
        let input = format!("2  {} -{}", u64_string, u64_string);

        let poly_1 = PolyZ::from_str(&input).unwrap();
        let poly_2 = poly_1.clone();

        // tests where the first coefficient is stored. Since both are larger than
        // an i64, both should be a pointer and their values should differ
        unsafe {
            assert_ne!((*poly_1.poly.coeffs).0, (*poly_2.poly.coeffs).0);
        }
        assert_eq!(poly_1.to_string(), poly_2.to_string())
    }

    /// check if several instantiations are cloned correctly
    #[test]
    fn small_examples() {
        let pos_1 = PolyZ::from_str("2  0 11").unwrap();
        let zero_1 = PolyZ::from_str("2  0 -11").unwrap();
        let neg_1 = PolyZ::from_str("2  0 1100").unwrap();

        let pos_2 = pos_1.clone();
        let zero_2 = zero_1.clone();
        let neg_2 = neg_1.clone();

        assert_eq!(pos_1.to_string(), pos_2.to_string());
        assert_eq!(zero_1.to_string(), zero_2.to_string());
        assert_eq!(neg_1.to_string(), neg_2.to_string());
    }

    /// check if a cloned value is still alive after the original value ran out of scope
    #[test]
    #[allow(clippy::redundant_clone)]
    fn keep_alive() {
        let a: PolyZ;
        {
            let b = PolyZ::from_str("2  0 1").unwrap();
            a = b.clone();
        }
        assert_eq!("2  0 1", a.to_string());
    }
}
