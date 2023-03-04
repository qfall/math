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
//! let a = PolyZ::from_str("3  0 1 2");
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
    /// let a = PolyZ::from_str("3  0 1 2");
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
    ///     let a = PolyZ::from_str("3  0 1 2");
    /// } // as a's scope ends here, it get's dropped
    /// ```
    ///
    /// ```
    /// use math::integer::PolyZ;
    /// use std::str::FromStr;
    ///
    /// let a = PolyZ::from_str("3  0 1 2");
    /// drop(a); // explicitly drops a's value
    /// ```
    fn drop(&mut self) {
        unsafe { fmpz_poly_clear(&mut self.poly) }
    }
}
