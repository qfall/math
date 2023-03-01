//! This module contains implementations of functions important for ownership such as the [std::clone::Clone], [std::marker::Copy], and/ or [std::ops::Drop] trait.
//!
//! The explicit functions contain the documentation.
//!
//! # Example
//! ```
//! use math::integer::Z;
//!
//! let a = Z::from_i64(1);
//! let b = a.clone();
//! drop(a);
//! ```

use super::Z;
use flint_sys::fmpz::{fmpz, fmpz_clear, fmpz_set};

impl Clone for Z {
    /// Clones the given element and returns a deep clone of the [Z] element.
    ///
    /// # Example
    /// ```
    /// use math::integer::Z;
    ///
    /// let a = Z::from_i64(1);
    /// let b = a.clone();
    /// ```
    fn clone(&self) -> Self {
        let mut value = fmpz(0);
        unsafe { fmpz_set(&mut value, &self.value) };
        Self { value }
    }
}

impl Drop for Z {
    /// Drops the given [Z] value and frees the allocated memory.
    ///
    /// # Examples
    /// ```
    /// use math::integer::Z;
    /// {
    ///     let z: Z = Z::from_i64(3);
    /// } // as z's scope ends here, it get's dropped
    /// ```
    ///
    /// ```
    /// use math::integer::Z;
    ///
    /// let z: Z = Z::from_i64(3);
    /// drop(z); // explicitly drops z's value
    /// ```
    fn drop(&mut self) {
        unsafe { fmpz_clear(&mut self.value) }
    }
}
