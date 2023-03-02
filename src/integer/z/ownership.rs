//! This module contains implementations of functions important for ownership such as the [`Clone`] and [`Drop`] trait.
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
    /// Clones the given element and returns a deep clone of the [`Z`] element.
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
    /// Drops the given [`Z`] value and frees the allocated memory.
    ///
    /// # Examples
    /// ```
    /// use math::integer::Z;
    /// {
    ///     let a = Z::from_i64(3);
    /// } // as a's scope ends here, it get's dropped
    /// ```
    ///
    /// ```
    /// use math::integer::Z;
    ///
    /// let a = Z::from_i64(3);
    /// drop(a); // explicitly drops a's value
    /// ```
    fn drop(&mut self) {
        unsafe { fmpz_clear(&mut self.value) }
    }
}

/// Test that the [`Clone`] trait is correctly implemented.
#[cfg(test)]
mod test_clone {

    use super::Z;

    // check if large positive and negative values are cloned correctly and stored at different places
    #[test]
    fn large_int() {
        let max_1 = Z::from(u64::MAX);
        let min_1 = Z::from(i64::MIN);

        let max_2 = max_1.clone();
        let min_2 = min_1.clone();

        assert_ne!(max_1.value.0, max_2.value.0);
        assert_ne!(min_1.value.0, min_2.value.0);
        assert_eq!(max_1, max_2);
        assert_eq!(min_1, min_2);
    }

    // check if small positive, negative and zero values are cloned correctly and kept on the stack
    #[test]
    fn small_int() {
        let pos_1 = Z::from(16);
        let zero_1 = Z::from(0);
        let neg_1 = Z::from(-16);

        let pos_2 = pos_1.clone();
        let zero_2 = zero_1.clone();
        let neg_2 = neg_1.clone();

        assert_eq!(pos_1.value.0, pos_2.value.0);
        assert_eq!(zero_1.value.0, zero_2.value.0);
        assert_eq!(neg_1.value.0, neg_2.value.0);
        assert_eq!(pos_1, pos_2);
        assert_eq!(zero_1, zero_2);
        assert_eq!(neg_1, neg_2);
    }

    // check if a cloned value is still alive after the original value ran out of scope
    #[test]
    fn keep_alive() {
        let a: Z;
        {
            let b = Z::from(5);
            a = b.clone();
        }
        assert_eq!(a, Z::from(5));
    }
}
