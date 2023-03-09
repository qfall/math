//! This module contains implementations of functions
//! important for ownership such as the [`Clone`] and [`Drop`] trait.
//!
//! The explicit functions contain the documentation.

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
        // a fresh fmpz value is created, set to the same value as the cloned one,
        // and wrapped in a new [`Z`] value. Hence, a fresh deep clone is created.
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
        // According to FLINT's documentation:
        // "Clears the given fmpz_t, releasing any memory associated with it,
        // either back to the stack or the OS, depending on whether the reentrant
        // or non-reentrant version of FLINT is built."
        // Hence, any memory allocated for values bigger than 2^62 is freed. The left
        // `i64` value is dropped automatically when the variable runs out of scope.

        unsafe { fmpz_clear(&mut self.value) }
    }
}

/// Test that the [`Clone`] trait is correctly implemented.
#[cfg(test)]
mod test_clone {

    use super::Z;

    /// check if large positive and negative values are cloned correctly
    /// additionally check if values are stored at different places in memory
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

    /// check if small positive, negative and zero values are cloned correctly
    /// additionally, check if the values are kept on the stack
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

    /// check if a cloned value is still alive after the original value ran out of scope
    #[test]
    #[allow(clippy::redundant_clone)]
    fn keep_alive() {
        let a: Z;
        {
            let b = Z::from(5);
            a = b.clone();
        }
        assert_eq!(a, Z::from(5));
    }
}

/// Test that the [`Drop`] trait is correctly implemented.
#[cfg(test)]
mod test_drop {

    use super::Z;

    /// Check whether freed memory is reused afterwards
    #[test]
    fn free_memory() {
        let a = Z::from(u64::MAX);
        let b = Z { value: a.value };

        drop(a);

        // instantiate different [`Z`] value to check if memory slot is reused for different value
        let c = Z::from(i64::MIN);
        assert_eq!(c.value.0, b.value.0);

        // memory slots differ due to previously created large integer
        assert_ne!(b.value.0, Z::from(u64::MAX).value.0);
    }

    /// This test shows why false copies are a problem, which are prevented for users of the library
    /// due to attribute privacy of the `value` attribute in [`Z`]
    #[test]
    fn memory_equality() {
        let a = Z::from(u64::MAX);
        // false clone/ copy of [`Z`] value allows for the [`fmpz`] value to be kept alive
        // after one reference was dropped and its referenced memory was freed
        let b = Z { value: a.value };

        drop(a);

        // any large new integer created is filled in the same memory space
        // as fmpz_equal first checks whether the pointers point to the same point in memory
        // and are then assumed to be the same, as they both point to the same value, these
        // values are equal afterwards. Even though, `b` pointed to a different value previously.
        assert_eq!(b, Z::from(i64::MIN));
    }
}
