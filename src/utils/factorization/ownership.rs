// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations for factorizations of [`Z`](crate::integer::Z) values.

use super::Factorization;
use flint_sys::fmpz_factor::fmpz_factor_clear;

impl Drop for Factorization {
    /// Drops the given [`Factorization`] value and frees the allocated memory.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::utils::Factorization;
    /// {
    ///     let fac = Factorization::from((8, 3));
    /// } // as fac's scope ends here, it get's dropped
    /// ```
    ///
    /// ```
    /// use qfall_math::utils::Factorization;
    ///
    /// let fac = Factorization::from((8, 3));
    /// drop(fac); // explicitly drops fac's value
    /// ```
    fn drop(&mut self) {
        unsafe { fmpz_factor_clear(&mut self.factors) }
    }
}

/// Test that the [`Drop`] trait is correctly implemented.
#[cfg(test)]
mod test_drop {
    use crate::utils::Factorization;

    /// Check whether freed memory is reused afterwards.
    #[test]
    fn free_memory() {
        let a = Factorization::from(u64::MAX);
        let a_p = a.factors.p;
        let _ = Factorization::from(u64::MAX);
        drop(a);
        let c = Factorization::from(u64::MAX);
        drop(c);

        // Instantiate new [`Factorization`] value to check if memory slot is reused for new value.
        let d = Factorization::from(u64::MAX);
        let d_p = d.factors.p;

        assert_eq!(a_p, d_p);
    }
}
