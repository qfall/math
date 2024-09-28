// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Default values for a [`Factorization`].

use super::Factorization;
use flint_sys::fmpz_factor::fmpz_factor_init;
use std::mem::MaybeUninit;

impl Default for Factorization {
    /// Returns an instantiation of [`Factorization`] with `1` as the only factor.
    ///
    /// # Examples
    /// ```
    /// use std::default::Default;
    /// use qfall_math::utils::Factorization;
    ///  
    /// let fac = Factorization::default();
    /// ```
    fn default() -> Self {
        let mut factors = MaybeUninit::uninit();

        unsafe {
            fmpz_factor_init(factors.as_mut_ptr());

            Self {
                factors: factors.assume_init(),
            }
        }
    }
}

#[cfg(test)]
mod tests_init {
    use crate::utils::Factorization;

    /// Ensure that [`Default`] initializes a [`Factorization`] with `1`.
    #[test]
    fn init_default() {
        let fac = Factorization::default();

        assert_eq!("[(1, 1)]", fac.to_string());
    }
}
