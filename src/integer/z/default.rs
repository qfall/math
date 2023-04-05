// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Default values for a [`Z`].

use super::Z;

impl Default for Z {
    /// Returns an instantiation of [`Z`] with value `0`.
    ///
    /// # Example:
    /// ```
    /// use std::default::Default;
    /// use qfall_math::integer::Z;
    ///  
    /// let a: Z = Z::default();
    /// ```
    fn default() -> Self {
        Z::from(0)
    }
}

impl Z {
    /// Returns an instantiation of [`Z`] with value `1`.
    ///
    /// # Example:
    /// ```
    /// use qfall_math::integer::Z;
    ///  
    /// let a: Z = Z::ONE;
    /// ```
    pub const ONE: Z = Z {
        value: flint_sys::fmpz::fmpz(1),
    };

    /// Returns an instantiation of [`Z`] with value `0`.
    ///
    /// # Example:
    /// ```
    /// use qfall_math::integer::Z;
    ///  
    /// let a: Z = Z::ZERO;
    /// ```
    pub const ZERO: Z = Z {
        value: flint_sys::fmpz::fmpz(0),
    };

    /// Returns an instantiation of [`Z`] with value `-1`.
    ///
    /// # Example:
    /// ```
    /// use qfall_math::integer::Z;
    ///  
    /// let a: Z = Z::MINUS_ONE;
    /// ```
    pub const MINUS_ONE: Z = Z {
        value: flint_sys::fmpz::fmpz(-1),
    };
}

#[cfg(test)]
mod tests_init {

    use super::Z;

    /// Ensure that [`Default`] initializes [`Z`] with `0`.
    #[test]
    fn init_default() {
        assert_eq!(Z::ZERO, Z::default());
    }

    /// Ensure that `ZERO` initializes [`Z`] with `0`.
    #[test]
    fn init_zero() {
        assert_eq!(Z::from(0), Z::ZERO);
    }

    /// Ensure that `ONE` initializes [`Z`] with `1`.
    #[test]
    fn init_one() {
        assert_eq!(Z::from(1), Z::ONE);
    }

    /// Ensure that `MINUS_ONE` initializes [`Z`] with `-1`.
    #[test]
    fn init_minus_one() {
        assert_eq!(Z::from(-1), Z::MINUS_ONE);
    }
}
