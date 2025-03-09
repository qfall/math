// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains an implementation to compute the bit-wise complement.

use crate::integer::Z;
use flint_sys::fmpz::fmpz_complement;

impl Z {
    /// Outputs the bit-wise complement of `self`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// let value = Z::from(4);
    ///
    /// let complement = value.bit_complement();
    /// let complement_twice = complement.bit_complement();
    ///
    /// assert_eq!(Z::from(-5), complement);
    /// assert_eq!(value, complement_twice);
    /// ```
    pub fn bit_complement(&self) -> Self {
        let mut out = Z::default();
        unsafe { fmpz_complement(&mut out.value, &self.value) };
        out
    }
}

#[cfg(test)]
mod test_bitxor {
    use super::Z;

    /// Ensures that [`Z::bit_complement`] works as intended for small numbers.
    #[test]
    fn small_numbers() {
        let value_0 = Z::from(12);
        let value_1 = Z::from(567);

        let com_0 = value_0.bit_complement();
        let com_1 = value_1.bit_complement();
        let comcom_0 = com_0.bit_complement();
        let comcom_1 = com_1.bit_complement();

        assert_eq!(Z::from(-13), com_0);
        assert_eq!(Z::from(-568), com_1);
        assert_eq!(value_0, comcom_0);
        assert_eq!(value_1, comcom_1);
    }

    /// Ensures that [`Z::bit_complement`] works as intended for large numbers.
    #[test]
    fn large_numbers() {
        let value_0 = Z::from(i64::MAX);
        let value_1 = Z::from(i64::MIN);

        let com_0 = value_0.bit_complement();
        let com_1 = value_1.bit_complement();
        let comcom_0 = com_0.bit_complement();
        let comcom_1 = com_1.bit_complement();

        assert_eq!(Z::from(i64::MIN), com_0);
        assert_eq!(Z::from(i64::MAX), com_1);
        assert_eq!(value_0, comcom_0);
        assert_eq!(value_1, comcom_1);
    }
}
