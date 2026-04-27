// Copyright 2026 Jan Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the `mod±` function for [`MatPolynomialRingZq`] values.

use crate::{
    integer::{MatPolyOverZ, Z},
    integer_mod_q::MatPolynomialRingZq,
    traits::{GetCoefficient, MatrixDimensions, MatrixGetEntry, MatrixSetEntry, SetCoefficient},
};
use std::ops::Rem;

impl MatPolynomialRingZq {
    /// Computes `self` mod± `modulus` as long as `modulus` is greater than 1, i.e.
    /// it returns a matrix containing polynomials with coefficients in `[-⌈q/2⌉, ⌈q/2⌉]`.
    ///
    /// Parameters:
    /// - `modulus`: specifies a non-zero integer
    ///   over which the remainder closest to `0` is computed
    ///
    /// Returns `self` mod± `modulus` as a [`MatPolyOverZ`] instance.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer::MatPolyOverZ, integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq}};
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 24").unwrap();
    /// let a = MatPolyOverZ::from_str("[[1  2],[1  42]]").unwrap();
    /// let mut a = MatPolynomialRingZq::from((a, &modulus));
    ///
    /// let c = a.mod_pm(24);
    ///
    /// assert_eq!(MatPolyOverZ::from_str("[[1  2],[1  -6]]").unwrap(), c);
    /// ```
    ///
    /// # Panics ...
    /// - if `modulus` is smaller than `2`.
    pub fn mod_pm(&self, modulus: impl Into<Z>) -> MatPolyOverZ {
        let modulus = modulus.into();
        assert!(modulus > 1, "Modulus can not be smaller than 2.");

        let mut mat = (&self.matrix).rem(&modulus);

        for row in 0..mat.get_num_rows() {
            for col in 0..mat.get_num_columns() {
                let mut entry = unsafe { mat.get_entry_unchecked(row, col) };
                for i in 0..=entry.get_degree() {
                    let mut coeff = unsafe { entry.get_coeff_unchecked(i) };
                    if coeff > modulus.div_floor(2) {
                        coeff -= &modulus;
                    }
                    unsafe { entry.set_coeff_unchecked(i, coeff) };
                }
                unsafe { mat.set_entry_unchecked(row, col, entry) };
            }
        }

        mat
    }
}

#[cfg(test)]
mod test_mod_pm {
    use super::Z;
    use crate::{
        integer::MatPolyOverZ,
        integer_mod_q::{MatPolynomialRingZq, Modulus, ModulusPolynomialRingZq},
    };
    use std::str::FromStr;

    /// Testing mod± for two owned
    #[test]
    fn mod_pm() {
        let poly_mod = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 257").unwrap();
        let a = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap();
        let a = MatPolynomialRingZq::from((a, &poly_mod));
        let b = Z::from(25);
        let modulus = Modulus::from(25);
        let c1 = a.clone().mod_pm(b);
        let c2 = a.clone().mod_pm(modulus);
        let cmp = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 -8, 1  -1]]").unwrap();
        assert_eq!(c1, cmp);
        assert_eq!(c2, cmp);
    }

    /// Testing mod± for large numbers
    #[test]
    fn mod_pm_large_numbers() {
        let poly_mod =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", u64::MAX)).unwrap();
        let a = MatPolyOverZ::from_str(&format!("[[1  2, 1  {}],[2  3 42, 1  24]]", u64::MAX - 1))
            .unwrap();
        let a = MatPolynomialRingZq::from((a, &poly_mod));
        let b = Z::from(u64::MAX - 2);
        let modulus = Modulus::from(u64::MAX - 2);
        let c1 = a.clone().mod_pm(&b);
        let c2 = a.clone().mod_pm(&modulus);
        let cmp = MatPolyOverZ::from_str("[[1  2, 1  1],[2  3 42, 1  24]]").unwrap();
        assert_eq!(c1, cmp);
        assert_eq!(c2, cmp);
    }

    /// Ensures that computing mod± a negative number results in a panic
    #[test]
    #[should_panic]
    fn mod_pm_negative_error() {
        let poly_mod = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 257").unwrap();
        let a = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap();
        let a = MatPolynomialRingZq::from((a, &poly_mod));
        let b = Z::from(-24);
        _ = a.mod_pm(&b);
    }

    /// Ensures that computing mod± 0 results in a panic
    #[test]
    #[should_panic]
    fn zero_modulus() {
        let poly_mod = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 257").unwrap();
        let a = MatPolyOverZ::from_str("[[1  2, 1  3],[2  3 42, 1  24]]").unwrap();
        let a = MatPolynomialRingZq::from((a, &poly_mod));
        _ = a.mod_pm(0);
    }

    /// Ensures that `mod±` is available for several types implementing [`Into<Z>`].
    #[test]
    fn availability() {
        let _ =
            MatPolynomialRingZq::from_str("[[1  2, 1  3],[2  3 42, 1  24]] / 4  1 0 0 1 mod 24")
                .unwrap()
                .mod_pm(2u8);
        let _ =
            MatPolynomialRingZq::from_str("[[1  2, 1  3],[2  3 42, 1  24]] / 4  1 0 0 1 mod 24")
                .unwrap()
                .mod_pm(2u16);
        let _ =
            MatPolynomialRingZq::from_str("[[1  2, 1  3],[2  3 42, 1  24]] / 4  1 0 0 1 mod 24")
                .unwrap()
                .mod_pm(2u32);
        let _ =
            MatPolynomialRingZq::from_str("[[1  2, 1  3],[2  3 42, 1  24]] / 4  1 0 0 1 mod 24")
                .unwrap()
                .mod_pm(2u64);
        let _ =
            MatPolynomialRingZq::from_str("[[1  2, 1  3],[2  3 42, 1  24]] / 4  1 0 0 1 mod 24")
                .unwrap()
                .mod_pm(2i8);
        let _ =
            MatPolynomialRingZq::from_str("[[1  2, 1  3],[2  3 42, 1  24]] / 4  1 0 0 1 mod 24")
                .unwrap()
                .mod_pm(2i16);
        let _ =
            MatPolynomialRingZq::from_str("[[1  2, 1  3],[2  3 42, 1  24]] / 4  1 0 0 1 mod 24")
                .unwrap()
                .mod_pm(2i32);
        let _ =
            MatPolynomialRingZq::from_str("[[1  2, 1  3],[2  3 42, 1  24]] / 4  1 0 0 1 mod 24")
                .unwrap()
                .mod_pm(2i64);
        let _ =
            MatPolynomialRingZq::from_str("[[1  2, 1  3],[2  3 42, 1  24]] / 4  1 0 0 1 mod 24")
                .unwrap()
                .mod_pm(Z::from(2));
    }
}
