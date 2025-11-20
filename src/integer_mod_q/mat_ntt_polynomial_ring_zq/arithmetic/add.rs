// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of addition for [`MatNTTPolynomialRingZq`].

use crate::{
    integer::Z,
    integer_mod_q::MatNTTPolynomialRingZq,
    macros::arithmetics::{
        arithmetic_assign_trait_borrowed_to_owned, arithmetic_trait_borrowed_to_owned,
        arithmetic_trait_mixed_borrowed_owned,
    },
    traits::CompareBase,
};
use flint_sys::fmpz_mod::fmpz_mod_add_fmpz;
use std::ops::{Add, AddAssign};

impl Add for &MatNTTPolynomialRingZq {
    type Output = MatNTTPolynomialRingZq;

    /// Adds `self` with `other`.
    ///
    /// Paramters:
    /// - `other`: specifies the NTT-representation of the polynomial to add to `self`
    ///
    /// Returns the NTT-representation of the sum of `self` and `other`.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::{MatNTTPolynomialRingZq, ModulusPolynomialRingZq};
    /// use crate::qfall_math::traits::SetCoefficient;
    /// use std::str::FromStr;
    /// let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
    /// modulus.set_ntt_unchecked(64);
    ///
    /// let a = MatNTTPolynomialRingZq::sample_uniform(2, 3, &modulus);
    /// let b = MatNTTPolynomialRingZq::sample_uniform(2, 3, &modulus);
    ///
    /// let c = a + b;
    /// ```
    ///
    /// # Panics ...
    /// - if the number of rows of `self` and `other` or their number of columns is not equal.
    /// - if their moduli do not match.
    fn add(self, other: Self) -> Self::Output {
        assert_eq!(
            self.nr_rows, other.nr_rows,
            "The number of rows of `self` and `other` has to be equal for matrix addition."
        );
        assert_eq!(
            self.nr_columns, other.nr_columns,
            "The number of columns of `self` and `other` has to be equal for matrix addition."
        );
        if !self.compare_base(other) {
            panic!("{}", self.call_compare_base_error(other).unwrap());
        }
        let mod_ctx = &self.modulus.get_fq_ctx().ctxp[0];

        let mut out = MatNTTPolynomialRingZq {
            matrix: vec![
                Z::default();
                self.modulus.get_degree() as usize * self.nr_rows * self.nr_columns
            ],
            nr_rows: self.nr_rows,
            nr_columns: self.nr_columns,
            modulus: self.modulus.clone(),
        };

        for i in 0..self.matrix.len() {
            unsafe {
                fmpz_mod_add_fmpz(
                    &mut out.matrix[i].value,
                    &self.matrix[i].value,
                    &other.matrix[i].value,
                    mod_ctx,
                );
            }
        }

        out
    }
}

arithmetic_trait_borrowed_to_owned!(
    Add,
    add,
    MatNTTPolynomialRingZq,
    MatNTTPolynomialRingZq,
    MatNTTPolynomialRingZq
);
arithmetic_trait_mixed_borrowed_owned!(
    Add,
    add,
    MatNTTPolynomialRingZq,
    MatNTTPolynomialRingZq,
    MatNTTPolynomialRingZq
);

impl AddAssign<&MatNTTPolynomialRingZq> for MatNTTPolynomialRingZq {
    /// Adds `self` with `other` reusing the memory of `self`.
    ///
    /// Paramters:
    /// - `other`: specifies the NTT-representation of the polynomial to add to `self`
    ///
    /// Computes the NTT-representation of the sum of `self` and `other`.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::{MatNTTPolynomialRingZq, ModulusPolynomialRingZq};
    /// use crate::qfall_math::traits::SetCoefficient;
    /// use std::str::FromStr;
    /// let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
    /// modulus.set_ntt_unchecked(64);
    ///
    /// let mut a = MatNTTPolynomialRingZq::sample_uniform(2, 3, &modulus);
    /// let b = MatNTTPolynomialRingZq::sample_uniform(2, 3, &modulus);
    ///
    /// a += b;
    /// ```
    ///
    /// # Panics ...
    /// - if the number of rows of `self` and `other` or their number of columns is not equal.
    /// - if their moduli do not match.
    fn add_assign(&mut self, other: &Self) {
        assert_eq!(
            self.nr_rows, other.nr_rows,
            "The number of rows of `self` and `other` has to be equal for matrix addition."
        );
        assert_eq!(
            self.nr_columns, other.nr_columns,
            "The number of columns of `self` and `other` has to be equal for matrix addition."
        );
        if !self.compare_base(other) {
            panic!("{}", self.call_compare_base_error(other).unwrap());
        }
        let mod_ctx = &self.modulus.get_fq_ctx().ctxp[0];

        for i in 0..self.matrix.len() {
            unsafe {
                fmpz_mod_add_fmpz(
                    &mut self.matrix[i].value,
                    &self.matrix[i].value,
                    &other.matrix[i].value,
                    mod_ctx,
                );
            }
        }
    }
}

arithmetic_assign_trait_borrowed_to_owned!(
    AddAssign,
    add_assign,
    MatNTTPolynomialRingZq,
    MatNTTPolynomialRingZq
);

#[cfg(test)]
mod test_add {
    use crate::{
        integer_mod_q::{
            MatNTTPolynomialRingZq, MatPolynomialRingZq, ModulusPolynomialRingZq, PolyOverZq,
        },
        traits::SetCoefficient,
    };
    use std::{ops::Add, str::FromStr};

    /// Ensure that the entrywise addition and the intuitive addition yields
    /// the same results for small parameters.
    #[test]
    fn test_small_params() {
        let n = 4;
        let modulus = 257;

        let mut mod_poly = PolyOverZq::from(modulus);
        mod_poly.set_coeff(0, 1).unwrap();
        mod_poly.set_coeff(n, 1).unwrap();

        let mut polynomial_modulus = ModulusPolynomialRingZq::from(&mod_poly);

        polynomial_modulus.set_ntt_unchecked(64);

        let p1 = MatPolynomialRingZq::sample_uniform(3, 4, &polynomial_modulus);
        let p2 = MatPolynomialRingZq::sample_uniform(3, 4, &polynomial_modulus);

        let ntt1 = MatNTTPolynomialRingZq::from(&p1);
        let ntt2 = MatNTTPolynomialRingZq::from(&p2);

        let res = ntt1.add(&ntt2);

        assert_eq!(&p1 + &p2, MatPolynomialRingZq::from(res))
    }

    /// Ensure that the entrywise addition and the intuitive addition yields
    /// the same results for the parameters from Dilithium.
    #[test]
    fn test_dilithium_params() {
        let n = 256;
        let modulus = 2_i64.pow(23) - 2_i64.pow(13) + 1;

        let mut mod_poly = PolyOverZq::from(modulus);
        mod_poly.set_coeff(0, 1).unwrap();
        mod_poly.set_coeff(n, 1).unwrap();

        let mut polynomial_modulus = ModulusPolynomialRingZq::from(&mod_poly);

        polynomial_modulus.set_ntt_unchecked(1753);

        let p1 = MatPolynomialRingZq::sample_uniform(4, 2, &polynomial_modulus);
        let p2 = MatPolynomialRingZq::sample_uniform(4, 2, &polynomial_modulus);

        let ntt1 = MatNTTPolynomialRingZq::from(&p1);
        let ntt2 = MatNTTPolynomialRingZq::from(&p2);

        let res = ntt1.add(&ntt2);

        assert_eq!(&p1 + &p2, MatPolynomialRingZq::from(res))
    }

    /// Ensure that the entrywise addition and the intuitive addition yields
    /// the same results for the parameters from Hawk1024.
    #[test]
    fn test_hawk1024_params() {
        let n = 1024;
        let modulus = 12289;

        let mut mod_poly = PolyOverZq::from(modulus);
        mod_poly.set_coeff(0, 1).unwrap();
        mod_poly.set_coeff(n, 1).unwrap();

        let mut polynomial_modulus = ModulusPolynomialRingZq::from(&mod_poly);

        polynomial_modulus.set_ntt_unchecked(1945);

        let p1 = MatPolynomialRingZq::sample_uniform(2, 2, &polynomial_modulus);
        let p2 = MatPolynomialRingZq::sample_uniform(2, 2, &polynomial_modulus);

        let ntt1 = MatNTTPolynomialRingZq::from(&p1);
        let ntt2 = MatNTTPolynomialRingZq::from(&p2);

        let res = ntt1.add(&ntt2);

        assert_eq!(&p1 + &p2, MatPolynomialRingZq::from(res))
    }

    /// Ensures that the function panics for differing moduli.
    #[test]
    #[should_panic]
    fn different_moduli() {
        let mut modulus0 = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
        modulus0.set_ntt_unchecked(64);
        let mut modulus1 = ModulusPolynomialRingZq::from_str("6  1 0 0 0 0 1 mod 257").unwrap();
        modulus1.set_ntt_unchecked(64);

        let a = MatNTTPolynomialRingZq::sample_uniform(2, 2, &modulus0);
        let b = MatNTTPolynomialRingZq::sample_uniform(2, 2, &modulus1);

        let _ = a + b;
    }

    /// Ensures that the function panics for differing dimensions.
    #[test]
    #[should_panic]
    fn different_dimensions() {
        let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
        modulus.set_ntt_unchecked(64);

        let a = MatNTTPolynomialRingZq::sample_uniform(2, 3, &modulus);
        let b = MatNTTPolynomialRingZq::sample_uniform(2, 2, &modulus);

        let _ = a + b;
    }
}

#[cfg(test)]
mod test_add_assign {
    use crate::{
        integer_mod_q::{
            MatNTTPolynomialRingZq, MatPolynomialRingZq, ModulusPolynomialRingZq, PolyOverZq,
        },
        traits::SetCoefficient,
    };
    use std::{ops::AddAssign, str::FromStr};

    /// Ensure that the entrywise addition and the intuitive addition yields
    /// the same results for small parameters.
    #[test]
    fn test_small_params() {
        let n = 4;
        let modulus = 257;

        let mut mod_poly = PolyOverZq::from(modulus);
        mod_poly.set_coeff(0, 1).unwrap();
        mod_poly.set_coeff(n, 1).unwrap();

        let mut polynomial_modulus = ModulusPolynomialRingZq::from(&mod_poly);

        polynomial_modulus.set_ntt_unchecked(64);

        let p1 = MatPolynomialRingZq::sample_uniform(3, 4, &polynomial_modulus);
        let p2 = MatPolynomialRingZq::sample_uniform(3, 4, &polynomial_modulus);

        let mut ntt1 = MatNTTPolynomialRingZq::from(&p1);
        let ntt2 = MatNTTPolynomialRingZq::from(&p2);

        ntt1.add_assign(&ntt2);

        assert_eq!(&p1 + &p2, MatPolynomialRingZq::from(ntt1))
    }

    /// Ensure that the entrywise addition and the intuitive addition yields
    /// the same results for the parameters from Dilithium.
    #[test]
    fn test_dilithium_params() {
        let n = 256;
        let modulus = 2_i64.pow(23) - 2_i64.pow(13) + 1;

        let mut mod_poly = PolyOverZq::from(modulus);
        mod_poly.set_coeff(0, 1).unwrap();
        mod_poly.set_coeff(n, 1).unwrap();

        let mut polynomial_modulus = ModulusPolynomialRingZq::from(&mod_poly);

        polynomial_modulus.set_ntt_unchecked(1753);

        let p1 = MatPolynomialRingZq::sample_uniform(4, 2, &polynomial_modulus);
        let p2 = MatPolynomialRingZq::sample_uniform(4, 2, &polynomial_modulus);

        let mut ntt1 = MatNTTPolynomialRingZq::from(&p1);
        let ntt2 = MatNTTPolynomialRingZq::from(&p2);

        ntt1.add_assign(&ntt2);

        assert_eq!(&p1 + &p2, MatPolynomialRingZq::from(ntt1))
    }

    /// Ensure that the entrywise addition and the intuitive addition yields
    /// the same results for the parameters from Hawk1024.
    #[test]
    fn test_hawk1024_params() {
        let n = 1024;
        let modulus = 12289;

        let mut mod_poly = PolyOverZq::from(modulus);
        mod_poly.set_coeff(0, 1).unwrap();
        mod_poly.set_coeff(n, 1).unwrap();

        let mut polynomial_modulus = ModulusPolynomialRingZq::from(&mod_poly);

        polynomial_modulus.set_ntt_unchecked(1945);

        let p1 = MatPolynomialRingZq::sample_uniform(2, 2, &polynomial_modulus);
        let p2 = MatPolynomialRingZq::sample_uniform(2, 2, &polynomial_modulus);

        let mut ntt1 = MatNTTPolynomialRingZq::from(&p1);
        let ntt2 = MatNTTPolynomialRingZq::from(&p2);

        ntt1.add_assign(&ntt2);

        assert_eq!(&p1 + &p2, MatPolynomialRingZq::from(ntt1))
    }

    /// Ensures that the function panics for differing moduli.
    #[test]
    #[should_panic]
    fn different_moduli() {
        let mut modulus0 = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
        modulus0.set_ntt_unchecked(64);
        let mut modulus1 = ModulusPolynomialRingZq::from_str("6  1 0 0 0 0 1 mod 257").unwrap();
        modulus1.set_ntt_unchecked(64);

        let mut a = MatNTTPolynomialRingZq::sample_uniform(2, 2, &modulus0);
        let b = MatNTTPolynomialRingZq::sample_uniform(2, 2, &modulus1);

        a += b;
    }

    /// Ensures that the function panics for differing dimensions.
    #[test]
    #[should_panic]
    fn different_dimensions() {
        let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
        modulus.set_ntt_unchecked(64);

        let mut a = MatNTTPolynomialRingZq::sample_uniform(2, 3, &modulus);
        let b = MatNTTPolynomialRingZq::sample_uniform(2, 2, &modulus);

        a += b;
    }
}
