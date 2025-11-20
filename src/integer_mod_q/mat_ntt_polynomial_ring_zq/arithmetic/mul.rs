// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of multiplication for [`MatNTTPolynomialRingZq`].

use crate::{
    integer::Z,
    integer_mod_q::MatNTTPolynomialRingZq,
    macros::arithmetics::{
        arithmetic_trait_borrowed_to_owned, arithmetic_trait_mixed_borrowed_owned,
    },
    traits::CompareBase,
};
use flint_sys::fmpz_mod::{fmpz_mod_add_fmpz, fmpz_mod_ctx, fmpz_mod_mul};
use std::ops::Mul;

impl Mul for &MatNTTPolynomialRingZq {
    type Output = MatNTTPolynomialRingZq;

    /// Multiplies `self` with `other`.
    ///
    /// Paramters:
    /// - `other`: specifies the NTT-representation of the polynomial to multiply to `self`
    ///
    /// Returns the NTT-representation of the multiplication of `self` and `other`.
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
    /// let b = MatNTTPolynomialRingZq::sample_uniform(3, 4, &modulus);
    ///
    /// let c = a * b;
    /// ```
    ///
    /// # Panics ...
    /// - if the number of rows of `self` and the number of columns of `other` does not match up.
    /// - if their moduli do not match.
    fn mul(self, other: Self) -> Self::Output {
        assert_eq!(self.nr_columns, other.nr_rows,
            "The number of rows of `self` and the number of columns of `other` has to be equal for matrix multiplication.");
        if !self.compare_base(other) {
            panic!("{}", self.call_compare_base_error(other).unwrap());
        }

        let mod_ctx = &self.modulus.get_fq_ctx().ctxp[0];

        let mut res = Vec::with_capacity(other.matrix.len());

        for col in 0..other.nr_columns {
            for row in 0..self.nr_rows {
                let mut entry = self.mul_entry(other, mod_ctx, row, col, 0);
                for i in 1..self.nr_columns {
                    let add_value = self.mul_entry(other, mod_ctx, row, col, i);

                    for j in 0..self.modulus.get_degree() as usize {
                        unsafe {
                            fmpz_mod_add_fmpz(
                                &mut entry[j].value,
                                &entry[j].value,
                                &add_value[j].value,
                                mod_ctx,
                            )
                        };
                    }
                }

                res.append(&mut entry);
            }
        }

        MatNTTPolynomialRingZq {
            matrix: res,
            nr_rows: self.nr_rows,
            nr_columns: other.nr_columns,
            modulus: self.modulus.clone(),
        }
    }
}

impl MatNTTPolynomialRingZq {
    /// Instantiates a new vector with the result of multiplying two entries/polynomials.
    ///
    /// Parameters:
    /// - `other`: the other [`MatNTTPolynomialRingZq`] that contains the polynomial to multiply with
    /// - `mod_ctx`: the [`fmpz_mod_ctx`] to reduce every coefficent by
    /// - `row`: refers to the row, where the resulting entry will be
    /// - `col`: refers to the resulting column, where the resulting will be
    /// - `index`: defines the summand to compute
    fn mul_entry(
        &self,
        other: &Self,
        mod_ctx: &fmpz_mod_ctx,
        row: usize,
        col: usize,
        index: usize,
    ) -> Vec<Z> {
        let mut entry = vec![Z::default(); self.modulus.get_degree() as usize];
        let entry_self = self.get_entry(row, index);
        let entry_other = other.get_entry(index, col);

        for i in 0..self.modulus.get_degree() as usize {
            unsafe {
                fmpz_mod_mul(
                    &mut entry[i].value,
                    &entry_self[i].value,
                    &entry_other[i].value,
                    mod_ctx,
                );
            }
        }

        entry
    }
}

arithmetic_trait_borrowed_to_owned!(
    Mul,
    mul,
    MatNTTPolynomialRingZq,
    MatNTTPolynomialRingZq,
    MatNTTPolynomialRingZq
);
arithmetic_trait_mixed_borrowed_owned!(
    Mul,
    mul,
    MatNTTPolynomialRingZq,
    MatNTTPolynomialRingZq,
    MatNTTPolynomialRingZq
);

#[cfg(test)]
mod test_mul {
    use crate::{
        integer_mod_q::{
            MatNTTPolynomialRingZq, MatPolynomialRingZq, ModulusPolynomialRingZq, PolyOverZq,
        },
        traits::SetCoefficient,
    };
    use std::{ops::Mul, str::FromStr};

    /// Ensure that the entrywise multiplication and the intuitive multiplication yields
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

        let p1 = MatPolynomialRingZq::sample_uniform(3, 3, &polynomial_modulus);
        let p2 = MatPolynomialRingZq::sample_uniform(3, 4, &polynomial_modulus);

        let ntt1 = MatNTTPolynomialRingZq::from(&p1);
        let ntt2 = MatNTTPolynomialRingZq::from(&p2);

        let ntt_res = ntt1.mul(&ntt2);

        assert_eq!(&p1 * &p2, MatPolynomialRingZq::from(ntt_res))
    }

    /// Ensure that the entrywise multiplication and the intuitive multiplication yields
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

        let p1 = MatPolynomialRingZq::sample_uniform(2, 3, &polynomial_modulus);
        let p2 = MatPolynomialRingZq::sample_uniform(3, 4, &polynomial_modulus);

        let ntt1 = MatNTTPolynomialRingZq::from(&p1);
        let ntt2 = MatNTTPolynomialRingZq::from(&p2);

        let ntt_res = ntt1.mul(&ntt2);

        assert_eq!(&p1 * &p2, MatPolynomialRingZq::from(ntt_res))
    }

    /// Ensure that the entrywise multiplication and the intuitive multiplication yields
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

        let p1 = MatPolynomialRingZq::sample_uniform(2, 3, &polynomial_modulus);
        let p2 = MatPolynomialRingZq::sample_uniform(3, 4, &polynomial_modulus);

        let ntt1 = MatNTTPolynomialRingZq::from(&p1);
        let ntt2 = MatNTTPolynomialRingZq::from(&p2);

        let ntt_res = ntt1.mul(&ntt2);

        assert_eq!(&p1 * &p2, MatPolynomialRingZq::from(ntt_res))
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

        let _ = a * b;
    }

    /// Ensures that the function panics for differing dimensions.
    #[test]
    #[should_panic]
    fn different_dimensions() {
        let mut modulus = ModulusPolynomialRingZq::from_str("5  1 0 0 0 1 mod 257").unwrap();
        modulus.set_ntt_unchecked(64);

        let a = MatNTTPolynomialRingZq::sample_uniform(2, 3, &modulus);
        let b = MatNTTPolynomialRingZq::sample_uniform(2, 2, &modulus);

        let _ = a * b;
    }
}
