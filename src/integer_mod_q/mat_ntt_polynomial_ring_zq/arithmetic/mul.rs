// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of multipliation for [`MatNTTPolynomialRingZq`].

use crate::{
    integer::Z,
    integer_mod_q::{MatNTTPolynomialRingZq, Modulus},
};
use flint_sys::fmpz_mod::{fmpz_mod_add_fmpz, fmpz_mod_ctx, fmpz_mod_mul};

impl MatNTTPolynomialRingZq {
    /// Multiplies `self` with `other`.
    ///
    /// Paramters:
    /// - `other`: specifies the NTT-representation of the polynomial to multiply to `self`
    /// - `modulus`: defines the modulus `q`
    ///
    /// Returns the NTT-representation of the multiplication of `self` and `other` generated
    /// with respect to `modulus`.
    ///
    /// # Example
    /// ```
    /// use qfall_math::integer_mod_q::{MatNTTPolynomialRingZq, Modulus};
    /// use crate::qfall_math::traits::SetCoefficient;
    ///
    /// let n = 4;
    /// let q = Modulus::from(257);
    ///
    /// let a = MatNTTPolynomialRingZq::sample_uniform(2, 3, n, &q);
    /// let b = MatNTTPolynomialRingZq::sample_uniform(3, 4, n, &q);
    ///
    /// a.mul(&b, &q);
    /// ```
    ///
    /// # Panics ...
    /// - if the `modulus` is smaller than `2`.
    /// - if the number of rows of `self` and the number of columns of `other` does not match up.
    /// - if the degree of the matrices is not equal.
    pub fn mul(&self, other: &Self, modulus: &Modulus) -> Self {
        assert_eq!(self.get_num_columns(), other.get_num_rows(),
            "The number of rows of `self` and the number of columns of `other` has to be equal for matrix multiplication.");
        assert_eq!(
            self.d, other.d,
            "The degree of both matrices' modulus has to be equal for multiplication."
        );

        let mod_ctx = modulus.get_fmpz_mod_ctx_struct();

        let mut res = Vec::with_capacity(other.matrix.len());

        for col in 0..other.get_num_columns() {
            for row in 0..self.get_num_rows() {
                let mut entry = self.mul_entry(other, mod_ctx, row, col, 0);
                for i in 1..self.get_num_columns() {
                    let add_value = self.mul_entry(other, mod_ctx, row, col, i);

                    for j in 0..self.d {
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
            d: self.d,
            nr_rows: self.nr_rows,
            nr_columns: other.nr_columns,
        }
    }

    fn mul_entry(
        &self,
        other: &Self,
        mod_ctx: &fmpz_mod_ctx,
        row: usize,
        col: usize,
        index: usize,
    ) -> Vec<Z> {
        let mut entry = vec![Z::default(); self.d];
        let entry_self = self.get_entry(row, index);
        let entry_other = other.get_entry(index, col);

        for i in 0..self.d {
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

#[cfg(test)]
mod test_mul {
    use crate::{
        integer_mod_q::{
            MatNTTPolynomialRingZq, MatPolynomialRingZq, Modulus, ModulusPolynomialRingZq,
            PolyOverZq,
        },
        traits::SetCoefficient,
    };

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

        let mut ntt_res = ntt1.mul(&ntt2, &Modulus::from(modulus));

        assert_eq!(
            &p1 * &p2,
            MatPolynomialRingZq::from((&mut ntt_res, &polynomial_modulus))
        )
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

        let mut ntt_res = ntt1.mul(&ntt2, &Modulus::from(modulus));

        assert_eq!(
            &p1 * &p2,
            MatPolynomialRingZq::from((&mut ntt_res, &polynomial_modulus))
        )
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

        let mut ntt_res = ntt1.mul(&ntt2, &Modulus::from(modulus));

        assert_eq!(
            &p1 * &p2,
            MatPolynomialRingZq::from((&mut ntt_res, &polynomial_modulus))
        )
    }
}
