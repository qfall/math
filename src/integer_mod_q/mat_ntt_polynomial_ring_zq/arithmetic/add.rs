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
    integer_mod_q::{MatNTTPolynomialRingZq, Modulus},
};
use flint_sys::fmpz_mod::fmpz_mod_add_fmpz;

impl MatNTTPolynomialRingZq {
    /// Adds `self` with `other`.
    ///
    /// Paramters:
    /// - `other`: specifies the NTT-representation of the polynomial to add to `self`
    /// - `modulus`: defines the modulus `q`
    ///
    /// Returns the NTT-representation of the sum of `self` and `other` generated
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
    /// let mut a = MatNTTPolynomialRingZq::sample_uniform(2, 3, n, &q);
    /// let b = MatNTTPolynomialRingZq::sample_uniform(2, 3, n, &q);
    ///
    /// let c = a.add(&b, &q);
    /// ```
    ///
    /// # Panics ...
    /// - if the `modulus` is smaller than `2`.
    /// - if the number of rows of `self` and `other` or their number of columns is not equal.
    /// - if the degree of the matrices is not equal.
    pub fn add(&self, other: &Self, modulus: &Modulus) -> MatNTTPolynomialRingZq {
        assert_eq!(
            self.nr_rows, other.nr_rows,
            "The number of rows of `self` and `other` has to be equal for matrix addition."
        );
        assert_eq!(
            self.nr_columns, other.nr_columns,
            "The number of columns of `self` and `other` has to be equal for matrix addition."
        );
        assert_eq!(
            self.d, other.d,
            "The degree of both matrices' modulus has to be equal for multiplication."
        );
        let mod_ctx = modulus.get_fmpz_mod_ctx_struct();

        let mut out = MatNTTPolynomialRingZq {
            matrix: vec![Z::default(); self.d * self.nr_rows * self.nr_columns],
            d: self.d,
            nr_rows: self.nr_rows,
            nr_columns: self.nr_columns,
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

    /// Adds `self` with `other` reusing the memory of `self`.
    ///
    /// Paramters:
    /// - `other`: specifies the NTT-representation of the polynomial to add to `self`
    /// - `modulus`: defines the modulus `q`
    ///
    /// Computes the NTT-representation of the sum of `self` and `other` generated
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
    /// let mut a = MatNTTPolynomialRingZq::sample_uniform(2, 3, n, &q);
    /// let b = MatNTTPolynomialRingZq::sample_uniform(2, 3, n, &q);
    ///
    /// a.add_assign(&b, &q);
    /// ```
    ///
    /// # Panics ...
    /// - if the `modulus` is smaller than `2`.
    /// - if the number of rows of `self` and `other` or their number of columns is not equal.
    /// - if the degree of the matrices is not equal.
    pub fn add_assign(&mut self, other: &Self, modulus: &Modulus) {
        assert_eq!(
            self.nr_rows, other.nr_rows,
            "The number of rows of `self` and `other` has to be equal for matrix addition."
        );
        assert_eq!(
            self.nr_columns, other.nr_columns,
            "The number of columns of `self` and `other` has to be equal for matrix addition."
        );
        assert_eq!(
            self.d, other.d,
            "The degree of both matrices' modulus has to be equal for multiplication."
        );
        let mod_ctx = modulus.get_fmpz_mod_ctx_struct();

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

#[cfg(test)]
mod test_add {
    use crate::{
        integer_mod_q::{
            MatNTTPolynomialRingZq, MatPolynomialRingZq, Modulus, ModulusPolynomialRingZq,
            PolyOverZq,
        },
        traits::SetCoefficient,
    };

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

        let mut res = ntt1.add(&ntt2, &Modulus::from(modulus));

        assert_eq!(
            &p1 + &p2,
            MatPolynomialRingZq::from((&mut res, &polynomial_modulus))
        )
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

        let mut res = ntt1.add(&ntt2, &Modulus::from(modulus));

        assert_eq!(
            &p1 + &p2,
            MatPolynomialRingZq::from((&mut res, &polynomial_modulus))
        )
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

        let mut res = ntt1.add(&ntt2, &Modulus::from(modulus));

        assert_eq!(
            &p1 + &p2,
            MatPolynomialRingZq::from((&mut res, &polynomial_modulus))
        )
    }
}

#[cfg(test)]
mod test_add_assign {
    use crate::{
        integer_mod_q::{
            MatNTTPolynomialRingZq, MatPolynomialRingZq, Modulus, ModulusPolynomialRingZq,
            PolyOverZq,
        },
        traits::SetCoefficient,
    };

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

        ntt1.add_assign(&ntt2, &Modulus::from(modulus));

        assert_eq!(
            &p1 + &p2,
            MatPolynomialRingZq::from((&mut ntt1, &polynomial_modulus))
        )
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

        ntt1.add_assign(&ntt2, &Modulus::from(modulus));

        assert_eq!(
            &p1 + &p2,
            MatPolynomialRingZq::from((&mut ntt1, &polynomial_modulus))
        )
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

        ntt1.add_assign(&ntt2, &Modulus::from(modulus));

        assert_eq!(
            &p1 + &p2,
            MatPolynomialRingZq::from((&mut ntt1, &polynomial_modulus))
        )
    }
}
