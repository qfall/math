// Copyright © 2023 Marcel Luca Schmidt, Marvin Beckmann, Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get information about a [`ModulusPolynomialRingZq].

use crate::{
    error::MathError,
    integer::Z,
    integer_mod_q::{Modulus, ModulusPolynomialRingZq, Zq},
    traits::GetCoefficient,
    utils::index::evaluate_index,
};
use flint_sys::{
    fmpz::fmpz_set,
    fmpz_mod::fmpz_mod_ctx_init,
    fmpz_mod_poly::fmpz_mod_poly_get_coeff_fmpz,
    fq::{fq_ctx_degree, fq_ctx_struct},
};
use std::{fmt::Display, mem::MaybeUninit, rc::Rc};

impl GetCoefficient<Zq> for ModulusPolynomialRingZq {
    /// Returns the coefficient of a polynomial [`ModulusPolynomialRingZq`] as a [`Zq`].
    ///
    /// If an index is provided which exceeds the highest set coefficient, `0` is returned.
    ///
    /// Parameters:
    /// - `index`: the index of the coefficient to get (has to be positive)
    ///
    /// Returns the coefficient as a [`Zq`], or a [`MathError`] if the provided index
    /// is negative and therefore invalid, or it does not fit into an [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::traits::*;
    /// use qfall_math::integer_mod_q::{Zq, ModulusPolynomialRingZq};
    /// use std::str::FromStr;
    ///
    /// let poly = ModulusPolynomialRingZq::from_str("4  0 1 2 3 mod 17").unwrap();
    ///
    /// let coeff_0: Zq = poly.get_coeff(0).unwrap();
    /// let coeff_1: Zq = poly.get_coeff(1).unwrap();
    /// let coeff_4: Zq = poly.get_coeff(4).unwrap();
    ///
    /// assert_eq!(Zq::from((0, 17)), coeff_0);
    /// assert_eq!(Zq::from((1, 17)), coeff_1);
    /// assert_eq!(Zq::from((0, 17)), coeff_4);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
    ///     either the index is negative or it does not fit into an [`i64`].
    fn get_coeff(&self, index: impl TryInto<i64> + Display) -> Result<Zq, MathError> {
        let index = evaluate_index(index)?;
        let mut out_z = Z::default();
        let mut ctx = MaybeUninit::uninit();

        unsafe {
            fmpz_mod_poly_get_coeff_fmpz(
                &mut out_z.value,
                &self.modulus.modulus[0],
                index,
                &self.get_fq_ctx_struct().ctxp[0],
            );

            fmpz_mod_ctx_init(ctx.as_mut_ptr(), &self.get_fq_ctx_struct().ctxp[0].n[0]);

            let modulus = Modulus {
                modulus: Rc::new(ctx.assume_init()),
            };

            Ok(Zq::from((out_z, modulus)))
        }
    }
}

impl GetCoefficient<Z> for ModulusPolynomialRingZq {
    /// Returns the coefficient of a polynomial [`ModulusPolynomialRingZq`] as a [`Z`].
    ///
    /// If an index is provided which exceeds the highest set coefficient, `0` is returned.
    ///
    /// Parameters:
    /// - `index`: the index of the coefficient to get (has to be positive)
    ///
    /// Returns the coefficient as a [`Z`], or a [`MathError`] if the provided index
    /// is negative and therefore invalid, or it does not fit into an [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::traits::*;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let poly = ModulusPolynomialRingZq::from_str("4  0 1 2 3 mod 17").unwrap();
    ///
    /// let coeff_0: Z = poly.get_coeff(0).unwrap();
    /// let coeff_1: Z = poly.get_coeff(1).unwrap();
    /// let coeff_4: Z = poly.get_coeff(4).unwrap();
    ///
    /// assert_eq!(Z::ZERO, coeff_0);
    /// assert_eq!(Z::ONE, coeff_1);
    /// assert_eq!(Z::ZERO, coeff_4);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
    ///     either the index is negative or it does not fit into an [`i64`].
    fn get_coeff(&self, index: impl TryInto<i64> + Display) -> Result<Z, MathError> {
        let index = evaluate_index(index)?;
        let mut out = Z::default();

        unsafe {
            fmpz_mod_poly_get_coeff_fmpz(
                &mut out.value,
                &self.modulus.modulus[0],
                index,
                &self.get_fq_ctx_struct().ctxp[0],
            )
        }

        Ok(out)
    }
}

impl ModulusPolynomialRingZq {
    /// Returns the [`fq_ctx_struct`] of a modulus and is only used internally.
    pub(crate) fn get_fq_ctx_struct(&self) -> &fq_ctx_struct {
        self.modulus.as_ref()
    }

    /// Returns the context integer as a [`Z`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let modulus_ring = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    ///
    /// let modulus = modulus_ring.get_q();
    ///
    /// let cmp_modulus = Z::from(17);
    /// assert_eq!(cmp_modulus, modulus);
    /// ```
    pub fn get_q(&self) -> Z {
        let mut out = Z::default();
        unsafe {
            fmpz_set(&mut out.value, &self.get_fq_ctx_struct().ctxp[0].n[0]);
        }
        out
    }

    /// Returns the degree of a polynomial [`ModulusPolynomialRingZq`] as a [`i64`].
    /// The zero polynomial has degree `-1`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let poly = ModulusPolynomialRingZq::from_str("4  0 1 2 3 mod 7").unwrap();
    ///
    /// let degree = poly.get_degree(); // This would only return 3
    /// ```
    pub fn get_degree(&self) -> i64 {
        unsafe { fq_ctx_degree(self.get_fq_ctx_struct()) }
    }
}

#[cfg(test)]
mod test_get_coeff_z {
    use crate::{
        integer::Z,
        integer_mod_q::{ModulusPolynomialRingZq, Zq},
        traits::GetCoefficient,
    };
    use std::str::FromStr;

    /// Ensure that `0` is returned if the provided index is not yet set.
    #[test]
    fn index_out_of_range() {
        let poly = ModulusPolynomialRingZq::from_str("4  0 1 2 3 mod 17").unwrap();

        let zero_coeff_1 = poly.get_coeff(4).unwrap();
        let zero_coeff_2 = poly.get_coeff(4).unwrap();

        assert_eq!(Z::ZERO, zero_coeff_1);
        assert_eq!(Zq::from((0, 17)), zero_coeff_2);
    }

    /// Tests if coefficients are returned correctly.
    #[test]
    fn positive_coeff() {
        let poly = ModulusPolynomialRingZq::from_str("4  0 1 2 3 mod 17").unwrap();

        let coeff_1 = poly.get_coeff(2).unwrap();
        let coeff_2 = poly.get_coeff(2).unwrap();

        assert_eq!(Z::from(2), coeff_1);
        assert_eq!(Zq::from((2, 17)), coeff_2);
    }

    /// Tests if large coefficients are returned correctly.
    #[test]
    fn large_coeff() {
        let poly =
            ModulusPolynomialRingZq::from_str(&format!("2  1 {} mod {}", u64::MAX - 1, u64::MAX))
                .unwrap();

        assert_eq!(Z::from(u64::MAX - 1), poly.get_coeff(1).unwrap());
        assert_eq!(
            Zq::from((u64::MAX - 1, u64::MAX)),
            poly.get_coeff(1).unwrap()
        );
    }

    /// Tests if negative index yields an error in get_coeff with [`Z`].
    #[test]
    #[should_panic]
    fn negative_index_error_z() {
        let poly = ModulusPolynomialRingZq::from_str("4  0 1 2 3 mod 17").unwrap();

        let _: Z = poly.get_coeff(-1).unwrap();
    }

    /// Tests if negative index yields an error in get_coeff with [`Zq`].
    #[test]
    #[should_panic]
    fn negative_index_error_zq() {
        let poly = ModulusPolynomialRingZq::from_str("4  0 1 2 3 mod 17").unwrap();

        let _: Zq = poly.get_coeff(-1).unwrap();
    }
}

#[cfg(test)]
mod test_get_degree {
    use crate::integer_mod_q::ModulusPolynomialRingZq;
    use std::str::FromStr;

    /// Ensures that degree is working for constant polynomials.
    #[test]
    fn degree_constant() {
        let degrees = [0, 1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let modulus_ring = ModulusPolynomialRingZq::from_str(&format!(
                "{}  {}1 mod 17",
                degree + 1,
                "0 ".repeat(degree)
            ))
            .unwrap();

            assert_eq!(degree as i64, modulus_ring.get_degree());
        }
    }

    /// Ensure that degree is working for polynomials with leading 0 coefficients.
    #[test]
    fn degree_leading_zeros() {
        let poly = ModulusPolynomialRingZq::from_str("4  1 0 0 0 mod 199").unwrap();

        let deg = poly.get_degree();

        assert_eq!(0, deg);
    }

    /// Ensure that degree is working for polynomials with many coefficients
    /// flint does not reduce the exponent due to computational cost.
    #[test]
    fn degree_many_coefficients() {
        let poly_1 = ModulusPolynomialRingZq::from_str("7  1 2 3 4 8 1 3 mod 2").unwrap();
        let poly_2 = ModulusPolynomialRingZq::from_str(&format!(
            "7  1 2 3 4 8 {} {} mod {}",
            u64::MAX,
            i64::MAX,
            u128::MAX
        ))
        .unwrap();

        let deg_1 = poly_1.get_degree();
        let deg_2 = poly_2.get_degree();

        assert_eq!(6, deg_1);
        assert_eq!(6, deg_2);
    }
}

#[cfg(test)]
mod test_get_q {
    use crate::{integer::Z, integer_mod_q::ModulusPolynomialRingZq};
    use std::str::FromStr;

    /// Ensure that the same modulus is correctly returned for a large modulus.
    #[test]
    fn correct_large() {
        let large_prime = u64::MAX - 58;
        let modulus_ring =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {large_prime}")).unwrap();

        let modulus = modulus_ring.get_q();

        let cmp_modulus = Z::from(large_prime);
        assert_eq!(cmp_modulus, modulus);
    }
}
