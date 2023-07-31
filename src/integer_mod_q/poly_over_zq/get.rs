// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get information about a [`PolyOverZq`] polynomial.

use super::PolyOverZq;
use crate::{
    error::MathError,
    integer::Z,
    integer_mod_q::{Modulus, Zq},
    traits::GetCoefficient,
    utils::index::evaluate_index,
};
use flint_sys::fmpz_mod_poly::{fmpz_mod_poly_degree, fmpz_mod_poly_get_coeff_fmpz};
use std::fmt::Display;

impl GetCoefficient<Zq> for PolyOverZq {
    /// Returns the coefficient of a polynomial [`PolyOverZq`] as a [`Zq`].
    ///
    /// If a index is provided which exceeds the highest set coefficient, `0` is returned.
    ///
    /// Parameters:
    /// - `index`: the index of the coefficient to get (has to be positive)
    ///
    /// Returns the coefficient as a [`Zq`] or a [`MathError`] if the provided index
    /// is negative and therefore invalid or it does not fit into an [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::traits::*;
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use qfall_math::integer_mod_q::Zq;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZq::from_str("4  0 1 2 3 mod 17").unwrap();
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
    /// either the index is negative or it does not fit into an [`i64`].
    fn get_coeff(&self, index: impl TryInto<i64> + Display) -> Result<Zq, MathError> {
        let out_z: Z = self.get_coeff(index)?;
        Ok(Zq::from((out_z, &self.modulus)))
    }
}

impl GetCoefficient<Z> for PolyOverZq {
    /// Returns the coefficient of a polynomial [`PolyOverZq`] as a [`Z`].
    ///
    /// If a index is provided which exceeds the highest set coefficient, `0` is returned.
    ///
    /// Parameters:
    /// - `index`: the index of the coefficient to get (has to be positive)
    ///
    /// Returns the coefficient as a [`Z`] or a [`MathError`] if the provided index
    /// is negative and therefore invalid or it does not fit into an [`i64`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::traits::*;
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZq::from_str("4  0 1 2 3 mod 17").unwrap();
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
    /// either the index is negative or it does not fit into an [`i64`].
    fn get_coeff(&self, index: impl TryInto<i64> + Display) -> Result<Z, MathError> {
        let index = evaluate_index(index)?;
        let mut out = Z::default();
        unsafe {
            fmpz_mod_poly_get_coeff_fmpz(
                &mut out.value,
                &self.poly,
                index,
                self.modulus.get_fmpz_mod_ctx_struct(),
            )
        }
        Ok(out)
    }
}

impl PolyOverZq {
    /// Returns the degree of a polynomial [`PolyOverZq`] as a [`i64`].
    /// The zero polynomial has degree '-1'.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZq::from_str("4  0 1 2 3 mod 7").unwrap();
    ///
    /// let degree = poly.get_degree(); // This would only return 3
    /// ```
    pub fn get_degree(&self) -> i64 {
        unsafe { fmpz_mod_poly_degree(&self.poly, self.modulus.get_fmpz_mod_ctx_struct()) }
    }

    /// Returns the modulus of the polynomial as a [`Modulus`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::PolyOverZq;
    /// use std::str::FromStr;
    ///
    /// let matrix = PolyOverZq::from_str("2  1 3 mod 7").unwrap();
    /// let modulus = matrix.get_mod();
    /// ```
    pub fn get_mod(&self) -> Modulus {
        self.modulus.clone()
    }
}

// we omit the tests for the value of the [`Zq`], and focus on the [`Modulus`] being set correctly
// since get_coefficient for [`Z`] is called, where we will check the value itself
#[cfg(test)]
mod test_get_coeff_zq_modulus {
    use crate::{
        integer_mod_q::{Modulus, PolyOverZq, Zq},
        traits::GetCoefficient,
    };
    use std::str::FromStr;

    /// Ensure that the [`Modulus`] is transferred correctly when accessing an index out of bounds
    #[test]
    fn index_out_of_range_modulus() {
        let modulus_str = format!("17{}", u64::MAX);
        let modulus = Modulus::from_str(&modulus_str).unwrap();

        let poly = PolyOverZq::from_str(&format!("4  0 1 2 3 mod {modulus_str}")).unwrap();

        let zero_coeff: Zq = poly.get_coeff(4).unwrap();

        assert_eq!(modulus, zero_coeff.modulus)
    }

    /// Ensure that the [`Modulus`] is transferred correctly when accessing an index in bounds
    #[test]
    fn index_in_range_modulus() {
        let modulus_str = format!("17{}", u64::MAX);
        let modulus = Modulus::from_str(&modulus_str).unwrap();

        let poly = PolyOverZq::from_str(&format!("4  0 1 2 3 mod {modulus_str}")).unwrap();

        let third_coeff: Zq = poly.get_coeff(3).unwrap();

        assert_eq!(modulus, third_coeff.modulus)
    }
}

#[cfg(test)]
mod test_get_coeff_z {
    use crate::{integer::Z, integer_mod_q::PolyOverZq, traits::GetCoefficient};
    use std::str::FromStr;

    /// Ensure that `0` is returned if the provided index is not yet set
    #[test]
    fn index_out_of_range() {
        let modulus_str = format!("17{}", u64::MAX);

        let poly = PolyOverZq::from_str(&format!("4  0 1 2 3 mod {modulus_str}")).unwrap();

        let zero_coeff = poly.get_coeff(4).unwrap();

        assert_eq!(Z::ZERO, zero_coeff)
    }

    /// Tests if positive coefficients are returned correctly
    #[test]
    fn positive_coeff() {
        let modulus_str = format!("17{}", u64::MAX);

        let poly = PolyOverZq::from_str(&format!("4  0 1 2 3 mod {modulus_str}")).unwrap();

        let coeff = poly.get_coeff(2).unwrap();

        assert_eq!(Z::from(2), coeff)
    }

    /// Tests if large coefficients are returned correctly
    #[test]
    fn large_coeff() {
        let modulus_str = format!("17{}", u64::MAX);
        let large_string = format!("2  {} {} mod {modulus_str}", u64::MAX, i64::MAX);
        let poly = PolyOverZq::from_str(&large_string).unwrap();

        assert_eq!(Z::from(u64::MAX), poly.get_coeff(0).unwrap());
        assert_eq!(Z::from(i64::MAX), poly.get_coeff(1).unwrap());
    }

    /// Tests if large negative coefficients are returned correctly
    #[test]
    fn large_modulus_applied_negative_large_coefficient() {
        let modulus_str = format!("{}", u64::MAX);
        let large_string = format!("2  -{} {} mod {modulus_str}", u64::MAX, i64::MAX);
        let poly = PolyOverZq::from_str(&large_string).unwrap();

        assert_eq!(Z::ZERO, poly.get_coeff(0).unwrap());
        assert_eq!(Z::from(i64::MAX), poly.get_coeff(1).unwrap());
    }
}

#[cfg(test)]
mod test_get_degree {
    use crate::integer_mod_q::PolyOverZq;
    use std::str::FromStr;

    /// Ensure that degree is working
    #[test]
    fn degree() {
        let poly = PolyOverZq::from_str("4  0 1 2 3 mod 7").unwrap();

        let deg = poly.get_degree();

        assert_eq!(3, deg);
    }

    /// Ensure that degree is working for constant polynomials
    #[test]
    fn degree_constant() {
        let poly1 = PolyOverZq::from_str("1  1 mod 19").unwrap();
        let poly2 = PolyOverZq::from_str("0 mod 19").unwrap();

        let deg1 = poly1.get_degree();
        let deg2 = poly2.get_degree();

        assert_eq!(0, deg1);
        assert_eq!(-1, deg2);
    }

    /// Ensure that degree is working for polynomials with leading 0 coefficients
    #[test]
    fn degree_leading_zeros() {
        let poly = PolyOverZq::from_str("4  1 0 0 0 mod 199").unwrap();

        let deg = poly.get_degree();

        assert_eq!(0, deg);
    }

    /// Ensure that degree is working for polynomials with many coefficients
    /// flint does not reduce the exponent due to computational cost
    #[test]
    fn degree_many_coefficients() {
        let poly1 = PolyOverZq::from_str("7  1 2 3 4 8 1 3 mod 2").unwrap();
        let poly2 = PolyOverZq::from_str(&format!(
            "7  1 2 3 4 8 {} {} mod {}",
            u64::MAX,
            i64::MAX,
            u128::MAX
        ))
        .unwrap();

        let deg1 = poly1.get_degree();
        let deg2 = poly2.get_degree();

        assert_eq!(6, deg1);
        assert_eq!(6, deg2);
    }
}

#[cfg(test)]
mod test_mod {
    use crate::integer_mod_q::{Modulus, PolyOverZq};
    use std::str::FromStr;

    /// Ensure that the getter for modulus works correctly.
    #[test]
    fn get_mod() {
        let poly = PolyOverZq::from_str("2  1 2 mod 7").unwrap();

        assert_eq!(poly.get_mod(), Modulus::from(7));
    }

    /// Ensure that the getter for modulus works with large numbers.
    #[test]
    fn get_mod_large() {
        let poly = PolyOverZq::from_str(&format!("2  1 2 mod {}", u64::MAX)).unwrap();

        assert_eq!(poly.get_mod(), Modulus::from(u64::MAX));
    }
}
