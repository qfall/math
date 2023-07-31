// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations for a [`Factorization`] of [`Z`] values.

use super::Factorization;
use crate::{integer::Z, traits::AsInteger};
use flint_sys::fmpz_factor::{_fmpz_factor_append, fmpz_factor_get_fmpz};

impl<Integer: AsInteger + Into<Z>> From<Integer> for Factorization {
    /// Convert an integer into a [`Factorization`].
    ///
    /// Parameters:
    /// - `factor`: the integer we want as a [`Factorization`] object.
    ///
    /// Returns a new [`Factorization`] with `factor` as the only factor.
    ///
    /// # Examples:
    /// ```
    /// use qfall_math::utils::Factorization;
    ///
    /// let fac = Factorization::from(10);
    /// ```
    fn from(factor: Integer) -> Self {
        let factor = factor.into();
        let mut out = Self::default();
        unsafe { _fmpz_factor_append(&mut out.factors, &factor.value, 1) };
        out
    }
}

impl<Integer: AsInteger + Into<Z>> From<(Integer, Integer)> for Factorization {
    /// Convert two integers into a [`Factorization`].
    ///
    /// Note that the order of the factors is not altered by this method.
    ///
    /// Parameters:
    /// - `factors`: a tuple with two integers we want in the [`Factorization`] object.
    ///
    /// Returns a new [`Factorization`] with `factor` as the only factor.
    ///
    /// # Examples:
    /// ```
    /// use qfall_math::utils::Factorization;
    ///
    /// let fac = Factorization::from((10, 5));
    /// ```
    fn from(factors: (Integer, Integer)) -> Self {
        let factor_1 = factors.0.into();
        let factor_2 = factors.1.into();
        let mut out = Self::default();
        unsafe { _fmpz_factor_append(&mut out.factors, &factor_1.value, 1) };
        unsafe { _fmpz_factor_append(&mut out.factors, &factor_2.value, 1) };
        out
    }
}

impl From<&Factorization> for Vec<(Z, u64)> {
    /// Convert a [`Factorization`] into a [`Vec<(Z, u64)>`].
    ///
    /// Parameters:
    /// - `factors`: the [`Factorization`] we want as a [`Vec<(Z, u64)>`] object.
    ///
    /// Returns a new [`Vec<(Z, u64)>`] with the factors from [`Factorization`]
    /// represented as tuples with bases as [`Z`] and exponents as [`u64`] values.
    ///
    /// # Examples:
    /// ```
    /// use qfall_math::utils::Factorization;
    ///
    /// let fac = Factorization::from(10);
    ///
    /// let vec = Vec::<(Z, u64)>::from(&fac);
    /// ```
    fn from(factors: &Factorization) -> Self {
        let mut out = Vec::new();

        if factors.factors.sign == -1 {
            out.push((Z::MINUS_ONE, 1));
        }

        for i in 0..factors.factors.num {
            let mut factor = Z::default();
            unsafe { fmpz_factor_get_fmpz(&mut factor.value, &factors.factors, i) };

            let exp = unsafe { *factors.factors.exp.offset(i.try_into().unwrap()) };
            out.push((factor, exp));
        }

        if out.is_empty() && factors.factors.sign == 1 {
            out.push((Z::ONE, 1));
        }
        out
    }
}

#[cfg(test)]
mod tests_from_one {
    use crate::utils::Factorization;

    /// Ensure that a [`Factorization`] is correctly created from one value.
    #[test]
    fn from_one() {
        let fac = Factorization::from(8);

        assert_eq!("[(8, 1)]", fac.to_string());
    }

    /// Ensure that a [`Factorization`] is correctly created from a big value.
    #[test]
    fn from_one_big() {
        let fac = Factorization::from(i64::MAX);

        assert_eq!(format!("[({}, 1)]", i64::MAX), fac.to_string());
    }

    /// Ensure that a [`Factorization`] is correctly created from a negative value.
    #[test]
    fn from_one_negative() {
        let fac = Factorization::from(-8);

        assert_eq!("[(-8, 1)]", fac.to_string());
    }
}

#[cfg(test)]
mod tests_from_two {
    use crate::utils::Factorization;

    /// Ensure that a [`Factorization`] is correctly created from two values
    /// and the order is correct.
    #[test]
    fn from_two() {
        let fac = Factorization::from((8, 3));

        assert_eq!("[(8, 1), (3, 1)]", fac.to_string());
    }

    /// Ensure that a [`Factorization`] is correctly created from big values.
    #[test]
    fn from_two_big() {
        let fac = Factorization::from((i64::MAX, 3));

        assert_eq!(format!("[({}, 1), (3, 1)]", i64::MAX), fac.to_string());
    }

    /// Ensure that a [`Factorization`] is correctly created from two negative values.
    #[test]
    fn from_two_negative() {
        let fac = Factorization::from((-8, -3));

        assert_eq!("[(-8, 1), (-3, 1)]", fac.to_string());
    }

    /// Ensure that a [`Factorization`] is not refined in from.
    #[test]
    fn from_two_unrefined() {
        let fac = Factorization::from((8, 8));

        assert_eq!("[(8, 1), (8, 1)]", fac.to_string());
    }
}

#[cfg(test)]
mod tests_from_fac {
    use crate::{integer::Z, utils::Factorization};

    /// Ensure that a [`Vec`] is correctly created from a [`Factorization`].
    #[test]
    fn from_fac() {
        let fac = Factorization::from((4, 3));
        let vec = Vec::<(Z, u64)>::from(&fac);

        assert_eq!(Z::from(4), vec[0].0);
        assert_eq!(Z::from(3), vec[1].0);

        assert_eq!(1, vec[0].1);
        assert_eq!(1, vec[1].1);
    }

    /// Ensure that a [`Vec`] is correctly created from a [`Factorization`]
    /// with big values.
    #[test]
    fn from_fac_big() {
        let fac = Factorization::from((i64::MAX, 3));
        let vec = Vec::<(Z, u64)>::from(&fac);

        assert_eq!(Z::from(i64::MAX), vec[0].0);
        assert_eq!(Z::from(3), vec[1].0);

        assert_eq!(1, vec[0].1);
        assert_eq!(1, vec[1].1);
    }

    /// Ensure that a [`Vec`] is correctly created from a [`Factorization`]
    /// with negative values.
    #[test]
    fn from_fac_negative() {
        let fac = Factorization::from((-i64::MAX, 3));
        let vec = Vec::<(Z, u64)>::from(&fac);

        assert_eq!(Z::from(-i64::MAX), vec[0].0);
        assert_eq!(Z::from(3), vec[1].0);

        assert_eq!(1, vec[0].1);
        assert_eq!(1, vec[1].1);
    }

    /// Ensure that a [`Vec`] is correctly created from a [`Factorization`].
    #[test]
    fn from_fac_one_entry() {
        let fac = Factorization::from(4);
        let vec = Vec::<(Z, u64)>::from(&fac);

        assert_eq!(Z::from(4), vec[0].0);

        assert_eq!(1, vec[0].1);
    }

    /// Ensure that a [`Vec`] is correctly created from a refined [`Factorization`].
    #[test]
    fn from_fac_refined() {
        let mut fac = Factorization::from((-1200, 20));
        fac.refine();

        let vec = Vec::<(Z, u64)>::from(&fac);

        assert_eq!(Z::MINUS_ONE, vec[0].0);
        assert_eq!(Z::from(3), vec[1].0);
        assert_eq!(Z::from(20), vec[2].0);

        assert_eq!(1, vec[0].1);
        assert_eq!(1, vec[1].1);
        assert_eq!(3, vec[2].1);
    }

    /// Ensure that a [`Vec`] is correctly created from a refined [`Factorization`].
    #[test]
    fn from_fac_one() {
        let mut fac = Factorization::from(1);
        fac.refine();

        let vec = Vec::<(Z, u64)>::from(&fac);

        assert_eq!(Z::ONE, vec[0].0);
        assert_eq!(1, vec[0].1);
    }

    /// Ensure that a [`Vec`] is correctly created from a refined [`Factorization`].
    #[test]
    fn from_fac_minus_one() {
        let mut fac = Factorization::from(-1);
        fac.refine();

        let vec = Vec::<(Z, u64)>::from(&fac);

        assert_eq!(Z::MINUS_ONE, vec[0].0);
        assert_eq!(1, vec[0].1);
    }

    /// Ensure that the doc test works.
    #[test]
    fn doc_test() {
        let fac = Factorization::from(10);
        let _vec = Vec::<(Z, u64)>::from(&fac);
    }
}
