// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Div`] trait for [`Z`] values.

use super::super::Z;
use crate::macros::arithmetics::{
    arithmetic_between_types, arithmetic_trait_borrowed_to_owned,
    arithmetic_trait_mixed_borrowed_owned,
};
use crate::rational::Q;
use flint_sys::fmpz::{fmpz_cdiv_q, fmpz_fdiv_q, fmpz_tdiv_qr};
use std::ops::Div;

impl Z {
    /// Divides `self` by `other` and the result is rounded down.
    ///
    /// Parameters:
    /// - `other`: specifies the value to divide `self` by
    ///
    /// Returns the quotient of both numbers as a [`Z`] floored.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let a: Z = Z::from(42);
    /// let b: Z = Z::from(20);
    ///
    /// let c = a.div_floor(&b);
    ///
    /// assert_eq!(Z::from(2), c);
    /// ```
    ///
    /// # Panics ...
    /// - if the divisor is `0`.
    pub fn div_floor(&self, other: &Self) -> Self {
        if other == &Z::ZERO {
            panic!("Tried to divide {} by 0", self);
        }
        let mut out = Z::default();
        unsafe {
            fmpz_fdiv_q(&mut out.value, &self.value, &other.value);
        }
        out
    }

    /// Divides `self` by `other` and the result is rounded up.
    ///
    /// Parameters:
    /// - `other`: specifies the value to divide `self` by
    ///
    /// Returns the quotient of both numbers as a [`Z`] ceiled.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let a: Z = Z::from(42);
    /// let b: Z = Z::from(20);
    ///
    /// let c = a.div_ceil(&b);
    ///
    /// assert_eq!(Z::from(3), c);
    /// ```
    ///
    /// # Panics ...
    /// - if the divisor is `0`.
    pub fn div_ceil(&self, other: &Self) -> Self {
        if other == &Z::ZERO {
            panic!("Tried to divide {} by 0", self);
        }
        let mut out = Z::default();
        unsafe {
            fmpz_cdiv_q(&mut out.value, &self.value, &other.value);
        }
        out
    }

    /// Divides `self` by `other` and returns a result if it is integer.
    ///
    /// Parameters:
    /// - `other`: specifies the value to divide `self` by
    ///
    /// Returns the quotient of both numbers as a [`Z`] or [`None`]
    /// if the quotient is not integer.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let a0: Z = Z::from(40);
    /// let a1: Z = Z::from(42);
    /// let b: Z = Z::from(20);
    ///
    /// let c0 = a0.div_exact(&b).unwrap();
    /// let c1 = a1.div_exact(&b);
    ///
    /// assert_eq!(Z::from(2), c0);
    /// assert!(c1.is_none());
    /// ```
    ///
    /// # Panics ...
    /// - if the divisor is `0`.
    pub fn div_exact(&self, other: &Self) -> Option<Self> {
        if other == &Z::ZERO {
            panic!("Tried to divide {} by 0", self);
        }

        let mut quotient = Z::default();
        let mut reminder = Z::default();
        unsafe {
            fmpz_tdiv_qr(
                &mut quotient.value,
                &mut reminder.value,
                &self.value,
                &other.value,
            );
        }

        if reminder != Z::ZERO {
            None
        } else {
            Some(quotient)
        }
    }
}

impl Div for &Z {
    type Output = Q;
    /// Implements the [`Div`] trait for two [`Z`] values s.t. its value is rounded down.
    /// [`Div`] is implemented for any combination of [`Z`] and borrowed [`Z`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to divide `self` by
    ///
    /// Returns the quotient of both numbers as a [`Z`] floored.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::rational::Q;
    ///
    /// let a = Z::from(42);
    /// let b = Z::from(20);
    ///
    /// let c: Z = &a / &b;
    /// let d: Z = a / b;
    /// let e: Z = &c / d;
    /// let f: Z = c / &e;
    ///
    /// assert_eq!(Q::ONE, e);
    /// assert_eq!(Q::try_from((2, 1)).unwrap(), f);
    /// ```
    ///
    /// # Panics ...
    /// - if the divisor is `0`.
    fn div(self, other: Self) -> Self::Output {
        Q::try_from((self, other)).unwrap()
    }
}

arithmetic_trait_borrowed_to_owned!(Div, div, Z, Z, Q);
arithmetic_trait_mixed_borrowed_owned!(Div, div, Z, Z, Q);
arithmetic_between_types!(Div, div, Z, Q, i64 i32 i16 i8 u64 u32 u16 u8);

#[cfg(test)]
mod test_div_floor {
    use super::Z;

    /// Checks whether `div_floor` correctly rounds non-exact quotients down
    #[test]
    fn floored() {
        let small = Z::from(-11);
        let large = Z::from(i32::MAX);
        let divisor = Z::from(2);

        let res_0 = small.div_floor(&divisor);
        let res_1 = large.div_floor(&divisor);

        assert_eq!(Z::from(-6), res_0);
        assert_eq!(Z::from(i32::MAX >> 1), res_1);
    }

    /// Checks whether `div_floor` correctly computes exact quotients
    #[test]
    fn exact() {
        let small = Z::from(10);
        let large = Z::from(i32::MIN);
        let divisor = Z::from(2);

        let res_0 = small.div_floor(&divisor);
        let res_1 = large.div_floor(&divisor);

        assert_eq!(Z::from(5), res_0);
        assert_eq!(Z::from(i32::MIN >> 1), res_1);
    }

    /// Checks whether `div_floor` panics if the divisor is `0`
    #[test]
    #[should_panic]
    fn division_by_zero() {
        let a = Z::from(100);

        let _ = a.div_floor(&Z::ZERO);
    }
}

#[cfg(test)]
mod test_div_ceil {
    use super::Z;

    /// Checks whether `div_ceil` correctly rounds non-exact quotients down
    #[test]
    fn ceiled() {
        let small = Z::from(-11);
        let large = Z::from(i32::MAX);
        let divisor = Z::from(2);

        let res_0 = small.div_ceil(&divisor);
        let res_1 = large.div_ceil(&divisor);

        assert_eq!(Z::from(-5), res_0);
        assert_eq!(Z::from((i32::MAX >> 1) + 1), res_1);
    }

    /// Checks whether `div_ceil` correctly computes exact quotients
    #[test]
    fn exact() {
        let small = Z::from(10);
        let large = Z::from(i32::MIN);
        let divisor = Z::from(2);

        let res_0 = small.div_ceil(&divisor);
        let res_1 = large.div_ceil(&divisor);

        assert_eq!(Z::from(5), res_0);
        assert_eq!(Z::from(i32::MIN >> 1), res_1);
    }

    /// Checks whether `div_ceil` panics if the divisor is `0`
    #[test]
    #[should_panic]
    fn division_by_zero() {
        let a = Z::from(100);

        let _ = a.div_ceil(&Z::ZERO);
    }
}

#[cfg(test)]
mod test_div_exact {
    use super::Z;

    /// Checks whether `div_exact` outputs [`None`] if the quotient is not integer
    #[test]
    fn non_exact() {
        let small = Z::from(-11);
        let large = Z::from(i32::MAX);
        let divisor = Z::from(2);

        let res_0 = small.div_exact(&divisor);
        let res_1 = large.div_exact(&divisor);

        assert!(res_0.is_none());
        assert!(res_1.is_none());
    }

    /// Checks whether `div_exact` correctly computes exact quotients
    #[test]
    fn exact() {
        let small = Z::from(10);
        let large = Z::from(i32::MIN);
        let divisor = Z::from(2);

        let res_0 = small.div_exact(&divisor).unwrap();
        let res_1 = large.div_exact(&divisor).unwrap();

        assert_eq!(Z::from(5), res_0);
        assert_eq!(Z::from(i32::MIN >> 1), res_1);
    }

    /// Checks whether `div_exact` panics if the divisor is `0`
    #[test]
    #[should_panic]
    fn division_by_zero() {
        let a = Z::from(100);

        let _ = a.div_exact(&Z::ZERO);
    }
}

#[cfg(test)]
mod test_div_between_types {

    use crate::integer::Z;

    /// testing division between different types
    #[test]
    #[allow(clippy::op_ref)]
    fn div() {
        let a: Z = Z::from(42);
        let b: u64 = 5;
        let c: u32 = 5;
        let d: u16 = 5;
        let e: u8 = 5;
        let f: i64 = 5;
        let g: i32 = 5;
        let h: i16 = 5;
        let i: i8 = 5;
        let _: Z = &a / &b;
        let _: Z = &a / &c;
        let _: Z = &a / &d;
        let _: Z = &a / &e;
        let _: Z = &a / &f;
        let _: Z = &a / &g;
        let _: Z = &a / &h;
        let _: Z = &a / &i;

        let _: Z = &b / &a;
        let _: Z = &c / &a;
        let _: Z = &d / &a;
        let _: Z = &e / &a;
        let _: Z = &f / &a;
        let _: Z = &g / &a;
        let _: Z = &h / &a;
        let _: Z = &i / &a;

        let _: Z = &a / b;
        let _: Z = &a / c;
        let _: Z = &a / d;
        let _: Z = &a / e;
        let _: Z = &a / f;
        let _: Z = &a / g;
        let _: Z = &a / h;
        let _: Z = &a / i;

        let _: Z = &b / Z::from(42);
        let _: Z = &c / Z::from(42);
        let _: Z = &d / Z::from(42);
        let _: Z = &e / Z::from(42);
        let _: Z = &f / Z::from(42);
        let _: Z = &g / Z::from(42);
        let _: Z = &h / Z::from(42);
        let _: Z = &i / Z::from(42);

        let _: Z = Z::from(42) / &b;
        let _: Z = Z::from(42) / &c;
        let _: Z = Z::from(42) / &d;
        let _: Z = Z::from(42) / &e;
        let _: Z = Z::from(42) / &f;
        let _: Z = Z::from(42) / &g;
        let _: Z = Z::from(42) / &h;
        let _: Z = Z::from(42) / &i;

        let _: Z = b / &a;
        let _: Z = c / &a;
        let _: Z = d / &a;
        let _: Z = e / &a;
        let _: Z = f / &a;
        let _: Z = g / &a;
        let _: Z = h / &a;
        let _: Z = i / &a;

        let _: Z = Z::from(42) / b;
        let _: Z = Z::from(42) / c;
        let _: Z = Z::from(42) / d;
        let _: Z = Z::from(42) / e;
        let _: Z = Z::from(42) / f;
        let _: Z = Z::from(42) / g;
        let _: Z = Z::from(42) / h;
        let _: Z = Z::from(42) / i;

        let _: Z = b / Z::from(42);
        let _: Z = c / Z::from(42);
        let _: Z = d / Z::from(42);
        let _: Z = e / Z::from(42);
        let _: Z = f / Z::from(42);
        let _: Z = g / Z::from(42);
        let _: Z = h / Z::from(42);
        let _: Z = i / Z::from(42);
    }
}

#[cfg(test)]
mod test_div {

    use super::Z;
    use crate::traits::Pow;

    /// testing division for two [`Z`]
    #[test]
    fn div() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Z = a / b;
        assert_eq!(c, Z::from(10));
    }

    /// testing division for two borrowed [`Z`]
    #[test]
    fn div_borrow() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Z = &a / &b;
        assert_eq!(c, Z::from(10));
    }

    /// testing division for borrowed [`Z`] and [`Z`]
    #[test]
    fn div_first_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Z = &a / b;
        assert_eq!(c, Z::from(10));
    }

    /// testing division for [`Z`] and borrowed [`Z`]
    #[test]
    fn div_second_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Z = a / &b;
        assert_eq!(c, Z::from(10));
    }

    /// testing division for big [`Z`]
    #[test]
    fn div_large_numbers() {
        let a: Z = Z::from(i64::MAX as u64 + 1);
        let b: Z = Z::from(2);
        let c: Z = Z::from(i32::MIN);
        let d: Z = Z::from(i32::MAX as u32 + 1);
        let e: Z = a / b;
        let f: Z = c / d;
        assert_eq!(e, Z::from(2).pow(62).unwrap());
        assert_eq!(f, Z::MINUS_ONE);
    }
}
