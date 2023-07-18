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
        assert!(!other.is_zero(), "Tried to divide {self} by zero.");
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
        assert!(!other.is_zero(), "Tried to divide {self} by zero.");
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
        assert!(!other.is_zero(), "Tried to divide {self} by zero.");

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
    /// let c: Q = &a / &b;
    /// let d: Q = a / b;
    ///
    /// assert_eq!(Q::from((21, 10)), c);
    /// assert_eq!(Q::from((21, 10)), d);
    /// ```
    ///
    /// # Panics ...
    /// - if the divisor is `0`.
    fn div(self, other: Self) -> Self::Output {
        Q::from((self, other))
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
        let large = Z::from(i64::MAX);
        let divisor = Z::from(2);

        let res_0 = small.div_floor(&divisor);
        let res_1 = large.div_floor(&divisor);

        assert_eq!(Z::from(-6), res_0);
        assert_eq!(Z::from(i64::MAX >> 1), res_1);
    }

    /// Checks whether `div_floor` correctly computes exact quotients
    #[test]
    fn exact() {
        let small = Z::from(10);
        let large = Z::from(i64::MIN);
        let divisor = Z::from(2);

        let res_0 = Z::ZERO.div_floor(&divisor);
        let res_1 = small.div_floor(&divisor);
        let res_2 = large.div_floor(&divisor);

        assert_eq!(Z::ZERO, res_0);
        assert_eq!(Z::from(5), res_1);
        assert_eq!(Z::from(i64::MIN >> 1), res_2);
    }

    /// Checks whether `div_floor` panics if the divisor is `0`
    #[test]
    #[should_panic]
    fn division_by_zero() {
        let a = Z::from(100);

        let _ = a.div_floor(&Z::ZERO);
    }
}

impl Div<&Q> for &Z {
    type Output = Q;

    /// Implements the [`Div`] trait for [`Z`] and [`Q`] values.
    /// [`Div`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    ///  - `other`: specifies the value to divide `self` by
    ///
    /// Returns the ratio of both numbers as a [`Q`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let a: Z = Z::from(-42);
    /// let b: Q = Q::from((42, 19));
    ///
    /// let c: Q = &a / &b;
    /// let d: Q = a / b;
    /// let e: Q = &Z::from(42) / d;
    /// let f: Q = Z::from(42) / &e;
    /// ```
    ///
    /// # Panics ...
    /// - if the divisor is `0`.
    fn div(self, other: &Q) -> Self::Output {
        assert!(!other.is_zero(), "Tried to divide {self} by zero.");
        Q::from(self.clone()) / other
    }
}

arithmetic_trait_borrowed_to_owned!(Div, div, Z, Q, Q);
arithmetic_trait_mixed_borrowed_owned!(Div, div, Z, Q, Q);

#[cfg(test)]
mod test_div_ceil {
    use super::Z;

    /// Checks whether `div_ceil` correctly rounds non-exact quotients down
    #[test]
    fn ceiled() {
        let small = Z::from(-11);
        let large = Z::from(i64::MAX);
        let divisor = Z::from(2);

        let res_0 = small.div_ceil(&divisor);
        let res_1 = large.div_ceil(&divisor);

        assert_eq!(Z::from(-5), res_0);
        assert_eq!(Z::from((i64::MAX >> 1) + 1), res_1);
    }

    /// Checks whether `div_ceil` correctly computes exact quotients
    #[test]
    fn exact() {
        let small = Z::from(10);
        let large = Z::from(i64::MIN);
        let divisor = Z::from(2);

        let res_0 = Z::ZERO.div_ceil(&divisor);
        let res_1 = small.div_ceil(&divisor);
        let res_2 = large.div_ceil(&divisor);

        assert_eq!(Z::ZERO, res_0);
        assert_eq!(Z::from(5), res_1);
        assert_eq!(Z::from(i64::MIN >> 1), res_2);
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
        let large = Z::from(i64::MAX);
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
        let large = Z::from(i64::MIN);
        let divisor = Z::from(2);

        let res_0 = Z::ZERO.div_exact(&divisor).unwrap();
        let res_1 = small.div_exact(&divisor).unwrap();
        let res_2 = large.div_exact(&divisor).unwrap();

        assert_eq!(Z::ZERO, res_0);
        assert_eq!(Z::from(5), res_1);
        assert_eq!(Z::from(i64::MIN >> 1), res_2);
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
    use crate::rational::Q;

    /// Testing division between different types
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

        let _: Q = &a / &b;
        let _: Q = &a / &c;
        let _: Q = &a / &d;
        let _: Q = &a / &e;
        let _: Q = &a / &f;
        let _: Q = &a / &g;
        let _: Q = &a / &h;
        let _: Q = &a / &i;

        let _: Q = &b / &a;
        let _: Q = &c / &a;
        let _: Q = &d / &a;
        let _: Q = &e / &a;
        let _: Q = &f / &a;
        let _: Q = &g / &a;
        let _: Q = &h / &a;
        let _: Q = &i / &a;

        let _: Q = &a / b;
        let _: Q = &a / c;
        let _: Q = &a / d;
        let _: Q = &a / e;
        let _: Q = &a / f;
        let _: Q = &a / g;
        let _: Q = &a / h;
        let _: Q = &a / i;

        let _: Q = &b / Z::from(42);
        let _: Q = &c / Z::from(42);
        let _: Q = &d / Z::from(42);
        let _: Q = &e / Z::from(42);
        let _: Q = &f / Z::from(42);
        let _: Q = &g / Z::from(42);
        let _: Q = &h / Z::from(42);
        let _: Q = &i / Z::from(42);

        let _: Q = Z::from(42) / &b;
        let _: Q = Z::from(42) / &c;
        let _: Q = Z::from(42) / &d;
        let _: Q = Z::from(42) / &e;
        let _: Q = Z::from(42) / &f;
        let _: Q = Z::from(42) / &g;
        let _: Q = Z::from(42) / &h;
        let _: Q = Z::from(42) / &i;

        let _: Q = b / &a;
        let _: Q = c / &a;
        let _: Q = d / &a;
        let _: Q = e / &a;
        let _: Q = f / &a;
        let _: Q = g / &a;
        let _: Q = h / &a;
        let _: Q = i / &a;

        let _: Q = Z::from(42) / b;
        let _: Q = Z::from(42) / c;
        let _: Q = Z::from(42) / d;
        let _: Q = Z::from(42) / e;
        let _: Q = Z::from(42) / f;
        let _: Q = Z::from(42) / g;
        let _: Q = Z::from(42) / h;
        let _: Q = Z::from(42) / i;

        let _: Q = b / Z::from(42);
        let _: Q = c / Z::from(42);
        let _: Q = d / Z::from(42);
        let _: Q = e / Z::from(42);
        let _: Q = f / Z::from(42);
        let _: Q = g / Z::from(42);
        let _: Q = h / Z::from(42);
        let _: Q = i / Z::from(42);
    }
}

#[cfg(test)]
mod test_div {
    use super::Z;
    use crate::rational::Q;
    use crate::traits::Pow;

    /// Testing division for two [`Z`]
    #[test]
    fn div() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Q = a / b;
        assert_eq!(c, Q::from((21, 2)));
    }

    /// Testing division for two borrowed [`Z`]
    #[test]
    fn div_borrow() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Q = &a / &b;
        assert_eq!(c, Q::from((21, 2)));
    }

    /// Testing division for borrowed [`Z`] and [`Z`]
    #[test]
    fn div_first_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Q = &a / b;
        assert_eq!(c, Q::from((21, 2)));
    }

    /// Testing division for [`Z`] and borrowed [`Z`]
    #[test]
    fn div_second_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(4);
        let c: Q = a / &b;
        assert_eq!(c, Q::from((21, 2)));
    }

    /// Testing division for big [`Z`]
    #[test]
    fn div_large_numbers() {
        let a: Z = Z::from(i64::MAX as u64 + 1);
        let b: Z = Z::from(2);
        let c: Z = Z::from(i64::MIN);
        let d: Z = Z::from(i64::MAX as u64 + 1);

        let e: Q = a / b;
        let f: Q = c / d;

        assert_eq!(e, Q::from(2).pow(62).unwrap());
        assert_eq!(f, Q::MINUS_ONE);
    }
}

#[cfg(test)]
mod test_div_between_z_and_q {
    use super::Z;
    use crate::rational::Q;

    /// Testing division for [`Z`] and [`Q`]
    #[test]
    fn div() {
        let a: Z = Z::from(4);
        let b: Q = Q::from((5, 7));
        let c: Q = a / b;
        assert_eq!(c, Q::from((28, 5)));
    }

    /// Testing division for both borrowed [`Z`] and [`Q`]
    #[test]
    fn div_borrow() {
        let a: Z = Z::from(4);
        let b: Q = Q::from((5, 7));
        let c: Q = &a / &b;
        assert_eq!(c, Q::from((28, 5)));
    }

    /// Testing division for borrowed [`Z`] and [`Q`]
    #[test]
    fn div_first_borrowed() {
        let a: Z = Z::from(4);
        let b: Q = Q::from((5, 7));
        let c: Q = &a / b;
        assert_eq!(c, Q::from((28, 5)));
    }

    /// Testing division for [`Z`] and borrowed [`Q`]
    #[test]
    fn div_second_borrowed() {
        let a: Z = Z::from(4);
        let b: Q = Q::from((5, 7));
        let c: Q = a / &b;
        assert_eq!(c, Q::from((28, 5)));
    }

    /// Testing division for big numbers
    #[test]
    fn div_large_numbers() {
        let a: Z = Z::from(u64::MAX);
        let b: Q = Q::from((1, u64::MAX));
        let c: Q = Q::from((u64::MAX, 2));

        let d: Q = &a / b;
        let e: Q = a / c;

        assert_eq!(d, Q::from(u64::MAX) / Q::from((1, u64::MAX)));
        assert_eq!(e, Q::from(u64::MAX) / Q::from((u64::MAX, 2)));
    }
}
