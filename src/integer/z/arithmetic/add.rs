// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Add`] trait for [`Z`] values.

use super::super::Z;
use crate::{
    integer::PolyOverZ,
    integer_mod_q::Zq,
    macros::arithmetics::{
        arithmetic_assign_between_types, arithmetic_assign_trait_borrowed_to_owned,
        arithmetic_between_types, arithmetic_trait_borrowed_to_owned,
        arithmetic_trait_mixed_borrowed_owned,
    },
    rational::Q,
};
use flint_sys::{
    fmpq::fmpq_add_fmpz,
    fmpz::{fmpz, fmpz_add, fmpz_add_si, fmpz_add_ui},
    fmpz_mod::fmpz_mod_add_fmpz,
};
use std::ops::{Add, AddAssign};

impl AddAssign<&Z> for Z {
    /// Computes the addition of `self` and `other` reusing
    /// the memory of `self`.
    /// [`AddAssign`] can be used on [`Z`] in combination with
    /// [`Z`], [`i64`], [`i32`], [`i16`], [`i8`], [`u64`], [`u32`], [`u16`] and [`u8`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`Z`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let mut a: Z = Z::from(42);
    /// let b: Z = Z::from(24);
    ///
    /// a += &b;
    /// a += b;
    /// a += 5;
    /// ```
    fn add_assign(&mut self, other: &Self) {
        unsafe { fmpz_add(&mut self.value, &self.value, &other.value) };
    }
}
impl AddAssign<i64> for Z {
    /// Documentation at [`Z::add_assign`].
    fn add_assign(&mut self, other: i64) {
        unsafe { fmpz_add_si(&mut self.value, &self.value, other) };
    }
}
impl AddAssign<u64> for Z {
    /// Documentation at [`Z::add_assign`].
    fn add_assign(&mut self, other: u64) {
        unsafe { fmpz_add_ui(&mut self.value, &self.value, other) };
    }
}

arithmetic_assign_trait_borrowed_to_owned!(AddAssign, add_assign, Z, Z);
arithmetic_assign_between_types!(AddAssign, add_assign, Z, i64, i32 i16 i8);
arithmetic_assign_between_types!(AddAssign, add_assign, Z, u64, u32 u16 u8);

impl Add for &Z {
    type Output = Z;
    /// Implements the [`Add`] trait for two [`Z`] values.
    /// [`Add`] is implemented for any combination of [`Z`] and borrowed [`Z`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`Z`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let a: Z = Z::from(42);
    /// let b: Z = Z::from(24);
    ///
    /// let c: Z = &a + &b;
    /// let d: Z = a + b;
    /// let e: Z = &c + d;
    /// let f: Z = c + &e;
    /// ```
    fn add(self, other: Self) -> Self::Output {
        let mut out = Z::default();
        unsafe {
            fmpz_add(&mut out.value, &self.value, &other.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, Z, Z, Z);
arithmetic_trait_mixed_borrowed_owned!(Add, add, Z, Z, Z);
arithmetic_between_types!(Add, add, Z, Z, i64 i32 i16 i8 u64 u32 u16 u8);

impl Add<&Q> for &Z {
    type Output = Q;

    /// Implements the [`Add`] trait for [`Z`] and [`Q`] values.
    /// [`Add`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    ///  - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`Q`].
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
    /// let c: Q = &a + &b;
    /// let d: Q = a + b;
    /// let e: Q = &Z::from(42) + d;
    /// let f: Q = Z::from(42) + &e;
    /// ```
    fn add(self, other: &Q) -> Self::Output {
        let mut out = Q::default();
        unsafe {
            fmpq_add_fmpz(&mut out.value, &other.value, &self.value);
        }
        out
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, Z, Q, Q);
arithmetic_trait_mixed_borrowed_owned!(Add, add, Z, Q, Q);
arithmetic_between_types!(Add, add, Z, Q, f32 f64);

impl Add<&Zq> for &Z {
    type Output = Zq;
    /// Implements the [`Add`] trait for [`Z`] and [`Zq`] values.
    /// [`Add`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    ///  - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`Zq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let a: Z = Z::from(42);
    /// let b: Zq = Zq::from((42, 19));
    ///
    /// let c: Zq = &a + &b;
    /// let d: Zq = a + b;
    /// let e: Zq = &Z::from(42) + d;
    /// let f: Zq = Z::from(42) + &e;
    /// ```
    fn add(self, other: &Zq) -> Self::Output {
        let mut out = fmpz(0);
        unsafe {
            fmpz_mod_add_fmpz(
                &mut out,
                &other.value.value,
                &self.value,
                other.modulus.get_fmpz_mod_ctx_struct(),
            );
        }
        Zq {
            modulus: other.modulus.clone(),
            value: Z { value: out },
        }
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, Z, Zq, Zq);
arithmetic_trait_mixed_borrowed_owned!(Add, add, Z, Zq, Zq);

impl Add<&PolyOverZ> for &Z {
    type Output = PolyOverZ;
    /// Implements the [`Add`] trait for [`Z`] and [`PolyOverZ`] values.
    /// [`Add`] is implemented for any combination of owned and borrowed values.
    ///
    /// Parameters:
    ///  - `other`: specifies the polynomial to add to `self`
    ///
    /// Returns the sum of both as a [`PolyOverZ`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::PolyOverZ;
    /// use qfall_math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let a: Z = Z::from(42);
    /// let b: PolyOverZ = PolyOverZ::from_str("4  5 1 2 3").unwrap();
    ///
    /// let c: PolyOverZ = &a + &b;
    /// let d: PolyOverZ = a + b;
    /// let e: PolyOverZ = &Z::from(42) + d;
    /// let f: PolyOverZ = Z::from(42) + &e;
    /// ```
    fn add(self, other: &PolyOverZ) -> Self::Output {
        // check if the first coefficient of the polynomial is initiated and
        // can be addressed
        if other.is_zero() {
            PolyOverZ::from(self)
        } else {
            let out = other.clone();
            unsafe {
                fmpz_add(out.poly.coeffs, &self.value, out.poly.coeffs);
            }
            out
        }
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, Z, PolyOverZ, PolyOverZ);
arithmetic_trait_mixed_borrowed_owned!(Add, add, Z, PolyOverZ, PolyOverZ);

#[cfg(test)]
mod test_add_assign {
    use crate::integer::Z;

    /// Ensure that `add_assign` works for small numbers.
    #[test]
    fn correct_small() {
        let mut a: Z = Z::MINUS_ONE;
        let b = Z::MINUS_ONE;
        let c = Z::ONE;

        a += &b;
        assert_eq!(-2, a);
        a += &c;
        assert_eq!(-1, a);
        a += &c;
        assert_eq!(0, a);
        a += &c;
        assert_eq!(1, a);
        a += &c;
        assert_eq!(2, a);
        a += 2 * b;
        assert_eq!(0, a);
    }

    /// Ensure that `add_assign` works for large numbers.
    #[test]
    fn correct_large() {
        let mut a: Z = Z::from(i64::MAX);
        let b = Z::from(i64::MIN);
        let c = Z::from(u64::MAX);

        a += b;
        assert_eq!(-1, a);
        a += c;
        assert_eq!(u64::MAX - 1, a);
    }

    /// Ensure that `add_assign` is available for all types.
    #[test]
    fn availability() {
        let mut a: Z = Z::from(42);
        let b: Z = Z::from(1);

        a += &b;
        a += b;
        a += 1_u8;
        a += 1_u16;
        a += 1_u32;
        a += 1_u64;
        a += 1_i8;
        a += 1_i16;
        a += 1_i32;
        a += 1_i64;
    }
}

#[cfg(test)]
mod test_add_between_types {
    use crate::integer::Z;

    /// Testing addition between different types
    #[test]
    #[allow(clippy::op_ref)]
    fn add() {
        let a: Z = Z::from(42);
        let b: u64 = 1;
        let c: u32 = 1;
        let d: u16 = 1;
        let e: u8 = 1;
        let f: i64 = 1;
        let g: i32 = 1;
        let h: i16 = 1;
        let i: i8 = 1;

        let _: Z = &a + &b;
        let _: Z = &a + &c;
        let _: Z = &a + &d;
        let _: Z = &a + &e;
        let _: Z = &a + &f;
        let _: Z = &a + &g;
        let _: Z = &a + &h;
        let _: Z = &a + &i;

        let _: Z = &b + &a;
        let _: Z = &c + &a;
        let _: Z = &d + &a;
        let _: Z = &e + &a;
        let _: Z = &f + &a;
        let _: Z = &g + &a;
        let _: Z = &h + &a;
        let _: Z = &i + &a;

        let _: Z = &a + b;
        let _: Z = &a + c;
        let _: Z = &a + d;
        let _: Z = &a + e;
        let _: Z = &a + f;
        let _: Z = &a + g;
        let _: Z = &a + h;
        let _: Z = &a + i;

        let _: Z = &b + Z::from(42);
        let _: Z = &c + Z::from(42);
        let _: Z = &d + Z::from(42);
        let _: Z = &e + Z::from(42);
        let _: Z = &f + Z::from(42);
        let _: Z = &g + Z::from(42);
        let _: Z = &h + Z::from(42);
        let _: Z = &i + Z::from(42);

        let _: Z = Z::from(42) + &b;
        let _: Z = Z::from(42) + &c;
        let _: Z = Z::from(42) + &d;
        let _: Z = Z::from(42) + &e;
        let _: Z = Z::from(42) + &f;
        let _: Z = Z::from(42) + &g;
        let _: Z = Z::from(42) + &h;
        let _: Z = Z::from(42) + &i;

        let _: Z = b + &a;
        let _: Z = c + &a;
        let _: Z = d + &a;
        let _: Z = e + &a;
        let _: Z = f + &a;
        let _: Z = g + &a;
        let _: Z = h + &a;
        let _: Z = i + &a;

        let _: Z = Z::from(42) + b;
        let _: Z = Z::from(42) + c;
        let _: Z = Z::from(42) + d;
        let _: Z = Z::from(42) + e;
        let _: Z = Z::from(42) + f;
        let _: Z = Z::from(42) + g;
        let _: Z = Z::from(42) + h;
        let _: Z = Z::from(42) + i;

        let _: Z = b + Z::from(42);
        let _: Z = c + Z::from(42);
        let _: Z = d + Z::from(42);
        let _: Z = e + Z::from(42);
        let _: Z = f + Z::from(42);
        let _: Z = g + Z::from(42);
        let _: Z = h + Z::from(42);
        let _: Z = i + Z::from(42);
    }
}

#[cfg(test)]
mod test_add_between_z_and_q {
    use super::Z;
    use crate::rational::Q;

    /// Ensuring addition between different types is available
    #[test]
    fn availability() {
        let a: Z = Z::from(42);
        let b: Q = Q::from((5, 7));

        let _: Q = &a + &b;
        let _: Q = &a + b.clone();
        let _: Q = a.clone() + &b;
        let _: Q = a.clone() + b;
        let _: Q = &a + 0.5_f32;
        let _: Q = &a + 0.5_f64;
        let _: Q = a.clone() + 0.5_f32;
        let _: Q = a.clone() + 0.5_f64;
        let _: Q = 0.5_f32 + &a;
        let _: Q = 0.5_f64 + &a;
        let _: Q = 0.5_f32 + a.clone();
        let _: Q = 0.5_f64 + a.clone();
    }

    /// Testing addition for [`Z`] and [`Q`]
    #[test]
    fn add() {
        let a: Z = Z::from(4);
        let b: Q = Q::from((5, 7));
        let c: Q = a + b;
        assert_eq!(c, Q::from((33, 7)));
    }

    /// Testing addition for both borrowed [`Z`] and [`Q`]
    #[test]
    fn add_borrow() {
        let a: Z = Z::from(4);
        let b: Q = Q::from((5, 7));
        let c: Q = &a + &b;
        assert_eq!(c, Q::from((33, 7)));
    }

    /// Testing addition for borrowed [`Z`] and [`Q`]
    #[test]
    fn add_first_borrowed() {
        let a: Z = Z::from(4);
        let b: Q = Q::from((5, 7));
        let c: Q = &a + b;
        assert_eq!(c, Q::from((33, 7)));
    }

    /// Testing addition for [`Z`] and borrowed [`Q`]
    #[test]
    fn add_second_borrowed() {
        let a: Z = Z::from(4);
        let b: Q = Q::from((5, 7));
        let c: Q = a + &b;
        assert_eq!(c, Q::from((33, 7)));
    }

    /// Testing addition for large numbers
    #[test]
    fn add_large_numbers() {
        let a: Z = Z::from(u64::MAX);
        let b: Q = Q::from((1, u64::MAX));
        let c: Q = Q::from((u64::MAX, 2));

        let d: Q = &a + b;
        let e: Q = a + c;

        assert_eq!(d, Q::from((1, u64::MAX)) + Q::from(u64::MAX));
        assert_eq!(e, Q::from(u64::MAX) + Q::from((u64::MAX, 2)));
    }
}

#[cfg(test)]
mod test_add {
    use super::Z;

    /// Testing addition for two [`Z`]
    #[test]
    fn add() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = a + b;
        assert_eq!(c, Z::from(66));
    }

    /// Testing addition for two borrowed [`Z`]
    #[test]
    fn add_borrow() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = &a + &b;
        assert_eq!(c, Z::from(66));
    }

    /// Testing addition for borrowed [`Z`] and [`Z`]
    #[test]
    fn add_first_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = &a + b;
        assert_eq!(c, Z::from(66));
    }

    /// Testing addition for [`Z`] and borrowed [`Z`]
    #[test]
    fn add_second_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = a + &b;
        assert_eq!(c, Z::from(66));
    }

    /// Testing addition for large numbers
    #[test]
    fn add_large_numbers() {
        let a: Z = Z::from(u64::MAX);
        let b: Z = Z::from(-221319874);
        let c: Z = Z::from(i64::MIN);

        let d: Z = &a + b;
        let e: Z = a + c;

        assert_eq!(d, Z::from(u64::MAX - 221319874));
        assert_eq!(e, Z::from(i64::MAX));
    }
}

#[cfg(test)]
mod test_add_between_z_and_zq {
    use super::Z;
    use crate::integer_mod_q::Zq;

    /// Testing addition for [`Z`] and [`Zq`]
    #[test]
    fn add() {
        let a: Z = Z::from(9);
        let b: Zq = Zq::from((4, 11));
        let c: Zq = a + b;
        assert_eq!(c, Zq::from((2, 11)));
    }

    /// Testing addition for both borrowed [`Z`] and [`Zq`]
    #[test]
    fn add_borrow() {
        let a: Z = Z::from(9);
        let b: Zq = Zq::from((4, 11));
        let c: Zq = &a + &b;
        assert_eq!(c, Zq::from((2, 11)));
    }

    /// Testing addition for borrowed [`Z`] and [`Zq`]
    #[test]
    fn add_first_borrowed() {
        let a: Z = Z::from(9);
        let b: Zq = Zq::from((4, 11));
        let c: Zq = &a + b;
        assert_eq!(c, Zq::from((2, 11)));
    }

    /// Testing addition for [`Z`] and borrowed [`Zq`]
    #[test]
    fn add_second_borrowed() {
        let a: Z = Z::from(9);
        let b: Zq = Zq::from((4, 11));
        let c: Zq = a + &b;
        assert_eq!(c, Zq::from((2, 11)));
    }

    /// Testing addition for large numbers
    #[test]
    fn add_large_numbers() {
        let a: Z = Z::from(u64::MAX);
        let b: Zq = Zq::from((i64::MAX, u64::MAX - 58));
        let c: Zq = Zq::from((i64::MAX - 1, i64::MAX));

        let d: Zq = &a + b;
        let e: Zq = a + c;

        assert_eq!(d, Zq::from(((u64::MAX - 1) / 2 + 58, u64::MAX - 58)));
        assert_eq!(e, Zq::from((0, i64::MAX)));
    }
}

#[cfg(test)]
mod test_add_between_z_and_poly_over_z {
    use super::Z;
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// Testing addition for [`Z`] and [`PolyOverZ`]
    #[test]
    fn add() {
        let a: Z = Z::from(9);
        let b: PolyOverZ = PolyOverZ::from_str("4  1 1 2 3").unwrap();
        let c: PolyOverZ = a + b;
        assert_eq!(c, PolyOverZ::from_str("4  10 1 2 3").unwrap());
    }

    /// Testing addition for both borrowed [`Z`] and [`PolyOverZ`]
    #[test]
    fn add_borrow() {
        let a: Z = Z::from(9);
        let b: PolyOverZ = PolyOverZ::from_str("4  1 1 2 3").unwrap();
        let c: PolyOverZ = &a + &b;
        assert_eq!(c, PolyOverZ::from_str("4  10 1 2 3").unwrap());
    }

    /// Testing addition for borrowed [`Z`] and [`PolyOverZ`]
    #[test]
    fn add_first_borrowed() {
        let a: Z = Z::from(9);
        let b: PolyOverZ = PolyOverZ::from_str("4  1 1 2 3").unwrap();
        let c: PolyOverZ = &a + b;
        assert_eq!(c, PolyOverZ::from_str("4  10 1 2 3").unwrap());
    }

    /// Testing addition for [`Z`] and borrowed [`PolyOverZ`]
    #[test]
    fn add_second_borrowed() {
        let a: Z = Z::from(9);
        let b: PolyOverZ = PolyOverZ::from_str("4  1 1 2 3").unwrap();
        let c: PolyOverZ = a + &b;
        assert_eq!(c, PolyOverZ::from_str("4  10 1 2 3").unwrap());
    }

    /// Testing addition for large numbers
    #[test]
    fn add_large_numbers() {
        let a: Z = Z::from(i64::MAX);
        let b: PolyOverZ =
            PolyOverZ::from_str(&format!("3  {} {} {}", i64::MAX, u64::MAX, i32::MAX)).unwrap();
        let c: PolyOverZ = a + b;
        assert_eq!(
            c,
            PolyOverZ::from_str(&format!("3  {} {} {}", u64::MAX - 1, u64::MAX, i32::MAX)).unwrap()
        );
    }

    /// Testing addition for an empty polynomial and a zero [`Z`]
    #[test]
    fn add_zero() {
        let a: Z = Z::from(15);
        let b: PolyOverZ = PolyOverZ::default();
        let c: PolyOverZ = a + b;
        assert_eq!(c, PolyOverZ::from_str("1  15").unwrap());

        let d: Z = Z::ZERO;
        let e: PolyOverZ = PolyOverZ::from_str("1  15").unwrap();
        let f: PolyOverZ = d + e;
        assert_eq!(f, PolyOverZ::from_str("1  15").unwrap());
    }
}
