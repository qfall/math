// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementation of the [`Add`] trait for [`Zq`] values.

use super::super::Zq;
use crate::{
    error::MathError,
    integer::Z,
    macros::arithmetics::{
        arithmetic_assign_between_types, arithmetic_assign_trait_borrowed_to_owned,
        arithmetic_between_types_zq, arithmetic_trait_borrowed_to_owned,
        arithmetic_trait_mixed_borrowed_owned,
    },
    traits::CompareBase,
};
use flint_sys::{
    fmpz::fmpz,
    fmpz_mod::{fmpz_mod_add, fmpz_mod_add_fmpz, fmpz_mod_add_si, fmpz_mod_add_ui},
};
use std::ops::{Add, AddAssign};

impl AddAssign<&Zq> for Zq {
    /// Computes the addition of `self` and `other` reusing
    /// the memory of `self`.
    /// [`AddAssign`] can be used on [`Zq`] in combination with
    /// [`Zq`], [`Z`], [`i64`], [`i32`], [`i16`], [`i8`], [`u64`], [`u32`], [`u16`] and [`u8`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers modulo `q` as a [`Zq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer_mod_q::Zq, integer::Z};
    ///
    /// let mut a: Zq = Zq::from((23, 42));
    /// let b: Zq = Zq::from((1, 42));
    /// let c: Z = Z::from(5);
    ///
    /// a += &b;
    /// a += b;
    /// a += 5;
    /// a += c;
    /// ```
    ///
    /// # Panics ...
    /// - if the moduli of both [`Zq`] mismatch.
    fn add_assign(&mut self, other: &Self) {
        if !self.compare_base(other) {
            panic!("{}", self.call_compare_base_error(other).unwrap());
        }

        unsafe {
            fmpz_mod_add(
                &mut self.value.value,
                &self.value.value,
                &other.value.value,
                self.modulus.get_fmpz_mod_ctx_struct(),
            )
        };
    }
}
impl AddAssign<i64> for Zq {
    /// Documentation at [`Zq::add_assign`].
    fn add_assign(&mut self, other: i64) {
        unsafe {
            fmpz_mod_add_si(
                &mut self.value.value,
                &self.value.value,
                other,
                self.modulus.get_fmpz_mod_ctx_struct(),
            )
        };
    }
}
impl AddAssign<u64> for Zq {
    /// Documentation at [`Zq::add_assign`].
    fn add_assign(&mut self, other: u64) {
        unsafe {
            fmpz_mod_add_ui(
                &mut self.value.value,
                &self.value.value,
                other,
                self.modulus.get_fmpz_mod_ctx_struct(),
            )
        };
    }
}
impl AddAssign<&Z> for Zq {
    /// Documentation at [`Zq::add_assign`].
    fn add_assign(&mut self, other: &Z) {
        unsafe {
            fmpz_mod_add_fmpz(
                &mut self.value.value,
                &self.value.value,
                &other.value,
                self.modulus.get_fmpz_mod_ctx_struct(),
            )
        };
    }
}

arithmetic_assign_trait_borrowed_to_owned!(AddAssign, add_assign, Zq, Zq);
arithmetic_assign_trait_borrowed_to_owned!(AddAssign, add_assign, Zq, Z);
arithmetic_assign_between_types!(AddAssign, add_assign, Zq, i64, i32 i16 i8);
arithmetic_assign_between_types!(AddAssign, add_assign, Zq, u64, u32 u16 u8);

impl Add for &Zq {
    type Output = Zq;
    /// Implements the [`Add`] trait for two [`Zq`] values.
    /// [`Add`] is implemented for any combination of [`Zq`] and borrowed [`Zq`].
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`Zq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    ///
    /// let a: Zq = Zq::from((23, 42));
    /// let b: Zq = Zq::from((1, 42));
    ///
    /// let c: Zq = &a + &b;
    /// let d: Zq = a + b;
    /// let e: Zq = &c + d;
    /// let f: Zq = c + &e;
    /// ```
    ///
    /// # Panics ...
    /// - if the moduli of both [`Zq`] mismatch.
    fn add(self, other: Self) -> Self::Output {
        self.add_safe(other).unwrap()
    }
}

impl Zq {
    /// Implements addition for two [`Zq`] values.
    ///
    ///
    /// Parameters:
    /// - `other`: specifies the value to add to `self`
    ///
    /// Returns the sum of both numbers as a [`Zq`] or an error if the modulus
    /// does mismatch.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    ///
    /// let a: Zq = Zq::from((23, 42));
    /// let b: Zq = Zq::from((1, 42));
    ///
    /// let c: Zq = a.add_safe(&b).unwrap();
    /// ```
    /// # Errors
    /// - Returns a [`MathError`] of type [`MathError::MismatchingModulus`] if the moduli of
    ///   both [`Zq`] mismatch.
    pub fn add_safe(&self, other: &Self) -> Result<Zq, MathError> {
        if !self.compare_base(other) {
            return Err(self.call_compare_base_error(other).unwrap());
        }
        let mut out = Zq::from((1, &self.modulus));
        unsafe {
            fmpz_mod_add(
                &mut out.value.value,
                &self.value.value,
                &other.value.value,
                self.modulus.get_fmpz_mod_ctx_struct(),
            );
        }
        Ok(out)
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, Zq, Zq, Zq);
arithmetic_trait_mixed_borrowed_owned!(Add, add, Zq, Zq, Zq);
arithmetic_between_types_zq!(Add, add, Zq, i64 i32 i16 i8 u64 u32 u16 u8);

impl Add<&Z> for &Zq {
    type Output = Zq;

    /// Implements the [`Add`] trait for [`Zq`] and [`Z`] values.
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
    /// let a: Zq = Zq::from((42, 19));
    /// let b: Z = Z::from(42);
    ///
    /// let c: Zq = &a + &b;
    /// let d: Zq = a + b;
    /// let e: Zq = &c + Z::from(42);
    /// let f: Zq = c + &Z::from(42);
    /// ```
    fn add(self, other: &Z) -> Self::Output {
        let mut out = fmpz(0);
        unsafe {
            fmpz_mod_add_fmpz(
                &mut out,
                &self.value.value,
                &other.value,
                self.modulus.get_fmpz_mod_ctx_struct(),
            );
        }
        Zq {
            modulus: self.modulus.clone(),
            value: Z { value: out },
        }
    }
}

arithmetic_trait_borrowed_to_owned!(Add, add, Zq, Z, Zq);
arithmetic_trait_mixed_borrowed_owned!(Add, add, Zq, Z, Zq);

#[cfg(test)]
mod test_add_assign {
    use crate::{integer::Z, integer_mod_q::Zq};

    /// Ensure that `add_assign` works for small numbers.
    #[test]
    fn correct_small() {
        let mut a: Zq = Zq::from((-1, 7));
        let b = Zq::from((-1, 7));
        let c = Zq::from((1, 7));

        a += &b;
        assert_eq!(Zq::from((5, 7)), a);
        a += &c;
        assert_eq!(Zq::from((6, 7)), a);
        a += &c;
        assert_eq!(Zq::from((0, 7)), a);
        a += &c;
        assert_eq!(Zq::from((1, 7)), a);
        a += &c;
        assert_eq!(Zq::from((2, 7)), a);
        a += 2 * b;
        assert_eq!(Zq::from((0, 7)), a);
    }

    /// Ensure that `add_assign` works for large numbers.
    #[test]
    fn correct_large() {
        let mut a = Zq::from((i64::MAX, u64::MAX));
        let b = Zq::from((i64::MIN + 2, u64::MAX));
        let c = Zq::from((u64::MAX - 1, u64::MAX));

        a += b;
        assert_eq!(Zq::from((1, u64::MAX)), a);
        a += c;
        assert_eq!(Zq::from((0, u64::MAX)), a);
    }

    /// Ensure that `add_assign` is available for all types.
    #[test]
    fn availability() {
        let mut a = Zq::from((3, 7));
        let b = Zq::from((1, 7));
        let c = Z::from(1);

        a += &b;
        a += b;
        a += &c;
        a += c;
        a += 1_u8;
        a += 1_u16;
        a += 1_u32;
        a += 1_u64;
        a += 1_i8;
        a += 1_i16;
        a += 1_i32;
        a += 1_i64;
    }

    /// Ensures that mismatching moduli result in a panic.
    #[test]
    #[should_panic]
    fn mismatching_moduli() {
        let mut a = Zq::from((3, 7));
        let b = Zq::from((1, 8));

        a += b;
    }
}

#[cfg(test)]
mod test_add {
    use super::Zq;

    /// Testing addition for two [`Zq`]
    #[test]
    fn add() {
        let a: Zq = Zq::from((11, 17));
        let b: Zq = Zq::from((12, 17));
        let c: Zq = a + b;
        assert_eq!(c, Zq::from((6, 17)));
    }

    /// Testing addition for two borrowed [`Zq`]
    #[test]
    fn add_borrow() {
        let a: Zq = Zq::from((10, 11));
        let b: Zq = Zq::from((1, 11));
        let c: Zq = &a + &b;
        assert_eq!(c, Zq::from((0, 11)));
    }

    /// Testing addition for borrowed [`Zq`] and [`Zq`]
    #[test]
    fn add_first_borrowed() {
        let a: Zq = Zq::from((2, 11));
        let b: Zq = Zq::from((5, 11));
        let c: Zq = &a + b;
        assert_eq!(c, Zq::from((7, 11)));
    }

    /// Testing addition for [`Zq`] and borrowed [`Zq`]
    #[test]
    fn add_second_borrowed() {
        let a: Zq = Zq::from((12, 11));
        let b: Zq = Zq::from((10, 11));
        let c: Zq = a + &b;
        assert_eq!(c, Zq::from((0, 11)));
    }

    /// Testing addition for large [`Zq`]
    #[test]
    fn add_large_numbers() {
        let a: Zq = Zq::from((u32::MAX, u32::MAX - 58));
        let b: Zq = Zq::from((i32::MAX, u32::MAX - 58));
        let c: Zq = a + b;
        assert_eq!(c, Zq::from(((u32::MAX - 1) / 2 + 58, u32::MAX - 58)));
    }

    /// Testing addition for [`Zq`] with different moduli does not work
    #[test]
    #[should_panic]
    fn add_mismatching_modulus() {
        let a: Zq = Zq::from((4, 11));
        let b: Zq = Zq::from((1, 3));
        let _c: Zq = a + b;
    }

    /// Testing whether add_safe throws an error for mismatching moduli
    #[test]
    fn add_safe_is_err() {
        let a: Zq = Zq::from((4, 11));
        let b: Zq = Zq::from((1, 3));
        assert!(&a.add_safe(&b).is_err());
    }
}

#[cfg(test)]
mod test_add_between_zq_and_z {
    use super::Z;
    use crate::integer_mod_q::Zq;

    /// Testing addition for [`Zq`] and [`Z`]
    #[test]
    fn add() {
        let a: Zq = Zq::from((4, 11));
        let b: Z = Z::from(9);
        let c: Zq = a + b;
        assert_eq!(c, Zq::from((2, 11)));
    }

    /// Testing addition for both borrowed [`Zq`] and [`Z`]
    #[test]
    fn add_borrow() {
        let a: Zq = Zq::from((4, 11));
        let b: Z = Z::from(9);
        let c: Zq = &a + &b;
        assert_eq!(c, Zq::from((2, 11)));
    }

    /// Testing addition for borrowed [`Zq`] and [`Z`]
    #[test]
    fn add_first_borrowed() {
        let a: Zq = Zq::from((4, 11));
        let b: Z = Z::from(9);
        let c: Zq = &a + b;
        assert_eq!(c, Zq::from((2, 11)));
    }

    /// Testing addition for [`Zq`] and borrowed [`Z`]
    #[test]
    fn add_second_borrowed() {
        let a: Zq = Zq::from((4, 11));
        let b: Z = Z::from(9);
        let c: Zq = a + &b;
        assert_eq!(c, Zq::from((2, 11)));
    }

    /// Testing addition for large numbers
    #[test]
    fn add_large_numbers() {
        let a: Zq = Zq::from((i64::MAX, u64::MAX - 58));
        let b: Zq = Zq::from((i64::MAX - 1, i64::MAX));
        let c: Z = Z::from(u64::MAX);

        let d: Zq = a + &c;
        let e: Zq = b + c;

        assert_eq!(d, Zq::from(((u64::MAX - 1) / 2 + 58, u64::MAX - 58)));
        assert_eq!(e, Zq::from((0, i64::MAX)));
    }
}

#[cfg(test)]
mod test_add_between_types {
    use crate::integer_mod_q::Zq;

    /// Testing addition between different types
    #[test]
    #[allow(clippy::op_ref)]
    fn add() {
        let a: Zq = Zq::from((4, 11));
        let b: u64 = 1;
        let c: u32 = 1;
        let d: u16 = 1;
        let e: u8 = 1;
        let f: i64 = 1;
        let g: i32 = 1;
        let h: i16 = 1;
        let i: i8 = 1;

        let _: Zq = &a + &b;
        let _: Zq = &a + &c;
        let _: Zq = &a + &d;
        let _: Zq = &a + &e;
        let _: Zq = &a + &f;
        let _: Zq = &a + &g;
        let _: Zq = &a + &h;
        let _: Zq = &a + &i;

        let _: Zq = &b + &a;
        let _: Zq = &c + &a;
        let _: Zq = &d + &a;
        let _: Zq = &e + &a;
        let _: Zq = &f + &a;
        let _: Zq = &g + &a;
        let _: Zq = &h + &a;
        let _: Zq = &i + &a;

        let _: Zq = &a + b;
        let _: Zq = &a + c;
        let _: Zq = &a + d;
        let _: Zq = &a + e;
        let _: Zq = &a + f;
        let _: Zq = &a + g;
        let _: Zq = &a + h;
        let _: Zq = &a + i;

        let _: Zq = &b + Zq::from((4, 11));
        let _: Zq = &c + Zq::from((4, 11));
        let _: Zq = &d + Zq::from((4, 11));
        let _: Zq = &e + Zq::from((4, 11));
        let _: Zq = &f + Zq::from((4, 11));
        let _: Zq = &g + Zq::from((4, 11));
        let _: Zq = &h + Zq::from((4, 11));
        let _: Zq = &i + Zq::from((4, 11));

        let _: Zq = Zq::from((4, 11)) + &b;
        let _: Zq = Zq::from((4, 11)) + &c;
        let _: Zq = Zq::from((4, 11)) + &d;
        let _: Zq = Zq::from((4, 11)) + &e;
        let _: Zq = Zq::from((4, 11)) + &f;
        let _: Zq = Zq::from((4, 11)) + &g;
        let _: Zq = Zq::from((4, 11)) + &h;
        let _: Zq = Zq::from((4, 11)) + &i;

        let _: Zq = b + &a;
        let _: Zq = c + &a;
        let _: Zq = d + &a;
        let _: Zq = e + &a;
        let _: Zq = f + &a;
        let _: Zq = g + &a;
        let _: Zq = h + &a;
        let _: Zq = i + &a;

        let _: Zq = Zq::from((4, 11)) + b;
        let _: Zq = Zq::from((4, 11)) + c;
        let _: Zq = Zq::from((4, 11)) + d;
        let _: Zq = Zq::from((4, 11)) + e;
        let _: Zq = Zq::from((4, 11)) + f;
        let _: Zq = Zq::from((4, 11)) + g;
        let _: Zq = Zq::from((4, 11)) + h;
        let _: Zq = Zq::from((4, 11)) + i;

        let _: Zq = b + Zq::from((4, 11));
        let _: Zq = c + Zq::from((4, 11));
        let _: Zq = d + Zq::from((4, 11));
        let _: Zq = e + Zq::from((4, 11));
        let _: Zq = f + Zq::from((4, 11));
        let _: Zq = g + Zq::from((4, 11));
        let _: Zq = h + Zq::from((4, 11));
        let _: Zq = i + Zq::from((4, 11));
    }
}
