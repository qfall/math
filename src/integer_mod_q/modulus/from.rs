// Copyright © 2023 Marvin Beckmann, Sven Moog
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`Modulus`] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use super::Modulus;
use crate::{
    error::MathError, integer::Z, macros::for_others::implement_empty_trait_owned_ref, traits::*,
};
use flint_sys::{
    fmpz::{fmpz, fmpz_clear, fmpz_cmp_si},
    fmpz_mod::fmpz_mod_ctx_init,
};
use std::{mem::MaybeUninit, rc::Rc, str::FromStr};

impl Modulus {
    /// Initialize a [`Modulus`] from an fmpz reference.
    ///
    /// Parameters:
    /// - `value`: the initial value the modulus should have.
    ///   It must be larger than one.
    ///
    /// Returns the new [`Modulus`] or an error, if the
    /// provided value was not greater than `1`.
    ///
    /// # Safety
    /// Since the parameter is a reference, it still has to be
    /// properly cleared outside this function.
    /// For example, by the drop trait of [`Z`].
    ///
    /// # Examples
    /// ```compile_fail
    /// use qfall_math::integer_mod_q::Modulus;
    /// use qfall_math::integer::Z;
    ///
    /// let z = Z::from(42);
    /// let modulus = Modulus::from_fmpz_ref(&z.value);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntToModulus`](MathError::InvalidIntToModulus)
    /// if the provided value is not greater than `1`.
    pub(crate) fn from_fmpz_ref(value: &fmpz) -> Result<Self, MathError> {
        if (unsafe { fmpz_cmp_si(value, 1) } <= 0) {
            let z = Z::from(value);
            return Err(MathError::InvalidIntToModulus(z.to_string()));
        }

        let mut ctx = MaybeUninit::uninit();
        unsafe {
            fmpz_mod_ctx_init(ctx.as_mut_ptr(), value);
            Ok(Self {
                modulus: Rc::new(ctx.assume_init()),
            })
        }
    }
}

/// A trait that filters for which types the `From for Modulus` should be implemented.
/// It is used as a workaround to implement the [`From`] trait without colliding
/// with the default implementation for [`Modulus`] and also to filter out
/// [`Zq`](crate::integer_mod_q::Zq) and [`&Modulus`].
trait IntoModulus {}
implement_empty_trait_owned_ref!(IntoModulus for Z fmpz u8 u16 u32 u64 i8 i16 i32 i64);

impl<Integer: AsInteger + IntoModulus> From<Integer> for Modulus {
    /// Create a [`Modulus`] from a positive integer.
    /// Parameters:
    /// - `value`: the initial value the modulus should have.
    ///   It must be larger than one.
    ///
    /// Returns the new [`Modulus`] or an panics, if the
    /// provided value was not greater than `1`.
    ///
    /// ```
    /// use qfall_math::integer_mod_q::Modulus;
    /// use qfall_math::integer::Z;
    ///
    /// let _ = Modulus::from(10);
    /// let _ = Modulus::from(u64::MAX);
    /// let _ = Modulus::from(Z::from(42));
    /// ```
    ///
    /// # Errors and Failures
    /// - Panics if the provided value is not greater than `1`.
    fn from(value: Integer) -> Self {
        match value.get_fmpz_ref() {
            Some(val) => Modulus::from_fmpz_ref(val).unwrap(),
            None => unsafe {
                let mut value = value.into_fmpz();
                let out = Modulus::from_fmpz_ref(&value);
                fmpz_clear(&mut value);
                out.unwrap()
            },
        }
    }
}

impl From<&Modulus> for Modulus {
    // This is more efficient than the generic implementation above
    // since only the smart pointer is increased here.

    /// Alias for [`Modulus::clone`].
    fn from(value: &Modulus) -> Self {
        value.clone()
    }
}

impl FromStr for Modulus {
    type Err = MathError;

    /// Create a [`Modulus`] from a string with a decimal number.
    ///
    /// Parameters:
    /// - `s`: the modulus of form: "[0-9]+" and not all zeros
    ///
    /// Returns a [`Modulus`] or an [`MathError`], if the provided string is not
    /// a valid modulus.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    ///
    /// let modulus = Modulus::from_str("42").unwrap();
    /// ```
    /// # Errors and Failures
    ///
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToZInput`](MathError::InvalidStringToZInput) if the
    /// provided string was not formatted correctly, e.g. not a correctly
    /// formatted [`Z`].
    /// - Returns a [`MathError`] of type
    /// [`InvalidIntToModulus`](MathError::InvalidIntToModulus)
    /// if the provided value is not greater than `1`.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let z = Z::from_str(s)?;

        Modulus::from_fmpz_ref(&z.value)
    }
}

#[cfg(test)]
mod test_from {
    use super::*;

    /// Showcase the different ways to initialize a [`Modulus`].
    #[test]
    fn available() {
        // signed rust integer
        let _ = Modulus::from(i8::MAX);
        let _ = Modulus::from(i16::MAX);
        let _ = Modulus::from(i32::MAX);
        let _ = Modulus::from(i64::MAX);
        let _ = Modulus::from(&i8::MAX);
        let _ = Modulus::from(&i16::MAX);
        let _ = Modulus::from(&i32::MAX);
        let _ = Modulus::from(&i64::MAX);

        // unsigned rust integer
        let _ = Modulus::from(u8::MAX);
        let _ = Modulus::from(u16::MAX);
        let _ = Modulus::from(u32::MAX);
        let _ = Modulus::from(u64::MAX);
        let _ = Modulus::from(&u8::MAX);
        let _ = Modulus::from(&u16::MAX);
        let _ = Modulus::from(&u32::MAX);
        let _ = Modulus::from(&u64::MAX);

        // from Z
        let _ = Modulus::from(Z::from(10));
        let _ = Modulus::from(&Z::from(10));

        // from fmpz
        let z = Z::from(42);
        let _ = Modulus::from(&z.value);
        let modulus = Modulus::from(z.value);

        // from Modulus
        let _ = Modulus::from(&modulus);
        let _ = Modulus::from(modulus);
    }

    /// Ensure that a modulus of one panics.
    #[test]
    #[should_panic]
    fn invalid_modulus() {
        let _ = Modulus::from(1);
    }

    /// Ensure that a large modulus is initialized correctly.
    #[test]
    fn large() {
        let modulus = Modulus::from(i64::MAX);

        assert_eq!(Z::from(modulus), Z::from(i64::MAX));
    }

    /// Ensure that a small modulus is initialized correctly.
    #[test]
    fn small() {
        let modulus = Modulus::from(2);

        assert_eq!(Z::from(modulus), Z::from(2));
    }
}

#[cfg(test)]
mod test_from_fmpz_ref {
    use super::*;
    use crate::integer::Z;

    /// Tests whether a small modulus ist instantiated correctly.
    #[test]
    fn working_example() {
        let z = Z::from(100);
        assert!(Modulus::from_fmpz_ref(&z.value).is_ok())
    }

    /// Tests whether a large modulus (> 64 bits) is instantiated correctly.
    #[test]
    fn large_modulus() {
        let z = &Z::from(u64::MAX);
        assert!(Modulus::from_fmpz_ref(&z.value).is_ok());
    }

    /// Tests whether a negative input value returns an error.
    #[test]
    fn negative_modulus() {
        let z = &Z::from(-42);
        assert!(Modulus::from_fmpz_ref(&z.value).is_err())
    }

    /// Tests whether a zero as input value returns an error.
    #[test]
    fn zero_modulus() {
        let z = &Z::ZERO;
        assert!(Modulus::from_fmpz_ref(&z.value).is_err())
    }
}

#[cfg(test)]
mod test_from_str {

    use super::Modulus;
    use std::str::FromStr;

    /// Tests whether a correctly formatted string outputs an instantiation of a
    /// Modulus, i.e. does not return an error.
    #[test]
    fn working_example() {
        assert!(Modulus::from_str("42").is_ok());
    }

    /// Tests whether a large value (> 64 bits) is instantiated correctly.
    #[test]
    fn large_value() {
        assert!(Modulus::from_str(&"1".repeat(65)).is_ok())
    }

    /// Tests whether a falsely formatted string (wrong whitespaces) returns an
    /// error.
    #[test]
    fn false_format_whitespaces() {
        assert!(Modulus::from_str("4 2").is_err());
    }

    /// Tests whether a falsely formatted string (wrong symbols) returns an error.
    #[test]
    fn false_format_symbols() {
        assert!(Modulus::from_str("b a").is_err());
    }

    /// Tests whether a false string (negative) returns an error.
    #[test]
    fn false_sign() {
        assert!(Modulus::from_str("-42").is_err());
    }
}
