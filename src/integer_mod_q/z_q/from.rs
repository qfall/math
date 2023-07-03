// Copyright © 2023 Sven Moog, Marcel Luca Schmidt, Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`Zq`] value from other types.

use super::Zq;
use crate::{error::MathError, integer::Z, integer_mod_q::Modulus};
use flint_sys::fmpz_mod::fmpz_mod_set_fmpz;
use std::str::FromStr;

impl Zq {
    /// Create [`Zq`] from a [`Z`] values and a [`Modulus`].
    ///
    /// As the [`Modulus`] object counts its references and
    /// its value itself is not cloned when a [`Modulus`] struct is cloned,
    /// we clone the wrapping [`Modulus`] object every time.
    ///
    /// Parameters:
    /// - `value` defines the value of the new [`Zq`].
    /// - `modulus` is the modulus used by [`Zq`].
    ///
    /// Returns the new `value` mod `modulus` as a [`Zq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::integer_mod_q::{Modulus, Zq};
    ///
    /// let value = Z::from(42);
    /// let modulus = Modulus::from(100);
    ///
    /// let answer_a = Zq::from_z_modulus(&value, &modulus);
    /// ```
    pub fn from_z_modulus(value: &Z, modulus: &Modulus) -> Self {
        let mut out = Z::default();

        unsafe {
            // Applies modulus to parameter and saves the new value into `value_fmpz`.
            // => No problem when the `value` parameter is later dropped.
            fmpz_mod_set_fmpz(
                &mut out.value,
                &value.value,
                modulus.get_fmpz_mod_ctx_struct(),
            );
        };

        Self {
            value: out,
            modulus: modulus.clone(),
        }
    }
}

impl<IntegerValue: Into<Z>, IntegerModulus: Into<Modulus>> From<(IntegerValue, IntegerModulus)>
    for Zq
{
    /// Create [`Zq`] from a tuple with the integer and the modulus.
    ///
    /// Parameters:
    /// - `value_modulus_tuple` is a tuple of integers `(value, modulus)`
    ///   The first and second element of the tuple may have different integer types.
    ///
    /// Returns the `value` mod `modulus` as a [`Zq`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::Zq;
    /// use qfall_math::integer::Z;
    ///
    /// let answer_a = Zq::from((1337 + 42, 1337));
    /// let answer_b = Zq::from((Z::from(42), 1337));
    ///
    /// assert_eq!(answer_a, answer_b);
    /// ```
    ///
    /// # Panics ...
    /// - if the modulus is not greater than `1`.
    fn from(value_modulus_tuple: (IntegerValue, IntegerModulus)) -> Self {
        let value = value_modulus_tuple.0.into();
        let modulus = value_modulus_tuple.1.into();

        let mut out = Zq { value, modulus };
        out.reduce();
        out
    }
}

impl FromStr for Zq {
    type Err = MathError;

    /// Create a [`Zq`] integer from a [`String`]
    /// The format of that string looks like this `12 mod 25` for the number 12
    /// under the modulus 25
    ///
    /// Parameters:
    /// - `s`: the integer and modulus value
    ///
    /// Returns a [`Zq`] or an error, if the provided string was not formatted
    /// correctly.
    ///
    /// # Examples:
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::integer_mod_q::Zq;
    ///  
    /// let a: Zq = "100 mod 3".parse().unwrap();
    /// let b: Zq = Zq::from_str("100 mod 3").unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToCStringInput`](MathError::InvalidStringToCStringInput)
    /// if the provided string contains a Nul byte.
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToZqInput`](MathError::InvalidStringToZqInput)
    /// if the provided string was not formatted correctly.
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToZInput`](MathError::InvalidStringToZInput)
    /// if the provided modulus was not formatted correctly to create a [`Z`]
    /// - Returns a [`MathError`] of type
    /// [`InvalidIntToModulus`](MathError::InvalidIntToModulus)
    /// if the provided value is not greater than `1`.
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToCStringInput`](MathError::InvalidStringToCStringInput)
    /// if the provided string contains a Nul byte.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let input_split: Vec<&str> = s.split("mod").collect();
        if input_split.len() != 2 {
            return Err(MathError::InvalidStringToZqInput(s.to_owned()));
        }

        // instantiate both parts of Zq element
        let modulus = Modulus::from_str(input_split[1].trim())?;
        let value = Z::from_str(input_split[0].trim())?;

        let mut out = Self { value, modulus };
        out.reduce();

        Ok(out)
    }
}

impl From<&Zq> for Zq {
    /// An alias for clone.
    /// It makes the use of generic `Into<Zq>` types easier.
    fn from(value: &Zq) -> Self {
        value.clone()
    }
}

#[cfg(test)]
mod test_from_z_modulus {
    // TODO: add more test cases once we have the equal comparison for Zq:
    // 1. Zq initialized with the same and different Modulus object
    //    (same modulus value) and the same number should be equal.
    // 2. assert that the different initialization methods have the same results.
    // 3. assert that the modulus is applied correctly

    use super::{Modulus, Zq};
    use crate::integer::Z;

    /// Test with small valid value and modulus.
    #[test]
    fn working_small() {
        let value = Z::from(10);
        let modulus = Modulus::from(&Z::from(15));

        let _ = Zq::from_z_modulus(&value, &modulus);
    }

    /// Test with large value and modulus (FLINT uses pointer representation).
    #[test]
    fn working_large() {
        let value = Z::from(u64::MAX - 1);
        let modulus = Modulus::from(&Z::from(u64::MAX));

        let _ = Zq::from_z_modulus(&value, &modulus);
    }
}

#[cfg(test)]
mod test_from_trait {
    use crate::{
        integer::Z,
        integer_mod_q::{Modulus, Zq},
    };

    /// Test that the different combinations of rust integers, [`Z`], and [`Modulus`]
    /// in their owned and borrowed form can be used to create a [`Zq`].
    #[test]
    fn different_types() {
        let int_8: i8 = 10;
        let int_16: i16 = 10;
        let int_32: i32 = 10;
        let int_64: i64 = 10;
        let uint_8: u8 = 10;
        let uint_16: u16 = 10;
        let uint_32: u32 = 10;
        let uint_64: u64 = 10;
        let z = Z::from(10);
        let modulus = Modulus::from(10);

        // owned, owned the same type in numerator and denominator
        let _ = Zq::from((int_8, int_8));
        let _ = Zq::from((int_16, int_16));
        let _ = Zq::from((int_32, int_32));
        let _ = Zq::from((int_64, int_64));
        let _ = Zq::from((uint_8, uint_8));
        let _ = Zq::from((uint_16, uint_16));
        let _ = Zq::from((uint_32, uint_32));
        let _ = Zq::from((uint_64, uint_64));
        let _ = Zq::from((z.clone(), z.clone()));
        let _ = Zq::from((modulus.clone(), modulus.clone()));

        // borrowed, borrowed the same type in numerator and denominator
        let _ = Zq::from((&int_8, &int_8));
        let _ = Zq::from((&int_16, &int_16));
        let _ = Zq::from((&int_32, &int_32));
        let _ = Zq::from((&int_64, &int_64));
        let _ = Zq::from((&uint_8, &uint_8));
        let _ = Zq::from((&uint_16, &uint_16));
        let _ = Zq::from((&uint_32, &uint_32));
        let _ = Zq::from((&uint_64, &uint_64));
        let _ = Zq::from((&z, &z));
        let _ = Zq::from((&modulus, &modulus));

        // From now on assume that i/u8, i/u16, i/u32 and i/u64 behave the same.
        // This assumption is reasonable, since their implementation is the same.

        // owned, owned mixed types
        let _ = Zq::from((int_8, z.clone()));
        let _ = Zq::from((z.clone(), int_8));
        let _ = Zq::from((int_8, modulus.clone()));
        let _ = Zq::from((z.clone(), modulus.clone()));
        let _ = Zq::from((modulus.clone(), int_8));
        let _ = Zq::from((modulus.clone(), z.clone()));

        // owned, borrowed mixed types
        let _ = Zq::from((int_8, &z));
        let _ = Zq::from((modulus.clone(), &z));
        let _ = Zq::from((z.clone(), &int_8));
        let _ = Zq::from((z.clone(), &modulus));
        let _ = Zq::from((int_8, &modulus));
        let _ = Zq::from((modulus.clone(), &int_8));

        // borrowed, owned mixed types
        let _ = Zq::from((&int_8, z.clone()));
        let _ = Zq::from((&modulus, z.clone()));
        let _ = Zq::from((&z, int_8));
        let _ = Zq::from((&z, modulus.clone()));
        let _ = Zq::from((&int_8, modulus.clone()));
        let _ = Zq::from((&modulus, int_8));

        // borrowed, borrowed mixed types
        let _ = Zq::from((&int_8, &z));
        let _ = Zq::from((&modulus, &z));
        let _ = Zq::from((&z, &int_8));
        let _ = Zq::from((&z, &modulus));
        let _ = Zq::from((&int_8, &modulus));
        let _ = Zq::from((&modulus, &int_8));
    }

    /// Ensure that the modulus calculation is performed at initialization.
    #[test]
    fn modulus_at_initialization() {
        let a = Zq::from((0, 10));
        let b = Zq::from((10, 10));

        assert_eq!(a, b);
    }

    /// Test with small valid value and modulus.
    #[test]
    fn working_small() {
        let zq_1 = Zq::from((10, 15));
        let zq_2 = Zq::from((Z::from(10), Modulus::from(15)));

        assert_eq!(zq_1, zq_2)
    }

    /// Test with large value and modulus (FLINT uses pointer representation).
    #[test]
    fn working_large() {
        let zq_1 = Zq::from((u64::MAX - 1, u64::MAX));
        let zq_2 = Zq::from((&Z::from(u64::MAX - 1), Modulus::from(u64::MAX)));

        assert_eq!(zq_1, zq_2)
    }

    /// Test with zero modulus (not valid)
    #[test]
    #[should_panic]
    fn modulus_zero() {
        let _ = Zq::from((10, 0));
    }

    /// Test with negative modulus (not valid)
    #[test]
    #[should_panic]
    fn modulus_negative() {
        let _ = Zq::from((10, -1));
    }
}

#[cfg(test)]
mod tests_from_str {
    use crate::integer_mod_q::Zq;
    use std::str::FromStr;

    /// Ensure that initialization with large numbers works.
    #[test]
    fn max_int_positive() {
        assert!(Zq::from_str(&format!("{} mod {}", i64::MAX, u64::MAX)).is_ok());
    }

    /// Ensure that initialization with large numbers (larger than [`i64`]) works.
    #[test]
    fn big_positive() {
        assert!(Zq::from_str(&format!("{} mod {}", u64::MAX, u128::MAX)).is_ok());
    }

    /// Ensure that initialization with large negative numbers works.
    #[test]
    fn max_int_negative() {
        assert!(Zq::from_str(&format!("-{} mod {}", i64::MAX, u64::MAX)).is_ok());
    }

    /// Ensure that initialization with large negative numbers (larger than [`i64`]) works.
    #[test]
    fn big_negative() {
        assert!(Zq::from_str(&format!("-{} mod {}", u64::MAX, u128::MAX)).is_ok());
    }

    /// Ensure that initialization with standard values works.
    #[test]
    fn normal_value() {
        assert!(Zq::from_str("42 mod 5").is_ok());
    }

    /// Ensure that initialization works with leading and trailing whitespaces.
    #[test]
    fn whitespaces_work() {
        assert!(Zq::from_str("    42 mod 5").is_ok());
        assert!(Zq::from_str("42 mod 5    ").is_ok());
        assert!(Zq::from_str("42    mod 5").is_ok());
        assert!(Zq::from_str("42 mod     5").is_ok());
    }

    /// Ensure that initialization yields an error with whitespaces in between.
    #[test]
    fn whitespaces_error() {
        assert!(Zq::from_str("4 2 mod 5").is_err());
        assert!(Zq::from_str("42 mo d 5").is_err());
        assert!(Zq::from_str("42 mod 5 0").is_err());
    }

    /// Ensure that wrong initialization yields an Error.
    #[test]
    fn error_wrong_letters() {
        assert!(Zq::from_str("hbrkt35itu3gg").is_err());
        assert!(Zq::from_str("3-2 mod 3").is_err());
        assert!(Zq::from_str("3 5").is_err());
        assert!(Zq::from_str("3%5").is_err());
        assert!(Zq::from_str("3/5 mod 3").is_err());
    }
}
