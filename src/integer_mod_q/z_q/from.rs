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
    /// Create [`Zq`] from two [`Z`] values.
    ///
    /// This function creates a copy of the value and creates a new [`Modulus`].
    /// Therefore, it should be avoided to create multiple values with the
    /// same [`Modulus`] with this function to improve performance.
    /// It is better to use [`Zq::from_z_modulus()`] instead.
    ///
    /// Parameters:
    /// - `value` defines the value of the new [`Zq`].
    /// - `modulus` is used to create a new [`Modulus`] context that will be
    ///   used by [`Zq`].
    ///
    /// Returns the new `value` mod `modulus` as a [`Zq`].
    ///
    /// # Example
    /// ```
    /// # use math::error::MathError;
    /// use math::integer::Z;
    /// use math::integer_mod_q::Zq;
    ///
    /// let value_a = Z::from(42);
    /// let value_b = Z::from(1337+42);
    /// let modulus = Z::from(1337);
    ///
    /// let answer_a = Zq::try_from_z_z(&value_a, &modulus)?;
    /// let answer_b = Zq::try_from_z_z(&value_b, &modulus)?;
    ///
    /// // TODO: assert_eq!(answer_a, answer_b); once equal for Zq is implemented
    /// # Ok::<(), MathError>(())
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///   [`InvalidIntToModulus`](MathError::InvalidIntToModulus) if the
    ///   provided value is not greater than `0`.
    pub fn try_from_z_z(value: &Z, modulus: &Z) -> Result<Self, MathError> {
        let modulus = Modulus::try_from_z(modulus)?;

        Ok(Self::from_z_modulus(value, &modulus))
    }

    /// Create [`Zq`] from a [`Z`] values and a [`Modulus`].
    ///
    /// As the [`Modulus`] object counts its references and
    /// its value itself is not cloned when a [`Modulus`] struct is cloned,
    /// we clone the wrapping [`Modulus`] object everytime.
    ///
    /// Parameters:
    /// - `value` defines the value of the new [`Zq`].
    /// - `modulus` is the modulus used by [`Zq`].
    ///
    /// Returns the new `value` mod `modulus` as a [`Zq`].
    ///
    /// # Example
    /// ```
    /// # use math::error::MathError;
    /// use math::integer::Z;
    /// use math::integer_mod_q::{Modulus, Zq};
    ///
    /// let value = Z::from(42);
    /// let modulus = Modulus::try_from(&Z::from(100))?;
    ///
    /// let answer_a = Zq::from_z_modulus(&value, &modulus);
    /// # Ok::<(), MathError>(())
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

    /// Create [`Zq`] from two values that can be converted to [`Z`].
    /// For example, [`i64`] and [`u32`].
    ///
    /// The parameters have to implement the [`Into<Z>`] trait, which is
    /// automatically the case if [`Z`] implements the [`From`] trait for this type.
    /// The first and second element of the tuple may have different types.
    ///
    /// Parameters:
    /// - `value` is the value of the new [`Zq`].
    /// - `modulus` defines the new [`Modulus`], which is part of [`Zq`].
    ///
    /// Returns the `value` mod `modulus` as a [`Zq`].
    ///
    /// # Example
    /// ```
    /// # use math::error::MathError;
    /// use math::integer::Z;
    /// use math::integer_mod_q::Zq;
    ///
    /// let value_a: Z = Z::from(42);
    /// let value_b: u64 = 1337+42;
    /// let modulus: i32 = 1337;
    ///
    /// let answer_a = Zq::try_from_int_int(value_a, modulus)?;
    /// let answer_b = Zq::try_from_int_int(value_b, modulus)?;
    ///
    /// // TODO: assert_eq!(answer_a, answer_b);
    /// # Ok::<(), MathError>(())
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///   [`InvalidIntToModulus`](MathError::InvalidIntToModulus) if the
    ///   provided value is not greater than `0`.
    pub fn try_from_int_int<T1: Into<Z>, T2: Into<Z>>(
        value: T1,
        modulus: T2,
    ) -> Result<Self, MathError> {
        let modulus: Z = modulus.into();
        let value: Z = value.into();
        Zq::try_from_z_z(&value, &modulus)
    }
}

impl<T1: Into<Z>, T2: Into<Z>> TryFrom<(T1, T2)> for Zq {
    type Error = MathError;
    /// Implements the [`TryFrom`] trait. It is used to create [`Zq`] from a tuple
    /// with two values that can be converted into [`Z`].
    ///
    /// The parameters have to implement the [`Into<Z>`] trait, which is
    /// automatically the case if [`Z`] implements the [`From`] trait for this type.
    /// The first and second element of the tuple may have different types.
    ///
    /// Parameters:
    /// - `value_modulus_tuple` is a tuple `(value, modulus)`:
    ///     - The first value defines the value of the new [`Zq`].
    ///     - The second value defines the new [`Modulus`], which is part of [`Zq`].
    ///
    /// Returns the `value` mod `modulus` as a [`Zq`].
    ///
    /// # Example
    /// ```
    /// # use math::error::MathError;
    /// use math::integer::Z;
    /// use math::integer_mod_q::Zq;
    ///
    /// let value_a: Z = Z::from(42);
    /// let value_b: u64 = 1337+42;
    /// let modulus: i32 = 1337;
    ///
    /// let answer_a = Zq::try_from((value_a, modulus))?;
    /// let answer_b = Zq::try_from((value_b, modulus))?;
    ///
    /// // TODO: assert_eq!(answer_a, answer_b);
    /// # Ok::<(), MathError>(())
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///   [`InvalidIntToModulus`](MathError::InvalidIntToModulus) if the
    ///   provided value is not greater than `0`.
    fn try_from(value_modulus_tuple: (T1, T2)) -> Result<Self, Self::Error> {
        let modulus = value_modulus_tuple.1;
        let value = value_modulus_tuple.0;
        Zq::try_from_int_int(value, modulus)
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
    /// # Example:
    /// ```
    /// use std::str::FromStr;
    /// use math::integer_mod_q::Zq;
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
    /// if the provided value is not greater than `0`.
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
        let modulus = Modulus::try_from(&Z::from(15)).unwrap();

        let _ = Zq::from_z_modulus(&value, &modulus);
    }

    /// Test with large value and modulus (FLINT uses pointer representation).
    #[test]
    fn working_large() {
        let value = Z::from(u64::MAX - 1);
        let modulus = Modulus::try_from(&Z::from(u64::MAX)).unwrap();

        let _ = Zq::from_z_modulus(&value, &modulus);
    }
}

#[cfg(test)]
mod test_try_from_z_z {
    use super::Zq;
    use crate::integer::Z;

    /// Test with small valid value and modulus.
    #[test]
    fn working_small() {
        let value = Z::from(10);
        let modulus = Z::from(15);

        let answer = Zq::try_from_z_z(&value, &modulus);
        assert!(answer.is_ok());
    }

    /// Test with large value and modulus (FLINT uses pointer representation).
    #[test]
    fn working_large() {
        let value = Z::from(u64::MAX - 1);
        let modulus = Z::from(u64::MAX);

        let answer = Zq::try_from_z_z(&value, &modulus);

        assert!(answer.is_ok());
    }

    /// Test with zero modulus (not valid)
    #[test]
    fn modulus_zero() {
        let value = Z::from(10);
        let modulus = Z::ZERO;

        let new_zq = Zq::try_from_z_z(&value, &modulus);

        assert!(new_zq.is_err());
    }

    /// Test with negative modulus (not valid)
    #[test]
    fn modulus_negative() {
        let value = Z::from(10);
        let modulus = Z::from(-1);

        let new_zq = Zq::try_from_z_z(&value, &modulus);

        assert!(new_zq.is_err());
    }
}

#[cfg(test)]
mod test_try_from_trait {

    use crate::{integer::Z, integer_mod_q::Zq};

    /// Showcase some of the different types supported by the trait.
    #[test]
    fn types_example() {
        // rust integers supported
        assert!(Zq::try_from((1u8, 2u16)).is_ok());
        assert!(Zq::try_from((1u32, 2u64)).is_ok());
        assert!(Zq::try_from((1i8, 2i16)).is_ok());
        assert!(Zq::try_from((1i32, 2i64)).is_ok());

        // [`Z`] supported
        assert!(Zq::try_from((Z::from(1), Z::from(2))).is_ok());
    }

    /// Ensure that the modulus calculation is performed at initialization.
    #[test]
    fn modulus_at_initialization() {
        let a = Zq::try_from((0, 10)).unwrap();
        let b = Zq::try_from((10, 10)).unwrap();

        // TODO: use Zq equal once implemented.
        assert_eq!(&a.value, &b.value);
        assert_eq!(&a.modulus, &b.modulus);
    }

    /// Test with small valid value and modulus.
    #[test]
    fn working_small() {
        let new_zq = Zq::try_from((10, 15));

        assert!(new_zq.is_ok());
    }

    /// Test with large value and modulus (FLINT uses pointer representation).
    #[test]
    fn working_large() {
        let new_zq = Zq::try_from((u64::MAX - 1, u64::MAX));

        assert!(new_zq.is_ok());
    }

    /// Test with zero modulus (not valid)
    #[test]
    fn modulus_zero() {
        let new_zq = Zq::try_from((10, 0));

        assert!(new_zq.is_err());
    }

    /// Test with negative modulus (not valid)
    #[test]
    fn modulus_negative() {
        let new_zq = Zq::try_from((10, -1));

        assert!(new_zq.is_err());
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
