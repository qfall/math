// Copyright © 2023 Marcel Luca Schmidt, Sven Moog
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`Q`] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use super::Q;
use crate::{
    error::MathError,
    integer::Z,
    macros::from::{from_trait, from_type},
    traits::{AsInteger, Pow},
};
use flint_sys::{
    fmpq::{fmpq, fmpq_canonicalise, fmpq_clear, fmpq_get_d, fmpq_set_str},
    fmpz::{fmpz_is_zero, fmpz_set},
};
use std::{ffi::CString, str::FromStr};

impl FromStr for Q {
    type Err = MathError;

    /// Create a [`Q`] rational from a [`String`]
    /// In the string should be two decimal numbers separated by `/`.
    /// Optionally, before one or both of them can be a `-`.
    /// The format of that string looks like this `-12/53`.
    ///
    /// If the number is an integer, the string can be in the format of one.
    /// The format of that string looks like this `-12`.
    /// It is automatically transformed to `-12/1`.
    ///
    /// Parameters:
    /// - `s`: the rational value
    ///
    /// Returns a [`Q`] or an error, if the provided string was not formatted
    /// correctly.
    ///
    /// # Examples
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::rational::Q;
    ///  
    /// let a: Q = "100/3".parse().unwrap();
    /// let b: Q = Q::from_str("100/3").unwrap();
    /// ```
    ///
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::rational::Q;
    ///  
    /// let q: Q = Q::from_str("-10/3").unwrap();
    /// let b: Q = Q::from_str("10/-3").unwrap();
    /// ```
    ///
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::rational::Q;
    ///  
    /// let q: Q = Q::from_str("-10").unwrap();
    /// let b: Q = Q::from_str("10").unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToQInput`](MathError::InvalidStringToQInput)
    /// if the provided string was not formatted correctly.
    /// - Returns a [`MathError`] of type
    /// [`DivisionByZeroError`](MathError::DivisionByZeroError)
    /// if the provided string has `0` as the denominator.
    fn from_str(s: &str) -> Result<Self, MathError> {
        if s.contains(char::is_whitespace) {
            return Err(MathError::InvalidStringToQInput(s.to_owned()));
        }

        // `fmpq::default()` returns the value `0/0`
        let mut value = fmpq::default();

        let c_string = CString::new(s)?;

        // -1 is returned if the string is an invalid input.
        //
        // Given the documentation `c_string.as_ptr()` is freed once c_string is deallocated
        // 'The pointer will be valid for as long as `self` is'
        // For reading more look at the documentation of `.as_ptr()`.
        //
        // since value is set to `0`, if an error occurs, we do not need to free
        // the allocated space manually
        if -1 == unsafe { fmpq_set_str(&mut value, c_string.as_ptr(), 10) } {
            return Err(MathError::InvalidStringToQInput(s.to_owned()));
        };

        // canonical form is expected by other functions
        unsafe { fmpq_canonicalise(&mut value) };

        // if `value.den` is set to `0`, `value.num` is not necessarily `0` as well.
        // hence we do need to free the allocated space of the numerator
        // manually by using `fmpq_clear`
        match unsafe { fmpz_is_zero(&value.den) } {
            0 => Ok(Q { value }),
            _ => {
                unsafe {
                    fmpq_clear(&mut value);
                }
                Err(MathError::DivisionByZeroError(s.to_owned()))
            }
        }
    }
}

impl Q {
    /// Create a new Integer that can grow arbitrary large.
    ///
    /// Parameters:
    /// - `value`: the initial value the integer should have
    ///
    /// Returns the new integer.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::rational::Q;
    ///
    /// let m = Z::from(17);
    ///
    /// let a: Q = Q::from_int(m);
    /// let b: Q = Q::from_int(17);
    /// ```
    pub fn from_int(value: impl Into<Z>) -> Self {
        let value = value.into();
        // this efficient implementation depends on Q::default instantiating 1 as denominator
        let mut out = Q::default();
        unsafe { fmpz_set(&mut out.value.num, &value.value) }
        out
    }

    /// Create a new rational number of type [`Q`] from a [`f64`].
    /// This function works with the exact float it received as input.
    /// Many numbers like `0.1` are not exactly representable as floats and
    /// will therefore not be instantiated as `1/10`.
    ///
    /// Input parameters:
    /// - `value` : The value the rational number will have, provided as a [`f64`]
    ///
    /// Returns a [`Q`].
    ///
    /// # Examples
    /// ```rust
    /// use qfall_math::rational::Q;
    ///
    /// let a: Q = Q::from_f64(0.3);
    /// let a: Q = Q::from_f64(-123.4567);
    /// ```
    pub fn from_f64(value: f64) -> Self {
        let bits: u64 = value.to_bits();
        let sign = if bits >> 63 == 0 {
            Q::ONE
        } else {
            Q::MINUS_ONE
        };
        let mut exponent: i16 = ((bits >> 52) & 0x7ff) as i16;
        let mantissa = if exponent == 0 {
            (bits & 0xfffffffffffff) << 1
        } else {
            // prepend one bit to the mantissa because the most significant bit is implicit
            (bits & 0xfffffffffffff) | 0x10000000000000
        };

        // -1023 because of the offset representation of the exponent
        // -52 because the mantissa is 52 bit long
        exponent -= 1023 + 52;
        let shift = match exponent {
            // This could be optimized with `fmpz_lshift_mpn` once it is part of flint_sys.
            e if e >= 1 => Q::from(2).pow(e).unwrap(),
            e => Q::from((1, 2)).pow(e.abs()).unwrap(),
        };

        sign * Z::from(mantissa) * shift
    }

    from_type!(f32, f64, Q, Q::from_f64);
}

impl<IntegerNumerator: AsInteger, IntegerDenominator: AsInteger>
    From<(IntegerNumerator, IntegerDenominator)> for Q
{
    /// Create a [`Q`] from two integers.
    /// The integer types can be, for example, [`Z`],
    /// [`Zq`](crate::integer_mod_q), [`u32`], [`i64`] or references to these types
    ///
    /// Parameters:
    /// - `num_den_tuple` is a tuple of integers `(numerator, denominator)`
    ///   The first and second element of the tuple may have different integer types.
    ///
    /// Returns a [`Q`] or a [`MathError`]
    ///
    /// # Examples
    /// ```rust
    /// use qfall_math::rational::Q;
    /// use qfall_math::integer::Z;
    ///
    /// let a = Q::from((42, &2));
    /// let b = Q::from((Z::from(84), 4));
    ///
    /// assert_eq!(a, b);
    /// ```
    ///
    /// # Panics ...
    /// - if the denominator is zero.
    fn from(num_den_tuple: (IntegerNumerator, IntegerDenominator)) -> Self {
        unsafe {
            let num = num_den_tuple.0.into_fmpz();
            let den = num_den_tuple.1.into_fmpz();

            if den.0 == 0 {
                panic!("Division by zero");
            }

            let mut value = fmpq { num, den };
            fmpq_canonicalise(&mut value);

            Q { value }
        }
    }
}

impl<T: Into<Z>> From<T> for Q {
    /// Create a new Integer that can grow arbitrary large.
    ///
    /// Parameters:
    /// - `value`: the initial value the integer should have
    ///
    /// Returns the new integer.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use qfall_math::integer::Z;
    ///
    /// let a: Q = Q::from(17);
    /// let b: Q = Q::from(Z::from(17));
    /// ```
    fn from(value: T) -> Self {
        Q::from_int(value)
    }
}

impl From<f64> for Q {
    /// Create a new rational number of type [`Q`] from a [`f64`].
    /// This function works with the bit representation of the float it received as input.
    /// Floats like `0.1` that are not completely representable,
    /// will not be instantiated as `1/10`.
    ///
    /// Input parameters:
    /// - `value` : The value the rational number will have, provided as a [`f64`]
    ///
    /// Returns a [`Q`].
    ///
    /// # Examples
    /// ```rust
    /// use qfall_math::rational::Q;
    ///
    /// let a: Q = Q::from(0.3);
    /// let a: Q = Q::from(-123.4567);
    /// ```
    fn from(value: f64) -> Self {
        Q::from_f64(value)
    }
}

from_trait!(f32, Q, Q::from_f32);

impl From<&Q> for f64 {
    /// Convert a rational [`Q`] into an [`f64`].
    /// The value is rounded to the closest [`f64`] representation.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    ///
    /// let one_half = Q::from((1,2));
    /// let float = f64::from(&one_half);
    ///
    /// assert_eq!(0.5, float);
    /// ```
    fn from(value: &Q) -> Self {
        unsafe { fmpq_get_d(&value.value) }
    }
}

impl From<&Q> for Q {
    /// An alias for clone.
    /// It makes the use of generic `Into<Q>` types easier.
    fn from(value: &Q) -> Self {
        value.clone()
    }
}

#[cfg(test)]
mod tests_from_str {
    use crate::rational::Q;
    use std::str::FromStr;

    /// Ensure that initialization with large numerators and denominators works.
    #[test]
    fn max_int_positive() {
        let mut s1 = (i64::MAX).to_string();
        s1.push('/');
        s1.push_str(&(i64::MAX).to_string());

        let mut s2 = ("1/").to_string();
        s2.push_str(&(i64::MAX).to_string());

        assert!(Q::from_str(&(i64::MAX).to_string()).is_ok());
        assert!(Q::from_str(&s1).is_ok());
        assert!(Q::from_str(&s2).is_ok());
    }

    /// Ensure that initialization with large numerators and denominators
    /// (larger than i64) works.
    #[test]
    fn big_positive() {
        let mut s1 = "1".repeat(65);
        s1.push('/');
        s1.push_str(&"1".repeat(65));

        let mut s2 = ("1/").to_string();
        s2.push_str(&"1".repeat(65));

        assert!(Q::from_str(&"1".repeat(65)).is_ok());
        assert!(Q::from_str(&s1).is_ok());
        assert!(Q::from_str(&s2).is_ok());
    }

    /// Ensure that initialization with large negative numerators and
    /// denominators works.
    #[test]
    fn max_int_negative() {
        let mut s1 = (i64::MIN).to_string();
        s1.push('/');
        s1.push_str(&(i64::MIN).to_string());

        let mut s2 = ("1/").to_string();
        s2.push_str(&(i64::MIN).to_string());

        assert!(Q::from_str(&(i64::MIN).to_string()).is_ok());
        assert!(Q::from_str(&s1).is_ok());
        assert!(Q::from_str(&s2).is_ok());
    }

    /// Ensure that initialization with large negative numerators and
    /// denominators (larger than [`i64`]) works.
    #[test]
    fn big_negative() {
        let mut s1 = "-".to_string();
        s1.push_str(&"1".repeat(65));
        s1.push('/');
        s1.push_str(&"1".repeat(65));

        let mut s2 = ("-1/").to_string();
        s2.push_str(&"1".repeat(65));

        assert!(Q::from_str(&"1".repeat(65)).is_ok());
        assert!(Q::from_str(&s1).is_ok());
        assert!(Q::from_str(&s2).is_ok());
    }

    /// Ensure that an initialization with two minus works.
    #[test]
    fn no_error_both_minus() {
        assert!(Q::from_str("-3/-2").is_ok());
    }

    /// Ensure that wrong initialization yields an Error.
    #[test]
    fn error_wrong_letters() {
        assert!(Q::from_str("hbrkt35itu3gg").is_err());
    }

    /// Ensure that wrong initialization yields an Error.
    #[test]
    fn error_wrong_order() {
        assert!(Q::from_str("3/2-").is_err());
    }

    /// Ensure that wrong initialization yields an Error.
    #[test]
    fn error_two_divisions() {
        assert!(Q::from_str("3/2/4").is_err());
    }

    /// Ensure that wrong initialization yields an Error.
    #[test]
    fn error_wrong_minus() {
        assert!(Q::from_str("-3-4/2").is_err());
    }

    /// Ensure that wrong initialization yields an Error.
    #[test]
    fn error_whitespace_mid() {
        assert!(Q::from_str("876/ 543").is_err());
    }

    /// Ensure that wrong initialization yields an Error.
    #[test]
    fn error_whitespace_start() {
        assert!(Q::from_str(" 876543").is_err());
    }

    /// Ensure that wrong initialization yields an Error.
    #[test]
    fn error_whitespace_end() {
        assert!(Q::from_str("876543 ").is_err());
    }

    /// Ensure that wrong initialization yields an Error.
    #[test]
    fn error_whitespace_minus() {
        assert!(Q::from_str("- 876543").is_err());
    }

    /// Ensure that values returned by [`Q::from_str()`] are canonical.
    #[test]
    fn canonical_result() {
        let one_1 = Q::from_str("1/1").unwrap();
        let one_2 = Q::from_str("2/2").unwrap();
        let one_3 = Q::from_str("-42/-42").unwrap();

        let zero_1 = Q::from_str("0/1").unwrap();
        let zero_2 = Q::from_str("0/42").unwrap();

        assert_eq!(one_1, one_2);
        assert_eq!(one_1, one_3);
        assert_eq!(zero_1, zero_2);
    }
}

#[cfg(test)]
mod test_from_int_int {
    use crate::integer::Z;
    use crate::integer_mod_q::Zq;
    use crate::rational::Q;

    /// Test that the different combinations of rust integers, [`Z`], and [`Zq`]
    /// in their owned and borrowed form can be used to create a [`Q`].
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
        let zq = Zq::from((10, 20));

        // owned, owned the same type in numerator and denominator
        let _ = Q::from((int_8, int_8));
        let _ = Q::from((int_16, int_16));
        let _ = Q::from((int_32, int_32));
        let _ = Q::from((int_64, int_64));
        let _ = Q::from((uint_8, uint_8));
        let _ = Q::from((uint_16, uint_16));
        let _ = Q::from((uint_32, uint_32));
        let _ = Q::from((uint_64, uint_64));
        let _ = Q::from((z.clone(), z.clone()));
        let _ = Q::from((zq.clone(), zq.clone()));

        // borrowed, borrowed the same type in numerator and denominator
        let _ = Q::from((&int_8, &int_8));
        let _ = Q::from((&int_16, &int_16));
        let _ = Q::from((&int_32, &int_32));
        let _ = Q::from((&int_64, &int_64));
        let _ = Q::from((&uint_8, &uint_8));
        let _ = Q::from((&uint_16, &uint_16));
        let _ = Q::from((&uint_32, &uint_32));
        let _ = Q::from((&uint_64, &uint_64));
        let _ = Q::from((&z, &z));
        let _ = Q::from((&zq, &zq));

        // From now on assume that i/u8, i/u16, i/u32 and i/u64 behave the same.
        // This assumption is reasonable, since their implementation is the same.

        // owned, owned mixed types
        let _ = Q::from((int_8, z.clone()));
        let _ = Q::from((zq.clone(), z.clone()));
        let _ = Q::from((z.clone(), int_8));
        let _ = Q::from((z.clone(), zq.clone()));
        let _ = Q::from((int_8, zq.clone()));
        let _ = Q::from((zq.clone(), int_8));

        // owned, borrowed mixed types
        let _ = Q::from((int_8, &z));
        let _ = Q::from((zq.clone(), &z));
        let _ = Q::from((z.clone(), &int_8));
        let _ = Q::from((z.clone(), &zq));
        let _ = Q::from((int_8, &zq));
        let _ = Q::from((zq.clone(), &int_8));

        // borrowed, owned mixed types
        let _ = Q::from((&int_8, z.clone()));
        let _ = Q::from((&zq, z.clone()));
        let _ = Q::from((&z, int_8));
        let _ = Q::from((&z, zq.clone()));
        let _ = Q::from((&int_8, zq.clone()));
        let _ = Q::from((&zq, int_8));

        // borrowed, borrowed mixed types
        let _ = Q::from((&int_8, &z));
        let _ = Q::from((&zq, &z));
        let _ = Q::from((&z, &int_8));
        let _ = Q::from((&z, &zq));
        let _ = Q::from((&int_8, &zq));
        let _ = Q::from((&zq, &int_8));
    }

    /// Ensure that large parameters work (FLINT uses pointer representation).
    #[test]
    fn working_large() {
        let numerator = u64::MAX;
        let denominator = u64::MAX - 1;
        let numerator_z = Z::from(numerator);
        let denominator_z = Z::from(denominator);

        let q_1 = Q::from((numerator, denominator));
        let q_2 = Q::from((numerator_z, denominator_z));

        assert_eq!(q_1, q_2);
    }

    /// Test with zero denominator (not valid -> should lead to an error)
    #[test]
    #[should_panic]
    fn divide_by_zero() {
        let _ = Q::from((10, 0));
    }

    /// Test with either negative denominator or numerator
    #[test]
    fn negative_small() {
        let numerator = 10;
        let denominator = -1;

        let q_1 = Q::from((numerator, denominator));
        let q_2 = Q::from((-numerator, -denominator));

        assert_eq!(q_1, q_2);
    }

    /// Ensure that the result is canonical for small parameters.
    #[test]
    fn canonical_small() {
        let numerator = 10;
        let denominator = 1;

        let q_1 = Q::from((numerator, denominator));
        let q_2 = Q::from((-numerator, -denominator));
        let q_3 = Q::from((numerator * 2, denominator * 2));

        let q_4_negative = Q::from((-numerator, denominator));
        let q_5_negative = Q::from((numerator, -denominator));

        assert_eq!(q_1, q_2);
        assert_eq!(q_1, q_3);

        assert_eq!(q_4_negative, q_5_negative);
    }

    /// Ensure that the result is canonical for large parameters.
    #[test]
    fn canonical_large() {
        let numerator = i64::MAX;
        let denominator = i64::MAX - 1;

        let numerator_z = Z::from(numerator);
        let denominator_z = Z::from(denominator);

        let q_1 = Q::from((numerator, denominator));
        let q_2 = Q::from((-numerator, -denominator));
        let q_3 = Q::from((&numerator_z, &denominator_z));
        let q_4 = Q::from((&numerator_z * 2, &denominator_z * 2));
        let q_5_negative = Q::from((-1 * &numerator_z, &denominator_z));
        let q_6_negative = Q::from((&numerator_z, -1 * &denominator_z));

        assert_eq!(q_1, q_2);
        assert_eq!(q_1, q_3);
        assert_eq!(q_1, q_4);
        assert_eq!(q_5_negative, q_6_negative);
    }
}

#[cfg(test)]
mod test_try_from_int_int {
    use crate::integer::Z;
    use crate::rational::Q;

    /// Test the different borrowed parameter types with small numerator and denominator.
    #[test]
    fn test_types_borrowed_small() {
        let numerator = 10;
        let denominator = 15;

        let q_1 = Q::try_from((&(numerator as u8), &(denominator as i8))).unwrap();
        let q_2 = Q::try_from((&(numerator as u16), &(denominator as i16))).unwrap();
        let q_3 = Q::try_from((&(numerator as u32), &(denominator))).unwrap();
        let q_4 = Q::try_from((&(numerator as u64), &(denominator as i64))).unwrap();
        let q_5 = Q::try_from((&Z::from(numerator), &Z::from(denominator))).unwrap();

        let q_6 = Q::try_from((&(numerator as i16), &(denominator as u16))).unwrap();
        let q_7 = Q::try_from((&(numerator as i16), &(denominator as i16))).unwrap();

        assert_eq!(q_1, q_2);
        assert_eq!(q_1, q_3);
        assert_eq!(q_1, q_4);
        assert_eq!(q_1, q_5);
        assert_eq!(q_1, q_6);
        assert_eq!(q_1, q_7);
    }

    /// Ensure that large parameters work (FLINT uses pointer representation).
    #[test]
    fn working_large() {
        let numerator = u64::MAX;
        let denominator = u64::MAX - 1;
        let numerator_z = Z::from(numerator);
        let denominator_z = Z::from(denominator);

        let q_1 = Q::try_from((&numerator, &denominator)).unwrap();
        let q_2 = Q::try_from((&numerator_z, &denominator_z)).unwrap();

        assert_eq!(q_1, q_2);
    }

    /// Test with zero denominator (not valid -> should lead to an error)
    #[test]
    #[should_panic]
    fn divide_by_zero() {
        let numerator = 10;
        let denominator = 0;

        let _ = Q::try_from((&numerator, &denominator));
    }

    /// Test with either negative denominator or numerator
    #[test]
    fn negative_small() {
        let numerator = 10;
        let denominator = -1;

        let q_1 = Q::try_from((&numerator, &denominator)).unwrap();
        let q_2 = Q::try_from((&-numerator, &-denominator)).unwrap();

        assert_eq!(q_1, q_2);
    }

    /// Ensure that the result is canonical for small parameters.
    #[test]
    fn canonical_small() {
        let numerator = 10;
        let denominator = 1;

        let q_1 = Q::try_from((&numerator, &denominator)).unwrap();
        let q_2 = Q::try_from((&-numerator, &-denominator)).unwrap();
        let q_3 = Q::try_from((&(numerator * 2), &(denominator * 2))).unwrap();

        let q_4_negative = Q::try_from((&-numerator, &denominator)).unwrap();
        let q_5_negative = Q::try_from((&numerator, &-denominator)).unwrap();

        assert_eq!(q_1, q_2);
        assert_eq!(q_1, q_3);

        assert_eq!(q_4_negative, q_5_negative);
    }

    /// Ensure that the result is canonical for large parameters.
    #[test]
    fn canonical_large() {
        let numerator = i64::MAX;
        let denominator = i64::MAX - 1;

        let numerator_z = Z::from(numerator);
        let denominator_z = Z::from(denominator);

        let q_1 = Q::try_from((&numerator, &denominator)).unwrap();
        let q_2 = Q::try_from((&-numerator, &-denominator)).unwrap();
        let q_3 = Q::try_from((&numerator_z, &denominator_z)).unwrap();
        let q_4 =
            Q::try_from((&(&numerator_z * Z::from(2)), &(&denominator_z * Z::from(2)))).unwrap();
        let q_5_negative = Q::try_from((&(&numerator_z * Z::from(-1)), &denominator_z)).unwrap();
        let q_6_negative = Q::try_from((&numerator_z, &(&denominator_z * Z::from(-1)))).unwrap();

        assert_eq!(q_1, q_2);
        assert_eq!(q_1, q_3);
        assert_eq!(q_1, q_4);
        assert_eq!(q_5_negative, q_6_negative);
    }
}

#[cfg(test)]
mod test_from_z {
    use super::Q;
    use crate::integer::Z;

    /// Ensure that the `from_int` function is available and works correctly for
    /// small and large instances of [`Z`] and structs implementing [`Into<Z>`].
    #[test]
    fn large_small_numbers() {
        let z_1 = Z::from(u64::MAX);
        let z_2 = Z::from(17);

        assert_eq!(Q::from(u64::MAX), Q::from_int(z_1));
        assert_eq!(Q::from(17), Q::from_int(z_2));
    }

    /// Ensure that the [`From`] trait is available and works correctly for
    /// small and large instances of [`Z`].
    #[test]
    fn from_trait() {
        let z_1 = Z::from(u64::MAX);
        let z_2 = Z::from(17);

        assert_eq!(Q::from(u64::MAX), Q::from(z_1));
        assert_eq!(Q::from(17), Q::from(z_2));
    }

    /// Ensure that all types that can be turned into an [`Z`]
    /// can be used to instantiate a [`Q`]
    #[test]
    fn from_into_z() {
        let _ = Q::from(u8::MAX);
        let _ = Q::from(u16::MAX);
        let _ = Q::from(u32::MAX);
        let _ = Q::from(u64::MAX);

        let _ = Q::from(i8::MIN);
        let _ = Q::from(i16::MIN);
        let _ = Q::from(i32::MIN);
        let _ = Q::from(i64::MIN);
    }
}

#[cfg(test)]
mod test_from_float {
    use super::Q;
    use std::{
        f64::consts::{E, LN_10, LN_2},
        str::FromStr,
    };

    /// Test that a large number is correctly converted from float.
    #[test]
    fn large_value() {
        // This is the exact value stored when creating a float with the value 1e+100
        let a: f64 = 10000000000000000159028911097599180468360808563945281389781327557747838772170381060813469985856815104.0;

        let q = Q::from(a);

        let cmp = Q::from_str("10000000000000000159028911097599180468360808563945281389781327557747838772170381060813469985856815104")
                    .unwrap();
        assert_eq!(q, cmp);
    }

    // Test that a small number is correctly converted from float.
    #[test]
    #[allow(clippy::excessive_precision)]
    fn small_value() {
        // This is the exact value stored when creating a float with the value 0.1
        let a: f64 = 0.1000000000000000055511151231257827021181583404541015625;

        let q = Q::from(a);

        let cmp = Q::from_str("1000000000000000055511151231257827021181583404541015625/10000000000000000000000000000000000000000000000000000000")
            .unwrap();
        assert_eq!(q, cmp);
    }

    /// Enure that the from works correctly for positive values
    #[test]
    fn positive() {
        let numerator = 150001;
        let denominator = 16;

        let value = Q::from(numerator as f64 / denominator as f64);

        let cmp = Q::from((numerator, denominator));
        assert_eq!(cmp, value)
    }

    /// Enure that the from works correctly for positive values
    #[test]
    fn negative() {
        let numerator = 150001;
        let denominator = -8;

        let value = Q::from(numerator as f64 / denominator as f64);

        let cmp = Q::from((numerator, denominator));
        assert_eq!(cmp, value)
    }

    /// Ensure that the [`From`] trait is available for [`f64`] constants
    #[test]
    fn from_trait() {
        let _ = Q::from(E);
        let _ = Q::from(LN_10);
        let _ = Q::from(LN_2);
    }

    /// test availability for [`f32`]
    #[test]
    fn from_f32_available() {
        let f: f32 = 42.17;

        let _ = Q::from(f);
        let _ = Q::from_f32(f);
    }
}

#[cfg(test)]
mod test_into_float {
    use super::*;

    /// Ensure that `1/2` is correctly converted to `0.5`.
    /// Special about `0.5` is that it can be exactly represented as a float.
    #[test]
    fn one_half() {
        let one_half = Q::from((1, 2));
        let float = f64::from(&one_half);

        assert_eq!(0.5, float);
    }

    /// Ensure that a roundtrip [`f64`] -> [`Q`] -> [`f64`]
    /// does not change the value.
    #[test]
    fn round_trip() {
        let start_values = vec![
            0.0,
            0.1,
            f64::MAX,
            f64::MIN,
            f64::MIN_POSITIVE,
            f64::EPSILON,
        ];

        for start in start_values {
            let end = f64::from(&Q::from(start));

            assert_eq!(start, end);
        }
    }
}

#[cfg(test)]
mod test_from_q_ref {
    use crate::rational::Q;

    /// Ensure that [`Q`] can be created from [`&Q`].
    #[test]
    fn availability() {
        let q = Q::from(u64::MAX);

        let _ = Q::from(&q);
    }
}
