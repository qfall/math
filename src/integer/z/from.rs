// Copyright © 2023 Sven Moog, Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to create a [`Z`] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [`From`] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use super::Z;
use crate::{
    error::MathError, integer_mod_q::Modulus, macros::for_others::implement_empty_trait_owned_ref,
    traits::AsInteger,
};
use flint_sys::fmpz::{fmpz, fmpz_combit, fmpz_get_si, fmpz_set, fmpz_set_str};
use std::{ffi::CString, str::FromStr};

impl Z {
    #[allow(dead_code)]
    /// Create a new Integer that can grow arbitrary large.
    ///
    /// Parameters:
    /// - `value`: the initial value the integer should have
    ///
    /// Returns the new integer.
    ///
    /// # Safety
    /// Since the parameter is a reference, it still has to be
    /// properly cleared outside this function.
    /// For example, by the drop trait of [`Z`].
    ///
    /// # Examples
    /// ```compile_fail
    /// use qfall_math::integer::Z;
    ///
    /// let z = Z::from(0);
    ///
    /// let a: Z = Z::from_fmpz_ref(&z.value);
    /// ```
    /// ```compile_fail
    /// use qfall_math::integer::Z;
    /// use flint_sys::fmpz::{fmpz,fmpz_clear};
    ///
    /// let value = fmpz(0);
    ///
    /// let a: Z = Z::from_fmpz_ref(&value);
    ///
    /// unsafe{fmpz_clear(&mut value)}
    /// ```
    pub(crate) fn from_fmpz_ref(value: &fmpz) -> Self {
        let mut out = Z::default();
        unsafe {
            fmpz_set(&mut out.value, value);
        }
        out
    }

    #[allow(dead_code)]
    /// Create a new Integer that can grow arbitrary large.
    ///
    /// Parameters:
    /// - `value`: the initial value the integer should have
    ///
    /// Returns the new integer.
    ///
    /// # Safety
    /// This function takes ownership. The caller has to ensure that the [`fmpz`]
    /// is not dropped somewhere else. This means that calling this function
    /// with a [`fmpz`] that is wrapped in a different data type is not allowed.
    ///
    /// # Examples
    /// ```compile_fail
    /// use qfall_math::integer::Z;
    /// use flint_sys::fmpz::fmpz;
    ///
    /// let value = fmpz(0);
    ///
    /// let a: Z = Z::from_fmpz(value);
    /// ```
    pub(crate) unsafe fn from_fmpz(value: fmpz) -> Self {
        Z { value }
    }

    /// Create a [`Z`] integer from a [`String`]. This function takes a base in which the number is represented between `2` and `62`
    ///
    /// Parameters:
    /// - `s`: the integer value as a string
    /// - `base`: the base in which the integer is represented
    ///
    /// Returns a [`Z`] or an error, if the provided string was not formatted
    /// correctly or the base is out bounds.
    ///
    /// # Examples:
    /// ```
    /// use qfall_math::integer::Z;
    ///  
    /// let a: Z = Z::from_str_b("100", 2).unwrap();
    /// assert_eq!(Z::from(4), a);
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if the
    /// base is not between `2` and `62`.
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToCStringInput`](MathError::InvalidStringToCStringInput)
    /// if the provided string contains a Nul byte.
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToZInput`](MathError::InvalidStringToZInput)
    /// if the provided string was not formatted correctly.
    pub fn from_str_b(s: &str, base: i32) -> Result<Self, MathError> {
        if !(2..=62).contains(&base) {
            return Err(MathError::OutOfBounds(
                "between 2 and 62".to_owned(),
                base.to_string(),
            ));
        }

        if s.contains(char::is_whitespace) {
            return Err(MathError::InvalidStringToZInput(s.to_owned()));
        }

        // since |value| = |0| < 62 bits, we do not need to free the allocated space manually
        let mut value: fmpz = fmpz(0);

        let c_string = CString::new(s)?;

        // -1 is returned if the string is an invalid input.
        // Given the documentation `c_string.as_ptr()` is freed once c_string is deallocated
        // 'The pointer will be valid for as long as `self` is'
        // For reading more look at the documentation of `.as_ptr()`.
        match unsafe { fmpz_set_str(&mut value, c_string.as_ptr(), base) } {
            0 => Ok(Z { value }),
            _ => Err(MathError::InvalidStringToZInput(s.to_owned())),
        }
    }

    /// Create a [`Z`] integer from an iterable of [`u8`]s, e.g. a vector of bytes.
    ///
    /// Parameters:
    /// - `bytes`: specifies an iterable of bytes that should be set in the new [`Z`] instance.
    /// The first byte should be the least significant byte, i.e. its first bit the
    /// least significant bit.
    ///
    /// Returns a [`Z`] with the value provided by the byte iterable.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// // instantiate a byte-vector correspinding to "100000001"
    /// // vec![0x01, 0x01] would also be sufficient
    /// let bytes: Vec<u8> = vec![1, 1];
    ///  
    /// let a: Z = Z::from_bytes(&bytes);
    /// assert_eq!(Z::from(257), a);
    /// ```
    pub fn from_bytes(bytes: &[u8]) -> Self {
        let mut res = Z::ZERO;
        for (i, byte) in bytes.iter().enumerate() {
            for j in 0..u8::BITS {
                // if j-th bit of `byte` is `1`, then set `i*8 + j`-th bit in fmpz to `1`
                if (byte >> j & 1) % 2 == 1 {
                    unsafe { fmpz_combit(&mut res.value, (i as u32 * u8::BITS + j) as u64) };
                }
            }
        }
        res
    }
}

/// A trait that indicates for which types the `From for Z` should be implemented.
/// It is used as a workaround to implement the [`From`] trait without colliding
/// with the default implementation for [`Z`] and also to filter out [`Zq`](crate::integer_mod_q::Zq).
trait IntoZ {}

implement_empty_trait_owned_ref!(IntoZ for Modulus u8 u16 u32 u64 i8 i16 i32 i64);
impl IntoZ for &Z {}

impl<Integer: AsInteger + IntoZ> From<Integer> for Z {
    /// Convert an integer to [`Z`].
    ///
    /// # Parameters:
    /// `value` must be a rust integer, [`Modulus`], or a reference of these types.
    ///
    /// Returns a new [`Z`] with the value specified in the parameter.
    ///
    /// # Examples:
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let a = Z::from(10);
    /// let b = Z::from(i64::MAX);
    /// let c = Z::from(&u64::MAX);
    /// ```
    fn from(value: Integer) -> Self {
        match value.get_fmpz_ref() {
            Some(val) => Z::from_fmpz_ref(val),
            None => unsafe {
                let value = value.into_fmpz();
                Z { value }
            },
        }
    }
}

impl FromStr for Z {
    type Err = MathError;

    /// Create a [`Z`] integer from a [`String`]
    /// The format of that string looks like this `(-)12` for the number 12 or -12
    ///
    /// Parameters:
    /// - `s`: the integer value
    ///
    /// Returns a [`Z`] or an error, if the provided string was not formatted
    /// correctly.
    ///
    /// # Examples:
    /// ```
    /// use std::str::FromStr;
    /// use qfall_math::integer::Z;
    ///  
    /// let a: Z = "100".parse().unwrap();
    /// let b: Z = Z::from_str("100").unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToCStringInput`](MathError::InvalidStringToCStringInput)
    /// if the provided string contains a Nul byte.
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToZInput`](MathError::InvalidStringToZInput)
    /// if the provided string was not formatted correctly.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Z::from_str_b(s, 10)
    }
}

impl TryFrom<&Z> for i64 {
    type Error = MathError;

    /// Converts a [`Z`] into an [`i64`]. If the value is either too large
    /// or too small an error is returned.
    ///
    /// Parameters:
    /// - `value`: the value that will be converted into an [`i64`]
    ///
    /// Returns the value as an [`i64`] or an error, if it does not fit
    /// into an [`i64`]
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let max = Z::from(i64::MAX);
    /// assert_eq!(i64::MAX, i64::try_from(&max).unwrap());
    ///
    /// let max = Z::from(u64::MAX);
    /// assert!(i64::try_from(&max).is_err());
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`ConversionError`](MathError::ConversionError)
    /// if the value does not fit into an [`i64`]
    fn try_from(value: &Z) -> Result<Self, Self::Error> {
        // fmpz_get_si returns the i64::MAX or respectively i64::MIN
        // if the value is too large/small to fit into an [`i64`].
        // Hence we are required to manually check if the value is actually correct
        let value_i64 = unsafe { fmpz_get_si(&value.value) };
        if &Z::from(value_i64) == value {
            Ok(value_i64)
        } else {
            Err(MathError::ConversionError(format!(
                "The provided value has to fit into an i64 and it doesn't as the 
                provided value is {}.",
                value
            )))
        }
    }
}

impl From<&Vec<u8>> for Z {
    /// Converts a byte vector of type [`u8`] to [`Z`] using [`Z::from_bytes`].
    fn from(value: &Vec<u8>) -> Self {
        Z::from_bytes(value)
    }
}

impl From<Vec<u8>> for Z {
    /// Converts a byte vector of type [`u8`] to [`Z`] using [`Z::from_bytes`].
    fn from(value: Vec<u8>) -> Self {
        Z::from_bytes(&value)
    }
}

#[cfg(test)]
mod test_from_bytes {
    use super::*;

    /// Checks whether small values are correctly instantiated by `from_bytes`
    /// and different byte representations are valid
    #[test]
    fn small_values() {
        let vec_0: Vec<u8> = vec![0];
        let vec_1: Vec<u8> = vec![0x00, 0x01];
        let vec_2: Vec<u8> = vec![1, 0];

        let res_0 = Z::from_bytes(&vec_0);
        let res_1 = Z::from_bytes(&vec_1);
        let res_2 = Z::from_bytes(&vec_2);

        assert_eq!(Z::ZERO, res_0);
        assert_eq!(Z::from(256), res_1);
        assert_eq!(Z::ONE, res_2);
    }

    /// Checks whether large values are correctly instantiated by `from_bytes`
    /// and different byte representations are valid
    #[test]
    fn large_values() {
        let vec_0: Vec<u8> = vec![255, 255, 255, 255, 255, 255, 255, 255];
        let vec_1: Vec<u8> = vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff];

        let res_0 = Z::from_bytes(&vec_0);
        let res_1 = Z::from_bytes(&vec_1);

        assert_eq!(Z::from(u64::MAX), res_0);
        assert_eq!(Z::from(u64::MAX), res_1);
    }

    /// Checks for availability of `from_bytes` for array-inputs and the `from` trait
    /// for vectors of borrowed and owned types
    #[test]
    fn availability() {
        let arr: [u8; 2] = [0x01, 0x01];
        let vec: Vec<u8> = vec![0x01, 0x01];

        let res_0 = Z::from_bytes(&arr);
        let res_1 = Z::from(&vec);
        let res_2 = Z::from(vec);

        assert_eq!(Z::from(257), res_0);
        assert_eq!(Z::from(257), res_1);
        assert_eq!(Z::from(257), res_2);
    }
}

#[cfg(test)]
/// Test the different implementations for types that implement [`AsInteger`] and [`IntoZ`]
mod tests_from_int {
    use super::*;
    use crate::integer_mod_q::Modulus;

    /// Ensure that the [`From`] trait is available for singed and unsigned integers
    /// of 8, 16, 32, and 64 bit length and for their owned and borrowed variants.
    /// Tested with their maximum value.
    #[test]
    fn rust_int_max() {
        // signed
        let _ = Z::from(i8::MAX);
        let _ = Z::from(i16::MAX);
        let _ = Z::from(i32::MAX);
        let _ = Z::from(i64::MAX);
        let _ = Z::from(&i8::MAX);
        let _ = Z::from(&i16::MAX);
        let _ = Z::from(&i32::MAX);
        let _ = Z::from(&i64::MAX);

        // unsigned
        let _ = Z::from(u8::MAX);
        let _ = Z::from(u16::MAX);
        let _ = Z::from(u32::MAX);
        let _ = Z::from(u64::MAX);
        let _ = Z::from(&u8::MAX);
        let _ = Z::from(&u16::MAX);
        let _ = Z::from(&u32::MAX);
        let _ = Z::from(&u64::MAX);
    }

    /// Ensure that the [`From`] trait is available for singed and unsigned integers
    /// of 8, 16, 32, and 64 bit length and for their owned and borrowed variants.
    /// Tested with their minimum value.
    #[test]
    fn rust_int_min() {
        // signed
        let _ = Z::from(i8::MIN);
        let _ = Z::from(i16::MIN);
        let _ = Z::from(i32::MIN);
        let _ = Z::from(i64::MIN);
        let _ = Z::from(&i8::MIN);
        let _ = Z::from(&i16::MIN);
        let _ = Z::from(&i32::MIN);
        let _ = Z::from(&i64::MIN);

        // unsigned
        let _ = Z::from(u8::MIN);
        let _ = Z::from(u16::MIN);
        let _ = Z::from(u32::MIN);
        let _ = Z::from(u64::MIN);
        let _ = Z::from(&u8::MIN);
        let _ = Z::from(&u16::MIN);
        let _ = Z::from(&u32::MIN);
        let _ = Z::from(&u64::MIN);
    }

    /// Ensure that the [`From`] trait is available for small and large,
    /// borrowed and owned [`Modulus`] instances.
    #[test]
    fn modulus() {
        let val_1 = Z::from(u64::MAX);
        let mod_1 = Modulus::try_from(&val_1).unwrap();
        let val_2 = Z::from(10);
        let mod_2 = Modulus::try_from(&val_2).unwrap();

        assert_eq!(val_1, Z::from(&mod_1));
        assert_eq!(val_2, Z::from(&mod_2));

        assert_eq!(val_1, Z::from(mod_1));
        assert_eq!(val_2, Z::from(mod_2));
    }

    /// Ensure that the [`From`] trait is available for small and large,
    /// borrowed and owned [`Z`] instances.
    #[test]
    fn z() {
        let original_large = Z::from(u64::MAX);
        let original_small = Z::ONE;

        assert_eq!(original_large, Z::from(&original_large));
        assert_eq!(original_large, original_large.clone());

        assert_eq!(original_small, Z::from(&original_small));
        assert_eq!(original_small, Z::ONE);
    }
}

#[cfg(test)]
mod tests_from_str {
    use crate::integer::Z;
    use std::str::FromStr;

    /// Ensure that initialization with large numbers works.
    #[test]
    fn max_int_positive() {
        assert!(Z::from_str(&(i64::MAX).to_string()).is_ok());
    }

    /// Ensure that initialization with large numbers (larger than i64) works.
    #[test]
    fn big_positive() {
        assert!(Z::from_str(&"1".repeat(65)).is_ok());
    }

    /// Ensure that initialization with large negative numbers works.
    #[test]
    fn max_int_negative() {
        assert!(Z::from_str(&(i64::MIN).to_string()).is_ok());
    }

    /// Ensure that initialization with large negative numbers (larger than i64) works.
    #[test]
    fn big_negative() {
        let mut s = "-".to_string();
        s.push_str(&"1".repeat(65));

        assert!(Z::from_str(&s).is_ok());
    }

    /// Ensure that wrong initialization yields an Error.
    #[test]
    fn error_wrong_letters() {
        assert!(Z::from_str("hbrkt35itu3gg").is_err());
    }

    /// Ensure that wrong initialization yields an Error.
    #[test]
    fn error_wrong_order() {
        assert!(Z::from_str("3-2").is_err());
    }

    /// Ensure that wrong initialization yields an Error.
    #[test]
    fn error_rational() {
        assert!(Z::from_str("876/543").is_err());
    }

    /// Ensure that wrong initialization yields an Error.
    #[test]
    fn whitespace_mid() {
        assert!(Z::from_str("876 543").is_err());
    }

    /// Ensure that wrong initialization yields an Error.
    #[test]
    fn whitespace_start() {
        assert!(Z::from_str(" 876543").is_err());
    }

    /// Ensure that wrong initialization yields an Error.
    #[test]
    fn whitespace_end() {
        assert!(Z::from_str("876543 ").is_err());
    }

    /// Ensure that wrong initialization yields an Error.
    #[test]
    fn whitespace_minus() {
        assert!(Z::from_str("- 876543").is_err());
    }
}

#[cfg(test)]
mod test_from_str_b {
    use crate::integer::Z;

    /// ensure that an error is returned, if an invalid base is provided
    #[test]
    fn out_of_bounds() {
        let value = "100010";

        assert!(Z::from_str_b(value, -1).is_err());
        assert!(Z::from_str_b(value, 0).is_err());
        assert!(Z::from_str_b(value, 1).is_err());
        assert!(Z::from_str_b(value, 63).is_err());
    }

    /// ensure that from_str works with a binary-string
    #[test]
    fn from_str_binary() {
        assert_eq!(Z::from(20), Z::from_str_b("10100", 2).unwrap());
        assert_eq!(Z::from(-20), Z::from_str_b("-10100", 2).unwrap());
    }

    /// ensure that from_str works with a hex-string
    #[test]
    fn from_str_hex() {
        assert_eq!(Z::from(160), Z::from_str_b("a0", 16).unwrap());
        assert_eq!(Z::from(-170), Z::from_str_b("-aa", 16).unwrap());
    }
}

#[cfg(test)]
mod test_from_fmpz {
    use super::Z;
    use flint_sys::fmpz::{fmpz, fmpz_set_ui};

    /// Ensure that `from_fmpz` is available for small and large numbers
    #[test]
    fn small_numbers() {
        let fmpz_1 = fmpz(0);
        let fmpz_2 = fmpz(100);

        assert_eq!(unsafe { Z::from_fmpz(fmpz_1) }, Z::ZERO);
        assert_eq!(unsafe { Z::from_fmpz(fmpz_2) }, Z::from(100));
    }

    /// Ensure that `from_fmpz` is available for small and large numbers
    #[test]
    fn large_numbers() {
        let mut fmpz_1 = fmpz(0);
        unsafe { fmpz_set_ui(&mut fmpz_1, u64::MAX) }

        assert_eq!(unsafe { Z::from_fmpz(fmpz_1) }, Z::from(u64::MAX));
    }
}

#[cfg(test)]
mod test_from_fmpz_ref {
    use super::Z;

    /// Ensure that `from_fmpz` is available for small and large numbers
    #[test]
    fn large_small_numbers() {
        let mod_1 = Z::from(u64::MAX);
        let mod_2 = Z::ZERO;

        let _ = Z::from_fmpz_ref(&mod_1.value);
        let _ = Z::from_fmpz_ref(&mod_2.value);
    }
}

#[cfg(test)]
mod test_try_from_into_i64 {
    use crate::integer::Z;

    //// ensure that an error is returned, if the value of the [`Z`]
    /// does not fit into an [`i64`]
    #[test]
    fn overflow() {
        assert!(i64::try_from(&Z::from(u64::MAX)).is_err());
        assert!(i64::try_from(&(-1 * Z::from(u64::MAX))).is_err());
    }

    /// ensure that a correct value is returned for values in bounds.
    #[test]
    fn correct() {
        let min = Z::from(i64::MIN);
        let max = Z::from(i64::MAX);
        let z_42 = Z::from(42);

        assert_eq!(i64::MIN, i64::try_from(&min).unwrap());
        assert_eq!(i64::MAX, i64::try_from(&max).unwrap());
        assert_eq!(0, i64::try_from(&Z::ZERO).unwrap());
        assert_eq!(42, i64::try_from(&z_42).unwrap());
    }
}
