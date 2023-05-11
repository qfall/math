// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains helpful functions on [`fmpz`] values in a ring/`modulus` context.

use super::Zq;
use crate::{
    integer::{fmpz_helpers::distance, Z},
    traits::AsInteger,
};
use flint_sys::fmpz::fmpz;

const ZERO_FMPZ: fmpz = fmpz(0);

/// Computes the shortest distance of `self` to the next zero instance
/// regarding the `modulus`.
///
/// WARNING: This function assumes `value` to be reduced,
/// i.e. `0 <= value < modulus`.
///
/// # Examples
/// ```compile_fail
/// use flint_sys::fmpz::fmpz;
/// use qfall_math::integer_mod_q::fmpz_mod_helpers::length;
///
/// let modulus = fmpz(15);
/// let value = fmpz(10);
///
/// let length = length(&value, &modulus);
///
/// assert_eq!(5, length.0);
/// ```
pub(crate) fn length(value: &fmpz, modulus: &fmpz) -> Z {
    let distance_zero = distance(&ZERO_FMPZ, value);
    let distance_modulus = distance(value, modulus);

    // if distance_zero < distance modulus => return distance_zero
    if distance_zero < distance_modulus {
        distance_zero
    } else {
        distance_modulus
    }
}

unsafe impl AsInteger for Zq {
    /// Documentation at [`AsInteger::into_fmpz`]
    unsafe fn into_fmpz(self) -> fmpz {
        AsInteger::into_fmpz(&self.value)
    }

    /// Documentation at [`AsInteger::get_fmpz_ref`]
    fn get_fmpz_ref(&self) -> Option<&fmpz> {
        AsInteger::get_fmpz_ref(&self.value)
    }
}

unsafe impl AsInteger for &Zq {
    /// Documentation at [`AsInteger::into_fmpz`]
    unsafe fn into_fmpz(self) -> fmpz {
        AsInteger::into_fmpz(&self.value)
    }

    /// Documentation at [`AsInteger::get_fmpz_ref`]
    fn get_fmpz_ref(&self) -> Option<&fmpz> {
        AsInteger::get_fmpz_ref(&self.value)
    }
}

#[cfg(test)]
mod test_as_integer_zq {
    use flint_sys::fmpz::{fmpz_clear, fmpz_set, fmpz_set_ui};

    use super::*;

    // Assert that the new fmpz is not related to the old one
    #[test]
    fn small_into_fmpz() {
        let mut value = unsafe {
            let zq = Zq::try_from((Z::from(42), Z::from(100))).unwrap();
            (&zq).into_fmpz()
        }; // z is dropped here

        // create a new `Z` to potentially overwrite the memory
        let _ = Z::from(12);

        let copy = Z::from_fmpz(value);
        assert_eq!(copy, Z::from(42));
    }

    /// Assert that the new [`fmpz`] is not effected by the original for large numbers.
    /// This can not be tested for an owned [`Zq`], since that would violate the
    /// ownership constrain -> not compiling.
    #[test]
    fn original_not_effecting_new_large() {
        let value = unsafe {
            let zq = Zq::try_from((i64::MAX - 1, i64::MAX)).unwrap();
            (&zq).into_fmpz()
        }; // z is dropped here

        // Create new Z values that would likely overwrite the memory of the original `Zq`.
        let _a = Z::from(u64::MAX);
        let _b = Z::from(u64::MAX);

        assert_eq!(Z::from_fmpz(value), Z::from(i64::MAX - 1));
    }

    /// Assert that the new [`fmpz`] is not effecting the original [`Zq`].
    #[test]
    fn new_not_effecting_original_large() {
        let zq = Zq::try_from((i64::MAX - 1, i64::MAX)).unwrap();
        let zq_copy = zq.clone();
        let mut value = unsafe { (&zq).into_fmpz() };

        // Setting the result of into_fmpz to a different value
        // is not effecting the original.
        unsafe { fmpz_set_ui(&mut value, u64::MAX) }
        assert_eq!(zq, zq_copy);

        // Clearing the new fmpz and creating new values that likely
        // occupy the memory of the just cleared value.
        unsafe { fmpz_clear(&mut value) };
        let _ = Z::from(u64::MAX - 1);
        let _ = Z::from(u64::MAX);

        assert_eq!(zq, zq_copy);
    }

    /// Assert that `get_fmpz_ref` returns a correct reference for small values
    #[test]
    fn get_ref_small() {
        let zq = Zq::try_from((10, 100)).unwrap();

        let z_ref = zq.get_fmpz_ref().unwrap();

        let cmp = Z::from_fmpz_ref(z_ref);
        assert_eq!(cmp, Z::from(10))
    }

    /// Assert that `get_fmpz_ref` returns a correct reference for large values
    #[test]
    fn get_ref_large() {
        let z = Z::from(u64::MAX);

        let z_ref = z.get_fmpz_ref().unwrap();
        let mut cmp = Z::default();
        unsafe { fmpz_set(&mut cmp.value, z_ref) };

        assert_eq!(cmp, z)
    }
}

#[cfg(test)]
mod test_length {
    use super::*;
    use crate::integer::Z;

    /// Checks whether lengths for values in rings are computed correctly for all possible cases
    /// (shortest distance to next zero is found) for small values
    #[test]
    fn small_values() {
        let modulus = fmpz(15);
        let pos_1 = fmpz(10);
        let pos_2 = fmpz(7);
        let zero = fmpz(0);

        assert_eq!(Z::from(5), length(&pos_1, &modulus));
        assert_eq!(Z::from(7), length(&pos_2, &modulus));
        assert_eq!(Z::ZERO, length(&zero, &modulus));
        assert_eq!(Z::ZERO, length(&modulus, &modulus));
    }

    /// Checks whether lengths for values in rings are computed correctly for all possible cases
    /// (shortest distance to next zero is found) for large values
    #[test]
    fn large_values() {
        let modulus = Z::from(u64::MAX);
        let pos_1 = Z::from(i64::MAX);
        let pos_2 = Z::from(u64::MAX - 58);

        assert_eq!(&Z::from(i64::MAX), &length(&pos_1.value, &modulus.value));
        assert_eq!(Z::from(58), length(&pos_2.value, &modulus.value));
    }
}
