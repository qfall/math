// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains helpful functions on [`fmpz`] values in a ring/`modulus` context.

use crate::integer::fmpz_helpers::distance;
use flint_sys::fmpz::{fmpz, fmpz_cmp};

const ZERO_FMPZ: fmpz = fmpz(0);

/// Computes the shortest distance of `self` to the next zero instance
/// regarding the `modulus`.
///
/// WARNING: This function assumes `value` to be reduced,
/// i.e. `0 <= value <= modulus`.
///
/// # Example
/// ```compile_fail
/// use flint_sys::fmpz::fmpz;
/// use math::integer_mod_q::fmpz_mod_helpers::length;
///
/// let modulus = fmpz(15);
/// let value = fmpz(10);
///
/// let length = length(&value, &modulus);
///
/// assert_eq!(5, length.0);
/// ```
pub(crate) fn length(value: &fmpz, modulus: &fmpz) -> fmpz {
    let distance_zero = distance(&ZERO_FMPZ, value);
    let distance_modulus = distance(value, modulus);

    // if distance_zero < distance modulus => return distance_zero
    if unsafe { fmpz_cmp(&distance_zero, &distance_modulus) } < 0 {
        distance_zero
    } else {
        distance_modulus
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

        assert_eq!(5, length(&pos_1, &modulus).0);
        assert_eq!(7, length(&pos_2, &modulus).0);
        assert_eq!(0, length(&zero, &modulus).0);
    }

    /// Checks whether lengths for values in rings are computed correctly for all possible cases
    /// (shortest distance to next zero is found) for large values
    #[test]
    fn large_values() {
        let modulus = Z::from(u64::MAX);
        let pos_1 = Z::from(i64::MAX);
        let pos_2 = Z::from(u64::MAX - 58);

        assert_eq!(0, unsafe {
            fmpz_cmp(
                &Z::from(9223372036854775807_u64).value,
                &length(&pos_1.value, &modulus.value),
            )
        });
        assert_eq!(58, length(&pos_2.value, &modulus.value).0);
    }
}
