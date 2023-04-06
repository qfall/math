// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains helpful functions on [`fmpz`].

use super::Z;
use flint_sys::fmpz::{fmpz, fmpz_abs, fmpz_cmpabs, fmpz_sub};

/// Efficiently finds maximum absolute value and returns
/// a cloned [`Z`] instance out of a vector of [`fmpz`] instances.
///
/// Parameters:
/// - `fmpz_vector`: contains a number of [`fmpz`] instances
///
/// Returns the maximum absolute value out of the given [`fmpz`] vector
/// as a cloned [`Z`] instance.
///
/// # Example
/// ```compile_fail
/// use flint_sys::fmpz::fmpz;
/// use qfall_math::integer::{fmpz_helpers::find_max_abs, Z};
///
/// let fmpz_vec = vec![fmpz(0), fmpz(-13), fmpz(10)];
///
/// let abs_max = find_max_abs(&fmpz_vec);
/// assert_eq!(Z::from(13), fmpz_vec);
/// ```
pub(crate) fn find_max_abs(fmpz_vector: &Vec<fmpz>) -> Z {
    // find maximum of absolute fmpz entries
    let mut max = &fmpz(0);
    for entry in fmpz_vector {
        if unsafe { fmpz_cmpabs(max, entry) } < 0 {
            max = entry;
        }
    }

    // clone and ensure that the output absolute maximum value is absolute
    let mut result = Z::ZERO;
    unsafe { fmpz_abs(&mut result.value, max) }
    result
}

/// Computes the absolute distance between two [`fmpz`] instances.
///
/// Parameters:
/// - `other`: specifies one of the [`fmpz`] values whose distance
/// is calculated to `self`
///
/// Returns the absolute difference, i.e. distance between the two given [`fmpz`]
/// instances as a new [`fmpz`] instance.
///
/// # Example
/// ```compile_fail
/// use flint_sys::fmpz::fmpz;
/// use qfall_math::integer::fmpz_helpers::distance;
///
/// let a = fmpz(1);
/// let b = fmpz(-15);
///
/// let distance = distance(&a, &b);
///
/// assert_eq!(16, distance.0);
/// ```
pub(crate) fn distance(value_1: &fmpz, value_2: &fmpz) -> fmpz {
    let mut out = fmpz(0);
    unsafe { fmpz_sub(&mut out, value_1, value_2) };
    unsafe { fmpz_abs(&mut out, &out) };
    out
}

#[cfg(test)]
mod test_find_max_abs {
    use super::*;
    use crate::integer::MatZ;
    use std::str::FromStr;

    /// Checks whether `find_max_abs` works correctly for small positive
    /// [`fmpz`] instances
    #[test]
    fn positive_small() {
        let mat = MatZ::from_str("[[1, 10, 100]]").unwrap();
        let fmpz_vector = mat.collect_entries();

        let abs_max = find_max_abs(&fmpz_vector);

        assert_eq!(abs_max, Z::from(100));
    }

    /// Checks whether `find_max_abs` works correctly for large positive
    /// [`fmpz`] instances
    #[test]
    fn positive_large() {
        let mat = MatZ::from_str(&format!("[[1, {}, {}, 10]]", i64::MAX, u64::MAX)).unwrap();
        let fmpz_vector = mat.collect_entries();

        let abs_max = find_max_abs(&fmpz_vector);

        assert_eq!(abs_max, Z::from(u64::MAX));
    }

    /// Checks whether `find_max_abs` works correctly for small negative
    /// [`fmpz`] instances
    #[test]
    fn negative_small() {
        let mat = MatZ::from_str("[[1, -10, -100]]").unwrap();
        let fmpz_vector = mat.collect_entries();

        let abs_max = find_max_abs(&fmpz_vector);

        assert_eq!(abs_max, Z::from(100));
    }

    /// Checks whether `find_max_abs` works correctly for large negative
    /// [`fmpz`] instances
    #[test]
    fn negative_large() {
        let mat = MatZ::from_str(&format!("[[1, {}, -{}, 10]]", i64::MAX, u64::MAX)).unwrap();
        let fmpz_vector = mat.collect_entries();

        let abs_max = find_max_abs(&fmpz_vector);

        assert_eq!(abs_max, Z::from(u64::MAX));
    }
}

#[cfg(test)]
mod test_distance {
    use super::distance;
    use super::Z;
    use flint_sys::fmpz::{fmpz, fmpz_cmp};

    /// Checks if distance is correctly output for small [`Z`] values
    /// and whether distance(a,b) == distance(b,a), distance(a,a) == 0
    #[test]
    fn small_values() {
        let a = fmpz(1);
        let b = fmpz(-15);
        let zero = fmpz(0);

        assert_eq!(1, distance(&a, &zero).0);
        assert_eq!(1, distance(&zero, &a).0);
        assert_eq!(16, distance(&a, &b).0);
        assert_eq!(16, distance(&b, &a).0);
        assert_eq!(15, distance(&b, &zero).0);
        assert_eq!(15, distance(&zero, &b).0);
        assert_eq!(0, distance(&b, &b).0);
        assert_eq!(0, distance(&a, &a).0);
        assert_eq!(0, distance(&zero, &zero).0);
    }

    /// Checks if distance is correctly output for large [`Z`] values
    /// and whether distance(a,b) == distance(b,a), distance(a,a) == 0
    #[test]
    fn large_values() {
        let a = Z::from(i64::MAX);
        let b = Z::from(i64::MIN);
        let zero = Z::ZERO;
        let cmp_b_pos = Z::from(i64::MAX as u64 + 1);

        assert_eq!(0, unsafe {
            fmpz_cmp(&(&a - &b).value, &distance(&a.value, &b.value))
        });
        assert_eq!(0, unsafe {
            fmpz_cmp(&(&a - &b).value, &distance(&b.value, &a.value))
        });
        assert_eq!(0, unsafe {
            fmpz_cmp(&a.value, &distance(&a.value, &zero.value))
        });
        assert_eq!(0, unsafe {
            fmpz_cmp(&(&a).value, &distance(&zero.value, &a.value))
        });
        assert_eq!(0, unsafe {
            fmpz_cmp(&cmp_b_pos.value, &distance(&b.value, &zero.value))
        });
        assert_eq!(0, unsafe {
            fmpz_cmp(&cmp_b_pos.value, &distance(&zero.value, &b.value))
        });
        assert_eq!(0, distance(&a.value, &a.value).0);
        assert_eq!(0, distance(&b.value, &b.value).0);
    }
}
