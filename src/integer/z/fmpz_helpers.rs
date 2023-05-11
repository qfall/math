// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains helpful functions on [`fmpz`].

use super::Z;
use crate::traits::AsInteger;
use flint_sys::fmpz::{
    fmpz, fmpz_abs, fmpz_cmpabs, fmpz_init_set_si, fmpz_init_set_ui, fmpz_set, fmpz_sub, fmpz_swap,
};

/// Efficiently finds maximum absolute value and returns
/// a cloned [`Z`] instance out of a vector of [`fmpz`] instances.
///
/// Parameters:
/// - `fmpz_vector`: contains a number of [`fmpz`] instances
///
/// Returns the maximum absolute value out of the given [`fmpz`] vector
/// as a cloned [`Z`] instance.
///
/// # Examples
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
    // It's not necessary to clear `fmpz(0)` since it's small
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
/// - `other`: specifies the [`fmpz`] value whose distance
/// is calculated to `self`
///
/// Returns the absolute difference, i.e. distance between the two given [`fmpz`]
/// instances as a new [`fmpz`] instance.
///
/// # Examples
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
pub(crate) fn distance(value_1: &fmpz, value_2: &fmpz) -> Z {
    let mut out = Z::ZERO;
    unsafe { fmpz_sub(&mut out.value, value_1, value_2) };
    unsafe { fmpz_abs(&mut out.value, &out.value) };
    out
}

unsafe impl AsInteger for u64 {
    unsafe fn into_fmpz(self) -> fmpz {
        let mut ret_value = fmpz(0);
        fmpz_init_set_ui(&mut ret_value, self);
        ret_value
    }
}

unsafe impl AsInteger for &u64 {
    unsafe fn into_fmpz(self) -> fmpz {
        let mut ret_value = fmpz(0);
        fmpz_init_set_ui(&mut ret_value, *self);
        ret_value
    }
}

macro_rules! AsInteger_singed {
    ($($type:ident)*) => {
        $(unsafe impl AsInteger for $type {
            unsafe fn into_fmpz(self) -> fmpz {
                let mut ret_value = fmpz(0);
                fmpz_init_set_si(&mut ret_value, self as i64);
                ret_value
            }
        }

        unsafe impl AsInteger for &$type {
            unsafe fn into_fmpz(self) -> fmpz {
                let mut ret_value = fmpz(0);
                fmpz_init_set_si(&mut ret_value, *self as i64);
                ret_value
            }
        }
    )*
    };
}

AsInteger_singed!(i8 u8 i16 u16 i32 u32 i64);

unsafe impl AsInteger for Z {
    unsafe fn into_fmpz(mut self) -> fmpz {
        let mut out = fmpz(0);
        fmpz_swap(&mut out, &mut self.value);
        out
    }

    fn get_fmpz_ref(&self) -> Option<&fmpz> {
        Some(&self.value)
    }
}

unsafe impl AsInteger for &Z {
    unsafe fn into_fmpz(self) -> fmpz {
        let mut value = fmpz(0);
        fmpz_set(&mut value, &self.value);
        value
    }

    fn get_fmpz_ref(&self) -> Option<&fmpz> {
        Some(&self.value)
    }
}

#[cfg(test)]
mod test_as_integer_z {
    use flint_sys::fmpz::{fmpz_clear, fmpz_set_ui};

    use super::*;

    // Assert that the new fmpz is not related to the old one
    #[test]
    fn small_into_fmpz() {
        let mut value = unsafe {
            let z = Z::from(42);
            (&z).into_fmpz()
        }; // z is dropped here

        let _ = Z::from(12);

        let copy = Z::from_fmpz(&value);
        assert_eq!(copy, Z::from(42));
        unsafe { fmpz_clear(&mut value) };
    }

    /// Assert that the new fmpz is not effected by the original for large numbers.
    /// This can not be tested for an owned [`Z`], since that would violate the
    /// ownership constrain -> not compiling.
    #[test]
    fn original_not_effecting_new_large() {
        let value = unsafe {
            let z = Z::from(i64::MAX);
            (&z).into_fmpz()
        }; // z is dropped here

        // Create new Z values that would likely overwrite the memory of the original z.
        let _a = Z::from(u64::MAX);
        let _b = Z::from(u64::MAX);

        assert_eq!(Z { value }, Z::from(i64::MAX));
    }

    /// Assert that the new [`fmpz`] is not effecting the original [`Z`].
    #[test]
    fn new_not_effecting_original_large() {
        let z = Z::from(i64::MAX);

        let mut value = unsafe { (&z).into_fmpz() };

        // Setting the result of into_fmpz to a different value
        // is not effecting the original.
        unsafe { fmpz_set_ui(&mut value, u64::MAX) }
        assert_eq!(z, Z::from(i64::MAX));

        // Clearing the new fmpz and creating new values that likely
        // occupy the memory of the just cleared value.
        unsafe { fmpz_clear(&mut value) };
        let _ = Z::from(u64::MAX - 1);
        let _ = Z::from(u64::MAX);

        assert_eq!(z, Z::from(i64::MAX));
    }

    // TODO: Add more test cases
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
    use flint_sys::fmpz::fmpz;

    /// Checks if distance is correctly output for small [`Z`] values
    /// and whether distance(a,b) == distance(b,a), distance(a,a) == 0
    #[test]
    fn small_values() {
        let a = fmpz(1);
        let b = fmpz(-15);
        let zero = fmpz(0);

        assert_eq!(Z::ONE, distance(&a, &zero));
        assert_eq!(Z::ONE, distance(&zero, &a));
        assert_eq!(Z::from(16), distance(&a, &b));
        assert_eq!(Z::from(16), distance(&b, &a));
        assert_eq!(Z::from(15), distance(&b, &zero));
        assert_eq!(Z::from(15), distance(&zero, &b));
        assert_eq!(Z::ZERO, distance(&b, &b));
        assert_eq!(Z::ZERO, distance(&a, &a));
        assert_eq!(Z::ZERO, distance(&zero, &zero));
    }

    /// Checks if distance is correctly output for large [`Z`] values
    /// and whether distance(a,b) == distance(b,a), distance(a,a) == 0
    #[test]
    fn large_values() {
        let a = Z::from(i64::MAX);
        let b = Z::from(i64::MIN);
        let zero = Z::ZERO;
        let b_abs = Z::ZERO - &b;

        assert_eq!(&a - &b, distance(&a.value, &b.value));
        assert_eq!(&a - &b, distance(&b.value, &a.value));
        assert_eq!(a, distance(&a.value, &zero.value));
        assert_eq!(a, distance(&zero.value, &a.value));
        assert_eq!(b_abs, distance(&b.value, &zero.value));
        assert_eq!(b_abs, distance(&zero.value, &b.value));
        assert_eq!(zero, distance(&a.value, &a.value));
        assert_eq!(zero, distance(&b.value, &b.value));
    }
}
