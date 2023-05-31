// Copyright © 2023 Niklas Siemer, Sven Moog
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
    /// Documentation at [`AsInteger::into_fmpz`]
    unsafe fn into_fmpz(self) -> fmpz {
        (&self).into_fmpz()
    }
}

unsafe impl AsInteger for &u64 {
    /// Documentation at [`AsInteger::into_fmpz`]
    unsafe fn into_fmpz(self) -> fmpz {
        let mut ret_value = fmpz(0);
        fmpz_init_set_ui(&mut ret_value, *self);
        ret_value
    }
}

/// Implement the [`AsInteger`] trait for the types in the parameter and their
/// borrowed version.This macro is just intended for the rust integer types
/// that can be converted into [`i64`].
macro_rules! implement_as_integer_over_i64 {
    ($($type:ident)*) => {
        $(
        /// Documentation at [`AsInteger::into_fmpz`]
        unsafe impl AsInteger for $type {
            unsafe fn into_fmpz(self) -> fmpz {
                (&self).into_fmpz()
            }
        }

        /// Documentation at [`AsInteger::into_fmpz`]
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

implement_as_integer_over_i64!(i8 u8 i16 u16 i32 u32 i64);

unsafe impl AsInteger for Z {
    /// Documentation at [`AsInteger::into_fmpz`]
    unsafe fn into_fmpz(mut self) -> fmpz {
        let mut out = fmpz(0);
        fmpz_swap(&mut out, &mut self.value);
        out
    }

    /// Documentation at [`AsInteger::get_fmpz_ref`]
    fn get_fmpz_ref(&self) -> Option<&fmpz> {
        Some(&self.value)
    }
}

unsafe impl AsInteger for &Z {
    /// Documentation at [`AsInteger::into_fmpz`]
    unsafe fn into_fmpz(self) -> fmpz {
        let mut value = fmpz(0);
        fmpz_set(&mut value, &self.value);
        value
    }

    /// Documentation at [`AsInteger::get_fmpz_ref`]
    fn get_fmpz_ref(&self) -> Option<&fmpz> {
        Some(&self.value)
    }
}

unsafe impl AsInteger for &fmpz {
    /// Documentation at [`AsInteger::into_fmpz`]
    unsafe fn into_fmpz(self) -> fmpz {
        let mut value = fmpz(0);
        fmpz_set(&mut value, self);
        value
    }

    /// Documentation at [`AsInteger::get_fmpz_ref`]
    fn get_fmpz_ref(&self) -> Option<&fmpz> {
        Some(self)
    }
}

unsafe impl AsInteger for fmpz {
    /// Documentation at [`AsInteger::into_fmpz`]
    unsafe fn into_fmpz(self) -> fmpz {
        (&self).into_fmpz()
    }

    /// Documentation at [`AsInteger::get_fmpz_ref`]
    fn get_fmpz_ref(&self) -> Option<&fmpz> {
        Some(self)
    }
}

#[cfg(test)]
mod test_as_integer_rust_ints {
    use crate::{integer::Z, traits::AsInteger};

    /// Assert that rust integers don't have an internal fmpz
    #[test]
    fn get_fmpz_ref_none() {
        assert!(10u8.get_fmpz_ref().is_none());
        assert!(10u16.get_fmpz_ref().is_none());
        assert!(10u32.get_fmpz_ref().is_none());
        assert!(10u64.get_fmpz_ref().is_none());
        assert!(10i8.get_fmpz_ref().is_none());
        assert!(10i16.get_fmpz_ref().is_none());
        assert!(10i32.get_fmpz_ref().is_none());
        assert!(10i64.get_fmpz_ref().is_none());
    }

    /// Assert that into_fmpz works correctly for small values
    #[test]
    fn into_fmpz_small() {
        let z = Z::from(10);

        unsafe {
            assert_eq!(z, Z::from_fmpz(10u8.into_fmpz()));
            assert_eq!(z, Z::from_fmpz(10u16.into_fmpz()));
            assert_eq!(z, Z::from_fmpz(10u32.into_fmpz()));
            assert_eq!(z, Z::from_fmpz(10u64.into_fmpz()));
            assert_eq!(z, Z::from_fmpz(10i8.into_fmpz()));
            assert_eq!(z, Z::from_fmpz(10i16.into_fmpz()));
            assert_eq!(z, Z::from_fmpz(10i32.into_fmpz()));
            assert_eq!(z, Z::from_fmpz(10i64.into_fmpz()));
        }
    }
}

#[cfg(test)]
mod test_as_integer_z {
    use super::*;

    /// Assert that the new [`fmpz`] contains the same value as the original
    /// for small values (FLINT is not using pointers).
    #[test]
    fn small_into_fmpz() {
        let z = Z::from(42);

        let copy_1 = unsafe { Z::from_fmpz((&z).into_fmpz()) };
        let copy_2 = unsafe { Z::from_fmpz(z.into_fmpz()) };

        assert_eq!(copy_1, Z::from(42));
        assert_eq!(copy_2, Z::from(42));
    }

    /// Assert that the new [`fmpz`] contains the same value as the original
    /// for large values (FLINT uses pointers).
    #[test]
    fn large_into_fmpz() {
        let z = Z::from(u64::MAX);

        let copy_1 = unsafe { Z::from_fmpz((&z).into_fmpz()) };
        let copy_2 = unsafe { Z::from_fmpz(z.into_fmpz()) };

        assert_eq!(copy_1, Z::from(u64::MAX));
        assert_eq!(copy_2, Z::from(u64::MAX));
    }

    /// Assert that the new [`fmpz`] using a different memory than the original
    /// (Also as a pointer representation)
    #[test]
    fn memory_safety() {
        let z = Z::from(i64::MAX);

        let value = unsafe { (&z).into_fmpz() };

        // The `fmpz` values have to point to different memory locations.
        assert_ne!(value.0, z.value.0);
    }

    /// Assert that `get_fmpz_ref` returns a correct reference for small values
    #[test]
    fn get_ref_small() {
        let z = Z::from(10);

        let z_ref_1 = z.get_fmpz_ref().unwrap();
        let z_ref_2 = (&z).get_fmpz_ref().unwrap();

        assert_eq!(z.value.0, z_ref_1.0);
        assert_eq!(z.value.0, z_ref_2.0);
    }

    /// Assert that `get_fmpz_ref` returns a correct reference for large values
    #[test]
    fn get_ref_large() {
        let z = Z::from(u64::MAX);

        let z_ref_1 = z.get_fmpz_ref().unwrap();
        let z_ref_2 = (&z).get_fmpz_ref().unwrap();

        assert_eq!(z.value.0, z_ref_1.0);
        assert_eq!(z.value.0, z_ref_2.0);
    }
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
