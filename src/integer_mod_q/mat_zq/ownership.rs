// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations of functions
//! important for ownership such as the [`Clone`] and [`Drop`] trait.
//!
//! The explicit functions contain the documentation.

use super::MatZq;
use crate::integer::Z;
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpz_mod_mat::{fmpz_mod_mat_clear, fmpz_mod_mat_init_set};

impl Clone for MatZq {
    /// Clones the given element and returns a deep clone of the [`MatZq`] element.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let str1 = "[[1,2,3],[4,5,6]] mod 4";
    /// let a = MatZq::from_str(str1).unwrap();
    /// let b = a.clone();
    /// ```
    fn clone(&self) -> Self {
        let mut out = MatZq::new(
            self.get_num_rows(),
            self.get_num_columns(),
            Z::from(self.get_mod()),
        )
        .unwrap();
        unsafe {
            fmpz_mod_mat_init_set(&mut out.matrix, &self.matrix);
        }
        out
    }
}

impl Drop for MatZq {
    /// Drops the given [`MatZq`] value and frees the allocated memory.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let str1 = "[[1,2,3],[4,5,6]] mod 4";
    /// {
    ///     let a = MatZq::from_str(str1).unwrap();
    /// } // as a's scope ends here, it get's dropped
    /// ```
    ///
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let str1 = "[[1,2,3],[4,5,6]] mod 4";
    /// let a = MatZq::from_str(str1).unwrap();
    /// drop(a); // explicitly drops a's value
    /// ```
    fn drop(&mut self) {
        unsafe { fmpz_mod_mat_clear(&mut self.matrix) }
    }
}

/// Test that the [`Clone`] trait is correctly implemented.
#[cfg(test)]
mod test_clone {
    use super::MatZq;
    use crate::integer::Z;
    use crate::traits::{GetEntry, GetNumColumns, GetNumRows};
    use std::str::FromStr;

    /// check if a cloned value is still alive after the original value ran out of scope
    #[test]
    #[allow(clippy::redundant_clone)]
    fn keep_alive() {
        let a: MatZq;
        let str1 = "[[1, 2, 3],[3, 4, 5]] mod 6";
        {
            let b = MatZq::from_str(str1).unwrap();

            a = b.clone();
        }

        assert_eq!(a.get_num_rows(), 2);
        assert_eq!(a.get_num_columns(), 3);

        assert_eq!(GetEntry::<Z>::get_entry(&a, 0, 0).unwrap(), 1.into());
        assert_eq!(GetEntry::<Z>::get_entry(&a, 0, 1).unwrap(), 2.into());
        assert_eq!(GetEntry::<Z>::get_entry(&a, 0, 2).unwrap(), 3.into());
        assert_eq!(GetEntry::<Z>::get_entry(&a, 1, 0).unwrap(), 3.into());
        assert_eq!(GetEntry::<Z>::get_entry(&a, 1, 1).unwrap(), 4.into());
        assert_eq!(GetEntry::<Z>::get_entry(&a, 1, 2).unwrap(), 5.into());
    }

    /// check whether the cloned entries are stored separately
    #[test]
    fn entries_stored_separately() {
        let a: MatZq;
        let string = format!("[[{}, {}],[-10, 0]] mod {}", i64::MAX, i64::MIN, u64::MAX);
        let b = MatZq::from_str(&string).unwrap();

        a = b.clone();

        assert_ne!(
            GetEntry::<Z>::get_entry(&a, 0, 0).unwrap().value.0,
            GetEntry::<Z>::get_entry(&b, 0, 0).unwrap().value.0
        );
        assert_ne!(
            GetEntry::<Z>::get_entry(&a, 0, 1).unwrap().value.0,
            GetEntry::<Z>::get_entry(&b, 0, 1).unwrap().value.0
        );
        assert_ne!(
            GetEntry::<Z>::get_entry(&a, 1, 0).unwrap().value.0,
            GetEntry::<Z>::get_entry(&b, 1, 0).unwrap().value.0
        );
        assert_eq!(
            GetEntry::<Z>::get_entry(&a, 1, 1).unwrap().value.0,
            GetEntry::<Z>::get_entry(&b, 1, 1).unwrap().value.0
        ); // kept on stack
    }

    /// Check if modulus is applied after cloning
    #[test]
    #[allow(clippy::redundant_clone)]
    fn modulus_applied() {
        let string = String::from("[[1, 2],[4, 5]] mod 4");
        let b = MatZq::from_str(&string).unwrap();

        let a = b.clone();

        assert_eq!(GetEntry::<Z>::get_entry(&a, 1, 1).unwrap(), 1.into());
        assert_eq!(GetEntry::<Z>::get_entry(&a, 1, 0).unwrap(), 0.into())
    }

    /// Check if large modulus is stored separately and therefore cloned deeply
    #[test]
    fn modulus_storage() {
        let string = format!("[[{}, {}],[-10, 0]] mod {}", i64::MAX, i64::MIN, u64::MAX);
        let b = MatZq::from_str(&string).unwrap();

        let a = b.clone();

        assert_ne!(a.matrix.mod_[0].0, b.matrix.mod_[0].0);
    }
}

/// Test that the [`Drop`] trait is correctly implemented.
#[cfg(test)]
mod test_drop {
    use super::MatZq;
    use crate::integer::Z;
    use crate::traits::GetEntry;
    use std::collections::HashSet;
    use std::str::FromStr;

    /// Creates a matrix with two large entries, drops it and outputs
    /// the points these two entries were stored in
    fn create_and_drop_matzq() -> (i64, i64, i64) {
        let string = format!("[[{}, {}]] mod {}", i64::MAX, i64::MIN, u64::MAX);
        let a = MatZq::from_str(&string).unwrap();

        let storage_mod = a.matrix.mod_[0].0;
        let storage_0 = GetEntry::<Z>::get_entry(&a, 0, 0).unwrap().value.0;
        let storage_1 = GetEntry::<Z>::get_entry(&a, 0, 1).unwrap().value.0;

        (storage_mod, storage_0, storage_1)
    }

    /// Check whether freed memory is reused afterwards
    #[test]
    fn free_memory() {
        let mut set = HashSet::new();

        for _i in 0..5 {
            let (a, b, c) = create_and_drop_matzq();
            set.insert(a);
            set.insert(b);
            set.insert(c);
        }

        assert!(set.len() < 15);
    }
}
