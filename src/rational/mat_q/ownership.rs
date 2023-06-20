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

use crate::traits::{GetNumColumns, GetNumRows};

use super::MatQ;
use flint_sys::fmpq_mat::{fmpq_mat_clear, fmpq_mat_set};

impl Clone for MatQ {
    /// Clones the given element and returns a deep clone of the given [`MatQ`] element.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let string = String::from("[[1/2, 2/3, 3/4],[3/1, 4/2, 5/4]]");
    /// let a = MatQ::from_str(&string).unwrap();
    /// let b = a.clone();
    /// ```
    fn clone(&self) -> Self {
        let mut mat = MatQ::new(self.get_num_rows(), self.get_num_columns());
        unsafe {
            fmpq_mat_set(&mut mat.matrix, &self.matrix);
        }
        mat
    }
}

impl Drop for MatQ {
    /// Drops the given [`MatQ`] value and frees the allocated memory.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let string = String::from("[[1/2, 2/3, 3/4],[3/1, 4/2, 5/4]]");
    /// {
    ///     let a = MatQ::from_str(&string).unwrap();
    /// } // as a's scope ends here, it get's dropped
    /// ```
    ///
    /// ```
    /// use qfall_math::rational::MatQ;
    /// use std::str::FromStr;
    ///
    /// let string = String::from("[[1/2, 2/3, 3/4],[3/1, 4/2, 5/4]]");
    /// let a = MatQ::from_str(&string).unwrap();
    /// drop(a); // explicitly drops a's value
    /// ```
    fn drop(&mut self) {
        unsafe { fmpq_mat_clear(&mut self.matrix) }
    }
}

/// Test that the [`Clone`] trait is correctly implemented.
#[cfg(test)]
mod test_clone {
    use super::MatQ;
    use crate::{
        rational::Q,
        traits::{GetEntry, GetNumColumns, GetNumRows},
    };
    use std::str::FromStr;

    /// check if a cloned value is still alive after the original value ran out of scope
    #[test]
    #[allow(clippy::redundant_clone)]
    fn keep_alive() {
        let a: MatQ;
        let str1 = "[[1/2, 2/3, 3/4],[3/1, 4/2, 5/4]]";
        {
            let b = MatQ::from_str(str1).unwrap();

            a = b.clone();
        }

        assert_eq!(a.get_num_rows(), 2);
        assert_eq!(a.get_num_columns(), 3);

        assert_eq!(a.get_entry(0, 0).unwrap(), Q::from((1, 2)));
        assert_eq!(a.get_entry(0, 1).unwrap(), Q::from((2, 3)));
        assert_eq!(a.get_entry(0, 2).unwrap(), Q::from((3, 4)));
        assert_eq!(a.get_entry(1, 0).unwrap(), Q::from((3, 1)));
        assert_eq!(a.get_entry(1, 1).unwrap(), Q::from((4, 2)));
        assert_eq!(a.get_entry(1, 2).unwrap(), Q::from((5, 4)));
    }

    /// check whether the cloned large entries are stored separately
    #[test]
    fn entries_stored_separately() {
        let a: MatQ;
        let string = format!(
            "[[{}/1,{}/2],[{}/3,{}/{}]]",
            u64::MAX,
            i64::MAX,
            i64::MIN,
            u64::MAX,
            i64::MIN
        );
        let b = MatQ::from_str(&string).unwrap();

        a = b.clone();

        assert_ne!(
            a.get_entry(0, 0).unwrap().value.num.0,
            b.get_entry(0, 0).unwrap().value.num.0
        );
        assert_ne!(
            a.get_entry(0, 1).unwrap().value.num.0,
            b.get_entry(0, 1).unwrap().value.num.0
        );
        assert_ne!(
            a.get_entry(1, 0).unwrap().value.num.0,
            b.get_entry(1, 0).unwrap().value.num.0
        );
        assert_ne!(
            a.get_entry(1, 1).unwrap().value.num.0,
            b.get_entry(1, 1).unwrap().value.num.0
        );
        assert_ne!(
            a.get_entry(1, 1).unwrap().value.den.0,
            b.get_entry(1, 1).unwrap().value.den.0
        );

        assert_eq!(
            a.get_entry(0, 1).unwrap().value.den.0,
            b.get_entry(0, 1).unwrap().value.den.0
        ); // reduction applied, hence kept on stack
    }
}

/// Test that the [`Drop`] trait is correctly implemented.
#[cfg(test)]
mod test_drop {
    use super::MatQ;
    use crate::traits::GetEntry;
    use std::collections::HashSet;
    use std::str::FromStr;

    /// Creates a matrix with two large entries, drops it and outputs
    /// the points these two entries were stored in
    fn create_and_drop_matq() -> (i64, i64, i64, i64) {
        let string = format!("[[{}/{},{}/{}]]", u64::MAX, i64::MIN, i64::MAX, 1);
        let a = MatQ::from_str(&string).unwrap();

        let storage_num_0 = a.get_entry(0, 0).unwrap().value.num.0;
        let storage_num_1 = a.get_entry(0, 1).unwrap().value.num.0;
        let storage_den_0 = a.get_entry(0, 0).unwrap().value.den.0;
        let storage_den_1 = a.get_entry(0, 1).unwrap().value.den.0;

        (storage_num_0, storage_num_1, storage_den_0, storage_den_1)
    }

    /// Check whether freed memory is reused afterwards
    #[test]
    fn free_memory() {
        let mut set = HashSet::new();

        for _i in 0..5 {
            set.insert(create_and_drop_matq());
        }

        assert!(set.len() < 5);
    }
}
