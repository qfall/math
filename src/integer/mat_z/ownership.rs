//! This module contains implementations of functions
//! important for ownership such as the [`Clone`] and [`Drop`] trait.
//!
//! The explicit functions contain the documentation.

use super::MatZ;
use flint_sys::fmpz_mat::{fmpz_mat_clear, fmpz_mat_set};

impl Clone for MatZ {
    /// Clones the given element and returns a deep clone of the [`MatZ`] element.
    ///
    /// # Example
    /// ```
    /// use math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let string = String::from("[[1, 2, 3],[3, 4, 5]]");
    /// let a = MatZ::from_str(&string).unwrap();
    /// let b = a.clone();
    /// ```
    fn clone(&self) -> Self {
        let mut mat = MatZ::new(self.get_num_rows(), self.get_num_columns()).unwrap();
        unsafe {
            fmpz_mat_set(&mut mat.matrix, &self.matrix);
        }
        mat
    }
}

impl Drop for MatZ {
    /// Drops the given [`MatZ`] value and frees the allocated memory.
    ///
    /// # Examples
    /// ```
    /// use math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let string = String::from("[[1, 2, 3],[3, 4, 5]]");
    /// {
    ///     let a = MatZ::from_str(&string).unwrap();
    /// } // as a's scope ends here, it get's dropped
    /// ```
    ///
    /// ```
    /// use math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let string = String::from("[[1, 2, 3],[3, 4, 5]]");
    /// let a = MatZ::from_str(&string).unwrap();
    /// drop(a); // explicitly drops a's value
    /// ```
    fn drop(&mut self) {
        unsafe { fmpz_mat_clear(&mut self.matrix) }
    }
}

/// Test that the [`Clone`] trait is correctly implemented.
#[cfg(test)]
mod test_clone {

    use super::MatZ;
    use std::str::FromStr;

    /// check if a cloned value is still alive after the original value ran out of scope
    #[test]
    #[allow(clippy::redundant_clone)]
    fn keep_alive() {
        let a: MatZ;
        let string = String::from("[[1, 2, 3],[3, 4, 5]]");
        {
            let b = MatZ::from_str(&string).unwrap();

            a = b.clone();
        }

        assert_eq!(a.get_num_rows(), 2);
        assert_eq!(a.get_num_columns(), 3);

        assert_eq!(a.get_entry(0, 0).unwrap(), 1.into());
        assert_eq!(a.get_entry(0, 1).unwrap(), 2.into());
        assert_eq!(a.get_entry(0, 2).unwrap(), 3.into());
        assert_eq!(a.get_entry(1, 0).unwrap(), 3.into());
        assert_eq!(a.get_entry(1, 1).unwrap(), 4.into());
        assert_eq!(a.get_entry(1, 2).unwrap(), 5.into());
    }

    /// check whether the cloned entries are stored separately
    #[test]
    fn entries_stored_separately() {
        let a: MatZ;
        // entries are 2^65 = 36893488147419103232, hence fmpz values kept on heap
        let string = String::from("[[36893488147419103232, 36893488147419103232],[36893488147419103232, 36893488147419103232]]");
        let b = MatZ::from_str(&string).unwrap();

        a = b.clone();

        assert_ne!(
            a.get_entry(0, 0).unwrap().value.0,
            b.get_entry(0, 0).unwrap().value.0
        );
        assert_ne!(
            a.get_entry(0, 1).unwrap().value.0,
            b.get_entry(0, 1).unwrap().value.0
        );
        assert_ne!(
            a.get_entry(1, 0).unwrap().value.0,
            b.get_entry(1, 0).unwrap().value.0
        );
        assert_ne!(
            a.get_entry(1, 1).unwrap().value.0,
            b.get_entry(1, 1).unwrap().value.0
        );
    }
}

/// Test that the [`Drop`] trait is correctly implemented.
#[cfg(test)]
mod test_drop {

    use super::MatZ;
    use std::collections::HashSet;
    use std::str::FromStr;

    /// Creates a matrix with two entries of size 2^65, drops it and outputs
    /// the points these two entries were stored in
    fn create_and_drop_matz() -> (i64, i64, i64) {
        // entries are 2^65 = 36893488147419103232, hence fmpz values kept on heap
        let string = String::from("[[36893488147419103232, 36893488147419103232]]");
        let a = MatZ::from_str(&string).unwrap();

        let storage_mat = unsafe { (*a.matrix.entries).0 };
        let storage_0 = a.get_entry(0, 0).unwrap().value.0;
        let storage_1 = a.get_entry(0, 1).unwrap().value.0;

        (storage_mat, storage_0, storage_1)
    }

    /// Check whether freed memory is reused afterwards
    #[test]
    fn free_memory() {
        let mut set = HashSet::new();

        for _i in 0..5 {
            set.insert(create_and_drop_matz());
        }

        assert!(set.len() < 5);
    }
}
