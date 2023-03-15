//! This module contains implementations of functions
//! important for ownership such as the [`Clone`] and [`Drop`] trait.
//!
//! The explicit functions contain the documentation.

use super::MatPolyOverZ;
use flint_sys::fmpz_poly_mat::{fmpz_poly_mat_clear, fmpz_poly_mat_set};

impl Clone for MatPolyOverZ {
    /// Clones the given element and returns a deep clone of the [`MatPolyOverZ`] element.
    ///
    /// # Example
    /// ```
    /// use math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a = MatPolyOverZ::from_str("[[2  0 1],[1  15]]").unwrap();
    /// let b = a.clone();
    /// ```
    fn clone(&self) -> Self {
        let mut clone = MatPolyOverZ::new(self.get_num_rows(), self.get_num_columns()).unwrap();

        unsafe { fmpz_poly_mat_set(&mut clone.matrix, &mut self.matrix.to_owned()) }

        clone
    }
}

impl Drop for MatPolyOverZ {
    /// Drops the given [`MatPolyOverZ`] value and frees the allocated memory.
    ///
    /// # Examples
    /// ```
    /// use math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    /// {
    ///     let a = MatPolyOverZ::from_str("[[2  0 1],[1  15]]").unwrap();
    /// } // as a's scope ends here, it get's dropped
    /// ```
    ///
    /// ```
    /// use math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let a = MatPolyOverZ::from_str("[[2  0 1],[1  15]]").unwrap();
    /// drop(a); // explicitly drops a's value
    /// ```
    fn drop(&mut self) {
        unsafe { fmpz_poly_mat_clear(&mut self.matrix) }
    }
}

/// Test that the [`Clone`] trait is correctly implemented.
#[cfg(test)]
mod test_clone {
    use crate::integer::MatPolyOverZ;
    use std::str::FromStr;

    /// check if a clone of a [`MatPolyOverZ`] with an entry larger than 64 bits works
    #[test]
    fn large_entries() {
        let u64_string = u64::MAX.to_string();
        let input = format!("[[2  {} -{}]]", u64_string, u64_string);

        let poly_1 = MatPolyOverZ::from_str(&input).unwrap();
        let poly_2 = poly_1.clone();

        // tests where the coefficients are stored. Since both are larger than
        // an i64, both should be a pointer and their values should differ
        unsafe {
            assert_ne!(
                (*(*poly_1.matrix.entries).coeffs.offset(0)).0,
                (*(*poly_2.matrix.entries).coeffs.offset(0)).0
            );
        }
        unsafe {
            assert_ne!(
                (*(*poly_1.matrix.entries).coeffs.offset(1)).0,
                (*(*poly_2.matrix.entries).coeffs.offset(1)).0
            );
        }

        // check if length of polynomial is correctly cloned
        assert_eq!(unsafe { *poly_1.matrix.entries.offset(0) }.length, 2);
        assert_eq!(unsafe { *poly_2.matrix.entries.offset(0) }.length, 2);

        assert_eq!(poly_1, poly_2);
    }

    /// check if several instantiations with small coefficients are cloned correctly
    #[test]
    fn small_examples() {
        let strings = vec!["[[2  0 11]]", "[[2  0 -11]]", "[[2  0 1100]]"];

        for string in strings {
            let poly_1 = MatPolyOverZ::from_str(&string).unwrap();

            let poly_2 = poly_1.clone();

            // Since both coefficients are smaller than an i64,
            // both should be stored directly on stack and their values should be equal
            unsafe {
                assert_eq!(
                    (*(*poly_1.matrix.entries).coeffs.offset(0)).0,
                    (*(*poly_2.matrix.entries).coeffs.offset(0)).0
                );
            }
            unsafe {
                assert_eq!(
                    (*(*poly_1.matrix.entries).coeffs.offset(1)).0,
                    (*(*poly_2.matrix.entries).coeffs.offset(1)).0
                );
            }

            // check if length of polynomial is correctly cloned
            assert_eq!(unsafe { *poly_1.matrix.entries.offset(0) }.length, 2);
            assert_eq!(unsafe { *poly_2.matrix.entries.offset(0) }.length, 2);

            assert_eq!(poly_1, poly_2);
        }
    }

    /// check if a cloned value is still alive after the original value ran out of scope
    #[test]
    #[allow(clippy::redundant_clone)]
    fn keep_alive() {
        let a: MatPolyOverZ;
        {
            let b = MatPolyOverZ::from_str("[[2  0 1],[1  15]]").unwrap();
            a = b.clone();
        }
        assert_eq!(a, MatPolyOverZ::from_str("[[2  0 1],[1  15]]").unwrap());
    }
}

/// Test that the [`Drop`] trait is correctly implemented.
#[cfg(test)]
mod test_drop {

    use super::MatPolyOverZ;
    use std::{collections::HashSet, str::FromStr};

    /// Creates and drops a [`MatPolyOverZ`], and returns the storage points in memory
    fn create_and_drop_poly_over_z() -> i64 {
        let a = MatPolyOverZ::from_str("[[1  36893488147419103232]]").unwrap();
        unsafe { *(*a.matrix.entries).coeffs.offset(0) }.0
    }

    /// Check whether freed memory is reused afterwards
    #[test]
    fn free_memory() {
        let mut set = HashSet::new();

        for _i in 0..5 {
            set.insert(create_and_drop_poly_over_z());
        }

        assert!(set.capacity() < 5);

        let a = MatPolyOverZ::from_str("[[2  36893488147419103232 36893488147419103233]]").unwrap();
        let storage_point = unsafe { *(*a.matrix.entries).coeffs.offset(0) }.0;

        // memory slots differ due to previously created large integer
        let d = MatPolyOverZ::from_str("[[2  36893488147419103232 36893488147419103233]]").unwrap();
        assert_ne!(
            storage_point,
            unsafe { *(*d.matrix.entries).coeffs.offset(0) }.0
        );
    }
}
