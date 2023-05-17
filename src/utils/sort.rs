// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Contains generic functions for sorting according to certain conditions.

/// Sorts the `cond_vec` and applies all changes to `id_vec` s.t. `id_vec` if
/// initialized with values 0 to n afterwards identifies the sorted permutation.
///
/// Assumes to be initialized with `low = 0`, `high = len(cond_vec) - 1`,
/// `id_vec` to be initialized with increasing values, as well as to be of same length as `cond_vec`.
///
/// Paramters:
/// - `cond_vec`: specifies a slice of entries which display the condition after which
/// is sorted
/// - `low`: specifies the lowest entry of the interval that should be sorted
/// - `high`: specifies the highest entry of the interval that should be sorted
/// - `id_vec`: specifies some identifying numbers in a vector of same length as `cond_vec`
/// to be able to permutate according to the sorting condition afterwards
///
/// # Examples
/// ```compile_fail
/// use qfall_math::utils::sort::quicksort;
///
/// let mut cond_vec = vec![3,2,1];
/// let mut id_vec = vec![0,1,2];
/// let index_last_element = cond_vec.len() - 1;
///
/// quicksort(&mut cond_vec, 0, index_last_element, &mut id_vec);
///
/// assert_eq!(cond_vec, vec![1,2,3]);
/// assert_eq!(id_vec, vec![2,1,0]);
/// ```
pub(crate) fn quicksort(
    cond_vec: &mut [impl PartialOrd],
    low: usize,
    high: usize,
    id_vec: &mut [usize],
) {
    if low < high {
        let pivot_location = partition(cond_vec, low, high, id_vec);
        if pivot_location != 0 {
            quicksort(cond_vec, low, pivot_location - 1, id_vec);
        }
        quicksort(cond_vec, pivot_location + 1, high, id_vec);
    }
}

/// Partitions by choosing `cond_vec[high]` as the pivot element and ensures that
/// all smaller elements are sorted to its left and all bigger ones to its right.
///
/// Paramters:
/// - `cond_vec`: specifies a slice of entries which display the condition after which
/// is sorted
/// - `low`: specifies the lowest entry of the interval that should be sorted
/// - `high`: specifies the highest entry of the interval that should be sorted
/// - `id_vec`: specifies some identifying numbers in a vector of same length as `cond_vec`
/// to be able to permutate according to the sorting condition afterwards
///
/// Returns the final [`usize`] index of this rounds pivot element splitting the
/// matrix / cond_vec with its value in smaller and bigger elements.
fn partition(
    cond_vec: &mut [impl PartialOrd],
    low: usize,
    high: usize,
    id_vec: &mut [usize],
) -> usize {
    // pivot at index `high`
    let mut tmp_pivot_index = low;

    for j in low..high {
        if cond_vec[j] <= cond_vec[high] {
            cond_vec.swap(j, tmp_pivot_index);
            id_vec.swap(j, tmp_pivot_index);
            tmp_pivot_index += 1;
        }
    }

    cond_vec.swap(tmp_pivot_index, high);
    id_vec.swap(tmp_pivot_index, high);

    tmp_pivot_index
}

#[cfg(test)]
mod test_quicksort {
    use super::{partition, quicksort};
    use crate::{integer::Z, rational::Q};

    /// Ensures that the doc test would compile and run correctly
    #[test]
    fn doc_test() {
        let mut cond_vec = vec![3, 2, 1];
        let mut id_vec = vec![0, 1, 2];
        let index_last_element = cond_vec.len() - 1;

        quicksort(&mut cond_vec, 0, index_last_element, &mut id_vec);

        assert_eq!(cond_vec, vec![1, 2, 3]);
        assert_eq!(id_vec, vec![2, 1, 0]);
    }

    /// Ensures that sorting works properly for a larger number of entries
    #[test]
    fn large_sample_number() {
        let mut cond_vec = vec![10, -3, 8, 9, -2, -1, 6, 0, 1, 11, 2, 3, 5, 7, 12, 4];
        let mut id_vec = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        let index_last_element = cond_vec.len() - 1;

        quicksort(&mut cond_vec, 0, index_last_element, &mut id_vec);

        assert_eq!(
            cond_vec,
            vec![-3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
        );
        assert_eq!(
            id_vec,
            vec![1, 4, 5, 7, 8, 10, 11, 15, 12, 6, 13, 2, 3, 0, 9, 14]
        );
    }

    /// Ensures that sorting works properly for condition type [`Z`] implementing [`PartialOrd`]
    #[test]
    fn cond_type_z() {
        let mut cond_vec = vec![Z::from(4), Z::ZERO, Z::from(i64::MIN), Z::from(i64::MAX)];
        let mut id_vec = vec![0, 1, 2, 3];
        let index_last_element = cond_vec.len() - 1;

        quicksort(&mut cond_vec, 0, index_last_element, &mut id_vec);

        assert_eq!(
            cond_vec,
            vec![Z::from(i64::MIN), Z::ZERO, Z::from(4), Z::from(i64::MAX)]
        );
        assert_eq!(id_vec, vec![2, 1, 0, 3]);
    }

    /// Ensures that sorting works properly for condition type [`Q`] implementing [`PartialOrd`]
    #[test]
    fn cond_type_q() {
        let mut cond_vec = vec![Q::ZERO, Q::from(4), Q::from(i64::MAX), Q::from(i64::MIN)];
        let mut id_vec = vec![0, 1, 2, 3];
        let index_last_element = cond_vec.len() - 1;

        quicksort(&mut cond_vec, 0, index_last_element, &mut id_vec);

        assert_eq!(
            cond_vec,
            vec![Q::from(i64::MIN), Q::ZERO, Q::from(4), Q::from(i64::MAX)]
        );
        assert_eq!(id_vec, vec![3, 0, 1, 2]);
    }

    /// Ensures that the pivot is placed correctly s.t. all entries to its left are
    /// smaller than the pivot and to its right are larger in the specified interval
    #[test]
    fn pivot_placement() {
        let mut cond_vec = vec![4, 0, 3, 1, 2, -1];
        let mut id_vec = vec![0, 1, 2, 3, 4, 5];

        partition(&mut cond_vec, 1, 4, &mut id_vec);

        assert_eq!(cond_vec, vec![4, 0, 1, 2, 3, -1]);
        assert_eq!(id_vec, vec![0, 1, 3, 4, 2, 5]);
    }
}
