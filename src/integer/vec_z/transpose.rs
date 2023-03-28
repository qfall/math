// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module containts the implementation of the `transpose` function.

use super::VecZ;

impl VecZ {
    /// Returns the transposed form of the given matrix,
    /// i.e. rows get transformed to columns and vice versa.
    ///
    /// # Example
    /// ```
    /// use math::integer::VecZ;
    /// use std::str::FromStr;
    ///
    /// let mat = VecZ::from_str("[[1,2,3]]").unwrap();
    /// let cmp = VecZ::from_str("[[1],[2],[3]]").unwrap();
    ///
    /// assert_eq!(mat.transpose(), cmp);
    /// ```
    pub fn transpose(&self) -> VecZ {
        Self {
            vector: self.vector.transpose(),
        }
    }
}

#[cfg(test)]
mod test_transpose {
    /// Further tests regarding large or small entries are omitted
    /// as they are part of the tests of the here called function
    /// [`MatZ::transpose`](crate::integer::MatZ::transpose)
    use super::VecZ;
    use std::str::FromStr;

    /// Checks if a vector is correctly converted to a one-row matrix
    #[test]
    fn column_to_row() {
        let vec = VecZ::from_str("[[1],[2],[3],[4]]").unwrap();
        let cmp = VecZ::from_str("[[1,2,3,4]]").unwrap();

        assert_eq!(cmp, vec.transpose());
    }

    /// Checks if a vector is correctly converted to a one-column matrix
    #[test]
    fn row_to_column() {
        let vec = VecZ::from_str("[[1,2,3,4,5]]").unwrap();
        let cmp = VecZ::from_str("[[1],[2],[3],[4],[5]]").unwrap();

        assert_eq!(cmp, vec.transpose());
    }
}
