// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module containts the implementation of the `transpose` function.

use super::{MatZ, VecZ};

impl VecZ {
    /// Returns the transposed form of the given matrix, i.e. rows get transformed to columns.
    ///
    /// # Example
    /// ```
    /// use math::integer::MatZ;
    /// use std::str::FromStr;
    ///
    /// let mat = MatZ::from_str("[[2,1],[2,1],[2,1]]").unwrap();
    /// let cmp = MatZ::from_str("[[2,2,2],[1,1,1]]").unwrap();
    ///
    /// assert_eq!(mat.transpose(), cmp);
    /// ```
    pub fn transpose(&self) -> MatZ {
        self.matrix.transpose()
    }
}

#[cfg(test)]
mod test_transpose {

    use super::{MatZ, VecZ};
    use std::str::FromStr;

    // Checks if a vector is correctly converted to a one column matrix
    #[test]
    fn row_to_column() {
        let mat = VecZ::from_str("[1,2,3]").unwrap();
        let cmp = MatZ::from_str("[[1,2,3]]").unwrap();

        assert_eq!(cmp, mat.transpose());
    }
}
