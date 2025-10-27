// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get information about a [`MatNTTPolynomialRingZq`] matrix.

use crate::{integer::Z, integer_mod_q::MatNTTPolynomialRingZq};

impl MatNTTPolynomialRingZq {
    /// Returns the number of rows of the matrix as a [`usize`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use qfall_math::traits::*;
    ///
    /// let matrix = MatZq::new(5, 6, 7);
    /// let rows = matrix.get_num_rows();
    /// ```
    pub fn get_num_rows(&self) -> usize {
        self.nr_rows
    }

    /// Returns the number of columns of the matrix as a [`usize`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use qfall_math::traits::*;
    ///
    /// let matrix = MatZq::new(5, 6, 7);
    /// let rows = matrix.get_num_columns();
    /// ```
    pub fn get_num_columns(&self) -> usize {
        self.nr_columns
    }

    pub fn get_entry(&self, row: usize, column: usize) -> &[Z] {
        let index = self.d * row + self.d * self.nr_rows * column;
        &self.matrix[index..index + self.d]
    }
}
