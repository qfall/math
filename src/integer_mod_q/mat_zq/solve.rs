// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations to solve linear equations over [`MatZq`]
//! with arbitrary moduli.

use super::MatZq;
use crate::{
    integer::Z,
    integer_mod_q::Zq,
    traits::{Concatenate, GetEntry, GetNumColumns, GetNumRows, Pow, SetEntry},
};

impl MatZq {
    /// Computes a solution for a system of linear equations under a certain modulus
    /// It solves `Ax = y` for `x` as a [MatZq].
    /// If no solution is found, `None` is returned
    ///
    /// Note that this function does not compute a solution whenever there is one.
    /// The complete correctness will be dealt with in the corresponding reference (TODO: Referenced in issue)
    ///
    /// Parameters:
    /// - `y`: The syndrome for which a solution has to be computed.
    ///
    /// Returns a solution for the linear system or `None`, if none could be computed.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::MatZq;
    /// use std::str::FromStr;
    ///
    /// let mat = MatZq::from_str("[[2,2,3],[2,5,7]] mod 8").unwrap();
    /// let y = MatZq::from_str("[[3],[5]] mod 8").unwrap();
    /// let x = mat.solve_gaussian_elimination(&y).unwrap();
    /// ```
    pub fn solve_gaussian_elimination(&self, y: &MatZq) -> Option<MatZq> {
        // append the solution vector to easily perform gaussian elimination
        let mut matrix = self.concat_horizontal(y).ok()?;

        // saves the indices, such that we do not have to go through the matrix after
        let mut indices = Vec::new();

        for j in 0..self.get_num_columns() {
            let used_rows = indices.iter().map(|(x, _)| *x).collect();
            if let Some((row_nr, inv)) = find_invertible_entry_column(&matrix, j, used_rows) {
                // save the position of `1` for that row
                indices.push((row_nr, j));
                let row = inv * matrix.get_row(row_nr).ok()?;
                matrix.set_row(row_nr, &row, 0).ok()?;

                // set all other entries in that column to `0` (gaussian elimination)
                for k in (0..matrix.get_num_rows()).filter(|x| *x != row_nr) {
                    let old_row = matrix.get_row(k).ok()?;
                    let entry: Z = old_row.get_entry(0, j).ok()?;
                    let new_row = &old_row - entry * &row;
                    matrix.set_row(k, &new_row, 0).ok()?;
                }
            }
        }

        // set the entries of the output vector using the indices vector
        let mut out = MatZq::new(self.get_num_columns(), 1, &matrix.get_mod()).ok()?;
        for (i, j) in indices.iter() {
            let entry: Z = matrix.get_entry(*i, matrix.get_num_columns() - 1).ok()?;
            out.set_entry(*j, 0, &entry).ok()?;
        }

        // check if we have computed a solution and return `None`
        if &(self * &out) != y {
            return None;
        }

        Some(out)
    }
}

/// Returns the row of the first invertible entry of that column
/// together with that specific invertible element.
/// If there is no invertible element, `None` is returned.
/// The rows specified in `used_rows` will be ignored.
///
/// Parameters:
/// - `matrix`: The matrix in which entries are searched for
/// - `column`: The column for which we are trying to find an invertible element
/// - `used_rows`: The rows which are not scanned for invertible elements
///
/// Returns the row and the entry of the first invertible element in that column, and
/// `None` if there is no such element
fn find_invertible_entry_column(
    matrix: &MatZq,
    column: i64,
    used_rows: Vec<i64>,
) -> Option<(i64, Zq)> {
    for i in (0..matrix.get_num_rows()).filter(|x| !used_rows.contains(x)) {
        let entry: Zq = matrix.get_entry(i, column).unwrap();
        if let Ok(inv) = entry.pow(-1) {
            return Some((i, inv));
        }
    }
    None
}

#[cfg(test)]
mod test_solve {
    use crate::{
        integer::Z,
        integer_mod_q::{MatZq, Modulus},
        traits::Pow,
    };
    use std::str::FromStr;

    /// Ensure that a solution is found, even if the matrix contains a
    /// column that is not invertible
    #[test]
    fn large_matrix() {
        // matrix of size `n x 2n\log q`, hence almost always invertible
        let mat = MatZq::sample_uniform(
            10,
            10 * 2 * 50,
            &Modulus::try_from(&Z::from(2).pow(50).unwrap()).unwrap(),
        )
        .unwrap();
        let y = MatZq::sample_uniform(
            10,
            1,
            &Modulus::try_from(&Z::from(2).pow(50).unwrap()).unwrap(),
        )
        .unwrap();

        let x = mat.solve_gaussian_elimination(&y).unwrap();

        assert_eq!(y, mat * x)
    }

    /// Ensure that a solution is found, even if the matrix contains a
    /// column that is not invertible
    #[test]
    #[ignore] // TODO: remove ignore, once issue is closed
    fn solution_without_invertible_columns() {
        let mat = MatZq::from_str("[[2,1],[3,1]] mod 6").unwrap();
        let y = MatZq::from_str("[[5],[2]] mod 6").unwrap();

        let x = mat.solve_gaussian_elimination(&y).unwrap();

        let cmp_sol = MatZq::from_str("[[3],[5]] mod 6").unwrap();
        assert_eq!(cmp_sol, x);
    }

    /// Ensure that `None` is returned, if there is no solution
    #[test]
    fn working() {
        let mat = MatZq::from_str("[[2,2,3],[2,5,7]] mod 8").unwrap();
        let y = MatZq::from_str("[[3],[5]] mod 8").unwrap();
        let x = mat.solve_gaussian_elimination(&y).unwrap();

        println!("{x}");
    }

    /// Ensure that the trivial solution can always be computed
    #[test]
    fn trivial_solution() {
        let mat = MatZq::from_str("[[2,2,3],[2,5,7]] mod 8").unwrap();
        let y = MatZq::from_str("[[0],[0]] mod 8").unwrap();
        let x = mat.solve_gaussian_elimination(&y).unwrap();

        assert_eq!(MatZq::new(3, 1, mat.get_mod()).unwrap(), x)
    }

    /// Ensure that for different moduli the function panics
    #[test]
    #[should_panic]
    fn different_moduli() {
        let mat = MatZq::from_str("[[2,2,3],[2,5,7]] mod 8").unwrap();
        let y = MatZq::from_str("[[0],[0]] mod 7").unwrap();
        let x = mat.solve_gaussian_elimination(&y).unwrap();

        assert_eq!(MatZq::new(3, 1, mat.get_mod()).unwrap(), x)
    }

    /// Ensure that for different lengths the function panics
    #[test]
    #[should_panic]
    fn different_sizes() {
        let mat = MatZq::from_str("[[2,2,3],[2,5,7]] mod 8").unwrap();
        let y = MatZq::from_str("[[0],[0],[0]] mod 8").unwrap();
        let x = mat.solve_gaussian_elimination(&y).unwrap();

        assert_eq!(MatZq::new(3, 1, mat.get_mod()).unwrap(), x)
    }
}

#[cfg(test)]
mod test_find_invertible_entry_column {
    use crate::{
        integer::Z,
        integer_mod_q::{mat_zq::solve::find_invertible_entry_column, MatZq},
    };
    use std::str::FromStr;

    /// Ensure that the inverse of the first element is returned with the correct entry
    /// if it has an inverse
    #[test]
    fn find_correct_entry() {
        let mat = MatZq::from_str("[[7],[5]] mod 8").unwrap();

        let (i, entry) = find_invertible_entry_column(&mat, 0, Vec::new()).unwrap();
        assert_eq!(0, i);
        assert_eq!(Z::from(7), entry.get_value());

        let (i, entry) = find_invertible_entry_column(&mat, 0, [0].to_vec()).unwrap();
        assert_eq!(1, i);
        assert_eq!(Z::from(5), entry.get_value());

        let invert = find_invertible_entry_column(&mat, 0, [0, 1].to_vec());
        assert!(invert.is_none())
    }
}
