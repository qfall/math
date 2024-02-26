// Copyright © 2023 Marcel Luca Schmidt, Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations to solve systems of linear equations
//! over [`MatZq`] with arbitrary moduli.

use super::MatZq;
use crate::{
    integer::{MatZ, Z},
    integer_mod_q::Zq,
    traits::{Concatenate, Gcd, GetEntry, GetNumColumns, GetNumRows, Pow, SetEntry, Xgcd},
    utils::Factorization,
};

impl MatZq {
    /// Computes a solution for a system of linear equations under a certain modulus.
    /// It solves `Ax = y` for `x` with `A` being a [`MatZq`] value.
    /// If no solution is found, `None` is returned.
    /// The function uses Gaussian elimination together with Factor refinement
    /// to split the modulus and the Chinese remainder theorem and Hensel lifting
    /// to combine solutions under the split modulus.
    /// For Hensel lifting we use the method from [\[1\]](<index.html#:~:text=[1]>).
    ///
    /// Note that this function does not compute a solution whenever there is one.
    /// If the matrix has not full rank under a modulus that divides the given one,
    /// `None` may be returned even if the system may be solvable.
    /// If the number of columns exceeds the number of rows by a factor of 2,
    /// this is very unlikely to happen.
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
    /// let mat = MatZq::from_str("[[2, 2, 3],[2, 5, 7]] mod 8").unwrap();
    /// let y = MatZq::from_str("[[3],[5]] mod 8").unwrap();
    /// let x = mat.solve_gaussian_elimination(&y).unwrap();
    ///
    /// assert_eq!(y, mat*x);
    /// ```
    ///
    /// # Panics ...
    /// - if the the number of rows of the matrix and the syndrome are different.
    /// - if the syndrome is not a column vector.
    /// - if the moduli mismatch.
    pub fn solve_gaussian_elimination(&self, y: &MatZq) -> Option<MatZq> {
        assert!(y.is_column_vector(), "The syndrome is not a column vector.");
        assert_eq!(
            y.get_num_rows(),
            self.get_num_rows(),
            "The syndrome and the matrix have a different number of rows."
        );
        assert_eq!(
            y.get_mod(),
            self.get_mod(),
            "The syndrome and the matrix have a different modulus"
        );

        // Append the solution vector to easily perform gaussian elimination.
        let mut matrix = self.concat_horizontal(y).unwrap();

        // Saves the indices of row and column, where we created a 1 entry
        // such that we do not have to go through the matrix afterwards.
        let mut indices = Vec::new();

        for column_nr in 0..self.get_num_columns() {
            let used_rows: Vec<i64> = indices.iter().map(|(row, _)| *row).collect();
            // Try to solve the system with the current modulus or
            // try to find a not invertible entry to split the modulus.
            if let Some((row_nr, inv)) =
                find_invertible_entry_column(&matrix, column_nr, &used_rows)
            {
                // Save the position of `1` for that column.
                indices.push((row_nr, column_nr));

                matrix.gauss_row_reduction(row_nr, column_nr, inv);
            } else if let Some(row_nr) =
                find_not_invertible_entry_column(&matrix, column_nr, &used_rows)
            {
                let entry: Z = matrix.get_entry(row_nr, column_nr).unwrap();

                // Factorize the modulus with the found entry, compute solutions
                // for the system under the split modulus and use the
                // Chinese Remainder Theorem to compute a solution based on these
                // sub-solutions.
                return self.factorization_and_crt(y, entry);
            }
        }

        // Set the entries of the output vector using the indices vector.
        let mut out = MatZq::new(self.get_num_columns(), 1, &matrix.get_mod());
        for (i, j) in indices.iter() {
            let entry: Z = matrix.get_entry(*i, -1).unwrap();
            out.set_entry(*j, 0, entry).unwrap();
        }

        Some(out)
    }

    /// Performs a row reduction from gaussian elimination, given an entry of
    /// the matrix and its inverse.
    /// Multiplies the given row of a matrix by the given inverse and reduces all
    /// other rows such that they have zeros in the given column.
    ///
    /// Parameters:
    /// - `row_nr`: The row where the entry is located
    /// - `column_nr`: The column where the entry is located
    /// - `inverse`: The inverse of the entry located at (row_nr, column_nr)
    fn gauss_row_reduction(&mut self, row_nr: i64, column_nr: i64, inverse: Zq) {
        let row = &self.get_row(row_nr).unwrap() * &inverse;
        self.set_row(row_nr, &row, 0).unwrap();

        // Set all other entries in that column to `0` (gaussian elimination).
        for row_nr in (0..self.get_num_rows()).filter(|x| *x != row_nr) {
            let entry: Z = self.get_entry(row_nr, column_nr).unwrap();
            if !entry.is_zero() {
                let old_row = self.get_row_mut(row_nr).unwrap();
                let new_row = &old_row - &(&entry * &row);
                drop(old_row);
                self.set_row(row_nr, &new_row, 0).unwrap();
            }
        }
    }

    /// Computes a solution for a system of linear equations under a certain modulus.
    /// It solves `Ax = y` for `x` with `A` being a [`MatZq`] value by first computing a
    /// factorization of the modulus, given an entry of the matrix that is not co-prime
    /// to the modulus.
    /// After that, it computes solutions for the system under the new factors and
    /// combines these solutions using the Chinese Remainder Theorem.
    /// If no solution is found, `None` is returned.
    ///
    /// Note that this function does not compute a solution whenever there is one.
    /// If the matrix has not full rank under a modulus that divides the given one,
    /// `None` may be returned even if the system may be solvable.
    /// If the number of columns exceeds the number of rows by a factor of 2,
    /// this is very unlikely to happen.
    ///
    /// Note that this function is a part of `solve_gaussian_elimination` and
    /// does not check for the correctness of the given parameters.
    ///
    /// Parameters:
    /// - `y`: The syndrome for which a solution has to be computed.
    /// - `entry`: A [`Z`] value that is not co-prime to the modulus.
    ///
    /// Returns a solution for the linear system or `None`, if none could be computed.
    fn factorization_and_crt(&self, y: &MatZq, entry: Z) -> Option<MatZq> {
        let modulus = Z::from(self.get_mod());
        let gcd = modulus.gcd(entry);

        let mut fac = Factorization::from((&gcd, &(modulus / &gcd).get_numerator()));
        fac.refine();
        let fac_vec = Vec::<(Z, u64)>::from(&fac);

        // Solve the equation under the different moduli.
        let mut solutions: Vec<MatZq> = vec![];
        for factor in fac_vec.iter() {
            let mut matrix = self.clone();
            let mut y = y.clone();
            matrix.change_modulus(factor.0.pow(factor.1).unwrap());
            y.change_modulus(factor.0.pow(factor.1).unwrap());

            // Compute a solution under the modulus z^a.
            if factor.1 > 1 {
                solutions.push(matrix.solve_hensel(&y, &factor.0, &factor.1)?);
            // Compute a solution under the new modulus.
            } else {
                solutions.push(matrix.solve_gaussian_elimination(&y)?);
            }
        }
        // Connect the solutions via the Chinese Remainder Theorem.
        self.crt_mat_zq(solutions, fac_vec)
    }

    /// Given a system of linear equations `Ax = y` with `A` being a [`MatZq`] value,
    /// this function combines solutions `x`for this system under co-prime moduli
    /// with the Chinese remainder theorem.
    /// If no solution exists, `None` is returned.
    ///
    /// Note that this function does not check for the correctness of the given
    /// parameters.
    ///
    /// Parameters:
    /// - `solutions`: The solutions under the co-prime moduli.
    /// - `moduli`: The moduli of the solutions in the form `z^a`.
    ///
    /// Returns a solution for the linear system or `None`, if none could be computed.
    ///
    /// # Panics ...
    /// - if the the number of elements in `solutions` is greater than the number
    /// of elements in `moduli`.
    fn crt_mat_zq(&self, mut solutions: Vec<MatZq>, mut moduli: Vec<(Z, u64)>) -> Option<MatZq> {
        while solutions.len() > 1 {
            // Compute Bézout’s identity: a x_1 + b x_2 = 1
            // by computing xgcd(x_1, x_2).
            let x_2_exponent = moduli.pop().unwrap();
            let x_1_exponent = moduli.pop().unwrap();
            let x_1 = x_1_exponent.0.pow(x_1_exponent.1).unwrap();
            let x_2 = x_2_exponent.0.pow(x_2_exponent.1).unwrap();
            let (_gcd, a, b) = x_1.xgcd(&x_2);
            let mut s_2 = solutions.pop().unwrap();
            let mut s_1 = solutions.pop().unwrap();
            s_2.change_modulus(Z::from(s_2.get_mod()) * Z::from(s_1.get_mod()));
            s_1.change_modulus(s_2.get_mod());
            solutions.push(s_2 * a * &x_1 + s_1 * b * &x_2);
            moduli.push((x_1 * x_2, 1));
        }
        solutions.pop()
    }

    /// Computes a solution for a system of linear equations under a modulus
    /// of the form `z^a`with the help of [\[1\]](<index.html#:~:text=[1]>).
    /// It solves `Ax = y` for `x` with `A` being a [`MatZq`] value.
    /// If no solution is found, `None` is returned.
    ///
    /// Note that this function does not compute a solution whenever there is one.
    /// If the matrix has not full rank under a modulus that divides the given one,
    /// `None` may be returned even if the system may be solvable.
    /// If the number of columns exceeds the number of rows by a factor of 2,
    /// this is very unlikely to happen.
    ///
    /// Note that this function is a part of `solve_gaussian_elimination` and
    /// does not check for the correctness of the given parameters.
    ///
    /// Parameters:
    /// - `y`: The syndrome for which a solution has to be computed.
    /// - `base`: The base of the modulus.
    /// - `power`: The power of the modulus.
    ///
    /// Returns a solution for the linear system or `None`, if none could be computed.
    fn solve_hensel(&self, y: &MatZq, base: &Z, power: &u64) -> Option<MatZq> {
        // Set `matrix_base` to the given matrix under `base` as the modulus to
        // compute a solution for the system under `base` as modulus.
        let mut matrix_base = self.clone();
        matrix_base.change_modulus(base);

        // Concatenate the matrix with the identity matrix under `base`
        // as its modulus to apply gaussian elimination on it.
        let mut matrix_identity_base_gauss = matrix_base
            .concat_horizontal(&MatZq::identity(
                self.get_num_rows(),
                self.get_num_rows(),
                base,
            ))
            .unwrap();

        // Saves the indices of row and column, where we created a 1 entry
        // such that we do not have to go through the matrix afterwards.
        let mut indices: Vec<(i64, i64)> = Vec::new();
        let mut used_rows: Vec<i64> = Vec::new();
        let mut row_count = 0;

        // Saves the permutation of the gaussian elimination.
        let mut permutation: Vec<i64> = vec![];
        for i in 0..self.get_num_rows() {
            permutation.push(i);
        }
        for column_nr in 0..self.get_num_columns() {
            if !indices.is_empty() && indices[indices.len() - 1].0 >= self.get_num_rows() {
                break;
            }

            // Try to solve the system under the current modulus.
            if let Some((row_nr, inv)) =
                find_invertible_entry_column(&matrix_identity_base_gauss, column_nr, &used_rows)
            {
                matrix_identity_base_gauss.gauss_row_reduction(row_nr, column_nr, inv);

                if row_count != row_nr {
                    matrix_identity_base_gauss
                        .swap_rows(row_count, row_nr)
                        .unwrap();

                    permutation.swap(row_count.try_into().unwrap(), row_nr.try_into().unwrap());
                }

                // Save the position of `1` for that row.
                indices.push((row_count, column_nr));
                used_rows.push(indices[indices.len() - 1].0);
                row_count += 1;
            // Search for a not invertible entry to divide the modulus.
            } else if let Some(row_nr) =
                find_not_invertible_entry_column(&matrix_identity_base_gauss, column_nr, &used_rows)
            {
                // Factorize the modulus with the found entry, compute solutions
                // for the system under the split modulus and use the
                // Chinese Remainder Theorem to compute a solution based on these
                // sub-solutions.
                let entry: Z = matrix_identity_base_gauss
                    .get_entry(row_nr, column_nr)
                    .unwrap();
                self.factorization_and_crt(y, entry);
            }
        }

        // Return `None` if the matrix has no full rank.
        if indices.is_empty()
            || indices[indices.len() - 1].0 + 1 < matrix_identity_base_gauss.get_num_rows()
        {
            return None;
        }

        // Pick the first columns out of the original matrix that form an invertible matrix.
        // Those columns exist, since the matrix was checked to be full rank.
        let mut invertible_matrix = MatZq::new(
            matrix_identity_base_gauss.get_num_rows(),
            matrix_identity_base_gauss.get_num_rows(),
            self.get_mod(),
        );
        for (current_column, (_row_nr, column_nr)) in indices.iter().enumerate() {
            invertible_matrix
                .set_column(current_column, self, *column_nr)
                .unwrap();
        }

        // The inverse of the previously picked square matrix consists of the last
        // columns of `matrix_identity_base_gauss`, since we concatenated an identity matrix.
        let mut matrix_identity_gauss = matrix_identity_base_gauss;
        matrix_identity_gauss.change_modulus(self.get_mod());
        let mut matrix_base_inv = MatZq::new(
            matrix_identity_gauss.get_num_rows(),
            matrix_identity_gauss.get_num_rows(),
            self.get_mod(),
        );
        for row_nr in 0..matrix_identity_gauss.get_num_rows() {
            matrix_base_inv
                .set_column(
                    row_nr,
                    &matrix_identity_gauss,
                    row_nr + self.get_num_columns(),
                )
                .unwrap();
        }

        // Use the method from [\[1\]](<index.html#:~:text=[1]>)
        // to compute a solution for the original system.
        let mut b_i = y.clone();
        let mut x_i = &matrix_base_inv * &b_i;
        let mut x = x_i.clone();
        for i in 1..*power {
            b_i = MatZq::from((
                &(unsafe { MatZ::from(&(b_i - &invertible_matrix * x_i)).div_exact(base) }),
                &self.get_mod(),
            ));
            x_i = &matrix_base_inv * &b_i;
            x = x + &x_i * &base.pow(i).unwrap();
        }

        let mut out = MatZq::new(self.get_num_columns(), 1, self.get_mod());
        for (current_row_x, (_row_nr, column_nr)) in indices.into_iter().enumerate() {
            let entry: Z = x.get_entry(current_row_x, 0).unwrap();
            out.set_entry(column_nr, 0, entry).unwrap();
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
    used_rows: &[i64],
) -> Option<(i64, Zq)> {
    for i in (0..matrix.get_num_rows()).filter(|x| !used_rows.contains(x)) {
        let entry: Zq = matrix.get_entry(i, column).unwrap();
        if let Ok(inv) = entry.pow(-1) {
            return Some((i, inv));
        }
    }
    None
}

/// Returns the row of the first not invertible entry of that column, that is not 0.
/// If there is no not invertible element unequal to 0, `None` is returned.
/// The rows specified in `used_rows` will be ignored.
///
/// Parameters:
/// - `matrix`: The matrix in which entries are searched for
/// - `column`: The column for which we are trying to find an invertible element
/// - `used_rows`: The rows which are not scanned for invertible elements
///
/// Returns the row and the entry of the first not invertible element in that column,
/// that is not 0, and `None` if there is no such element
fn find_not_invertible_entry_column(matrix: &MatZq, column: i64, used_rows: &[i64]) -> Option<i64> {
    for i in (0..matrix.get_num_rows()).filter(|x| !used_rows.contains(x)) {
        let entry: Zq = matrix.get_entry(i, column).unwrap();
        if !entry.is_zero() {
            if let Err(_inv) = entry.pow(-1) {
                return Some(i);
            }
        }
    }
    None
}

#[cfg(test)]
mod test_solve_gauss {
    use crate::{
        integer::Z,
        integer_mod_q::{MatZq, Modulus},
        traits::Pow,
    };
    use std::str::FromStr;

    /// Ensure that a solution is found with prime modulus.
    #[test]
    fn solution_prime_modulus() {
        let mat = MatZq::from_str("[[5, 6],[11, 12]] mod 13").unwrap();
        let y = MatZq::from_str("[[5],[2]] mod 13").unwrap();

        let x = mat.solve_gaussian_elimination(&y).unwrap();

        let cmp_sol = MatZq::from_str("[[5],[1]] mod 13").unwrap();
        assert_eq!(cmp_sol, x);
    }

    /// Ensure that a solution is found with prime modulus and more rows than columns.
    #[test]
    fn solution_more_rows_than_columns_prime() {
        let mat = MatZq::from_str("[[5, 6],[11, 12],[11, 12]] mod 13").unwrap();
        let y = MatZq::from_str("[[5],[2],[2]] mod 13").unwrap();

        let x = mat.solve_gaussian_elimination(&y).unwrap();

        let cmp_sol = MatZq::from_str("[[5],[1]] mod 13").unwrap();
        assert_eq!(cmp_sol, x);
    }

    /// Ensure that a solution is found with invertible columns.
    #[test]
    fn solution_invertible_columns() {
        let mat = MatZq::from_str("[[3, 1],[11, 13]] mod 20").unwrap();
        let y = MatZq::from_str("[[5],[2]] mod 20").unwrap();

        let x = mat.solve_gaussian_elimination(&y).unwrap();

        let cmp_sol = MatZq::from_str("[[11],[12]] mod 20").unwrap();
        assert_eq!(cmp_sol, x);
    }

    /// Ensure that a solution is found, even if the matrix contains a
    /// column that is not invertible.
    #[test]
    fn solution_with_one_uninvertible_column() {
        let mat = MatZq::from_str("[[2, 1],[3, 1]] mod 210").unwrap();
        let y = MatZq::from_str("[[5],[2]] mod 210").unwrap();

        let x = mat.solve_gaussian_elimination(&y).unwrap();

        let cmp_sol = MatZq::from_str("[[207],[11]] mod 210").unwrap();
        assert_eq!(cmp_sol, x);
    }

    /// Ensure that a solution is found, even if the matrix contains no
    /// column that is invertible.
    #[test]
    fn solution_without_invertible_columns() {
        let mat = MatZq::from_str("[[2, 1],[6, 2]] mod 6").unwrap();
        let y = MatZq::from_str("[[5],[2]] mod 6").unwrap();

        let x = mat.solve_gaussian_elimination(&y).unwrap();

        let cmp_sol = MatZq::from_str("[[2],[1]] mod 6").unwrap();
        assert_eq!(cmp_sol, x);
    }

    /// Ensure that a solution is found, even if the modulus is a power of a prime.
    #[test]
    fn solution_prime_power() {
        let mat = MatZq::from_str("[[2, 2, 3],[2, 5, 7]] mod 8").unwrap();
        let y = MatZq::from_str("[[0],[1]] mod 8").unwrap();

        let x = mat.solve_gaussian_elimination(&y).unwrap();

        assert_eq!(MatZq::from_str("[[0],[3],[6]] mod 8").unwrap(), x)
    }

    /// Ensure that the trivial solution can always be computed.
    #[test]
    fn trivial() {
        let mat = MatZq::from_str("[[2, 2, 3],[2, 5, 7]] mod 8").unwrap();
        let y = MatZq::from_str("[[0],[0]] mod 8").unwrap();

        let x = mat.solve_gaussian_elimination(&y).unwrap();

        assert_eq!(MatZq::new(3, 1, mat.get_mod()), x);
    }

    /// Ensure that a solution containing only one vector of the matrix is found.
    #[test]
    fn simple() {
        let mat = MatZq::from_str("[[2, 2, 3],[2, 5, 7]] mod 1048576").unwrap();
        let y = MatZq::from_str("[[0],[1]] mod 1048576").unwrap();

        let x = mat.solve_gaussian_elimination(&y).unwrap();

        assert_eq!(y, mat * x);
    }

    /// Ensure that a solution is found, even if the modulus is a large power of a prime.
    #[test]
    fn large_modulus() {
        let modulus = Modulus::from(Z::from(2).pow(50).unwrap());

        // matrix of size `n x 2n * log q`, hence almost always invertible
        let mat = MatZq::sample_uniform(10, 10 * 2 * 50, &modulus);
        let y = MatZq::sample_uniform(10, 1, &modulus);

        let x = mat.solve_gaussian_elimination(&y).unwrap();

        assert_eq!(y, mat * x)
    }

    /// Ensure that a solution is found, even if a matrix in `solve_hensel` has
    /// rows containing only zeros after gaussian elimination.
    #[test]
    #[ignore]
    fn solution_zero_rows() {
        let mat = MatZq::from_str("[[6, 1],[3, 1]] mod 36").unwrap();
        let y = MatZq::from_str("[[6],[3]] mod 36").unwrap();

        let x = mat.solve_gaussian_elimination(&y).unwrap();

        let cmp_sol = MatZq::from_str("[[1],[0]] mod 6").unwrap();
        assert_eq!(cmp_sol, x);
    }

    /// Ensure that a solution is found with prime modulus and more rows than columns
    /// (This test does not work with the current implementation).
    #[test]
    #[ignore]
    fn solution_more_rows() {
        let mat = MatZq::from_str("[[5, 6],[11, 12],[11, 12]] mod 20").unwrap();
        let y = MatZq::from_str("[[5],[2],[2]] mod 20").unwrap();

        let x = mat.solve_gaussian_elimination(&y).unwrap();

        let cmp_sol = MatZq::from_str("[[5],[1]] mod 20").unwrap();
        assert_eq!(cmp_sol, x);
    }

    /// Ensure that a solution is found in random matrices (for testing purposes).
    #[test]
    #[ignore]
    fn random_matrix_modulus() {
        // modulus: 2:100,      rows: 1:10,     columns: 1:10    => <7% false Nones
        // modulus: 2:10000,    rows: 1:10,     columns: 1:10    => <7% false Nones
        // modulus: 2:10000,    rows: 1:10,     columns: 10:20   => <0.5% false Nones
        // modulus: 2:10000,    rows: 50:100,   columns: 100:200 => not measurable

        let mut none_count = 0;
        let mut correct_count = 0;
        let mut false_count = 0;

        for i in 0..1000 {
            let modulus_sample = Z::sample_uniform(2, 10000).unwrap();
            let row_sample = &Z::sample_uniform(50, 100).unwrap();
            let column_sample = &Z::sample_uniform(100, 200).unwrap();

            let modulus = Modulus::from(modulus_sample);
            let mat = MatZq::sample_uniform(row_sample, column_sample, &modulus);
            let x = MatZq::sample_uniform(column_sample, 1, &modulus);
            let y = &mat * &x;

            if let Some(solution) = mat.solve_gaussian_elimination(&y) {
                if &mat * &solution == y {
                    correct_count += 1;
                    println!("{}: Correct!", i);
                } else {
                    false_count += 1;
                    println!("{}: False", i);
                    println!("\t Matrix: {} \n\t y: {} \n\t x: {}", &mat, y, &x);
                }
            } else {
                none_count += 1;
                println!("{}: None", i);
                println!("\t Matrix: {} \n\t y: {} \n\t x: {}", mat, y, x);
            }
        }

        println!("Nones: {}", none_count);
        println!("Corrects: {}", correct_count);
        println!("False: {}", false_count);
    }

    /// Ensure that for different moduli the function panics.
    #[test]
    #[should_panic]
    fn different_moduli() {
        let mat = MatZq::from_str("[[2, 2, 3],[2, 5, 7]] mod 8").unwrap();
        let y = MatZq::from_str("[[0],[0]] mod 7").unwrap();
        let _ = mat.solve_gaussian_elimination(&y).unwrap();
    }

    /// Ensure that for different number of rows the function panics.
    #[test]
    #[should_panic]
    fn different_nr_rows() {
        let mat = MatZq::from_str("[[2, 2, 3],[2, 5, 7]] mod 8").unwrap();
        let y = MatZq::from_str("[[0],[0],[0]] mod 8").unwrap();
        let _ = mat.solve_gaussian_elimination(&y).unwrap();
    }

    /// Ensure that for non-column vectors, the function panics.
    #[test]
    #[should_panic]
    fn not_column_vector() {
        let mat = MatZq::from_str("[[2, 2, 3],[2, 5, 7]] mod 8").unwrap();
        let y = MatZq::from_str("[[0, 1],[0, 1]] mod 8").unwrap();
        let _ = mat.solve_gaussian_elimination(&y).unwrap();
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
    /// if it has an inverse.
    #[test]
    fn find_correct_entry() {
        let mat = MatZq::from_str("[[7],[5]] mod 8").unwrap();

        let (i, entry) = find_invertible_entry_column(&mat, 0, &Vec::new()).unwrap();
        assert_eq!(0, i);
        assert_eq!(Z::from(7), entry.get_value());

        let (i, entry) = find_invertible_entry_column(&mat, 0, [0].as_ref()).unwrap();
        assert_eq!(1, i);
        assert_eq!(Z::from(5), entry.get_value());

        let invert = find_invertible_entry_column(&mat, 0, [0, 1].as_ref());
        assert!(invert.is_none())
    }
}

#[cfg(test)]
mod test_find_uninvertible_entry_column {
    use crate::integer_mod_q::{mat_zq::solve::find_not_invertible_entry_column, MatZq};
    use std::str::FromStr;

    /// Ensure that the first element is returned, that is not invertible
    /// (if no entries are invertible in a column).
    #[test]
    fn find_correct_entry() {
        let mat = MatZq::from_str("[[4],[2]] mod 8").unwrap();

        let i = find_not_invertible_entry_column(&mat, 0, &Vec::new()).unwrap();
        assert_eq!(0, i);

        let i = find_not_invertible_entry_column(&mat, 0, [0].as_ref()).unwrap();
        assert_eq!(1, i);

        let invert = find_not_invertible_entry_column(&mat, 0, [0, 1].as_ref());
        assert!(invert.is_none())
    }
}
