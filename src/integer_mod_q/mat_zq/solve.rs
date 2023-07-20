// Copyright © 2023 Marcel Luca Schmidt, Marvin Beckmann
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
    integer::{Factorization, MatZ, Z},
    integer_mod_q::{Modulus, Zq},
    traits::{Concatenate, Gcd, GetEntry, GetNumColumns, GetNumRows, Pow, SetEntry, Xgcd},
};

impl MatZq {
    /// Computes a solution for a system of linear equations under a certain modulus.
    /// It solves `Ax = y` for `x` with `A` being a [MatZq] value.
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
    ///
    /// assert_eq!(y, mat*x);
    /// ```
    ///
    /// # Panics ...
    /// - if the the number of rows of the matrix and the syndrome are different.
    /// - if the syndrome is not a column vector.
    /// - if the moduli mismatch.
    pub fn solve_gaussian_elimination(&self, result: &MatZq) -> Option<MatZq> {
        assert!(
            result.is_column_vector(),
            "The syndrome is not a column vector."
        );
        assert_eq!(
            result.get_num_rows(),
            self.get_num_rows(),
            "The syndrome and the matrix have a different number of rows."
        );
        assert_eq!(
            result.get_mod(),
            self.get_mod(),
            "The syndrome and the matrix have a different modulus"
        );

        // append the solution vector to easily perform gaussian elimination
        let mut matrix = self.concat_horizontal(result).ok()?;

        // saves the indices of row and column, where we created a 1 entry
        // such that we do not have to go through the matrix afterwards
        let mut indices = Vec::new();

        println!("impossible");

        for column_nr in 0..self.get_num_columns() {
            let used_rows: Vec<i64> = indices.iter().map(|(row, _)| *row).collect();
            // try to solve with current modulus
            if let Some((row_nr, inv)) =
                find_invertible_entry_column(&matrix, column_nr, used_rows.clone())
            {
                // save the position of `1` for that row
                indices.push((row_nr, column_nr));
                let row = inv * matrix.get_row(row_nr).ok()?;
                matrix.set_row(row_nr, &row, 0).ok()?;

                // set all other entries in that column to `0` (gaussian elimination)
                for row_nr in (0..matrix.get_num_rows()).filter(|x| *x != row_nr) {
                    let old_row = matrix.get_row(row_nr).ok()?;
                    let entry: Z = old_row.get_entry(0, column_nr).ok()?;
                    let new_row = &old_row - entry * &row;
                    matrix.set_row(row_nr, &new_row, 0).ok()?;
                }
            // search for not invertible entry to divide modulus
            } else if let Some(row_nr) =
                find_not_invertible_entry_column(&matrix, column_nr, used_rows)
            {
                // factorise the modulus with the found entry
                let entry: Z = matrix.get_entry(row_nr, column_nr).ok()?;
                let gcd = Z::from(self.get_mod()).gcd(entry);
                let mut fac =
                    Factorization::from((&gcd, &(Z::from(self.get_mod()) / &gcd).get_numerator()));
                fac.refine();
                let mut fac_vec = Vec::<(Z, u64)>::from(&fac);

                // solve the equation under the different moduli
                let mut solutions: Vec<MatZq> = vec![];
                for factor in fac_vec.iter() {
                    // compute solution under the modulus p^m with p prime according to TODO
                    if factor.1 > 1 {
                        solutions.push(
                            MatZq::from((
                                &MatZ::from(self),
                                &Modulus::from(&factor.0.pow(factor.1).unwrap()),
                            ))
                            .solve_hensel(
                                &MatZq::from((
                                    &MatZ::from(result),
                                    &Modulus::from(&factor.0.pow(factor.1).unwrap()),
                                )),
                                &factor.0,
                                &factor.1,
                            )?,
                        );
                    // try to compute solution with new modulus
                    } else {
                        solutions.push(
                            MatZq::from((
                                &MatZ::from(self),
                                &Modulus::from(&factor.0.pow(factor.1).unwrap()),
                            ))
                            .solve_gaussian_elimination(
                                &MatZq::from((
                                    &MatZ::from(result),
                                    &Modulus::from(&factor.0.pow(factor.1).unwrap()),
                                )),
                            )?,
                        );
                    }
                }
                // connect the solutions via the Chinese Remainder Theorem
                loop {
                    if solutions.len() > 1 {
                        // compute Bézout’s identity: a x_1 + b x_2 = 1
                        // by computing xgcd(x_1, x_2)
                        let x_2_exp = fac_vec.pop()?;
                        let x_1_exp = fac_vec.pop()?;
                        let x_1 = x_1_exp.0.pow(x_1_exp.1).unwrap();
                        let x_2 = x_2_exp.0.pow(x_2_exp.1).unwrap();

                        let (_gcd, a, b) = x_1.xgcd(&x_2);

                        let mut s_2 = solutions.pop().unwrap();
                        let mut s_1 = solutions.pop().unwrap();
                        s_2 = MatZq::from((
                            &MatZ::from(&s_2),
                            &(Z::from(s_2.get_mod()) * Z::from(s_1.get_mod())).into(),
                        ));
                        s_1 = MatZq::from((&MatZ::from(&s_1), &s_2.get_mod()));
                        solutions.push(s_2 * a * x_1 + s_1 * b * x_2);
                    } else {
                        return Some(solutions[0].clone());
                    }
                }
            }
        }

        // set the entries of the output vector using the indices vector
        let mut out = MatZq::new(self.get_num_columns(), 1, &matrix.get_mod());
        for (i, j) in indices.iter() {
            let entry: Z = matrix.get_entry(*i, matrix.get_num_columns() - 1).ok()?;
            out.set_entry(*j, 0, &entry).ok()?;
        }

        println!("hose");

        // check if we have computed a solution and return `None`
        if &(self * &out) != result {
            println!("falsy");
            return None;
        }
        println!("hhhhhhhhhhhhhhhhh {}", out);

        Some(out)
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
    fn solve_hensel(&self, result: &MatZq, base: &Z, power: &u64) -> Option<MatZq> {
        let matrix_solution_base = MatZq::from((
            &MatZ::from(&self.concat_horizontal(result).unwrap()),
            &Modulus::from(base),
        ));
        let mut matrix_solution_identity_base_gauss = matrix_solution_base
            .concat_horizontal(&MatZq::identity(
                self.get_num_rows(),
                self.get_num_rows(),
                base,
            ))
            .unwrap();
        //let matrix_prime_gauss = matrix_prime.clone().gaussian_elimination_prime();

        // saves the indices of row and column, where we created a 1 entry
        // such that we do not have to go through the matrix afterwards
        let mut indices: Vec<(i64, i64)> = Vec::new();
        let mut row_count = 0;
        let mut permutation: Vec<i64> = vec![];

        for i in 0..self.get_num_rows() {
            permutation.push(i);
        }

        for column_nr in 0..self.get_num_columns() {
            if !indices.is_empty() {}
            if !indices.is_empty() && indices[indices.len() - 1].0 >= self.get_num_rows() {
                break;
            }

            let used_rows: Vec<i64> = indices.iter().map(|(row, _)| *row).collect();
            // try to solve with current modulus
            if let Some((row_nr, inv)) = find_invertible_entry_column(
                &matrix_solution_identity_base_gauss,
                column_nr,
                used_rows.clone(),
            ) {
                let row = inv * matrix_solution_identity_base_gauss.get_row(row_nr).ok()?;
                matrix_solution_identity_base_gauss
                    .set_row(row_nr, &row, 0)
                    .ok()?;

                // set all other entries in that column to `0` (gaussian elimination)
                for row_nr in
                    (0..matrix_solution_identity_base_gauss.get_num_rows()).filter(|x| *x != row_nr)
                {
                    let old_row = matrix_solution_identity_base_gauss.get_row(row_nr).ok()?;
                    let entry: Z = old_row.get_entry(0, column_nr).ok()?;
                    let new_row = &old_row - entry * &row;
                    matrix_solution_identity_base_gauss
                        .set_row(row_nr, &new_row, 0)
                        .ok()?;
                }

                if row_count != row_nr {
                    matrix_solution_identity_base_gauss
                        .swap_rows(row_count, row_nr)
                        .unwrap();

                    permutation.swap(row_count.try_into().unwrap(), row_nr.try_into().unwrap());
                }
                // save the position of `1` for that row
                indices.push((row_count, column_nr));

                row_count += 1;
            // search for not invertible entry to divide modulus
            } else if let Some(row_nr) = find_not_invertible_entry_column(
                &matrix_solution_identity_base_gauss,
                column_nr,
                used_rows,
            ) {
                // factorise the modulus with the found entry
                let entry: Z = matrix_solution_identity_base_gauss
                    .get_entry(row_nr, column_nr)
                    .ok()?;
                let gcd = Z::from(self.get_mod()).gcd(entry);
                // TODO smarter factorization with base of modulus
                let mut fac =
                    Factorization::from((&gcd, &(Z::from(self.get_mod()) / &gcd).get_numerator()));
                fac.refine();
                let mut fac_vec = Vec::<(Z, u64)>::from(&fac);

                // solve the equation under the different moduli
                let mut solutions: Vec<MatZq> = vec![];
                for factor in fac_vec.iter() {
                    // compute solution under the modulus p^m with p prime according to TODO
                    if factor.1 > 1 {
                        solutions.push(
                            MatZq::from((
                                &MatZ::from(self),
                                &Modulus::from(&factor.0.pow(factor.1).unwrap()),
                            ))
                            .solve_hensel(
                                &MatZq::from((
                                    &MatZ::from(result),
                                    &Modulus::from(&factor.0.pow(factor.1).unwrap()),
                                )),
                                &factor.0,
                                &factor.1,
                            )?,
                        );
                    // try to compute solution with new modulus
                    } else {
                        solutions.push(
                            MatZq::from((
                                &MatZ::from(self),
                                &Modulus::from(&factor.0.pow(factor.1).unwrap()),
                            ))
                            .solve_gaussian_elimination(
                                &MatZq::from((
                                    &MatZ::from(result),
                                    &Modulus::from(&factor.0.pow(factor.1).unwrap()),
                                )),
                            )?,
                        );
                    }
                }
                // connect the solutions via the Chinese Remainder Theorem
                loop {
                    if solutions.len() > 1 {
                        // compute Bézout’s identity: a x_1 + b x_2 = 1
                        // by computing xgcd(x_1, x_2)
                        let x_2_exp = fac_vec.pop()?;
                        let x_1_exp = fac_vec.pop()?;
                        let x_1 = x_1_exp.0.pow(x_1_exp.1).unwrap();
                        let x_2 = x_2_exp.0.pow(x_2_exp.1).unwrap();

                        let (_gcd, a, b) = x_1.xgcd(&x_2);

                        let mut s_2 = solutions.pop().unwrap();
                        let mut s_1 = solutions.pop().unwrap();
                        s_2 = MatZq::from((
                            &MatZ::from(&s_2),
                            &(Z::from(s_2.get_mod()) * Z::from(s_1.get_mod())).into(),
                        ));
                        s_1 = MatZq::from((&MatZ::from(&s_1), &s_2.get_mod()));
                        solutions.push(s_2 * a * x_1 + s_1 * b * x_2);
                    } else {
                        return Some(solutions[0].clone());
                    }
                }
            }
        }

        // This matrix will contain all rows that are not `0` (fr means full rank).
        let mut matrix_solution_identity_base_gauss_fr =
            matrix_solution_identity_base_gauss.clone();

        if indices[indices.len() - 1].0 + 1 < self.get_num_rows() {
            for row_nr in indices[indices.len() - 1].0 + 1..self.get_num_rows() {
                let entry: Z = matrix_solution_identity_base_gauss
                    .get_entry(row_nr, self.get_num_rows())
                    .unwrap();
                if !entry.is_zero() {
                    println!("impossible");
                    return None;
                }
            }

            matrix_solution_identity_base_gauss_fr = MatZq::new(
                indices[indices.len() - 1].0 + 1,
                matrix_solution_identity_base_gauss.get_num_columns(),
                matrix_solution_identity_base_gauss.get_mod(),
            );

            for row_nr in 0..indices[indices.len() - 1].0 + 1 {
                matrix_solution_identity_base_gauss_fr
                    .set_row(row_nr, &matrix_solution_identity_base_gauss, row_nr)
                    .unwrap();
            }
        }

        if matrix_solution_identity_base_gauss_fr.get_num_rows() > self.get_num_columns() {
            println!("What if rows > columns?");
            return None;
        }

        let mut square_matrix_rows_base = MatZq::new(
            matrix_solution_identity_base_gauss_fr.get_num_rows(),
            matrix_solution_base.get_num_columns(),
            base,
        );
        let mut square_matrix_rows = MatZq::new(
            matrix_solution_identity_base_gauss_fr.get_num_rows(),
            self.get_num_columns(),
            self.get_mod(),
        );

        let rank: usize = (indices[indices.len() - 1].0 + 1).try_into().unwrap();
        let mut zero_rows = permutation[rank..].to_vec();
        zero_rows.sort();
        println!("zero_rows_len: {}", zero_rows.len());
        zero_rows.push(self.get_num_rows());
        let mut current_row = 0;
        let mut last_zero_row = 0;
        for zero_row_nr in &zero_rows {
            for row_nr in last_zero_row..*zero_row_nr {
                square_matrix_rows_base
                    .set_row(current_row, &matrix_solution_base, row_nr)
                    .unwrap();
                square_matrix_rows
                    .set_row(current_row, self, row_nr)
                    .unwrap();
                current_row += 1;
            }
            last_zero_row = current_row + 1;
        }

        let mut square_matrix_base = MatZq::new(
            square_matrix_rows_base.get_num_rows(),
            square_matrix_rows_base.get_num_rows(),
            base,
        );
        let mut square_matrix = MatZq::new(
            square_matrix_rows.get_num_rows(),
            square_matrix_rows.get_num_rows(),
            self.get_mod(),
        );

        for (current_column, (_row_nr, column_nr)) in indices.iter().enumerate() {
            square_matrix_base
                .set_column(current_column, &square_matrix_rows_base, *column_nr)
                .unwrap();
            square_matrix
                .set_column(current_column, &square_matrix_rows, *column_nr)
                .unwrap();
        }

        let matrix_solution_identity_gauss_fr = MatZq::from((
            &MatZ::from(&matrix_solution_identity_base_gauss_fr),
            &self.get_mod(),
        ));
        let mut matrix_base_inv = MatZq::new(
            matrix_solution_identity_gauss_fr.get_num_rows(),
            matrix_solution_identity_gauss_fr.get_num_rows(),
            &self.get_mod(),
        );

        // TODO just take good columns
        let mut current_row = 0;
        let mut last_zero_row = 0;
        for zero_row_nr in &zero_rows {
            for row_nr in self.get_num_columns() + 1 + last_zero_row
                ..self.get_num_columns() + 1 + *zero_row_nr
            {
                matrix_base_inv
                    .set_column(current_row, &matrix_solution_identity_gauss_fr, row_nr)
                    .unwrap();
                current_row += 1;
            }
            last_zero_row = current_row + 1;
        }

        /*
        let mut zero_count = 0;
        let mut zero_columns: Vec<i64> = vec![];
        let mut square_matrix_prime = MatZq::new(self.get_num_rows(), self.get_num_rows(), prime);
        let mut square_matrix =
            MatZq::new(self.get_num_rows(), self.get_num_rows(), self.get_mod());
        for column_nr in 0..matrix_prime_gauss.get_num_columns() {
            if column_nr - zero_count >= self.get_num_rows() {
                break;
            } else if Z::is_zero(
                &matrix_prime_gauss
                    .get_entry(column_nr - zero_count, column_nr)
                    .unwrap(),
            ) {
                zero_count += 1;
                zero_columns.push(column_nr);
            } else {
                square_matrix_prime
                    .set_column(column_nr - zero_count, &matrix_prime, column_nr)
                    .unwrap();
                square_matrix
                    .set_column(column_nr - zero_count, self, column_nr)
                    .unwrap();
            }
        }*/

        /*
        let matrix_prime_inv = &MatZq::from((
            &MatZ::from(&square_matrix_prime.inverse_prime()?),
            &self.get_mod(),
        ));*/

        let mut b_i = MatZq::new(
            matrix_solution_identity_gauss_fr.get_num_rows(),
            1,
            result.get_mod(),
        );

        let mut current_row = 0;
        let mut last_zero_row = 0;
        for zero_row_nr in zero_rows {
            for row_nr in last_zero_row..zero_row_nr {
                b_i.set_row(current_row, result, row_nr).unwrap();
                current_row += 1;
            }
            last_zero_row = current_row + 1;
        }

        let mut x_i = &matrix_base_inv * &b_i;
        let mut x = x_i.clone();
        for i in 1..*power {
            b_i = MatZq::from((
                &(unsafe { MatZ::from(&(b_i - &square_matrix * x_i)).div_exact(base) }),
                &self.get_mod(),
            ));
            x_i = &matrix_base_inv * &b_i;
            x = x + &x_i * &base.pow(i).unwrap();
        }

        let mut out = MatZq::new(self.get_num_columns(), 1, self.get_mod());
        for (current_row_x, (_row_nr, column_nr)) in indices.into_iter().enumerate() {
            out.set_entry(
                column_nr,
                0,
                GetEntry::<Z>::get_entry(&x, current_row_x, 0).unwrap(),
            )
            .unwrap();
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
fn find_not_invertible_entry_column(
    matrix: &MatZq,
    column: i64,
    used_rows: Vec<i64>,
) -> Option<i64> {
    for i in (0..matrix.get_num_rows()).filter(|x| !used_rows.contains(x)) {
        let entry: Zq = matrix.get_entry(i, column).unwrap();
        if entry != Zq::from((Z::ZERO, entry.get_mod())) {
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

    /// Ensure that a solution is found, even if the matrix contains no
    /// column that is invertible
    #[test]
    fn solution_without_invertible_columns() {
        let mat = MatZq::from_str("[[2,1],[3,1]] mod 6").unwrap();
        let y = MatZq::from_str("[[5],[2]] mod 6").unwrap();

        let x = mat.solve_gaussian_elimination(&y).unwrap();

        let cmp_sol = MatZq::from_str("[[3],[5]] mod 6").unwrap();
        assert_eq!(cmp_sol, x);
    }

    /// Ensure that a solution is found, even if the matrix contains a
    /// column that is not invertible
    #[test]
    fn solution_with_one_uninvertible_column() {
        let mat = MatZq::from_str("[[2,1],[3,1]] mod 210").unwrap();
        let y = MatZq::from_str("[[5],[2]] mod 210").unwrap();

        let x = mat.solve_gaussian_elimination(&y).unwrap();

        let cmp_sol = MatZq::from_str("[[207],[11]] mod 210").unwrap();
        assert_eq!(cmp_sol, x);
    }

    /// Ensure that a solution is found, even if the modulus is a power of a prime
    #[test]
    fn solution_prime_power() {
        let mat = MatZq::from_str("[[2,2,3],[2,5,7]] mod 8").unwrap();
        let y = MatZq::from_str("[[0],[1]] mod 8").unwrap();
        let x = mat.solve_gaussian_elimination(&y).unwrap();

        assert_eq!(MatZq::from_str("[[0],[3],[6]] mod 8").unwrap(), x)
    }

    /// Ensure that a solution is found, even if the matrix contains no
    /// column that is invertible
    #[test]
    fn solution_not_prime_power() {
        let mat = MatZq::from_str("[[6,1],[3,1]] mod 36").unwrap();
        let y = MatZq::from_str("[[6],[3]] mod 36").unwrap();

        let x = mat.solve_gaussian_elimination(&y).unwrap();
        println!("solution: {}", x);

        let cmp_sol = MatZq::from_str("[[1],[0]] mod 6").unwrap();
        assert_eq!(cmp_sol, x);
    }

    /// Ensure that the trivial solution can always be computed
    #[test]
    fn trivial_solution() {
        let mat = MatZq::from_str("[[2,2,3],[2,5,7]] mod 8").unwrap();
        let y = MatZq::from_str("[[0],[0]] mod 8").unwrap();
        let x = mat.solve_gaussian_elimination(&y).unwrap();

        assert_eq!(MatZq::new(3, 1, mat.get_mod()), x)
    }

    /// Ensure that a solution is found, even if the modulus is a power of a prime
    #[test]
    fn solution_prime_powerssssss() {
        let mat = MatZq::from_str("[[2,2,3],[2,5,7]] mod 1048576").unwrap();
        let y = MatZq::from_str("[[0],[1]] mod 1048576").unwrap();
        let x = mat.solve_gaussian_elimination(&y).unwrap();

        println!("{}", x);

        assert_eq!(y, mat * x);
    }

    /// Ensure that a solution is found, even if the modulus is a large power of a prime
    #[test]
    #[ignore]
    fn large_matrix() {
        let modulus = Modulus::from(Z::from(2).pow(3).unwrap());

        // matrix of size `n x 2n\log q`, hence almost always invertible
        let mat = MatZq::sample_uniform(10, 10 * 2 * 50, &modulus);
        let y = MatZq::sample_uniform(10, 1, &modulus);

        let x = mat.solve_gaussian_elimination(&y).unwrap();

        println!("{}", &mat * &x);
        println!("{}", &y);

        assert_eq!(y, mat * x)
    }

    /// Ensure that a solution is found, even if the modulus is a large power of a prime
    #[test]
    #[ignore]
    fn large_matrix_test_none() {
        let matrix = MatZq::from_str("[[384, 234, 177, 166, 506, 291, 184, 588, 351, 370, 481, 451, 158, 608, 416, 521, 110, 465, 481, 134, 379, 291, 159, 477, 76, 609, 401, 145, 289, 248, 478, 201, 384, 486, 116, 47, 408, 549, 572, 312, 107, 264, 548, 308, 364, 93, 300, 332, 421, 189, 335, 409, 130, 300, 134, 501, 524, 403, 71, 240, 548, 536, 405, 96, 155, 578, 433, 330, 347, 247, 180, 15, 304, 575, 60, 336, 86, 476, 250, 88, 517, 554, 574, 409, 260, 388, 4, 445, 317, 269, 446, 271, 617, 322, 402, 57, 433, 533, 30, 184, 303, 396, 566, 438, 223, 436, 272, 407, 6, 576, 337, 278, 413, 576, 40, 281, 376, 216, 315, 591, 284, 96, 407, 413, 478, 108, 399, 588, 618, 257, 316, 584, 445, 618],[82, 327, 365, 439, 122, 447, 499, 137, 131, 114, 403, 541, 128, 25, 337, 337, 268, 467, 318, 455, 396, 444, 276, 21, 485, 317, 171, 15, 491, 118, 339, 283, 258, 505, 131, 173, 195, 75, 321, 119, 280, 603, 354, 314, 447, 377, 468, 617, 219, 117, 330, 392, 383, 222, 228, 110, 117, 546, 220, 466, 349, 45, 261, 367, 291, 7, 483, 554, 618, 500, 33, 324, 153, 227, 388, 497, 225, 64, 451, 544, 126, 416, 240, 567, 408, 72, 254, 614, 356, 89, 95, 392, 266, 458, 303, 266, 226, 521, 189, 510, 278, 301, 156, 487, 62, 335, 174, 550, 51, 623, 233, 477, 473, 145, 77, 300, 606, 149, 340, 430, 489, 249, 416, 124, 519, 599, 92, 103, 452, 601, 176, 398, 597, 430],[410, 503, 319, 403, 498, 395, 373, 441, 20, 358, 344, 84, 292, 523, 561, 469, 194, 587, 310, 225, 580, 364, 108, 469, 447, 133, 208, 44, 210, 343, 79, 324, 162, 152, 529, 41, 426, 580, 140, 402, 262, 363, 97, 45, 98, 12, 496, 499, 357, 128, 175, 560, 86, 3, 332, 44, 408, 475, 36, 292, 571, 231, 180, 191, 593, 599, 226, 107, 200, 615, 597, 544, 302, 261, 459, 325, 177, 228, 291, 507, 576, 77, 229, 60, 135, 347, 80, 379, 152, 552, 162, 90, 609, 547, 235, 330, 177, 260, 358, 547, 283, 198, 472, 38, 333, 524, 82, 256, 381, 190, 29, 23, 379, 517, 225, 267, 569, 241, 60, 275, 592, 289, 179, 213, 161, 199, 510, 565, 410, 217, 358, 67, 227, 408],[294, 166, 173, 172, 236, 298, 274, 112, 369, 52, 262, 619, 597, 564, 393, 21, 607, 521, 1, 532, 65, 414, 219, 217, 107, 237, 17, 516, 302, 225, 221, 430, 594, 30, 15, 516, 303, 327, 568, 376, 22, 202, 1, 538, 573, 214, 3, 244, 454, 620, 531, 547, 305, 422, 179, 79, 124, 429, 147, 366, 111, 587, 33, 602, 242, 344, 430, 184, 12, 331, 461, 329, 46, 263, 448, 151, 33, 108, 459, 472, 182, 548, 229, 507, 577, 456, 184, 142, 210, 507, 404, 552, 172, 323, 354, 377, 407, 195, 69, 354, 553, 267, 425, 327, 510, 36, 515, 345, 429, 48, 227, 381, 445, 406, 118, 180, 316, 589, 416, 170, 502, 546, 213, 128, 368, 590, 623, 414, 479, 510, 518, 395, 588, 40],[548, 14, 369, 22, 28, 322, 531, 7, 264, 498, 588, 561, 411, 263, 312, 521, 520, 485, 101, 159, 622, 430, 35, 437, 268, 20, 172, 406, 622, 417, 324, 1, 510, 402, 42, 450, 123, 505, 478, 174, 122, 153, 346, 502, 327, 504, 531, 388, 516, 373, 335, 189, 484, 499, 137, 475, 489, 491, 306, 556, 152, 593, 514, 514, 527, 358, 123, 420, 291, 378, 356, 332, 613, 532, 403, 33, 344, 133, 509, 209, 433, 157, 191, 393, 374, 216, 456, 156, 544, 491, 118, 489, 524, 332, 36, 550, 242, 425, 389, 422, 295, 164, 211, 256, 240, 138, 202, 167, 70, 351, 442, 414, 474, 481, 55, 411, 430, 0, 132, 509, 340, 340, 339, 526, 231, 594, 241, 282, 420, 45, 96, 136, 59, 257],[16, 224, 303, 252, 441, 377, 28, 382, 301, 584, 599, 561, 303, 233, 356, 465, 289, 272, 310, 535, 444, 550, 415, 224, 516, 449, 38, 542, 222, 67, 149, 610, 116, 234, 342, 168, 488, 344, 527, 548, 394, 340, 98, 84, 463, 507, 278, 610, 65, 509, 499, 109, 38, 362, 181, 491, 192, 337, 356, 235, 548, 544, 203, 211, 393, 63, 148, 234, 52, 541, 259, 248, 85, 0, 435, 24, 185, 449, 212, 109, 586, 491, 250, 499, 620, 272, 203, 481, 360, 41, 367, 482, 40, 212, 596, 546, 85, 219, 156, 188, 328, 366, 517, 77, 320, 577, 216, 558, 611, 85, 179, 320, 590, 257, 524, 204, 484, 539, 285, 254, 408, 3, 281, 97, 222, 343, 493, 412, 509, 567, 57, 435, 281, 574],[415, 13, 311, 317, 583, 81, 474, 534, 285, 82, 593, 335, 581, 411, 54, 561, 359, 142, 361, 80, 273, 368, 96, 588, 147, 617, 95, 521, 67, 475, 30, 535, 421, 418, 466, 614, 422, 42, 48, 6, 346, 587, 24, 160, 36, 112, 107, 24, 407, 614, 616, 370, 137, 384, 146, 11, 7, 234, 561, 362, 384, 529, 52, 167, 170, 143, 235, 352, 238, 98, 473, 128, 106, 498, 2, 546, 288, 340, 343, 312, 318, 85, 546, 446, 494, 195, 209, 358, 220, 402, 32, 357, 616, 417, 115, 339, 136, 350, 204, 608, 349, 67, 358, 550, 182, 551, 150, 57, 333, 515, 274, 511, 281, 348, 466, 333, 11, 49, 499, 280, 529, 405, 505, 225, 483, 195, 304, 165, 92, 239, 76, 419, 270, 523],[149, 264, 535, 595, 585, 342, 303, 331, 409, 42, 241, 17, 78, 609, 3, 310, 236, 530, 116, 601, 368, 174, 489, 179, 139, 79, 87, 522, 158, 357, 481, 137, 416, 610, 417, 321, 1, 137, 212, 368, 32, 479, 56, 313, 568, 476, 533, 553, 239, 324, 160, 467, 112, 189, 374, 120, 532, 431, 452, 223, 298, 473, 208, 583, 526, 426, 58, 199, 331, 18, 463, 237, 112, 570, 124, 51, 603, 113, 556, 14, 145, 426, 145, 186, 342, 263, 490, 539, 227, 294, 69, 532, 611, 46, 26, 252, 267, 171, 4, 199, 608, 147, 3, 132, 116, 525, 557, 591, 553, 587, 300, 378, 620, 538, 192, 404, 175, 503, 600, 438, 356, 590, 232, 418, 217, 515, 539, 382, 341, 511, 132, 222, 559, 570],[71, 271, 416, 246, 94, 609, 425, 329, 450, 445, 376, 461, 219, 80, 229, 547, 201, 34, 529, 543, 520, 198, 426, 214, 382, 537, 259, 119, 104, 619, 544, 319, 533, 451, 593, 439, 366, 478, 457, 22, 32, 459, 387, 82, 389, 188, 573, 86, 368, 122, 458, 164, 364, 465, 269, 422, 184, 390, 553, 601, 552, 565, 368, 486, 406, 350, 369, 47, 518, 101, 7, 49, 545, 97, 436, 84, 351, 596, 70, 542, 87, 556, 287, 465, 160, 86, 279, 144, 418, 392, 511, 339, 222, 338, 130, 0, 38, 39, 28, 209, 573, 140, 214, 98, 255, 429, 403, 322, 22, 517, 147, 580, 201, 289, 558, 310, 480, 201, 480, 464, 90, 591, 257, 123, 306, 82, 297, 519, 586, 78, 119, 507, 378, 615],[595, 66, 373, 65, 602, 63, 20, 620, 489, 10, 95, 324, 134, 409, 570, 286, 21, 143, 178, 373, 353, 161, 103, 264, 319, 529, 205, 538, 163, 131, 521, 555, 353, 309, 573, 46, 80, 176, 297, 316, 576, 360, 93, 478, 500, 176, 358, 463, 275, 546, 33, 267, 535, 217, 582, 455, 107, 420, 161, 615, 488, 487, 564, 331, 395, 28, 48, 253, 133, 618, 596, 12, 471, 500, 266, 90, 448, 376, 428, 208, 278, 442, 230, 541, 122, 217, 81, 356, 248, 261, 526, 519, 492, 80, 46, 380, 348, 67, 227, 330, 258, 400, 394, 275, 207, 271, 599, 537, 563, 164, 293, 324, 236, 534, 57, 310, 392, 84, 3, 50, 595, 569, 4, 364, 451, 554, 38, 366, 245, 437, 502, 153, 202, 87],[191, 262, 452, 168, 170, 294, 148, 397, 208, 343, 504, 561, 196, 124, 479, 518, 559, 411, 288, 623, 518, 499, 267, 282, 210, 525, 34, 564, 402, 403, 131, 106, 523, 532, 16, 487, 497, 458, 452, 534, 296, 198, 62, 35, 17, 2, 366, 160, 445, 224, 580, 259, 228, 578, 371, 520, 197, 227, 201, 519, 313, 497, 240, 623, 421, 435, 39, 272, 20, 304, 224, 592, 566, 286, 42, 80, 23, 508, 311, 265, 353, 599, 27, 562, 491, 394, 219, 469, 472, 417, 4, 380, 491, 400, 432, 426, 293, 502, 101, 78, 144, 611, 389, 205, 85, 617, 142, 525, 11, 177, 85, 376, 342, 325, 574, 372, 85, 282, 49, 201, 352, 294, 485, 441, 194, 544, 409, 381, 176, 380, 391, 45, 577, 246],[248, 300, 341, 5, 449, 281, 91, 179, 164, 22, 320, 334, 232, 386, 525, 135, 281, 334, 290, 477, 498, 29, 146, 194, 476, 128, 521, 358, 119, 313, 470, 426, 587, 7, 609, 464, 139, 299, 310, 590, 554, 41, 266, 105, 27, 187, 247, 148, 465, 580, 257, 20, 570, 196, 573, 232, 50, 396, 225, 248, 214, 571, 156, 393, 423, 411, 169, 417, 98, 175, 237, 418, 462, 619, 502, 531, 459, 101, 492, 62, 79, 150, 464, 366, 349, 146, 510, 404, 385, 245, 440, 26, 119, 67, 21, 101, 77, 537, 582, 393, 565, 91, 549, 128, 440, 51, 486, 214, 200, 596, 202, 30, 393, 6, 470, 271, 153, 290, 72, 484, 512, 188, 550, 461, 298, 409, 52, 129, 183, 449, 277, 363, 356, 475],[143, 327, 74, 131, 486, 201, 232, 29, 196, 580, 563, 517, 51, 366, 498, 298, 22, 157, 169, 443, 548, 421, 485, 186, 547, 368, 180, 362, 515, 466, 484, 85, 100, 174, 564, 598, 532, 86, 522, 504, 585, 327, 519, 606, 32, 516, 95, 274, 147, 302, 595, 188, 179, 513, 358, 544, 13, 54, 276, 558, 194, 199, 601, 225, 542, 276, 556, 49, 472, 573, 618, 569, 603, 420, 436, 201, 460, 180, 595, 607, 173, 565, 32, 256, 439, 42, 588, 378, 224, 67, 203, 152, 457, 440, 443, 390, 245, 221, 300, 247, 57, 590, 100, 269, 522, 81, 577, 556, 184, 431, 372, 151, 269, 330, 295, 354, 546, 472, 316, 233, 290, 314, 99, 312, 479, 43, 553, 117, 237, 316, 546, 100, 445, 283],[551, 423, 434, 97, 427, 374, 22, 174, 434, 59, 281, 337, 577, 589, 92, 426, 487, 59, 33, 85, 153, 510, 175, 108, 225, 534, 73, 310, 80, 429, 502, 562, 254, 93, 454, 492, 474, 87, 79, 563, 359, 536, 325, 543, 540, 15, 290, 16, 601, 604, 80, 332, 46, 240, 426, 547, 225, 77, 442, 407, 403, 402, 218, 136, 258, 608, 498, 559, 492, 12, 36, 100, 102, 272, 344, 593, 438, 350, 151, 26, 259, 368, 22, 513, 371, 232, 571, 621, 540, 350, 385, 264, 79, 449, 500, 42, 110, 205, 77, 545, 332, 402, 7, 373, 561, 114, 242, 343, 578, 101, 551, 262, 582, 333, 534, 54, 50, 360, 581, 172, 535, 7, 212, 604, 399, 59, 56, 145, 330, 325, 556, 182, 290, 518]] mod 624").unwrap();
        let y = MatZq::from_str("[[260],[446],[373],[171],[114],[564],[287],[302],[439],[479],[364],[613],[68],[197]] mod 624").unwrap();
        let x = matrix.solve_gaussian_elimination(&y).unwrap();

        assert_eq!(y, matrix * x);
    }

    /// Ensure that a solution is found, even if the modulus is a large power of a prime
    #[test]
    fn random_matrix_modulus() {
        let mut none_count = 0;
        let mut correct_count = 0;
        let mut false_count = 0;

        for i in 0..100 {
            let modulus_sample = Z::sample_uniform(100, 1000).unwrap();
            let row_sample = &Z::sample_uniform(1, 500).unwrap();
            let column_sample = &Z::sample_uniform(1, 500).unwrap();

            let modulus = Modulus::from(modulus_sample);

            // matrix of size `n x 2n\log q`, hence almost always invertible
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

        //println!("{}", &mat * &x);
        //println!("{}", &y);

        //assert_eq!(y, mat * x)
    }

    /// Ensure that for different moduli the function panics
    #[test]
    #[should_panic]
    fn different_moduli() {
        let mat = MatZq::from_str("[[2,2,3],[2,5,7]] mod 8").unwrap();
        let y = MatZq::from_str("[[0],[0]] mod 7").unwrap();
        let _ = mat.solve_gaussian_elimination(&y).unwrap();
    }

    /// Ensure that for different number of rows the function panics
    #[test]
    #[should_panic]
    fn different_nr_rows() {
        let mat = MatZq::from_str("[[2,2,3],[2,5,7]] mod 8").unwrap();
        let y = MatZq::from_str("[[0],[0],[0]] mod 8").unwrap();
        let _ = mat.solve_gaussian_elimination(&y).unwrap();
    }

    /// Ensure that for non-column vectors, the function panics
    #[test]
    #[should_panic]
    fn not_column_vector() {
        let mat = MatZq::from_str("[[2,2,3],[2,5,7]] mod 8").unwrap();
        let y = MatZq::from_str("[[0, 1],[0, 1]] mod 8").unwrap();
        let _ = mat.solve_gaussian_elimination(&y).unwrap();
    }
}

#[cfg(test)]
mod test_solve_hensel {
    use crate::{
        integer::Z,
        integer_mod_q::{MatZq, Modulus},
        traits::Pow,
    };

    /// Ensure that a solution is found, even if the modulus is a large power of a prime
    #[test]
    fn large_matrix_m() {
        let modulus = Modulus::from(Z::from(2).pow(40).unwrap());

        // matrix of size `n x 2n\log q`, hence almost always invertible
        let mat = MatZq::sample_uniform(10, 10 * 2 * 50, &modulus);
        let y = MatZq::sample_uniform(10, 1, &modulus);

        let x = mat.solve_hensel(&y, &Z::from(2), &40).unwrap();

        println!("{}", &mat * &x);
        println!("{}", &y);

        assert_eq!(y, mat * x)
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

#[cfg(test)]
mod test_find_uninvertible_entry_column {
    use crate::integer_mod_q::{mat_zq::solve::find_not_invertible_entry_column, MatZq};
    use std::str::FromStr;

    /// Ensure that the inverse of the first element is returned with the correct entry
    /// if it has an inverse
    #[test]
    fn find_correct_entry() {
        let mat = MatZq::from_str("[[4],[2]] mod 8").unwrap();

        let i = find_not_invertible_entry_column(&mat, 0, Vec::new()).unwrap();
        assert_eq!(0, i);

        let i = find_not_invertible_entry_column(&mat, 0, [0].to_vec()).unwrap();
        assert_eq!(1, i);

        let invert = find_not_invertible_entry_column(&mat, 0, [0, 1].to_vec());
        assert!(invert.is_none())
    }
}
