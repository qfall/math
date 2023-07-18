// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes core functionality to sample according to the
//! discrete gaussian distribution.
//!
//! The main references are listed in the following
//! and will be further referenced in submodules by these numbers:
//! - \[1\] Gentry, Craig and Peikert, Chris and Vaikuntanathan, Vinod (2008).
//! Trapdoors for hard lattices and new cryptographic constructions.
//! In: Proceedings of the fortieth annual ACM symposium on Theory of computing.
//! <https://citeseerx.ist.psu.edu/document?doi=d9f54077d568784c786f7b1d030b00493eb3ae35>

use super::uniform::sample_uniform_rejection;
use crate::{
    error::MathError,
    integer::{MatZ, Z},
    rational::{MatQ, Q},
    traits::{GetNumColumns, GetNumRows, Pow},
};
use rand::RngCore;

#[allow(dead_code)]
/// Chooses a sample according to the discrete Gaussian distribution out of
/// `[center - ⌈s * log_2(n)⌉ , center + ⌊s * log_2(n)⌋ ]`.
///
/// This function implements discrete Gaussian sampling according to the definition of
/// SampleZ as in [\[1\]](<index.html#:~:text=[1]>).
///
/// Parameters:
/// - `n`: specifies the range from which is sampled
/// - `center`: specifies the position of the center with peak probability
/// - `s`: specifies the Gaussian parameter, which is proportional
/// to the standard deviation `sigma * sqrt(2 * pi) = s`
///
/// Returns a sample chosen according to the specified discrete Gaussian distribution or
/// a [`MathError`] if the specified parameters were not chosen appropriately,
/// i.e. `n > 1` and `s > 0`.
///
/// # Examples
/// ```compile_fail
/// use qfall_math::{integer::Z, rational::Q};
/// use qfall_math::utils::sample::discrete_gauss::sample_z;
/// let n = Z::from(1024);
/// let center = Q::ZERO;
/// let gaussian_parameter = Q::ONE;
///
/// let sample = sample_z(&n, &center, &gaussian_parameter).unwrap();
/// ```
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
/// if the `n <= 1` or `s <= 0`.
pub(crate) fn sample_z(n: &Z, center: &Q, s: &Q) -> Result<Z, MathError> {
    // TODO: Change this functions signature to use std_deviation/ sigma and not Gaussian parameter
    if n <= &Z::ONE {
        return Err(MathError::InvalidIntegerInput(format!(
            "The value {} was provided for parameter n of the function sample_z.
            This function expects this input to be bigger than 1.",
            n
        )));
    }
    if s <= &Q::ZERO {
        return Err(MathError::InvalidIntegerInput(format!(
            "The value {} was provided for parameter s of the function sample_z.
            This function expects this input to be bigger than 0.",
            s
        )));
    }

    let lower_bound = (center - s * n.log(2).unwrap()).ceil();
    let upper_bound = (center + s * n.log(2).unwrap()).floor();
    let interval_size = &upper_bound - &lower_bound;

    // sample x in [c - s * log_2(n), c + s * log_2(n)]
    let mut sample = &lower_bound + sample_uniform_rejection(&interval_size).unwrap();

    // rejection sample according to GPV08
    // https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=d9f54077d568784c786f7b1d030b00493eb3ae35
    // this eprint version explains in more detail how sample_z works
    let mut rng = rand::thread_rng();
    // TODO: Change to Q::from_f64 once it works appropriately for large scale
    while gaussian_function(&sample, center, s) <= Q::from((rng.next_u64(), u64::MAX)) {
        sample = &lower_bound + sample_uniform_rejection(&interval_size).unwrap();
    }

    Ok(sample)
}

/// Computes the value of the Gaussian function for `x`.
///
/// **WARNING:** This functions assumes `s != 0`.
///
/// Parameters:
/// - `x`: specifies the value/ sample for which the Gaussian function's value is computed
/// - `c`: specifies the position of the center with peak probability
/// - `s`: specifies the Gaussian parameter, which is proportional
/// to the standard deviation `sigma * sqrt(2 * pi) = s`
///
/// Returns the computed value of the Gaussian function for `x`.
///
/// # Examples
/// ```compile_fail
/// use qfall_math::{integer::Z, rational::Q};
/// use qfall_math::utils::sample::discrete_gauss::gaussian_function;
/// let sample = Z::ONE;
/// let center = Q::ZERO;
/// let gaussian_parameter = Q::ONE;
///
/// let probability = gaussian_function(&sample, &center, &gaussian_parameter);
/// ```
///
/// # Panics ...
/// - if `s = 0`.
fn gaussian_function(x: &Z, c: &Q, s: &Q) -> Q {
    // TODO: Change this functions signature to use std_deviation/ sigma and not Gaussian parameter
    let num = Q::MINUS_ONE * Q::PI * (x - c).pow(2).unwrap();
    let den = s.pow(2).unwrap();
    let res: Q = num / den;
    res.exp()
}

/// SampleD samples a discrete Gaussian from the lattice with `basis` using [`sample_z`] as a subroutine.
///
/// We do not check whether `basis` is actually a basis. Hence, the callee is
/// responsible for making sure that `basis` provides a suitable basis.
///
/// Parameters:
/// - `basis`: specifies a basis for the lattice from which is sampled
/// - `n`: specifies the range from which [`sample_z`] samples
/// - `center`: specifies the positions of the center with peak probability
/// - `s`: specifies the Gaussian parameter, which is proportional
/// to the standard deviation `sigma * sqrt(2 * pi) = s`
///
/// Returns a vector with discrete gaussian error based on a lattice point
/// as in [\[1\]](<index.html#:~:text=[1]>): SampleD.
///
/// # Examples
/// ```compile_fail
/// use qfall_math::{integer::{MatZ, Z}, rational::{MatQ, Q}};
/// use qfall_math::utils::sample::discrete_gauss::sample_d;
/// let basis = MatZ::identity(5, 5);
/// let n = Z::from(1024);
/// let center = MatQ::new(5, 1);
/// let gaussian_parameter = Q::ONE;
///
/// let sample = sample_d(basis, &n, &center, &gaussian_parameter).unwrap();
/// ```
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
/// if the `n <= 1` or `s <= 0`.
/// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
/// if the number of rows of the `basis` and `center` differ.
/// - Returns a [`MathError`] of type [`InvalidMatrix`](MathError::InvalidMatrix)
/// if `center` is not a column vector.
pub(crate) fn sample_d(basis: &MatZ, n: &Z, center: &MatQ, s: &Q) -> Result<MatZ, MathError> {
    let mut center = center.clone();
    if center.get_num_rows() != basis.get_num_rows() {
        return Err( MathError::MismatchingMatrixDimension(format!(
            "sample_d requires center and basis to have the same number of columns, but they were {} and {}.",
            center.get_num_rows(),
            basis.get_num_rows())
        ));
    }
    if !center.is_column_vector() {
        return Err(MathError::InvalidMatrix(format!(
            "sample_d expects center to be a column vector, but it has dimensions {}x{}.",
            center.get_num_rows(),
            center.get_num_columns()
        )));
    }
    if s < &Q::ZERO {
        return Err(MathError::InvalidIntegerInput(format!(
            "The value {s} was provided for parameter s of the function sample_z.
            This function expects this input to be bigger than 0."
        )));
    }

    let basis_gso = MatQ::from(basis).gso();

    let mut out = MatZ::new(basis_gso.get_num_rows(), 1);

    for i in (0..basis_gso.get_num_columns()).rev() {
        // basisvector_i = b_tilde[i]
        let basisvector_orth_i = basis_gso.get_column(i).unwrap();

        // define the center for sample_z as c2 = <c, b_tilde[i]> / <b_tilde[i], b_tilde[i]>;
        let c2 = center.dot_product(&basisvector_orth_i).unwrap()
            / basisvector_orth_i.dot_product(&basisvector_orth_i).unwrap();

        // Defines the gaussian parameter to be normalized along the basis vector: s2 = s / ||b_tilde[i]||
        let s2 = s / (basisvector_orth_i.norm_eucl_sqrd().unwrap().sqrt());

        // sample z ~ D_{Z, s2, c2}
        let z = sample_z(n, &c2, &s2)?;

        // update the center c = c - z * b[i]
        let basisvector_i = basis.get_column(i).unwrap();
        center = center - MatQ::from(&(&z * &basisvector_i));

        // out = out + z * b[i]
        out = &out + &z * &basisvector_i;
    }

    Ok(out)
}

#[cfg(test)]
mod test_sample_z {
    use super::{sample_z, Q, Z};

    /// Ensures that the doc tests works correctly
    #[test]
    fn doc_test() {
        let n = Z::from(1024);
        let center = Q::ZERO;
        let gaussian_parameter = Q::ONE;

        let sample = sample_z(&n, &center, &gaussian_parameter).unwrap();

        assert!(Z::from(-10) <= sample);
        assert!(sample <= Z::from(10));
    }

    /// Checks whether samples are kept in correct interval for a small interval
    #[test]
    fn small_interval() {
        let n = Z::from(1024);
        let center = Q::from(15);
        let gaussian_parameter = Q::from((1, 2));

        for _ in 0..64 {
            let sample = sample_z(&n, &center, &gaussian_parameter).unwrap();

            assert!(Z::from(10) <= sample);
            assert!(sample <= Z::from(20));
        }
    }

    /// Checks whether samples are kept in correct interval for a large interval
    #[test]
    fn large_interval() {
        let n = Z::from(i64::MAX as u64 + 1);
        let center = Q::MINUS_ONE;
        let gaussian_parameter = Q::ONE;

        for _ in 0..256 {
            let sample = sample_z(&n, &center, &gaussian_parameter).unwrap();

            assert!(Z::from(-64) <= sample);
            assert!(sample <= Z::from(62));
        }
    }

    /// Checks whether `sample_z` returns an error if the gaussian parameter `s <= 0`
    #[test]
    fn invalid_gaussian_parameter() {
        let n = Z::from(4);
        let center = Q::ZERO;

        assert!(sample_z(&n, &center, &Q::ZERO).is_err());
        assert!(sample_z(&n, &center, &Q::MINUS_ONE).is_err());
        assert!(sample_z(&n, &center, &Q::from(i64::MIN)).is_err());
    }

    /// Checks whether `sample_z` returns an error if `n <= 1`
    #[test]
    fn invalid_n() {
        let center = Q::MINUS_ONE;
        let gaussian_parameter = Q::ONE;

        assert!(sample_z(&Z::ONE, &center, &gaussian_parameter).is_err());
        assert!(sample_z(&Z::ZERO, &center, &gaussian_parameter).is_err());
        assert!(sample_z(&Z::MINUS_ONE, &center, &gaussian_parameter).is_err());
        assert!(sample_z(&Z::from(i64::MIN), &center, &gaussian_parameter).is_err());
    }
}

#[cfg(test)]
mod test_gaussian_function {
    use super::{gaussian_function, Q, Z};
    use crate::traits::Distance;

    /// Ensures that the doc test would run properly
    #[test]
    fn doc_test() {
        let sample = Z::ONE;
        let center = Q::ZERO;
        let gaussian_parameter = Q::ONE;
        // result roughly 0.0432139 computed via WolframAlpha
        let cmp = Q::from((43214, 1_000_000));

        let value = gaussian_function(&sample, &center, &gaussian_parameter);

        assert!(cmp.distance(&value) < Q::from((1, 1_000_000)));
    }

    /// Checks whether the values for small values are computed appropriately
    /// and with appropriate precision
    #[test]
    fn small_values() {
        let sample_0 = Z::ZERO;
        let sample_1 = Z::MINUS_ONE;
        let center = Q::MINUS_ONE;
        let gaussian_parameter_0 = Q::from((1, 2));
        let gaussian_parameter_1 = Q::from((3, 2));
        // result roughly 0.00000348734 computed via WolframAlpha
        let cmp_0 = Q::from((349, 100_000_000));
        // result 0.247520 computed via WolframAlpha
        let cmp_1 = Q::from((24752, 100_000));

        let res_0 = gaussian_function(&sample_0, &center, &gaussian_parameter_0);
        let res_1 = gaussian_function(&sample_0, &center, &gaussian_parameter_1);
        let res_2 = gaussian_function(&sample_1, &center, &gaussian_parameter_0);
        let res_3 = gaussian_function(&sample_1, &center, &gaussian_parameter_1);

        assert!(cmp_0.distance(&res_0) < Q::from((3, 1_000_000_000)));
        assert!(cmp_1.distance(&res_1) < Q::from((1, 1_000_000)));
        assert_eq!(Q::ONE, res_2);
        assert_eq!(Q::ONE, res_3);
    }

    /// Checks whether the values for large values are computed appropriately
    /// and with appropriate precision
    #[test]
    fn large_values() {
        let sample = Z::from(i64::MAX);
        let center = Q::from(i64::MAX as u64 + 1);
        let gaussian_parameter = Q::from((1, 2));
        // result roughly 0.00000348734 computed via WolframAlpha
        let cmp = Q::from((349, 100_000_000));

        let res = gaussian_function(&sample, &center, &gaussian_parameter);

        assert!(cmp.distance(&res) < Q::from((3, 1_000_000_000)));
    }

    /// Checks whether `s = 0` results in a panic
    #[test]
    #[should_panic]
    fn invalid_s() {
        let sample = Z::from(i64::MAX);
        let center = Q::from(i64::MAX as u64 + 1);
        let gaussian_parameter = Q::ZERO;

        let _ = gaussian_function(&sample, &center, &gaussian_parameter);
    }
}

#[cfg(test)]
mod test_sample_d {
    use crate::traits::{Concatenate, GetNumColumns, Pow};
    use crate::utils::sample::discrete_gauss::sample_d;
    use crate::{
        integer::{MatZ, Z},
        rational::{MatQ, Q},
    };
    use flint_sys::fmpz_mat::fmpz_mat_hnf;
    use std::str::FromStr;

    /// Ensures that the doc-test compiles and runs properly
    #[test]
    fn doc_test() {
        let basis = MatZ::identity(5, 5);
        let n = Z::from(1024);
        let center = MatQ::new(5, 1);
        let gaussian_parameter = Q::ONE;

        let _ = sample_d(&basis, &n, &center, &gaussian_parameter).unwrap();
    }

    /// Ensures that `sample_d` works properly for a non-zero center
    #[test]
    fn non_zero_center() {
        let basis = MatZ::identity(5, 5);
        let n = Z::from(1024);
        let center = MatQ::identity(5, 1);
        let gaussian_parameter = Q::ONE;

        let _ = sample_d(&basis, &n, &center, &gaussian_parameter).unwrap();
    }

    /// Ensures that `sample_d` works properly for a different basis
    #[test]
    fn non_identity_basis() {
        let basis = MatZ::from_str("[[2,1],[1,2]]").unwrap();
        let n = Z::from(1024);
        let center = MatQ::new(2, 1);
        let gaussian_parameter = Q::ONE;

        let _ = sample_d(&basis, &n, &center, &gaussian_parameter).unwrap();
    }

    /// Ensures that `sample_d` outputs a vector that's part of the specified lattice
    ///
    /// Checks whether the Hermite Normal Form HNF of the basis is equal to the HNF of
    /// the basis concatenated with the sampled vector. If it is part of the lattice, it
    /// should become a zero vector at the end of the matrix.
    #[test]
    fn point_of_lattice() {
        let basis = MatZ::from_str("[[7,0],[7,3]]").unwrap();
        let n = Z::from(1024);
        let center = MatQ::new(2, 1);
        let gaussian_parameter = Q::ONE;

        let sample = sample_d(&basis, &n, &center, &gaussian_parameter).unwrap();

        // check whether hermite normal form of HNF(b) = HNF([b|sample_vector])
        let basis_concat_sample = basis.concat_horizontal(&sample).unwrap();
        let mut hnf_basis = MatZ::new(2, 2);
        unsafe { fmpz_mat_hnf(&mut hnf_basis.matrix, &basis.matrix) };
        let mut hnf_basis_concat_sample = MatZ::new(2, 3);
        unsafe {
            fmpz_mat_hnf(
                &mut hnf_basis_concat_sample.matrix,
                &basis_concat_sample.matrix,
            )
        };
        assert_eq!(
            hnf_basis.get_column(0).unwrap(),
            hnf_basis_concat_sample.get_column(0).unwrap()
        );
        assert_eq!(
            hnf_basis.get_column(1).unwrap(),
            hnf_basis_concat_sample.get_column(1).unwrap()
        );
        // check whether last vector is zero, i.e. was linearly dependend and part of lattice
        assert_eq!(
            MatZ::new(2, 1),
            hnf_basis_concat_sample.get_column(2).unwrap()
        );
    }

    /// Checks whether `sample_d` returns an error if the gaussian parameter `s <= 0`
    #[test]
    fn invalid_gaussian_parameter() {
        let basis = MatZ::identity(5, 5);
        let n = Z::from(1024);
        let center = MatQ::new(5, 1);

        assert!(sample_d(&basis, &n, &center, &Q::ZERO).is_err());
        assert!(sample_d(&basis, &n, &center, &Q::MINUS_ONE).is_err());
        assert!(sample_d(&basis, &n, &center, &Q::from(i64::MIN)).is_err());
    }

    /// Checks whether `sample_d` returns an error if `n <= 1`
    #[test]
    fn invalid_n() {
        let basis = MatZ::identity(5, 5);
        let center = MatQ::new(5, 1);
        let gaussian_parameter = Q::ONE;

        assert!(sample_d(&basis, &Z::ONE, &center, &gaussian_parameter).is_err());
        assert!(sample_d(&basis, &Z::ZERO, &center, &gaussian_parameter).is_err());
        assert!(sample_d(&basis, &Z::MINUS_ONE, &center, &gaussian_parameter).is_err());
        assert!(sample_d(&basis, &Z::from(i64::MIN), &center, &gaussian_parameter).is_err());
    }

    /// Checks whether `sample_d` returns an error if the basis and center number of rows differs
    #[test]
    fn mismatching_matrix_dimensions() {
        let basis = MatZ::identity(3, 5);
        let n = Z::from(1024);
        let center = MatQ::new(4, 1);
        let gaussian_parameter = Q::ONE;

        let res = sample_d(&basis, &n, &center, &gaussian_parameter);

        assert!(res.is_err());
    }

    /// Checks whether `sample_d` returns an error if center isn't a column vector
    #[test]
    fn center_not_column_vector() {
        let basis = MatZ::identity(2, 2);
        let n = Z::from(1024);
        let center = MatQ::new(2, 2);
        let gaussian_parameter = Q::ONE;

        let res = sample_d(&basis, &n, &center, &gaussian_parameter);

        assert!(res.is_err());
    }

    /// Ensures that the concentration bound holds.
    #[test]
    fn concentration_bound() {
        let n = Z::from(20);
        let basis = MatZ::sample_uniform(&n, &n, 0, 5000).unwrap();
        let orth = MatQ::from(&basis).gso();
        let mut len = Q::ZERO;
        for i in 0..orth.get_num_columns() {
            let column = orth.get_column(i).unwrap();
            let column_len = column.norm_eucl_sqrd().unwrap().sqrt();
            if column_len > len {
                len = column_len
            }
        }

        let expl_text = String::from("This test can fail with probability close to 0. 
        It fails if the length of the sampled is longer than expected. 
        If this happens, rerun the tests several times and check whether this issue comes up again.");

        let center = MatQ::new(&n, 1);
        let gaussian_parameter =
            len * n.log(2).unwrap().sqrt() * (n.log(2).unwrap().log(2).unwrap());

        for _ in 0..20 {
            let res = sample_d(&basis, &n, &center, &gaussian_parameter).unwrap();

            assert!(
                res.norm_eucl_sqrd().unwrap() <= gaussian_parameter.pow(2).unwrap().round() * &n,
                "{expl_text}"
            );
        }
    }
}
