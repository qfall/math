// Copyright © 2025 Niklas Siemer
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
//!   Trapdoors for hard lattices and new cryptographic constructions.
//!   In: Proceedings of the fortieth annual ACM symposium on Theory of computing.
//!   <https://citeseerx.ist.psu.edu/document?doi=d9f54077d568784c786f7b1d030b00493eb3ae35>

use super::uniform::UniformIntegerSampler;
use crate::{
    error::{MathError, StringConversionError},
    integer::{MatZ, Z},
    rational::{MatQ, Q},
    traits::{MatrixDimensions, MatrixGetSubmatrix, Pow},
};
use rand::Rng;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Defines whether a lookup-table should be precomputed, filled on-the-fly,
/// or not used at all for a discrete Gaussian sampler.
#[derive(PartialEq, Clone, Copy, Serialize, Deserialize, Debug)]
pub enum LookupTableSetting {
    Precompute,
    FillOnTheFly,
    NoLookup,
}

/// This is the global variable used in all `sample_discrete_gauss` and `sample_d`
/// functions. Its value should be in `ω(log(sqrt(n)))`. We set it (as most other libraries)
/// statically to `6.0`.
///
/// You can use and change in an `unsafe` environment.
/// ```compile_fail
/// unsafe { TAILCUT = 4.0 };
/// ```
/// Make sure that the tailcut stays positive and large enough for your purposes.
/// If you use multi-threading, read up on the behaviour of a `static mut` variable.
/// Our tests only cover cases where `TAILCUT = 6.0`.
pub static mut TAILCUT: f64 = 6.0;

/// Enables for discrete Gaussian sampling out of
/// `[⌈center - s * tailcut⌉ , ⌊center + s * tailcut⌋ ]`.
///
/// **WARNING:** If the attributes are not set using [`DiscreteGaussianIntegerSampler::init`],
/// we can't guarantee sampling from the correct discrete Gaussian distribution.
/// Altering any value will invalidate the [`HashMap`] in `table` and might invalidate
/// other attributes, too.
///
/// Attributes:
/// - `center`: specifies the position of the center with peak probability
/// - `s`: specifies the Gaussian parameter, which is proportional
///   to the standard deviation `sigma * sqrt(2 * pi) = s`
/// - `lower_bound`: specifies the lower bound to sample uniformly from
/// - `interval_size`: specifies the interval size to sample uniformly from
/// - `lookup_table_setting`: Specifies whether a lookup-table should be used and
///   how it should be filled, i.e. lazily on-the-fly (impacting sampling time slightly) or precomputed
/// - `table`: the lookup-table if one is used
///
/// # Examples
/// ```
/// use qfall_math::{integer::Z, rational::Q};
/// use qfall_math::utils::sample::discrete_gauss::{DiscreteGaussianIntegerSampler, LookupTableSetting};
/// let n = Z::from(1024);
/// let center = 0.0;
/// let gaussian_parameter = 1.0;
/// let tailcut = 6.0;
///
/// let mut dgis = DiscreteGaussianIntegerSampler::init(center, gaussian_parameter, tailcut, LookupTableSetting::NoLookup).unwrap();
///
/// let sample = dgis.sample_z();
/// ```
#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct DiscreteGaussianIntegerSampler {
    pub center: Q,
    pub s: Q,
    pub lower_bound: Z,
    pub interval_size: Z,
    pub lookup_table_setting: LookupTableSetting,
    pub table: HashMap<Z, f64>,
}

impl DiscreteGaussianIntegerSampler {
    /// Initializes the [`DiscreteGaussianIntegerSampler`] with
    /// - `center` as the center of the discrete Gaussian to sample from,
    /// - `s` defining the Gaussian parameter, which is proportional
    ///   to the standard deviation `sigma * sqrt(2 * pi) = s`,
    /// - `lower_bound` as `⌈center - 6 * s⌉`,
    /// - `interval_size` as `⌊center + 6 * s⌋ - ⌈center - 6 * s⌉ + 1`, and
    /// - `table` as an empty [`HashMap`] to store evaluations of the Gaussian function.
    ///
    /// Parameters:
    /// - `n`: specifies the range from which is sampled
    /// - `center`: as the center of the discrete Gaussian to sample from
    /// - `s`: specifies the Gaussian parameter, which is proportional
    ///   to the standard deviation `sigma * sqrt(2 * pi) = s`
    ///
    /// Returns a sample chosen according to the specified discrete Gaussian distribution or
    /// a [`MathError`] if the specified parameters were not chosen appropriately,
    /// i.e. `n > 1` or `s > 0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer::Z, rational::Q};
    /// use qfall_math::utils::sample::discrete_gauss::{DiscreteGaussianIntegerSampler, LookupTableSetting};
    /// let center = 0.0;
    /// let gaussian_parameter = 1.0;
    /// let tailcut = 6.0;
    ///
    /// let mut dgis = DiscreteGaussianIntegerSampler::init(center, gaussian_parameter, tailcut, LookupTableSetting::Precompute).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    ///   if `tailcut < 0` or `s < 0`.
    pub fn init(
        center: impl Into<Q>,
        s: impl Into<Q>,
        tailcut: impl Into<Q>,
        lookup_table_setting: LookupTableSetting,
    ) -> Result<Self, MathError> {
        let center = center.into();
        let mut s = s.into();
        let tailcut = tailcut.into();
        if tailcut < Q::ZERO {
            return Err(MathError::InvalidIntegerInput(format!(
                "The value {tailcut} was provided for parameter tailcut of the function sample_z.
                This function expects this input no smaller than 0."
            )));
        }
        if s < Q::ZERO {
            return Err(MathError::InvalidIntegerInput(format!(
                "The value {s} was provided for parameter s of the function sample_z.
                This function expects this input to be no smaller than 0."
            )));
        }
        if s == Q::ZERO {
            // Ensure that s != 0 s.t. we can divide by s^2 in the Gaussian function
            s = Q::from(0.00001);
        }

        let lower_bound = (&center - &s * &tailcut).ceil();
        let upper_bound = (&center + &s * tailcut).floor();
        // interval [lower_bound, upper_bound] has upper_bound - lower_bound + 1 elements in it
        let interval_size = &upper_bound - &lower_bound + Z::ONE;

        let mut table = HashMap::new();

        if lookup_table_setting != LookupTableSetting::NoLookup && interval_size > u16::MAX {
            println!(
                "WARNING: A completely filled lookup table will exceed 2^16 entries. You should reconsider your sampling method for discrete Gaussians."
            )
        }

        if lookup_table_setting == LookupTableSetting::Precompute {
            let mut i = lower_bound.clone();
            while i <= upper_bound {
                let evaluated_gauss_function = gaussian_function(&i, &center, &s);
                table.insert(i.clone(), evaluated_gauss_function);
                i += Z::ONE;
            }
        }

        Ok(Self {
            center,
            s,
            lower_bound,
            interval_size,
            lookup_table_setting,
            table,
        })
    }

    /// Chooses a sample according to the discrete Gaussian distribution out of
    /// `[lower_bound , lower_bound + interval_size ]`.
    ///
    /// This function implements discrete Gaussian sampling according to the definition of
    /// SampleZ as in [\[1\]](<index.html#:~:text=[1]>).
    ///
    /// # Examples
    /// ```
    /// use qfall_math::{integer::Z, rational::Q};
    /// use qfall_math::utils::sample::discrete_gauss::{DiscreteGaussianIntegerSampler, LookupTableSetting};
    /// let center = 0.0;
    /// let gaussian_parameter = 1.0;
    /// let tailcut = 6.0;
    ///
    /// let mut dgis = DiscreteGaussianIntegerSampler::init(center, gaussian_parameter, tailcut, LookupTableSetting::Precompute).unwrap();
    ///
    /// let sample = dgis.sample_z();
    /// ```
    pub fn sample_z(&mut self) -> Z {
        let mut rng = rand::rng();
        let mut uis = UniformIntegerSampler::init(&self.interval_size).unwrap();
        loop {
            // sample x in [c - s * tailcut, c + s * tailcut]
            let sample = &self.lower_bound + uis.sample();

            let evaluated_gauss_function: &f64 = match self.lookup_table_setting {
                LookupTableSetting::NoLookup => &gaussian_function(&sample, &self.center, &self.s),
                LookupTableSetting::FillOnTheFly => {
                    let pot_evaluated_gauss_function = self.table.get(&sample);
                    match pot_evaluated_gauss_function {
                        Some(x) => x,
                        None => &{
                            // if the entry doesn't exist yet, compute and insert it
                            let evaluated_function =
                                gaussian_function(&sample, &self.center, &self.s);
                            self.table.insert(sample.clone(), evaluated_function);
                            evaluated_function
                        },
                    }
                }
                LookupTableSetting::Precompute => self.table.get(&sample).unwrap(),
            };

            let random_f64: f64 = rng.random();
            if evaluated_gauss_function >= &random_f64 {
                return sample;
            }
        }
    }
}

/// Computes the value of the Gaussian function for `x`.
///
/// **Warning**: This functions assumes `s != 0`.
///
/// Parameters:
/// - `x`: specifies the value/ sample for which the Gaussian function's value is computed
/// - `c`: specifies the position of the center with peak probability
/// - `s`: specifies the Gaussian parameter, which is proportional
///   to the standard deviation `sigma * sqrt(2 * pi) = s`
///
/// Returns the computed value of the Gaussian function for `x`.
///
/// # Examples
/// ```
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
/// - if `-π * (x - c)^2 / s^2` is larger than [`f64::MAX`]
pub fn gaussian_function(x: &Z, c: &Q, s: &Q) -> f64 {
    let num = Q::MINUS_ONE * Q::PI * (x - c).pow(2).unwrap();
    let den = s.pow(2).unwrap();
    let res = f64::from(&(num / den));
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
///   to the standard deviation `sigma * sqrt(2 * pi) = s`
///
/// Returns a vector with discrete gaussian error based on a lattice point
/// as in [\[1\]](<index.html#:~:text=[1]>): SampleD or a [`MathError`], if the
/// `n <= 1` or `s <= 0`, the number of rows of the `basis` and `center` differ,
/// or `center` is not a column vector.
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
///   if `n <= 1` or `s <= 0`.
/// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
///   if the number of rows of the `basis` and `center` differ.
/// - Returns a [`MathError`] of type [`StringConversionError`](MathError::StringConversionError)
///   if `center` is not a column vector.
pub(crate) fn sample_d(basis: &MatZ, center: &MatQ, s: &Q) -> Result<MatZ, MathError> {
    let basis_gso = MatQ::from(basis).gso();
    sample_d_precomputed_gso(basis, &basis_gso, center, s)
}

/// SampleD samples a discrete Gaussian from the lattice with `basis` using [`sample_z`] as a subroutine.
///
/// We do not check whether `basis` is actually a basis or whether `basis_gso` is
/// actually the gso of `basis`. Hence, the callee is responsible for making sure that
/// `basis` provides a suitable basis and `basis_gso` is a corresponding GSO.
///
/// Parameters:
/// - `basis`: specifies a basis for the lattice from which is sampled
/// - `basis_gso`: specifies the precomputed gso for `basis`
/// - `n`: specifies the range from which [`sample_z`] samples
/// - `center`: specifies the positions of the center with peak probability
/// - `s`: specifies the Gaussian parameter, which is proportional
///   to the standard deviation `sigma * sqrt(2 * pi) = s`
///
/// Returns a vector with discrete gaussian error based on a lattice point
/// as in [\[1\]](<index.html#:~:text=[1]>): SampleD or a [`MathError`], if the
/// `n <= 1` or `s <= 0`, the number of rows of the `basis` and `center` differ,
/// or `center` is not a column vector.
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
/// let basis_gso = basis.gso();
///
/// let sample = sample_d(basis, &basis_gso, &n, &center, &gaussian_parameter).unwrap();
/// ```
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
///   if `n <= 1` or `s <= 0`.
/// - Returns a [`MathError`] of type [`MismatchingMatrixDimension`](MathError::MismatchingMatrixDimension)
///   if the number of rows of the `basis` and `center` differ.
/// - Returns a [`MathError`] of type [`StringConversionError`](MathError::StringConversionError)
///   if `center` is not a column vector.
///
/// # Panics ...
/// - if the number of rows/columns of `basis_gso` and `basis` mismatch.
pub(crate) fn sample_d_precomputed_gso(
    basis: &MatZ,
    basis_gso: &MatQ,
    center: &MatQ,
    s: &Q,
) -> Result<MatZ, MathError> {
    let mut center = center.clone();
    assert_eq!(
        basis.get_num_rows(),
        basis_gso.get_num_rows(),
        "The provided gso can not be based on the provided base, \
        as they do not have the same number of rows."
    );
    assert_eq!(
        basis.get_num_columns(),
        basis_gso.get_num_columns(),
        "The provided gso can not be based on the provided base, \
        as they do not have the same number of columns."
    );
    if center.get_num_rows() != basis.get_num_rows() {
        return Err(MathError::MismatchingMatrixDimension(format!(
            "sample_d requires center and basis to have the same number of columns, but they were {} and {}.",
            center.get_num_rows(),
            basis.get_num_rows()
        )));
    }
    if !center.is_column_vector() {
        Err(StringConversionError::InvalidMatrix(format!(
            "sample_d expects center to be a column vector, but it has dimensions {}x{}.",
            center.get_num_rows(),
            center.get_num_columns()
        )))?;
    }
    if s < &Q::ZERO {
        return Err(MathError::InvalidIntegerInput(format!(
            "The value {s} was provided for parameter s of the function sample_z.
            This function expects this input to be larger than 0."
        )));
    }

    let mut out = MatZ::new(basis_gso.get_num_rows(), 1);

    for i in (0..basis_gso.get_num_columns()).rev() {
        // basisvector_i = b_tilde[i]
        let basisvector_orth_i = unsafe { basis_gso.get_column_unchecked(i) };

        // define the center for sample_z as c_2 = <c, b_tilde[i]> / <b_tilde[i], b_tilde[i]>;
        let c_2 = center.dot_product(&basisvector_orth_i).unwrap()
            / basisvector_orth_i.dot_product(&basisvector_orth_i).unwrap();

        // Defines the gaussian parameter to be normalized along the basis vector: s2 = s / ||b_tilde[i]||
        let s_2 = s / (basisvector_orth_i.norm_eucl_sqrd().unwrap().sqrt());

        // sample z ~ D_{Z, s2, c2}
        let mut dgis = DiscreteGaussianIntegerSampler::init(
            &c_2,
            &s_2,
            unsafe { TAILCUT },
            LookupTableSetting::FillOnTheFly,
        )?;
        let z = dgis.sample_z();

        // update the center c = c - z * b[i]
        let basisvector_i = unsafe { basis.get_column_unchecked(i) };
        center -= MatQ::from(&(&z * &basisvector_i));

        // out = out + z * b[i]
        out = &out + &z * &basisvector_i;
    }

    Ok(out)
}

#[cfg(test)]
mod test_discrete_gaussian_integer_sampler {
    use super::DiscreteGaussianIntegerSampler;
    use crate::{
        rational::Q,
        utils::sample::discrete_gauss::{LookupTableSetting, TAILCUT},
    };

    /// Checks whether samples are kept in correct interval for a small interval.
    #[test]
    fn small_interval() {
        let center = Q::from(15);
        let gaussian_parameter = Q::from((1, 2));

        let mut dgis = DiscreteGaussianIntegerSampler::init(
            &center,
            &gaussian_parameter,
            8.0,
            LookupTableSetting::FillOnTheFly,
        )
        .unwrap();

        for _ in 0..64 {
            let sample = dgis.sample_z();

            assert!(10 <= sample);
            assert!(sample <= 20);
        }
    }

    /// Checks whether samples are kept in correct interval for a large interval.
    #[test]
    fn large_interval() {
        let center = Q::MINUS_ONE;
        let gaussian_parameter = Q::ONE;

        let mut dgis = DiscreteGaussianIntegerSampler::init(
            &center,
            &gaussian_parameter,
            unsafe { TAILCUT },
            LookupTableSetting::FillOnTheFly,
        )
        .unwrap();

        for _ in 0..256 {
            let sample = dgis.sample_z();

            assert!(-64 <= sample);
            assert!(sample <= 62);
        }
    }

    /// Checks whether `sample_z` returns an error if the gaussian parameter `s < 0`.
    #[test]
    fn invalid_gaussian_parameter() {
        let center = Q::ZERO;

        assert!(
            DiscreteGaussianIntegerSampler::init(
                &center,
                &Q::MINUS_ONE,
                6.0,
                LookupTableSetting::FillOnTheFly
            )
            .is_err()
        );
        assert!(
            DiscreteGaussianIntegerSampler::init(
                &center,
                &Q::from(i64::MIN),
                6.0,
                LookupTableSetting::FillOnTheFly
            )
            .is_err()
        );
    }

    /// Checks whether `sample_z` returns an error if `n < 0`.
    #[test]
    fn invalid_tailcut() {
        let center = Q::MINUS_ONE;
        let gaussian_parameter = Q::ONE;

        assert!(
            DiscreteGaussianIntegerSampler::init(
                &center,
                &gaussian_parameter,
                -0.1,
                LookupTableSetting::FillOnTheFly
            )
            .is_err()
        );
        assert!(
            DiscreteGaussianIntegerSampler::init(
                &center,
                &gaussian_parameter,
                i64::MIN,
                LookupTableSetting::FillOnTheFly
            )
            .is_err()
        );
    }
}

#[cfg(test)]
mod test_gaussian_function {
    use super::{Q, Z, gaussian_function};
    use crate::traits::Distance;

    /// Ensures that the doc test would run properly.
    #[test]
    fn doc_test() {
        let sample = Z::ONE;
        let center = Q::ZERO;
        let gaussian_parameter = Q::ONE;
        // result roughly 0.0432139 computed via WolframAlpha
        let cmp = Q::from((43214, 1_000_000));

        let value = gaussian_function(&sample, &center, &gaussian_parameter);

        assert!(cmp.distance(&Q::from(value)) < Q::from((1, 1_000_000)));
    }

    /// Checks whether the values for small values are computed appropriately
    /// and with appropriate precision.
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

        assert!(cmp_0.distance(&Q::from(res_0)) < Q::from((3, 1_000_000_000)));
        assert!(cmp_1.distance(&Q::from(res_1)) < Q::from((1, 1_000_000)));
        assert_eq!(1.0, res_2);
        assert_eq!(1.0, res_3);
    }

    /// Checks whether the values for large values are computed appropriately
    /// and with appropriate precision.
    #[test]
    fn large_values() {
        let sample = Z::from(i64::MAX);
        let center = Q::from(i64::MAX as u64 + 1);
        let gaussian_parameter = Q::from((1, 2));
        // result roughly 0.00000348734 computed via WolframAlpha
        let cmp = Q::from((349, 100_000_000));

        let res = gaussian_function(&sample, &center, &gaussian_parameter);

        assert!(cmp.distance(&Q::from(res)) < Q::from((3, 1_000_000_000)));
    }

    /// Checks whether `s = 0` results in a panic.
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
    use super::sample_d_precomputed_gso;
    use crate::traits::{Concatenate, MatrixDimensions, MatrixGetSubmatrix, Pow};
    use crate::utils::sample::discrete_gauss::sample_d;
    use crate::{
        integer::{MatZ, Z},
        rational::{MatQ, Q},
    };
    use flint_sys::fmpz_mat::fmpz_mat_hnf;
    use std::str::FromStr;

    /// Ensures that the doc-test compiles and runs properly.
    #[test]
    fn doc_test() {
        let basis = MatZ::identity(5, 5);
        let center = MatQ::new(5, 1);
        let gaussian_parameter = Q::ONE;
        let basis_gso = MatQ::from(&basis).gso();

        let _ = sample_d(&basis, &center, &gaussian_parameter).unwrap();
        let _ = sample_d_precomputed_gso(&basis, &basis_gso, &center, &gaussian_parameter).unwrap();
    }

    /// Ensures that `sample_d` works properly for a non-zero center.
    #[test]
    fn non_zero_center() {
        let basis = MatZ::identity(5, 5);
        let center = MatQ::identity(5, 1);
        let gaussian_parameter = Q::ONE;
        let basis_gso = MatQ::from(&basis).gso();

        let _ = sample_d(&basis, &center, &gaussian_parameter).unwrap();
        let _ = sample_d_precomputed_gso(&basis, &basis_gso, &center, &gaussian_parameter).unwrap();
    }

    /// Ensures that `sample_d` works properly for a different basis.
    #[test]
    fn non_identity_basis() {
        let basis = MatZ::from_str("[[2, 1],[1, 2]]").unwrap();
        let center = MatQ::new(2, 1);
        let gaussian_parameter = Q::ONE;
        let basis_gso = MatQ::from(&basis).gso();

        let _ = sample_d(&basis, &center, &gaussian_parameter).unwrap();
        let _ = sample_d_precomputed_gso(&basis, &basis_gso, &center, &gaussian_parameter).unwrap();
    }

    /// Ensures that `sample_d` outputs a vector that's part of the specified lattice.
    ///
    /// Checks whether the Hermite Normal Form HNF of the basis is equal to the HNF of
    /// the basis concatenated with the sampled vector. If it is part of the lattice, it
    /// should become a zero vector at the end of the matrix.
    #[test]
    fn point_of_lattice() {
        let basis = MatZ::from_str("[[7, 0],[7, 3]]").unwrap();
        let center = MatQ::new(2, 1);
        let gaussian_parameter = Q::ONE;
        let basis_gso = MatQ::from(&basis).gso();

        let sample = sample_d(&basis, &center, &gaussian_parameter).unwrap();
        let sample_prec =
            sample_d_precomputed_gso(&basis, &basis_gso, &center, &gaussian_parameter).unwrap();

        // check whether hermite normal form of HNF(b) = HNF([b|sample_vector])
        let basis_concat_sample = basis.concat_horizontal(&sample).unwrap();
        let basis_concat_sample_prec = basis.concat_horizontal(&sample_prec).unwrap();
        let mut hnf_basis = MatZ::new(2, 2);
        unsafe { fmpz_mat_hnf(&mut hnf_basis.matrix, &basis.matrix) };
        let mut hnf_basis_concat_sample = MatZ::new(2, 3);
        let mut hnf_basis_concat_sample_prec = MatZ::new(2, 3);
        unsafe {
            fmpz_mat_hnf(
                &mut hnf_basis_concat_sample.matrix,
                &basis_concat_sample.matrix,
            )
        };
        unsafe {
            fmpz_mat_hnf(
                &mut hnf_basis_concat_sample_prec.matrix,
                &basis_concat_sample_prec.matrix,
            )
        };
        assert_eq!(
            hnf_basis.get_column(0).unwrap(),
            hnf_basis_concat_sample.get_column(0).unwrap()
        );
        assert_eq!(
            hnf_basis.get_column(0).unwrap(),
            hnf_basis_concat_sample_prec.get_column(0).unwrap()
        );
        assert_eq!(
            hnf_basis.get_column(1).unwrap(),
            hnf_basis_concat_sample.get_column(1).unwrap()
        );
        assert_eq!(
            hnf_basis.get_column(1).unwrap(),
            hnf_basis_concat_sample_prec.get_column(1).unwrap()
        );
        // check whether last vector is zero, i.e. was linearly dependent and part of lattice
        assert!(hnf_basis_concat_sample.get_column(2).unwrap().is_zero());
        assert!(
            hnf_basis_concat_sample_prec
                .get_column(2)
                .unwrap()
                .is_zero()
        );
    }

    /// Checks whether `sample_d` returns an error if the gaussian parameter `s < 0`.
    #[test]
    fn invalid_gaussian_parameter() {
        let basis = MatZ::identity(5, 5);
        let center = MatQ::new(5, 1);
        let basis_gso = MatQ::from(&basis).gso();

        assert!(sample_d(&basis, &center, &Q::MINUS_ONE).is_err());
        assert!(sample_d(&basis, &center, &Q::from(i64::MIN)).is_err());

        assert!(sample_d_precomputed_gso(&basis, &basis_gso, &center, &Q::MINUS_ONE).is_err());
        assert!(sample_d_precomputed_gso(&basis, &basis_gso, &center, &Q::from(i64::MIN)).is_err());
    }

    /// Checks whether `sample_d` returns an error if the basis and center number of rows differs.
    #[test]
    fn mismatching_matrix_dimensions() {
        let basis = MatZ::identity(3, 5);
        let center = MatQ::new(4, 1);
        let gaussian_parameter = Q::ONE;
        let basis_gso = MatQ::from(&basis).gso();

        let res = sample_d(&basis, &center, &gaussian_parameter);
        let res_prec = sample_d_precomputed_gso(&basis, &basis_gso, &center, &gaussian_parameter);

        assert!(res.is_err());
        assert!(res_prec.is_err());
    }

    /// Checks whether `sample_d` returns an error if center isn't a column vector.
    #[test]
    fn center_not_column_vector() {
        let basis = MatZ::identity(2, 2);
        let center = MatQ::new(2, 2);
        let gaussian_parameter = Q::ONE;
        let basis_gso = MatQ::from(&basis).gso();

        let res = sample_d(&basis, &center, &gaussian_parameter);
        let res_prec = sample_d_precomputed_gso(&basis, &basis_gso, &center, &gaussian_parameter);

        assert!(res.is_err());
        assert!(res_prec.is_err());
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
            let res = sample_d(&basis, &center, &gaussian_parameter).unwrap();
            let res_prec =
                sample_d_precomputed_gso(&basis, &orth, &center, &gaussian_parameter).unwrap();

            assert!(
                res.norm_eucl_sqrd().unwrap() <= gaussian_parameter.pow(2).unwrap().round() * &n,
                "{expl_text}"
            );
            assert!(
                res_prec.norm_eucl_sqrd().unwrap()
                    <= gaussian_parameter.pow(2).unwrap().round() * &n,
                "{expl_text}"
            );
        }
    }

    /// Ensure that an orthogonalized base with not matching rows panics.
    #[test]
    #[should_panic]
    fn precomputed_gso_mismatching_rows() {
        let n = Z::from(20);
        let basis = MatZ::sample_uniform(&n, &n, 0, 5000).unwrap();
        let center = MatQ::new(&n, 1);
        let false_gso = MatQ::new(basis.get_num_rows() + 1, basis.get_num_columns());

        let _ = sample_d_precomputed_gso(&basis, &false_gso, &center, &Q::from(5)).unwrap();
    }
    /// Ensure that an orthogonalized base with not matching columns panics.
    #[test]
    #[should_panic]
    fn precomputed_gso_mismatching_columns() {
        let n = Z::from(20);
        let basis = MatZ::sample_uniform(&n, &n, 0, 5000).unwrap();
        let center = MatQ::new(&n, 1);
        let false_gso = MatQ::new(basis.get_num_rows(), basis.get_num_columns() + 1);

        let _ = sample_d_precomputed_gso(&basis, &false_gso, &center, &Q::from(5)).unwrap();
    }
}
