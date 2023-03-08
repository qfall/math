//! `MatQ` is a type of matrix with rational entries of arbritrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpq_mat::fmpq_mat_struct;

#[allow(dead_code)]
#[derive(Debug)]
/// [`MatQ`] is a matrix with entries of type [`Q`](crate::rational::Q).
///
/// Attributes:
/// - `matrix`: holds [FLINT](https://flintlib.org/)'s [struct](fmpq_mat_struct)
///     of the [`Q`](crate::rational::Q) matrix
///
/// # Examples
pub struct MatQ {
    pub(crate) matrix: fmpq_mat_struct,
}
