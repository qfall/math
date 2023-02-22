//! `MatQ` is a type of matrix with rational entries of arbritrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpq_mat::fmpq_mat_struct;

#[derive(Debug)]
pub struct MatQ {
    pub(crate) matrix: fmpq_mat_struct,
}
