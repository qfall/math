//! `MatQ` is a type of matrix with arbritrary rational entries.
//! This implementation uses the [Flint](https://flintlib.org/) library.

use flint_sys::fmpq_mat::fmpq_mat_struct;

#[derive(Debug)]
pub struct MatQ {
    matrix: fmpq_mat_struct,
}
