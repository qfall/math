//! `MatZ` is a type of matrix with integer entries of arbitrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_mat::fmpz_mat_struct;

mod from;
mod get;
mod set;

#[allow(dead_code)]
#[derive(Debug)]
pub struct MatZ {
    pub(crate) matrix: fmpz_mat_struct,
}
