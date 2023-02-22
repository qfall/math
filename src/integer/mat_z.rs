//! `MatZ` is a type of matrix with arbritrary integer entries.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_mat::fmpz_mat_struct;

#[derive(Debug)]
pub struct MatZ {
    pub(crate) matrix: fmpz_mat_struct,
}
