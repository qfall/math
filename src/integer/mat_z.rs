//! `MatZ` is a type of matrix with arbritrary integer entries.
//! This implementation uses the [Flint](https://flintlib.org/) library.

use flint_sys::fmpz_mat::fmpz_mat_struct;

#[derive(Debug)]
pub struct MatZ {
    matrix: fmpz_mat_struct,
}
