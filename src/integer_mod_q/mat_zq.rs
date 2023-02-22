//! `MatZq` is a type of matrix with integer entries of arbitrary length modulo `q`.
//! This implementation uses the [Flint](https://flintlib.org/) library.

use flint_sys::fmpz_mod_mat::fmpz_mod_mat_struct;

#[derive(Debug)]
pub struct MatZq {
    pub(crate) matrix: fmpz_mod_mat_struct,
}
