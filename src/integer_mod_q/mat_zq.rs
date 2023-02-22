//! `MatZq` is a type of matrix with integer entries of arbitrary length modulo `q`.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_mod_mat::fmpz_mod_mat_struct;

#[allow(dead_code)]
#[derive(Debug)]
pub struct MatZq {
    pub(crate) matrix: fmpz_mod_mat_struct,
}
