//! `MatZq` is a type of matrix with entries is `Zq`.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_mod_mat::fmpz_mod_mat_struct;

#[derive(Debug)]
pub struct MatZq {
    matrix: fmpz_mod_mat_struct,
}
