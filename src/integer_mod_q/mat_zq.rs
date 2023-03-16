//! `MatZq` is a type of matrix with integer entries of arbitrary length modulo `q`.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_mod_mat::fmpz_mod_mat_struct;

mod from;

#[allow(dead_code)]
#[derive(Debug)]
/// [`MatZq`] is a matrix with entries of type [`Zq`](crate::integer_mod_q::Zq).
///
/// Attributes:
/// - `matrix`: holds [FLINT](https://flintlib.org/)'s [struct](fmpz_mod_mat_struct)
///     of the [`Zq`](crate::integer_mod_q::Zq) matrix
///
/// # Examples
pub struct MatZq {
    pub(crate) matrix: fmpz_mod_mat_struct,
}
