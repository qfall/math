//! `MatZ` is a type of matrix with integer entries of arbitrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_mat::fmpz_mat_struct;

mod from;
mod get;
mod ownership;
mod set;

/// [`MatZ`] is a matrix with entries of type [`Z`](crate::integer::Z).
///
/// Attributes:
/// - `matrix`: holds [FLINT](https://flintlib.org/)'s [struct](fmpz_mat_struct)
///     of the [`Z`](crate::integer::Z) matrix
///
/// # Examples
#[derive(Debug)]
pub struct MatZ {
    pub(crate) matrix: fmpz_mat_struct,
}
