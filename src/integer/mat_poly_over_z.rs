//! [`MatPolyOverZ`] is a type of matrix with entries of [`PolyOverZ`](crate::integer::PolyOverZ).
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_poly_mat::fmpz_poly_mat_struct;

mod cmp;
mod from;
mod get;
mod ownership;
mod properties;
mod set;

#[derive(Debug)]
/// [`MatPolyOverZ`] is a matrix with entries of type [`PolyOverZ`](crate::integer::PolyOverZ).
///
/// Attributes:
/// - `matrix`: holds [FLINT](https://flintlib.org/)'s [struct](fmpz_poly_mat_struct)
///     of the [`PolyOverZ`](crate::integer::PolyOverZ) matrix
///
/// # Examples
pub struct MatPolyOverZ {
    pub(crate) matrix: fmpz_poly_mat_struct,
}
