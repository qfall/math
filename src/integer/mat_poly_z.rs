//! [MatPolyZ] is a matrix of size at most 63 bits with entries of
//! [PolyZ](crate::integer::PolyZ).
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_poly_mat::fmpz_poly_mat_struct;

#[doc(hidden)]
pub mod conversions;
#[doc(hidden)]
pub mod from;

#[allow(dead_code)]
#[derive(Debug)]
/// [MatPolyZ] is a matrix of size at most 63 bits with entries of
/// [PolyZ](crate::integer::PolyZ).
///
// Attributes:
// - `mat`: holds the content of the matrix
//
/// # Example(s)
/// [TODO: Code examples]
pub struct MatPolyZ {
    pub(crate) mat: fmpz_poly_mat_struct,
}
