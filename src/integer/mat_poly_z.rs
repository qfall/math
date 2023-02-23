//! [MatPolyZ] is a type matrix with entries that are polynomials with integer coefficients of arbitrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_poly_mat::fmpz_poly_mat_struct;

#[doc(hidden)]
pub mod conversions;
#[doc(hidden)]
pub mod from;

#[allow(dead_code)]
#[derive(Debug)]
/// [MatPolyZ] is a type matrix with entries that are polynomials with integer coefficients of arbitrary length.
///
/// Attributes:
/// - `mat`: holds the content of the matrix
///
/// # Example(s)
/// [TODO: Code examples]
pub struct MatPolyZ {
    pub(crate) mat: fmpz_poly_mat_struct,
}
