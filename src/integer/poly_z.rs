//! [PolyZ] is a type of polynomial with integer coefficients of arbitrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_poly::fmpz_poly_struct;

#[doc(hidden)]
pub mod conversions;
#[doc(hidden)]
pub mod from;

#[derive(Debug)]
pub struct PolyZ {
    pub(crate) poly: fmpz_poly_struct,
}
