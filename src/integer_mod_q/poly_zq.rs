//! [PolyZq] is a type of polynomial with integer coefficients modulo q of arbitrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_mod_poly::fmpz_mod_poly_struct;

use super::modulus::Modulus;

#[doc(hidden)]
pub mod conversions;
#[doc(hidden)]
pub mod from;

#[allow(dead_code)]
#[derive(Debug)]
pub struct PolyZq {
    pub(crate) poly: fmpz_mod_poly_struct,
    pub(crate) modulus: Modulus,
}
