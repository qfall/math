//! [`PolyOverZq`] is a type of polynomial with arbitrarily many coefficients of type
//! [`Zq`](crate::integer_mod_q::Zq).
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use super::modulus::Modulus;
use flint_sys::fmpz_mod_poly::fmpz_mod_poly_struct;

mod cmp;
mod from;
mod ownership;
mod properties;
mod to_string;

#[allow(dead_code)]
#[derive(Debug)]
/// [`PolyOverZq`] is a type of polynomial with arbitrarily many coefficients of type
/// [`Zq`](crate::integer_mod_q::Zq).
///
// Attributes:
// - `poly`: holds the content of the polynomial
// - `modulus`: holds the value of the modulus
//
/// # Example
/// ```rust
/// use math::integer_mod_q::PolyOverZq;
/// use std::str::FromStr;
///
/// let poly = PolyOverZq::from_str("4  0 1 -2 3 mod 42").unwrap();
/// ```
pub struct PolyOverZq {
    pub(crate) poly: fmpz_mod_poly_struct,
    pub(crate) modulus: Modulus,
}
