//! [`PolyOverZ`] is a type of polynomial with arbitrarily many coefficients of type
//! [`Z`](crate::integer::Z)
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_poly::fmpz_poly_struct;

mod evaluate;
mod from;
mod get;
mod ownership;
mod set;
mod to_string;

#[derive(Debug)]
/// [`PolyOverZ`] is a type of polynomial with arbitrarily many coefficients of type
/// [`Z`](crate::integer::Z).
///
// Attributes:
// - `poly`: holds the content of the polynomial
//
/// # Example
/// ```rust
/// use math::integer::PolyOverZ;
/// use std::str::FromStr;
///
/// let poly = PolyOverZ::from_str("4  0 1 2 3").unwrap();
/// ```
pub struct PolyOverZ {
    pub(crate) poly: fmpz_poly_struct,
}
