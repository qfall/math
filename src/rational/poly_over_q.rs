//! [`PolyOverQ`] is a type of polynomial with arbitrarily many coefficients of type
//! [`Q`](crate::rational::Q).
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpq_poly::fmpq_poly_struct;

mod from;
mod to_string;

#[derive(Debug)]
/// [`PolyOverQ`] is a type of polynomial with arbitrarily many coefficients of type
/// [`Q`](crate::rational::Q).
///
// Attributes:
// - `poly`: holds the content of the polynomial
//
/// # Example
/// ```rust
/// use math::rational::PolyOverQ;
/// use std::str::FromStr;
///
/// let poly = PolyOverQ::from_str("5  0 1/3 2/10 -3/2 1").unwrap();
/// ```
pub struct PolyOverQ {
    pub(crate) poly: fmpq_poly_struct,
}
