//! [`PolyOverQ`] is a type of polynomial with arbitrarily many coefficients of type
//! [`Q`](crate::rational::Q).
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpq_poly::fmpq_poly_struct;

mod cmp;
mod default;
mod evaluate;
mod from;
mod get;
mod ownership;
mod to_string;

/// [`PolyOverQ`] is a type of polynomial with arbitrarily many coefficients of type
/// [`Q`](crate::rational::Q).
///
// Attributes:
// - `poly`: holds the content of the polynomial
//
/// # Example
/// ```
/// use math::rational::PolyOverQ;
/// use std::str::FromStr;
///
/// let poly = PolyOverQ::from_str("5  0 1/3 2/10 -3/2 1").unwrap();
/// ```
#[derive(Debug)]
pub struct PolyOverQ {
    pub(crate) poly: fmpq_poly_struct,
}
