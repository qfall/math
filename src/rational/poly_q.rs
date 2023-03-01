//! [`PolyQ`] is a type of polynomial with arbitrarily many coefficients of type
//! [`Q`](crate::rational::q::Q).
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpq_poly::fmpq_poly_struct;

pub mod from;
pub mod to_string;

#[derive(Debug)]
/// [`PolyQ`] is a type of polynomial with arbitrarily many coefficients of type
/// [`Q`](crate::rational::q::Q).
///
// Attributes:
// - `poly`: holds the content of the polynomial
//
/// # Example
/// ```rust
/// use math::rational::PolyQ;
/// use std::str::FromStr;
///
/// let poly = PolyQ::from_str("5  0 1/3 2/10 -3/2 1").unwrap();
/// ```
pub struct PolyQ {
    pub(crate) poly: fmpq_poly_struct,
}
