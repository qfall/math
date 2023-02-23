//! [PolyQ] is a type of polynomial with integer coefficients of arbitrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpq_poly::fmpq_poly_struct;

#[doc(hidden)]
pub mod conversions;
#[doc(hidden)]
pub mod from;

#[derive(Debug)]
/// [PolyQ] is a type of polynomial with integer coefficients of arbitrary length.
///
/// Attributes:
/// - `poly`: holds the content of the polynomial
///
/// # Example
/// ```rust
/// use math::rational::PolyQ;
/// use std::str::FromStr;
///
/// let poly = PolyQ::from_str("4  0 1/3 2/10 -3/2").unwrap();
/// ```
pub struct PolyQ {
    pub(crate) poly: fmpq_poly_struct,
}
