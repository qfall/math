//! [PolyZ] is a type of polynomial with arbitrarily many coefficients of type
//! [Z](crate::integer::z::Z)
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_poly::fmpz_poly_struct;

#[doc(hidden)]
pub mod conversions;
#[doc(hidden)]
pub mod from;

#[derive(Debug)]
/// [PolyZ] is a type of polynomial with arbitrarily many coefficients of type
/// [Z](crate::integer::z::Z)
///
// Attributes:
// - `poly`: holds the content of the polynomial
//
/// # Example
/// ```rust
/// use math::integer::PolyZ;
/// use std::str::FromStr;
///
/// let poly = PolyZ::from_str("4  0 1 2 3").unwrap();
/// ```
pub struct PolyZ {
    pub(crate) poly: fmpz_poly_struct,
}
