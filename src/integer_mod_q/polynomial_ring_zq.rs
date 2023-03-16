//! [`PolynomialRingZq`] is a type of ring over PolyOverZq/f(X).
//! Where f(X) is a [`PolyOverZq`](crate::integer_mod_q::PolyOverZq).
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use super::ModulusPolynomialRingZq;
use crate::integer::PolyOverZ;

#[allow(dead_code)]
/// [`PolynomialRingZq`] represents polynomials over the finite field
/// [`PolyOverZq`](crate::integer_mod_q::PolyOverZq)/f(X) where `q` is prime and f(X) is a polynomial over [`Zq`](super::Zq).
///
/// Attributes
/// - `poly`: holds the value
/// - `modulus`: holds the prime `q` and f(X)
///
/// # Example
#[derive(PartialEq, Eq)]
pub struct PolynomialRingZq {
    poly: PolyOverZ,
    modulus: ModulusPolynomialRingZq,
}
