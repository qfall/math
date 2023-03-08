//! [`PolynomialRingZq`] is a type of ring over $Z[X]/f(X)$.
//! Where f(X) is a [`PolyOverZq`](crate::integer_mod_q::PolyZq).
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use super::ModulusPolynomialRingZq;
use crate::integer::PolyOverZ;

#[allow(dead_code)]
/// [`PolynomialRingZq`] represents polynomials over the finite field
/// Zq[X]/f(X) where q is prime and f(X) is irreducible.
///
/// Attributes
/// - `poly`: holds the value
/// - `modulus`: holds the prime q and f(X)
///
/// # Example
pub struct PolynomialRingZq {
    poly: PolyOverZ,
    modulus: ModulusPolynomialRingZq,
}
