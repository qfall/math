//! [`PolynomialRingZq`] is a type of ring over $Z[X]/f(X)$.
//! Where f(X) is a [`PolyOverZq`](crate::integer_mod_q::PolyZq).
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use super::ModulusPolynomialRingZq;
use crate::integer::PolyOverZ;

#[allow(dead_code)]
pub struct PolynomialRingZq {
    poly: PolyOverZ,
    modulus: ModulusPolynomialRingZq,
}
