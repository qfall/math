//! [`PolynomialRingZq`] is a type of ring over PolyOverZq/f(X).
//! Where f(X) is a [`PolyOverZq`](crate::integer_mod_q::PolyOverZq).
//! This implementation uses the [FLINT](https://flintlib.org/) library.
//!
//! **For Developers**: The [`ModulusPolynomialRingZq`] is not applied automatically, and
//! has to be called in the functions individually. Additionally the comparisons
//! assume that the entries are reduced, hence not reduction is performed in the check.
//!
//! The DEVELOPER has to call the [`PolynomialRingZq::reduce`], whenever
//! a computation may exceed the modulus, because it is not reduced automatically

use super::ModulusPolynomialRingZq;
use crate::integer::PolyOverZ;

mod from;
mod reduce;

#[allow(dead_code)]
/// [`PolynomialRingZq`] represents polynomials over the finite field
/// [`PolyOverZq`](crate::integer_mod_q::PolyOverZq)/f(X) where `q` is prime and f(X) is a polynomial over [`Zq`](super::Zq).
///
/// Attributes
/// - `poly`: holds the value
/// - `modulus`: holds the prime `q` and f(X)
///
/// # Example
#[derive(PartialEq, Eq, Debug)]
pub struct PolynomialRingZq {
    poly: PolyOverZ,
    modulus: ModulusPolynomialRingZq,
}
