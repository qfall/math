//! This module contains implementations of finite fields
//! such as [`PolynomialRingZq`] which corresponds to
//! Zq[X]/f(X) where f(X) is a [`PolyOverZq`](crate::integer_mod_q::PolyOverZq).

mod modulus_polynomial_ring_zq;
mod polynomial_ring_zq;

pub use modulus_polynomial_ring_zq::ModulusPolynomialRingZq;
pub use polynomial_ring_zq::PolynomialRingZq;
