//! [`ModulusPolynomialRingZq`] is the context object for
//! [`PolynomialRingZq`](super::PolynomialRingZq).
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fq::fq_ctx_struct;

mod from;
mod get;
mod to_string;

/// [`ModulusPolynomialRingZq`] represents the modulus object for
/// [`PolynomialRingZq`](crate::finite_fields::PolynomialRingZq)
///
/// Attributes
/// - `modulus`: holds the specific content, i.e. the prime q and f(X); it
/// holds [FLINT](https://flintlib.org/)'s [struct](fq_ctx_struct)
///
/// # Example
/// ```rust
/// use math::finite_fields::ModulusPolynomialRingZq;
/// use math::integer_mod_q::PolyOverZq;
/// use std::str::FromStr;
///
/// // initialize X^2 + 1 mod 17, i.e. an irreducible polynomial with prime modulus
/// let poly_mod = PolyOverZq::from_str("3  1 0 1 mod 17").unwrap();
/// let modulus = ModulusPolynomialRingZq::from(&poly_mod);
pub struct ModulusPolynomialRingZq {
    modulus: fq_ctx_struct,
}
