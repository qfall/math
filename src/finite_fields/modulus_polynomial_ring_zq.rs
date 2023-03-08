//! [`ModulusPolynomialRingZq`] is the context object for
//! [`PolynomialRingZq`](super::PolynomialRingZq).
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fq::fq_ctx_struct;

mod from;
mod get;
mod to_string;

pub struct ModulusPolynomialRingZq {
    modulus: fq_ctx_struct,
}
