//! Implementations to get content of a
//! [`ModulusPolynomialRingZq].

use super::ModulusPolynomialRingZq;
use flint_sys::fq::fq_ctx_struct;

impl ModulusPolynomialRingZq {
    /// Returns the [`fq_ctx_struct`] of a modulus and is only used internally.
    pub(crate) fn get_fq_ctx_struct(&self) -> &fq_ctx_struct {
        self.modulus.as_ref()
    }
}
