//! Implementations to get content of a
//! [`Modulus`].

use super::Modulus;
use flint_sys::fmpz_mod::fmpz_mod_ctx_struct;

impl Modulus {
    /// Returns the [`fmpz_mod_ctx_struct`] of a modulus and is only used internally.
    /// TODO: If the reference-counter is implemented, place the corresponding get_method here
    #[allow(dead_code)]
    pub(crate) fn get_fq_ctx_struct(&self) -> &fmpz_mod_ctx_struct {
        &self.modulus
    }
}
