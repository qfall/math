use flint_sys::fmpz::fmpz_is_prime;

use super::Modulus;

impl Modulus {
    pub fn is_prime(&self) -> bool {
        1 == unsafe { fmpz_is_prime(&self.get_fq_ctx_struct().n[0]) }
    }
}
