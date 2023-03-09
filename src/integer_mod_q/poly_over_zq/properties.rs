use flint_sys::fmpz_mod_poly_factor::fmpz_mod_poly_is_irreducible;

use super::PolyOverZq;

impl PolyOverZq {
    pub fn is_irreducible(&self) -> bool {
        1 == unsafe { fmpz_mod_poly_is_irreducible(&self.poly, self.modulus.get_fq_ctx_struct()) }
    }
}
