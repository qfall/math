use flint_sys::fmpz_mod_poly_factor::fmpz_mod_poly_is_irreducible;

use super::PolyOverZq;

impl PolyOverZq {
    pub fn is_irreducible(&self) -> bool {
        1 == unsafe { fmpz_mod_poly_is_irreducible(&self.poly, self.modulus.get_fq_ctx_struct()) }
    }
}

#[cfg(test)]
mod test_is_irreducible {
    use crate::integer_mod_q::PolyOverZq;
    use std::str::FromStr;

    /// ensure that a irreducible [`PolyOverZq`] of degree 1 returns `true`
    #[test]
    fn poly_is_irreducible_degree_one() {
        // X^2 + 1 is irreducible over Zq
        let poly_irr = PolyOverZq::from_str("2  1 1 mod 17").unwrap();
        println!("{}", poly_irr);
        assert!(poly_irr.is_irreducible())
    }

    /// ensure that a irreducible [`PolyOverZq`] returns `true`
    #[test]
    fn poly_is_irreducible() {
        // 9X^2 + 12X + 10 is irreducible over Z17
        let poly_irr = PolyOverZq::from_str("3  10 12 9 mod 17").unwrap();
        assert!(poly_irr.is_irreducible())
    }

    /// ensure that a reducible [`PolyOverZq`] returns `false`
    #[test]
    fn poly_is_reducible() {
        let poly_irr = PolyOverZq::from_str("3  1 2 1 mod 17").unwrap();
        assert!(!poly_irr.is_irreducible())
    }
}
