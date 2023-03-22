//! Implementations to reduce a [`PolynomialRingZq`] with the
//! [`ModulusPolynomialRingZq`](crate::integer_mod_q::ModulusPolynomialRingZq).
//!
//! **For Developers** note: The [`ModulusPolynomialRingZq`](crate::integer_mod_q::ModulusPolynomialRingZq)
//! is not applied automatically, and has to be called in the functions individually.
//! Additionally the comparisons assume that the entries are reduced,
//! hence no reduction is performed in the check.

use super::PolynomialRingZq;
use flint_sys::fq::fq_reduce;

impl PolynomialRingZq {
    /// This function manually applies the modulus
    /// [`ModulusPolynomialRingZq`](crate::integer_mod_q::ModulusPolynomialRingZq)
    /// to the given polynomial [`PolyOverZ`](crate::integer::PolyOverZ)
    /// in the [`PolynomialRingZq`].
    ///
    /// # Example
    /// ```compile_fail
    /// use math::integer_mod_q::PolynomialRingZq;
    /// use math::integer_mod_q::ModulusPolynomialRingZq;
    /// use math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    /// let poly = PolyOverZ::from_str("4  -1 0 1 1").unwrap();
    /// let mut poly_ring = PolynomialRingZq::from((&poly, &modulus));
    ///
    /// poly_ring.reduce()
    /// ```
    pub(crate) fn reduce(&mut self) {
        unsafe { fq_reduce(&mut self.poly.poly, self.modulus.get_fq_ctx_struct()) }
    }
}

#[cfg(test)]
mod test_reduced {
    use crate::{
        integer::PolyOverZ,
        integer_mod_q::{ModulusPolynomialRingZq, PolynomialRingZq},
    };
    use std::str::FromStr;

    const BITPRIME64: u64 = 18446744073709551557;

    /// ensure that the entries are reduced
    #[test]
    fn reduces() {
        let modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", BITPRIME64)).unwrap();
        let poly = PolyOverZ::from_str(&format!("4  {} {} 1 1", BITPRIME64 + 2, u64::MAX)).unwrap();
        let mut poly_ring = PolynomialRingZq { poly, modulus };

        let cmp_modulus =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {}", BITPRIME64)).unwrap();
        let cmp_poly = PolyOverZ::from_str("3  1 58 1").unwrap();
        let cmp_poly_ring = PolynomialRingZq {
            poly: cmp_poly.clone(),
            modulus: cmp_modulus,
        };

        // we only compare the parts individually, not under the modulus, hence they should not be the same
        // unless they have been reduced
        assert_ne!(poly_ring.poly, cmp_poly);
        assert_ne!(poly_ring, cmp_poly_ring);

        poly_ring.reduce();
        assert_eq!(poly_ring.poly, cmp_poly);
        assert_eq!(poly_ring, cmp_poly_ring);
    }
}
