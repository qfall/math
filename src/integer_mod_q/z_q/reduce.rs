//! Implementations to reduce a [`Z`](crate::integer::Z) with the [`Modulus`](crate::integer_mod_q::Modulus).
//!
//! **For Developers** note: The [`Modulus`](crate::integer_mod_q::Modulus)
//! is not applied automatically, and has to be called in the functions individually.
//! Additionally the comparisons assume that the entries are reduced,
//! hence no reduction is performed in the check.

use super::Zq;
use flint_sys::fmpz_mod::fmpz_mod_set_fmpz;

impl Zq {
    /// This function manually applies the
    /// [`Modulus`](crate::integer_mod_q::Modulus)
    /// to the given [`Z`](crate::integer::Z)
    /// in the [`Zq`].
    ///
    /// # Example
    /// ```compile_fail
    /// use math::integer_mod_q::Zq;
    /// use math::integer_mod_q::Modulus;
    /// use math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let modulus = Modulus::from_str("17").unwrap();
    /// let z = Z::from_str("18").unwrap();
    /// let mut zq = Zq::from_z_modulus(&z, &modulus);
    ///
    /// zq.reduce();
    /// ```
    pub(crate) fn reduce(&mut self) {
        unsafe {
            // Applies modulus to parameter and saves the new value
            fmpz_mod_set_fmpz(
                &mut self.value.value,
                &self.value.value,
                self.modulus.get_fmpz_mod_ctx_struct(),
            );
        };
    }
}

#[cfg(test)]
mod test_reduce {
    use crate::{
        integer::Z,
        integer_mod_q::{Modulus, Zq},
    };
    use std::str::FromStr;

    const BITPRIME64: u64 = u64::MAX - 58;

    /// ensure that large entries are reduced correctly
    #[test]
    fn reduces_large() {
        let modulus = Modulus::from_str(&format!("{}", BITPRIME64)).unwrap();
        let value = Z::from_str(&format!("{}", u64::MAX)).unwrap();
        let mut original = Zq { value, modulus };

        let cmp_modulus = Modulus::from_str(&format!("{}", BITPRIME64)).unwrap();
        let cmp_value = Z::from_str("58").unwrap();

        let cmp = Zq {
            value: cmp_value,
            modulus: cmp_modulus,
        };

        assert_ne!(original, cmp);

        original.reduce();

        assert_eq!(original, cmp);
    }

    /// ensure that small entries are reduced correctly
    #[test]
    fn reduces_small() {
        let modulus = Modulus::from_str("17").unwrap();
        let value = Z::from_str("20").unwrap();
        let mut original = Zq { value, modulus };

        let cmp_modulus = Modulus::from_str("17").unwrap();
        let cmp_value = Z::from_str("3").unwrap();

        let cmp = Zq {
            value: cmp_value,
            modulus: cmp_modulus,
        };

        assert_ne!(original, cmp);

        original.reduce();

        assert_eq!(original, cmp);
    }
}
