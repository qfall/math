//! Implementations to check certain properties of [`Modulus`]
//! This includes checks such as primeness.

use super::Modulus;
use flint_sys::fmpz::fmpz_is_prime;

impl Modulus {
    /// Checks if a [`Modulus`] is prime.
    ///
    /// Returns true if the modulus is prime.
    ///
    /// ```
    /// use std::str::FromStr;
    /// use math::integer_mod_q::Modulus;
    ///
    /// let modulus = Modulus::from_str("17").unwrap();
    /// assert!(modulus.is_prime())
    /// ```
    pub fn is_prime(&self) -> bool {
        1 == unsafe { fmpz_is_prime(&self.get_fmpz_mod_ctx_struct().n[0]) }
    }
}

#[cfg(test)]
mod test_is_prime {

    use crate::integer_mod_q::Modulus;
    use std::str::FromStr;

    /// ensure that if a [`Modulus`] is instantiated with a prime, `true` is returned
    #[test]
    fn modulus_is_prime() {
        let modulus = Modulus::from_str(&format!("{}", 2_i32.pow(16) + 1)).unwrap();
        assert!(modulus.is_prime())
    }

    /// ensure that if a [`Modulus`] is instantiated with a non-prime, `false` is returned
    #[test]
    fn modulus_is_not_prime() {
        let modulus = Modulus::from_str(&format!("{}", 2_i32.pow(16))).unwrap();
        assert!(!modulus.is_prime())
    }
}
