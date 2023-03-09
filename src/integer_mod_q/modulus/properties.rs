use flint_sys::fmpz::fmpz_is_prime;

use super::Modulus;

impl Modulus {
    pub fn is_prime(&self) -> bool {
        1 == unsafe { fmpz_is_prime(&self.get_fq_ctx_struct().n[0]) }
    }
}

#[cfg(test)]
mod test_is_prime {
    use std::str::FromStr;

    use crate::integer_mod_q::Modulus;

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
