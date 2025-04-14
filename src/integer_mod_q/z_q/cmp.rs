use super::Zq;
use crate::{error::MathError, traits::CompareBase};

impl CompareBase for Zq {
    fn compare_base(&self, other: &Self) -> bool {
        self.get_mod() == other.get_mod()
    }

    fn call_compare_base_error(&self, other: &Self) -> Option<MathError> {
        Some(MathError::MismatchingModulus(format!(
            "The moduli of the ring elements mismatch. One of them is {} and the other is {}.
            The desired operation is not defined and an error is returned.",
            self.get_mod(),
            other.get_mod()
        )))
    }
}

/// Test that the [`CompareBase`] trait uses an actual implementation.
#[cfg(test)]
mod test_compare_base {
    use crate::{integer_mod_q::Zq, traits::CompareBase};
    use std::str::FromStr;

    /// Ensures that the [`CompareBase`] trait uses an actual implementation.
    #[test]
    fn different_base() {
        let v1 = Zq::from_str("2 mod 17").unwrap();
        let v2 = Zq::from_str("2 mod 19").unwrap();

        assert!(!v1.compare_base(&v2));
        assert!(v1.call_compare_base_error(&v2).is_some())
    }

    /// Ensures that the same base return `true`.
    #[test]
    fn same_base() {
        let v1 = Zq::from_str("2 mod 17").unwrap();
        let v2 = Zq::from_str("2 mod 17").unwrap();

        assert!(v1.compare_base(&v2));
    }
}
