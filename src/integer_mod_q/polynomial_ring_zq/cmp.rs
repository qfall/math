use super::PolynomialRingZq;
use crate::{error::MathError, traits::CompareBase};

impl CompareBase for PolynomialRingZq {
    fn compare_base(&self, other: &Self) -> bool {
        self.get_mod() == other.get_mod()
    }

    fn call_compare_base_error(&self, other: &Self) -> Option<MathError> {
        Some(MathError::MismatchingModulus(format!(
            "The moduli of the matrices mismatch. One of them is {} and the other is {}.
            The desired operation is not defined and an error is returned.",
            self.get_mod(),
            other.get_mod()
        )))
    }
}

/// Test that the [`CompareBase`] trait uses an actual implementation.
#[cfg(test)]
mod test_compare_base {
    use crate::{integer_mod_q::PolynomialRingZq, traits::CompareBase};
    use std::str::FromStr;

    /// Ensures that the [`CompareBase`] trait uses an actual implementation.
    #[test]
    fn different_base() {
        let p1 = PolynomialRingZq::from_str("0 / 3  1 1 2 mod 7").unwrap();
        let p2 = PolynomialRingZq::from_str("2  7 14 / 2  1 1  mod 7").unwrap();

        assert!(!p1.compare_base(&p2));
        assert!(p1.call_compare_base_error(&p2).is_some())
    }

    /// Ensures that the same base return `true`.
    #[test]
    fn same_base() {
        let p1 = PolynomialRingZq::from_str("0 / 2  1 1 mod 7").unwrap();
        let p2 = PolynomialRingZq::from_str("2  7 14 / 2  1 1  mod 7").unwrap();

        assert!(p1.compare_base(&p2));
    }
}
