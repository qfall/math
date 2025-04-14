use super::MatPolynomialRingZq;
use crate::{error::MathError, traits::CompareBase};

impl CompareBase for MatPolynomialRingZq {
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
    use crate::{
        integer_mod_q::{MatPolynomialRingZq, ModulusPolynomialRingZq},
        traits::CompareBase,
    };
    use std::str::FromStr;

    /// Ensures that the [`CompareBase`] trait uses an actual implementation.
    #[test]
    fn different_base() {
        let modulus = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
        let one_1 = MatPolynomialRingZq::identity(10, 7, &modulus);
        let modulus = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 23").unwrap();
        let one_2 = MatPolynomialRingZq::identity(10, 7, &modulus);

        assert!(!one_1.compare_base(&one_2));
        assert!(one_1.call_compare_base_error(&one_2).is_some())
    }

    /// Ensures that the same base return `true`.
    #[test]
    fn same_base() {
        let modulus = ModulusPolynomialRingZq::from_str("3  1 0 1 mod 17").unwrap();
        let one_1 = MatPolynomialRingZq::identity(10, 7, &modulus);
        let one_2 = MatPolynomialRingZq::identity(29, 3, &modulus);

        assert!(one_1.compare_base(&one_2));
    }
}
