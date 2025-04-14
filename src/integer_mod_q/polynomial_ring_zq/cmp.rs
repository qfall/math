use super::PolynomialRingZq;
use crate::{error::MathError, traits::CompareBase};

impl CompareBase for PolynomialRingZq {
    fn compare_base(&self, other: &Self) -> bool {
        self.get_mod() == other.get_mod()
    }

    fn call_compare_base_error(&self, other: &Self) -> Result<(), MathError> {
        Err(MathError::MismatchingModulus(format!(
            "The moduli of the matrices mismatch. One of them is {} and the other is {}.
            The desired operation is not defined and an error is returned.",
            self.get_mod(),
            other.get_mod()
        )))
    }
}
