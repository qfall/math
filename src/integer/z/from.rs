//! Implementations to create a [Z] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [From] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use flint_sys::fmpz::{fmpz, fmpz_init_set_si};

use super::Z;
use crate::macros;

impl Z {
    /// Create a new Integer that can grow arbitrary large.
    ///
    /// Input parameters:
    /// * value: the initial value the integer should have
    ///
    /// Output:
    /// * The new integer
    ///
    /// # Example
    /// ```rust
    /// use math::integer::Z;
    ///
    /// let a: Z = Z::from_i64(42);
    /// ```
    pub fn from_i64(value: i64) -> Self {
        let mut ret_value = fmpz(0);
        unsafe { fmpz_init_set_si(&mut ret_value, value) }
        Z { value: ret_value }
    }
}

macros::from_trait!(i64, Z, Z::from_i64);

#[cfg(test)]
mod tests {
    use super::Z;

    // Ensure that initialization with large numbers works.
    // Numbers larger than 2^62 bits are represented differently in Flint.
    #[test]
    fn from_i64_max_positive() {
        Z::from_i64(i64::MAX);
    }

    // Ensure that initialization with large negative numbers works.
    // Numbers smaller than -2^62 bits are represented differently in Flint.
    #[test]
    fn from_i64_max_negative() {
        Z::from_i64(i64::MIN);
    }

    // Ensure that the from trait is available for i64 values
    #[test]
    fn from_i64_trait() {
        let _ = Z::from(-10i64);
    }
}
