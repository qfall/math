//! Implementations to create a [Z] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [From] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use flint_sys::fmpz::{fmpz, fmpz_init_set_si};

use super::Z;

impl Z {
    /// Create a new Integer that can grow arbitrary large.
    ///
    /// Input parameters:
    /// * initial: the initial value the integer should have
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
    pub fn from_i64(initial: i64) -> Self {
        let mut ret_value = fmpz(0);
        unsafe { fmpz_init_set_si(&mut ret_value, initial) }
        Z { value: ret_value }
    }
}

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
}
