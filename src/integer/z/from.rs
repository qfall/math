//! Implementations to create a [Z] value from other types.
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [From] trait should be implemented.
//!
//! The explicit functions contain the documentation.

use flint_sys::fmpz::{fmpz, fmpz_init_set_si, fmpz_init_set_ui};

use super::Z;
use crate::macros;

impl Z {
    /// Create a new Integer that can grow arbitrary large.
    ///
    /// Input parameters:
    /// - value: the initial value the integer should have
    /// Returns the new integer.
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

    /// Create a new Integer that can grow arbitrary large.
    ///
    /// Input parameters:
    /// - value: the initial value the integer should have
    /// Returns the new integer.
    ///
    /// # Example
    /// ```rust
    /// use math::integer::Z;
    ///
    /// let a: Z = Z::from_u64(42);
    /// ```
    pub fn from_u64(value: u64) -> Self {
        let mut ret_value = fmpz(0);
        unsafe { fmpz_init_set_ui(&mut ret_value, value) }
        Z { value: ret_value }
    }

    // Generate from_<type> functions for singed and unsigned source types.
    macros::from_type!(i32, i64, Z, Z::from_i64);
    macros::from_type!(i16, i64, Z, Z::from_i64);
    macros::from_type!(i8, i64, Z, Z::from_i64);

    macros::from_type!(u32, u64, Z, Z::from_u64);
    macros::from_type!(u16, u64, Z, Z::from_u64);
    macros::from_type!(u8, u64, Z, Z::from_u64);
}

// Generate From trait for the different types.
macros::from_trait!(i64, Z, Z::from_i64);
macros::from_trait!(i32, Z, Z::from_i32);
macros::from_trait!(i16, Z, Z::from_i16);
macros::from_trait!(i8, Z, Z::from_i8);

macros::from_trait!(u64, Z, Z::from_u64);
macros::from_trait!(u32, Z, Z::from_u32);
macros::from_trait!(u16, Z, Z::from_u16);
macros::from_trait!(u8, Z, Z::from_u8);

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

    // Ensure that the from_<type_name> functions are available for
    // singed and unsigned integers of 8, 16, 32, and 64 bit length.
    // Tested with their maximum value.
    #[test]
    fn from_functions_max() {
        // signed
        let _ = Z::from_i8(i8::MAX);
        let _ = Z::from_i16(i16::MAX);
        let _ = Z::from_i32(i32::MAX);
        let _ = Z::from_i64(i64::MAX);

        // unsigned
        let _ = Z::from_u8(u8::MAX);
        let _ = Z::from_u16(u16::MAX);
        let _ = Z::from_u32(u32::MAX);
        let _ = Z::from_u64(u64::MAX);
    }

    // Ensure that the from trait is available for singed and unsigned integers
    // of 8, 16, 32, and 64 bit length. Tested with their maximum value.
    #[test]
    fn from_trait_max() {
        // signed
        let _ = Z::from(i8::MAX);
        let _ = Z::from(i16::MAX);
        let _ = Z::from(i32::MAX);
        let _ = Z::from(i64::MAX);

        // unsigned
        let _ = Z::from(u8::MAX);
        let _ = Z::from(u16::MAX);
        let _ = Z::from(u32::MAX);
        let _ = Z::from(u64::MAX);
    }

    // Ensure that the from trait is available for singed and unsigned integers
    // of 8, 16, 32, and 64 bit length. Tested with their minimum value.
    #[test]
    fn from_trait_min() {
        // signed
        let _ = Z::from(i8::MIN);
        let _ = Z::from(i16::MIN);
        let _ = Z::from(i32::MIN);
        let _ = Z::from(i64::MIN);

        // unsigned
        let _ = Z::from(u8::MIN);
        let _ = Z::from(u16::MIN);
        let _ = Z::from(u32::MIN);
        let _ = Z::from(u64::MIN);
    }
}
