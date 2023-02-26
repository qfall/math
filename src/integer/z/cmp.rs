use super::Z;

use flint_sys::fmpz::fmpz_equal;

impl PartialEq for Z {
    /// Checks if two integers are equal.
    ///
    /// Input parameters:
    /// * other: the other value that is used to compare the elements
    ///
    /// # Example
    /// ```rust
    /// use math::integer::Z;
    ///
    /// let a: Z = Z::from_i64(42);
    /// let b: Z = Z::from_i64(24);
    /// let compared: bool = (a == b);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        unsafe { 1 == fmpz_equal(&self.value, &other.value) }
    }
}

// always a == a
impl Eq for Z {}

#[cfg(test)]
mod tests {
    use super::Z;

    // Assert 42 != 24
    #[test]
    fn not_equal() {
        let a = Z::from_i64(42);
        let b = Z::from_i64(24);

        assert_ne!(a, b);
    }

    // Test for equality with a large number that uses FLINT's pointer representation.
    #[test]
    fn equal_u64_max() {
        let a = Z::from_u64(u64::MAX);
        let b = Z::from_u64(u64::MAX);

        assert_eq!(a, b);
    }

    // Test for non equality with large numbers that use FLINT's pointer representation.
    #[test]
    fn not_equal_large() {
        let a = Z::from_u64(u64::MAX);
        let b = Z::from_u64(u64::MAX - 1);

        assert_ne!(a, b);
        assert!(a != b);
    }
}
