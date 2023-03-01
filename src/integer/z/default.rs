//! Default value for a [`Z`].

use flint_sys::fmpz::fmpz;

use super::Z;

impl Default for Z {
    /// Returns an instantiation of [`Z`] with value `0`.
    ///
    /// # Example:
    /// ```rust
    /// use std::default::Default;
    /// use math::integer::Z;
    ///  
    /// let a: Z = Z::default();
    /// ```
    fn default() -> Self {
        Z { value: fmpz(0) }
    }
}

#[cfg(test)]
mod tests_init {

    use super::Z;

    // Ensure that initialization of default value works.
    #[test]
    fn init() {
        assert_eq!(Z::default(), Z::from(0));
    }
}
