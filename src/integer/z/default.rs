//! Default value for a [`Z`].

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
        Z::from(0)
    }
}

#[cfg(test)]
mod tests_init {

    use super::Z;

    /// Ensure that [`Default`] initializes [`Z`] with `0`.
    #[test]
    fn init() {
        assert_eq!(Z::default(), Z::from(0));
    }
}
