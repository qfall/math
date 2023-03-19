//! Default values for a [`Z`].

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

impl Z {
    /// Returns an instantiation of [`Z`] with value `1`.
    ///
    /// # Example:
    /// ```rust
    /// use math::integer::Z;
    ///  
    /// let a: Z = Z::ONE;
    /// ```
    pub const ONE: Z = Z {
        value: flint_sys::fmpz::fmpz(1),
    };
}

#[cfg(test)]
mod tests_init {

    use super::Z;

    /// Ensure that [`Default`] initializes [`Z`] with `0`.
    #[test]
    fn init_0() {
        assert_eq!(Z::from(0), Z::default());
    }

    /// Ensure that ONE initializes [`Z`] with `1`.
    #[test]
    fn init_1() {
        assert_eq!(Z::from(1), Z::ONE);
    }
}
