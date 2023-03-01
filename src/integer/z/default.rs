//! Default value for a [`Z`].

use flint_sys::fmpz::fmpz;

use super::Z;

impl Default for Z {
    /// Create a default [`Z`] integer from a in form of `0`.
    ///
    /// Returns a [`Z`].
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
mod tests {
    use super::Z;

    // Ensure that initialization of default value works.
    #[test]
    fn init() {
        let _: Z = Z::default();
    }
}
