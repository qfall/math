//! Default value for a [`Q`].

use flint_sys::{fmpq::fmpq, fmpz::fmpz};

use super::Q;

impl Default for Q {
    /// Create a default [`Q`] rational from a in form of `0/1`.
    ///
    /// Returns a [`Q`].
    ///
    /// # Example:
    /// ```rust
    /// use std::default::Default;
    /// use math::rational::Q;
    ///  
    /// let a: Q = Q::default();
    /// ```
    fn default() -> Self {
        Q {
            value: fmpq {
                num: fmpz(0),
                den: fmpz(1),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Q;

    // Ensure that initialization of default value works.
    #[test]
    fn from_i64_max_positive() {
        let _: Q = Q::default();
    }
}
