//! Default value for a [`Q`].

use super::Q;
use flint_sys::{fmpq::fmpq, fmpz::fmpz};

impl Default for Q {
    /// Returns an instantiation of [`Q`] with value '0/1'.
    ///
    /// # Example:
    /// ```rust
    /// use std::default::Default;
    /// use math::rational::Q;
    ///  
    /// let a: Q = Q::default();
    /// ```
    fn default() -> Self {
        // TODO use from
        Q {
            value: fmpq {
                num: fmpz(0),
                den: fmpz(1),
            },
        }
    }
}

#[cfg(test)]
mod tests_init {

    use super::Q;
    use flint_sys::{
        fmpq::{fmpq, fmpq_equal},
        fmpz::fmpz,
    };

    /// TODO add cmp test

    /// Ensure that initialization of default value works.
    #[test]
    fn init() {
        assert!(unsafe {
            fmpq_equal(
                &Q::default().value,
                &fmpq {
                    num: fmpz(0),
                    den: fmpz(1),
                },
            ) != 0
        });
    }
}
