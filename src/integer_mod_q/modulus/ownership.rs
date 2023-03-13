//! This module contains implementations of functions
//! important for ownership such as the [`Clone`] and [`Drop`] trait.
//!
//! The explicit functions contain the documentation.

use super::Modulus;
use flint_sys::fmpz_mod::fmpz_mod_ctx_clear;
use std::rc::Rc;

impl Clone for Modulus {
    /// Clones the given element and returns another cloned reference
    /// to the [`fmpz_mod_ctx`](flint_sys::fmpz_mod::fmpz_mod_ctx) element.
    ///
    /// # Example
    /// ```
    /// use math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    ///
    /// let a = Modulus::from_str("3").unwrap();
    /// let b = a.clone();
    /// ```
    fn clone(&self) -> Self {
        Modulus {
            modulus: Rc::clone(&self.modulus),
        }
    }
}

impl Drop for Modulus {
    /// Drops the given reference to the [`fmpz_mod_ctx`](flint_sys::fmpz_mod::fmpz_mod_ctx) element
    /// and frees the allocated memory if no references are left.
    ///
    /// # Examples
    /// ```
    /// use math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    /// {
    ///     let a = Modulus::from_str("3").unwrap();
    /// } // as a's scope ends here, it get's dropped
    /// ```
    ///
    /// ```
    /// use math::integer_mod_q::Modulus;
    /// use std::str::FromStr;
    ///
    /// let a = Modulus::from_str("3").unwrap();
    /// drop(a); // explicitly drops a's value
    /// ```
    ///
    /// # WARNING
    /// A [`nmod_t`](flint_sys::nmod_vec::nmod_t) struct can currently not be cleared and
    /// produces a memory leak every time a [`Modulus`] object should be cleared entirely.
    fn drop(&mut self) {
        if Rc::strong_count(&self.modulus) <= 1 {
            let mut a = *self.modulus;
            unsafe {
                fmpz_mod_ctx_clear(&mut a);
            }
        }
    }
}

/// Test that the [`Clone`] trait is correctly implemented.
#[cfg(test)]
mod test_clone {

    use super::Modulus;
    use std::{rc::Rc, str::FromStr};

    #[test]
    fn add_references() {
        let a = Modulus::from_str("3").unwrap();
        assert_eq!(Rc::strong_count(&a.modulus), 1);

        let b = a.clone();

        assert_eq!(Rc::strong_count(&a.modulus), 2);
        assert_eq!(Rc::strong_count(&b.modulus), 2);

        let c = b.clone();

        assert_eq!(Rc::strong_count(&a.modulus), 3);
        assert_eq!(Rc::strong_count(&b.modulus), 3);
        assert_eq!(Rc::strong_count(&c.modulus), 3);
    }

    /// Check if clone points to same point in memory
    #[test]
    fn same_reference() {
        let a = Modulus::from_str(&"1".repeat(65)).unwrap();

        let b = a.clone();

        assert_eq!(
            &a.get_fmpz_mod_ctx_struct().to_owned().n[0].0,
            &b.get_fmpz_mod_ctx_struct().to_owned().n[0].0
        );
    }
}

#[cfg(test)]
mod test_drop {

    use super::Modulus;
    use crate::integer::Z;
    use std::{rc::Rc, str::FromStr};

    /// Check whether references are decreased when dropping instances
    #[test]
    fn references_decreased() {
        let a = Modulus::from_str("3").unwrap();
        assert_eq!(Rc::strong_count(&a.modulus), 1);

        {
            let b = a.clone();

            assert_eq!(Rc::strong_count(&a.modulus), 2);
            assert_eq!(Rc::strong_count(&b.modulus), 2);
        }

        assert_eq!(Rc::strong_count(&a.modulus), 1);

        let b = a.clone();
        assert_eq!(Rc::strong_count(&a.modulus), 2);
        assert_eq!(Rc::strong_count(&b.modulus), 2);

        let c = b.clone();
        assert_eq!(Rc::strong_count(&a.modulus), 3);
        assert_eq!(Rc::strong_count(&b.modulus), 3);
        assert_eq!(Rc::strong_count(&c.modulus), 3);

        drop(a);
        assert_eq!(Rc::strong_count(&b.modulus), 2);
    }

    /// Check whether freed memory is reused afterwards
    #[test]
    fn free_memory() {
        let string = "1".repeat(65);
        let a = Modulus::from_str(&string).unwrap();
        let point_in_memory = a.get_fmpz_mod_ctx_struct().n[0].0;

        drop(a);

        // instantiate different modulus to check if memory slot is reused for different modulus
        let c = Modulus::from_str(&string).unwrap();
        assert_eq!(c.get_fmpz_mod_ctx_struct().n[0].0, point_in_memory + 4);

        // memory slots differ due to previously created large integer
        assert_ne!(
            point_in_memory,
            Modulus::try_from_z(&Z::from(u64::MAX))
                .unwrap()
                .get_fmpz_mod_ctx_struct()
                .n[0]
                .0
        );
    }
}
