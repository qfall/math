//! This module contains implementations of functions
//! important for ownership such as the [`Clone`] and [`Drop`] trait.
//!
//! The explicit functions contain the documentation.

use super::Zq;
use flint_sys::{fmpz::fmpz_clear, fmpz_mod::fmpz_mod_set_fmpz};
use std::mem::MaybeUninit;

impl Clone for Zq {
    /// Returns a deep clone of the given [`Zq`] element.
    /// The value of the [`Modulus`](crate::integer_mod_q::Modulus) is not cloned.
    /// Lookup [`Modulus::clone`](crate::integer_mod_q::Modulus::clone) for further information.
    ///
    /// # Example
    /// ```
    /// use math::integer_mod_q::Zq;
    /// use math::integer::Z;
    ///
    /// let value = Z::from_i64(i64::MAX);
    /// let modulus = Z::from_u64(13);
    /// let a = Zq::try_from_z_z(&value, &modulus).unwrap();
    ///
    /// let b = a.clone();
    /// ```
    fn clone(&self) -> Self {
        let mut value_fmpz = MaybeUninit::uninit();

        let value_fmpz = unsafe {
            fmpz_mod_set_fmpz(
                value_fmpz.as_mut_ptr(),
                &self.value,
                self.modulus.get_fmpz_mod_ctx_struct(),
            );
            value_fmpz.assume_init()
        };

        Zq {
            value: value_fmpz,
            modulus: self.modulus.clone(),
        }
    }
}

impl Drop for Zq {
    /// Drops the given [`Zq`] element and its reference to the [`Modulus`](crate::integer_mod_q::Modulus)
    /// clearing the memory storage if it's not referenced by another instance.
    ///
    /// # Examples
    /// ```
    /// use math::integer_mod_q::Zq;
    /// use math::integer::Z;
    ///
    /// let value = Z::from_i64(i64::MAX);
    /// let modulus = Z::from_u64(13);
    /// {
    ///     let a = Zq::try_from_z_z(&value, &modulus).unwrap();
    /// } // as a's scope ends here, it get's dropped
    /// ```
    ///
    /// ```
    /// use math::integer_mod_q::Zq;
    /// use math::integer::Z;
    ///
    /// let value = Z::from_i64(i64::MAX);
    /// let modulus = Z::from_u64(13);
    /// let a = Zq::try_from_z_z(&value, &modulus).unwrap();
    /// drop(a); // explicitly drops a's value
    /// ```
    fn drop(&mut self) {
        unsafe {
            fmpz_clear(&mut self.value);
        }
    }
}

/// Test that the [`Clone`] trait is correctly implemented.
#[cfg(test)]
mod test_clone {

    use super::Zq;
    use crate::{integer::Z, integer_mod_q::Modulus};
    use std::str::FromStr;

    /// Check if clone points to same point in memory
    #[test]
    fn same_reference() {
        let value = Z::from_u64(u64::MAX);
        let string = "1".repeat(63);
        let modulus = Modulus::from_str(&string).unwrap();

        let a = Zq::from_z_modulus(&value, &modulus);

        let b = a.clone();

        // check that modulus is stored at same place in memory
        assert_eq!(
            &a.modulus.get_fmpz_mod_ctx_struct().n[0].0,
            &b.modulus.get_fmpz_mod_ctx_struct().n[0].0
        );

        // check that value is stored separately in memory
        assert_ne!(&a.value.0, &b.value.0);
    }
}

#[cfg(test)]
mod test_drop {

    use super::Zq;
    use crate::integer::Z;
    use std::collections::HashSet;

    /// Creates and drops a [`Zq`] object, and outputs
    /// the storage point in memory of its [`fmpz`](flint_sys::fmpz::fmpz)
    /// and [`Modulus`](crate::integer_mod_q::Modulus)
    fn create_and_drop_modulus() -> (i64, i64) {
        let value = Z::from_i64(i64::MAX);
        let modulus = Z::from_u64(13);
        let a = Zq::try_from_z_z(&value, &modulus).unwrap();

        (a.value.0, a.modulus.modulus.n[0].0)
    }

    /// Check whether freed memory is reused afterwards
    #[test]
    fn free_memory() {
        let mut storage_addresses = HashSet::new();

        for _i in 0..5 {
            storage_addresses.insert(create_and_drop_modulus());
        }

        if storage_addresses.capacity() == 5 {
            panic!("No storage address of dropped modulus was reused.");
        }
    }
}
