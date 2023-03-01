//! Implementations to create a [`Zq`] value from other types.

use super::Zq;
use crate::{error::MathError, integer::Z, integer_mod_q::Modulus};
use flint_sys::fmpz_mod::fmpz_mod_set_fmpz;
use std::mem::MaybeUninit;

impl Zq {
    /// Create [`Zq`] from two [`Z`] values.
    ///
    /// Parameters:
    /// - `value` defines the value of the new [`Zq`].
    /// - `modulus` is used to create a new [`Modulus`] context that will be
    ///   used by [`Zq`].
    ///
    /// Returns the new `value` mod `modulus` as a [`Zq`].
    ///
    /// # Example(s)
    /// ```
    /// # use math::error::MathError;
    /// use math::integer::Z;
    /// use math::integer_mod_q::Zq;
    ///
    /// let value_a = Z::from(42);
    /// let value_b = Z::from(1337+42);
    /// let modulus = Z::from(1337);
    ///
    /// let answer_a = Zq::try_from_z_z(value_a, &modulus)?;
    /// let answer_b = Zq::try_from_z_z(value_b, &modulus)?;
    ///
    /// // TODO: assert_eq!(answer_a, answer_b); once equal for Zq is implemented
    /// # Ok::<(), MathError>(())
    /// ```
    ///
    /// # Errors and Failures [optional]
    /// - Returns a [`MathError`] of type
    ///   [`InvalidIntToModulus`](MathError::InvalidIntToModulus) if the
    ///   provided value is not greater than zero.
    pub fn try_from_z_z(value: Z, modulus: &Z) -> Result<Self, MathError> {
        let modulus = Modulus::try_from_z(modulus)?;

        let mut value_fmpz = MaybeUninit::uninit();
        let value_fmpz = unsafe {
            fmpz_mod_set_fmpz(value_fmpz.as_mut_ptr(), &value.value, &modulus.modulus);
            value_fmpz.assume_init()
        };

        Ok(Zq {
            value: value_fmpz,
            modulus,
        })
    }
}

impl<T1: Into<Z>, T2: Into<Z>> TryFrom<(T1, T2)> for Zq {
    type Error = MathError;
    /// Implements the [`TryFrom`] trait. It is used to create [`Zq`] from a tuple
    /// with two values that can be converted into [`Z`].
    ///
    /// The parameters have to implement the [`Into<Z>`] trait, which is
    /// automatically the case if [`Z`] implements the [`From`] trait for this type.
    /// The first and second element of the tuple may have different types.
    ///
    /// Parameters:
    /// - `value_modulus_tuple` is a tuple `(value, modulus)`:
    ///     - The first value defines the value of the new [`Zq`].
    ///     - The second value defines the new [`Modulus`], which is part of [`Zq`].
    ///
    /// Returns the `value` mod `modulus` as a [`Zq`].
    ///
    /// # Example(s)
    /// ```
    /// # use math::error::MathError;
    /// use math::integer::Z;
    /// use math::integer_mod_q::Zq;
    ///
    /// let value_a: Z = Z::from(42);
    /// let value_b: u64 = 1337+42;
    /// let modulus: i32 = 1337;
    ///
    /// let answer_a = Zq::try_from((value_a, modulus))?;
    /// let answer_b = Zq::try_from((value_b, modulus))?;
    ///
    /// // TODO: assert_eq!(answer_a, answer_b);
    /// # Ok::<(), MathError>(())
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    ///   [`InvalidIntToModulus`](MathError::InvalidIntToModulus) if the
    ///   provided value is not greater than zero.
    fn try_from(value_modulus_tuple: (T1, T2)) -> Result<Self, Self::Error> {
        let modulus: Z = value_modulus_tuple.1.into();
        Zq::try_from_z_z(value_modulus_tuple.0.into(), &modulus)
    }
}

#[cfg(test)]
mod test_try_from_z_z {
    // TODO: add more test cases
    use super::Zq;
    use crate::integer::Z;

    /// Test with small valid value and modulus.
    #[test]
    fn working_small() {
        let value = Z::from(10);
        let modulus = Z::from(15);

        let answer = Zq::try_from_z_z(value, &modulus);
        assert!(answer.is_ok());
    }

    /// Test with large value and modulus (FLINT uses pointer representation).
    #[test]
    fn working_large() {
        let value = Z::from(u64::MAX - 1);
        let modulus = Z::from(u64::MAX);

        let answer = Zq::try_from_z_z(value, &modulus);

        assert!(answer.is_ok());
    }

    /// Test with zero modulus (not valid)
    #[test]
    fn modulus_zero() {
        let value = Z::from(10);
        let modulus = Z::from(0);

        let new_zq = Zq::try_from_z_z(value, &modulus);

        assert!(new_zq.is_err());
    }

    /// Test with negative modulus (not valid)
    #[test]
    fn modulus_negative() {
        let value = Z::from(10);
        let modulus = Z::from(-1);

        let new_zq = Zq::try_from_z_z(value, &modulus);

        assert!(new_zq.is_err());
    }
}

#[cfg(test)]
mod test_try_from_trait {
    use flint_sys::fmpz::fmpz_equal;

    use crate::{integer::Z, integer_mod_q::Zq};

    /// Showcase some of the different types supported by the trait.
    #[test]
    fn types_example() {
        // rust integers supported
        assert!(Zq::try_from((1u8, 2u16)).is_ok());
        assert!(Zq::try_from((1u32, 2u64)).is_ok());
        assert!(Zq::try_from((1i8, 2i16)).is_ok());
        assert!(Zq::try_from((1i32, 2i64)).is_ok());

        // [`Z`] supported
        assert!(Zq::try_from((Z::from(1), Z::from(2))).is_ok());
    }

    /// Ensure that the modulus calculation is performed at initialization.
    #[test]
    fn modulus_at_initialization() {
        let a = Zq::try_from((0, 10)).unwrap();
        let b = Zq::try_from((10, 10)).unwrap();

        // TODO: use Zq equal once implemented.
        assert!(unsafe { fmpz_equal(&a.value, &b.value) } == 1)
    }

    /// Test with small valid value and modulus.
    #[test]
    fn working_small() {
        let new_zq = Zq::try_from((10, 15));

        assert!(new_zq.is_ok());
    }

    /// Test with large value and modulus (FLINT uses pointer representation).
    #[test]
    fn working_large() {
        let new_zq = Zq::try_from((u64::MAX - 1, u64::MAX));

        assert!(new_zq.is_ok());
    }

    /// Test with zero modulus (not valid)
    #[test]
    fn modulus_zero() {
        let new_zq = Zq::try_from((10, 0));

        assert!(new_zq.is_err());
    }

    /// Test with negative modulus (not valid)
    #[test]
    fn modulus_negative() {
        let new_zq = Zq::try_from((10, -1));

        assert!(new_zq.is_err());
    }
}
