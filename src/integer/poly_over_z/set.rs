//! Implementations to set coefficients for a [`PolyOverZ`] value from other types.
//! Each reasonable type should be used to set a coefficient.

use super::PolyOverZ;
use crate::{
    error::MathError, integer::Z, macros::for_others::implement_for_others_set_coeff,
    traits::SetCoefficient, utils::coordinate::evaluate_coordinate,
};
use flint_sys::fmpz_poly::fmpz_poly_set_coeff_fmpz;
use std::fmt::Display;

impl SetCoefficient<Z> for PolyOverZ {
    // It is limited to i16, because an i32 as a coefficient would simply take far too
    // much memory to be allocated:
    // #number of coefficients * # minimum size of an entry =
    // 2^32*64 = 274.877.906.944 Bits ≈ 34 GB since every entry
    // is saved on their own
    /// Sets the coefficient of a polynomial [`PolyOverZ`].
    /// We advise to use small coefficients, since already 2^32 coefficients take space
    /// of roughly 34 GB. If not careful, be prepared that memory problems can occur, if
    /// the coordinate is very high.
    ///
    /// All entries which are not directly addressed are automatically treated as zero.
    ///
    /// Parameters:
    /// - `coordinate`: the coordinate of the coefficient to set (has to be positive)
    /// - `value`: the new value the coordinate should have
    ///
    /// # Examples
    /// ```
    /// use math::integer::PolyOverZ;
    /// use math::traits::SetCoefficient;
    /// use std::str::FromStr;
    ///
    /// let mut poly = PolyOverZ::from_str("4  0 1 2 3").unwrap();
    /// let value = 1000;
    ///
    /// assert!(poly.set_coeff(4, value).is_ok());
    /// ```
    ///
    /// ```
    /// use math::integer::PolyOverZ;
    /// use math::integer::Z;
    /// use math::traits::SetCoefficient;
    /// use std::str::FromStr;
    ///
    /// let mut poly = PolyOverZ::from_str("4  0 1 2 3").unwrap();
    /// let value = Z::from(100);
    ///
    /// assert!(poly.set_coeff(4, value).is_ok());
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
    /// either the coordinate is negative or it does not fit into an [`i64`].
    fn set_coeff(
        &mut self,
        coordinate: impl TryInto<i64> + Display + Copy,
        value: Z,
    ) -> Result<(), MathError> {
        self.set_coeff(coordinate, &value)
    }
}

impl SetCoefficient<&Z> for PolyOverZ {
    /// Sets the coefficient of a polynomial [`PolyOverZ`].
    /// We advise to use small coefficients, since already 2^32 coefficients take space
    /// of roughly 34 GB. If not careful, be prepared that memory problems can occur, if
    /// the coordinate is very high.
    ///
    /// All entries which are not directly addressed are automatically treated as zero.
    ///
    /// Parameters:
    /// - `coordinate`: the coordinate of the coefficient to set (has to be positive)
    /// - `value`: the new value the coordinate should have from a borrowed [`Z`].
    ///
    /// # Example
    /// ```
    /// use math::integer::PolyOverZ;
    /// use math::integer::Z;
    /// use math::traits::SetCoefficient;
    /// use std::str::FromStr;
    ///
    /// let mut poly = PolyOverZ::from_str("4  0 1 2 3").unwrap();
    /// let value = Z::from(1000);
    ///
    /// assert!(poly.set_coeff(4, &value).is_ok());
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
    /// either the coordinate is negative or it does not fit into an [`i64`].
    fn set_coeff(
        &mut self,
        coordinate: impl TryInto<i64> + Display + Copy,
        value: &Z,
    ) -> Result<(), MathError> {
        let coordinate = evaluate_coordinate(coordinate)?;

        unsafe {
            fmpz_poly_set_coeff_fmpz(&mut self.poly, coordinate, &value.value);
        };
        Ok(())
    }
}

implement_for_others_set_coeff!(i64, Z, PolyOverZ);
implement_for_others_set_coeff!(i32, Z, PolyOverZ);
implement_for_others_set_coeff!(i16, Z, PolyOverZ);
implement_for_others_set_coeff!(i8, Z, PolyOverZ);
implement_for_others_set_coeff!(u64, Z, PolyOverZ);
implement_for_others_set_coeff!(u32, Z, PolyOverZ);
implement_for_others_set_coeff!(u16, Z, PolyOverZ);
implement_for_others_set_coeff!(u8, Z, PolyOverZ);

#[cfg(test)]
mod test_set_coeff {

    use crate::{
        integer::{PolyOverZ, Z},
        traits::SetCoefficient,
    };
    use std::str::FromStr;

    /// ensure that the negative coordinates return an error
    #[test]
    fn set_min_negative_coeff() {
        let mut poly = PolyOverZ::from_str("2  1 1").unwrap();

        assert!(poly.set_coeff(i64::MIN, 2).is_err());
        assert!(poly.set_coeff(i32::MIN, 2).is_err());
        assert!(poly.set_coeff(i16::MIN, 2).is_err());
        assert!(poly.set_coeff(i8::MIN, 2).is_err());
    }

    /// ensure that coefficients up to 2^15 -1 work
    #[test]
    fn set_max_coeff() {
        let mut poly = PolyOverZ::from_str("2  1 1").unwrap();

        assert!(poly.set_coeff(i8::MAX, 2).is_ok());
        assert!(poly.set_coeff(i16::MAX, 2).is_ok());
    }

    /// ensure that the max of [`u8`] and [`u16`] works as a coefficient
    #[test]
    fn set_unsigned_coeff() {
        let mut poly = PolyOverZ::from_str("2  1 1").unwrap();

        assert!(poly.set_coeff(u8::MAX, 2).is_ok());
        assert!(poly.set_coeff(u16::MAX, 2).is_ok());
    }

    /// ensure that a general case is working
    #[test]
    fn set_coeff_working() {
        let mut poly = PolyOverZ::from_str("4  0 1 2 3").unwrap();
        let value = 10000;

        poly.set_coeff(0, value).unwrap();
        poly.set_coeff(5, value).unwrap();
        assert_eq!(PolyOverZ::from_str("6  10000 1 2 3 0 10000").unwrap(), poly);
    }

    /// ensure that the correct coefficient is set and all others are set to zero
    #[test]
    fn set_coeff_rest_zero() {
        let mut poly = PolyOverZ::from_str("0").unwrap();

        poly.set_coeff(4, -10).unwrap();
        assert_eq!(PolyOverZ::from_str("5  0 0 0 0 -10").unwrap(), poly);
    }

    /// ensure that setting with a z works
    #[test]
    fn set_coeff_z() {
        let mut poly = PolyOverZ::from_str("0").unwrap();

        poly.set_coeff(4, Z::from(123)).unwrap();
        assert_eq!(PolyOverZ::from_str("5  0 0 0 0 123").unwrap(), poly);
    }
}
