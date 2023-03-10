//! Implementations to get coefficients of a [`PolyOverZ`].
//! Each reasonable type should be allowed as a coordinate.

use super::PolyOverZ;
use crate::{error::MathError, integer::Z, utils::coordinate::evaluate_coordinate};
use flint_sys::fmpz_poly::{fmpz_poly_get_coeff_fmpz, fmpz_poly_length};
use std::fmt::Display;

impl PolyOverZ {
    /// Returns the coefficient of a polynomial [`PolyOverZ`] as a [`Z`].
    ///
    /// If a coordinate is provided which exceeds the highest set coefficient, zero is returned.
    ///
    /// Parameters:
    /// - `coordinate`: the coordinate of the coefficient to get (has to be positive)
    ///
    /// Returns the coefficient as a [`Z`] or a [`MathError`] if the provided coordinate is negative and therefore invalid.
    ///
    /// # Example
    /// ```rust
    /// use math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZ::from_str("4  0 1 2 3").unwrap();
    ///
    /// let coeff_0 = poly.get_coeff(0).unwrap();
    /// let coeff_1 = poly.get_coeff(1).unwrap();
    /// let coeff_4 = poly.get_coeff(4).unwrap(); // This would only return 0
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
    /// either the coordinate is negative or it does not fit into an [`i64`].
    pub fn get_coeff<S: TryInto<i64> + Display + Copy>(
        &self,
        coordinate: S,
    ) -> Result<Z, MathError> {
        let mut out = Z::default();
        let coordinate = evaluate_coordinate(coordinate)?;
        unsafe { fmpz_poly_get_coeff_fmpz(&mut out.value, &self.poly, coordinate) }
        Ok(out)
    }

    /// Returns the length of the polynomial, which is one higher than the degree of the
    /// polynomial
    ///
    /// # Example
    /// ```rust
    /// use math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZ::from_str("4  0 1 2 3").unwrap();
    ///
    /// let length = poly.get_length();
    /// # assert_eq!(4, length);
    /// ```
    pub fn get_length(&self) -> i64 {
        unsafe { fmpz_poly_length(&self.poly) }
    }
}

#[cfg(test)]
mod test_get_coeff {

    use crate::integer::{PolyOverZ, Z};
    use std::str::FromStr;

    /// ensure that 0 is returned if the provided index is not yet set
    #[test]
    fn index_out_of_range() {
        let poly = PolyOverZ::from_str("4  0 1 2 3").unwrap();

        let zero_coeff = poly.get_coeff(4).unwrap();

        assert_eq!(Z::from(0), zero_coeff)
    }

    /// tests if negative coefficients are returned correctly
    #[test]
    fn negative_coeff() {
        let poly = PolyOverZ::from_str("4  0 1 2 -3").unwrap();

        let coeff = poly.get_coeff(3).unwrap();

        assert_eq!(Z::from(-3), coeff)
    }

    /// tests if positive coefficients are returned correctly
    #[test]
    fn positive_coeff() {
        let poly = PolyOverZ::from_str("4  0 1 2 -3").unwrap();

        let coeff = poly.get_coeff(2).unwrap();

        assert_eq!(Z::from(2), coeff)
    }

    /// tests if large coefficients are returned correctly
    #[test]
    fn large_coeff() {
        let large_string = format!("2  {} {}", u64::MAX, i64::MIN);
        let poly = PolyOverZ::from_str(&large_string).unwrap();

        assert_eq!(Z::from(u64::MAX), poly.get_coeff(0).unwrap());
        assert_eq!(Z::from(i64::MIN), poly.get_coeff(1).unwrap());
    }
}

#[cfg(test)]
mod test_get_length {
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// ensure that the length of the polynomial is returned
    #[test]
    fn correct_length() {
        let large_string = format!("2  {} {}", u64::MAX, i64::MIN);
        let poly = PolyOverZ::from_str(&large_string).unwrap();

        assert_eq!(2, poly.get_length());
    }
}
