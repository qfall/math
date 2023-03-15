//! Implementations to get coefficients of a [`PolyOverQ`].
//! Each reasonable type should be allowed as a coordinate.

use super::PolyOverQ;
use crate::{
    error::MathError, rational::Q, traits::GetCoefficient, utils::coordinate::evaluate_coordinate,
};
use flint_sys::fmpq_poly::fmpq_poly_get_coeff_fmpq;
use std::fmt::Display;

impl GetCoefficient<Q> for PolyOverQ {
    /// Returns the coefficient of a polynomial [`PolyOverQ`] as a [`Q`].
    ///
    /// If a coordinate is provided which exceeds the highest set coefficient, zero is returned.
    ///
    /// Parameters:
    /// - `coordinate`: the coordinate of the coefficient to get (has to be positive)
    ///
    /// Returns the coefficient as a [`Q`] or a [`MathError`] if the provided coordinate
    /// is negative and therefore invalid or it does not fit into an [`i64`].
    ///
    /// # Example
    /// ```rust
    /// use math::rational::PolyOverQ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverQ::from_str("4  0 1 2/3 3/2").unwrap();
    ///
    /// let coeff_0 = poly.get_coeff(0).unwrap();
    /// let coeff_1 = poly.get_coeff(1).unwrap();
    /// let coeff_4 = poly.get_coeff(4).unwrap(); // This would only return 0
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
    /// either the coordinate is negative or it does not fit into an [`i64`].
    fn get_coeff(&self, coordinate: impl TryInto<i64> + Display + Copy) -> Result<Q, MathError> {
        let mut out = Q::default();
        let coordinate = evaluate_coordinate(coordinate)?;
        unsafe { fmpq_poly_get_coeff_fmpq(&mut out.value, &self.poly, coordinate) }
        Ok(out)
    }
}

#[cfg(test)]
mod test_get_coeff {
    use crate::{
        rational::{PolyOverQ, Q},
        traits::GetCoefficient,
    };
    use std::str::FromStr;

    /// ensure that 0 is returned if the provided index is not yet set
    #[test]
    fn index_out_of_range() {
        let poly = PolyOverQ::from_str("4  0 1 2/3 3/2").unwrap();

        let zero_coeff = poly.get_coeff(4).unwrap();

        assert_eq!(Q::from_str("0/1").unwrap(), zero_coeff)
    }

    /// test if coordinates smaller than zero return an error
    #[test]
    fn index_too_small() {
        let poly = PolyOverQ::default();

        assert!(poly.get_coeff(-1).is_err());
    }

    /// tests if negative coefficients are returned correctly
    #[test]
    fn negative_coeff() {
        let poly = PolyOverQ::from_str("4  0 1 2/3 -3/2").unwrap();

        let coeff = poly.get_coeff(3).unwrap();

        assert_eq!(Q::from_str("-3/2").unwrap(), coeff)
    }

    /// tests if positive coefficients are returned correctly
    #[test]
    fn positive_coeff() {
        let poly = PolyOverQ::from_str("4  0 1 2/3 -3/2").unwrap();

        let coeff = poly.get_coeff(2).unwrap();

        assert_eq!(Q::from_str("2/3").unwrap(), coeff)
    }

    /// tests if large coefficients are returned correctly
    #[test]
    fn large_coeff() {
        let q_str = format!("-{}/{}", u64::MAX, i64::MIN,);
        let large_string = format!("2  {} {}", q_str, u64::MAX);
        let poly = PolyOverQ::from_str(&large_string).unwrap();

        assert_eq!(Q::from_str(&q_str).unwrap(), poly.get_coeff(0).unwrap());
        assert_eq!(
            Q::from_str(&u64::MAX.to_string()).unwrap(),
            poly.get_coeff(1).unwrap()
        );
    }

    /// tests if large negative coefficients are returned correctly
    #[test]
    fn large_coeff_neg() {
        let q_str = format!("{}/{}", u64::MAX, i64::MIN,);
        let large_string = format!("2  {} {}", q_str, u64::MAX);
        let poly = PolyOverQ::from_str(&large_string).unwrap();

        assert_eq!(Q::from_str(&q_str).unwrap(), poly.get_coeff(0).unwrap());
        assert_eq!(
            Q::from_str(&u64::MAX.to_string()).unwrap(),
            poly.get_coeff(1).unwrap()
        );
    }
}
