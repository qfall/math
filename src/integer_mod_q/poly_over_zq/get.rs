//! Implementations to get coefficients of a [`PolyOverZq`].
//! Each reasonable type should be allowed as a coordinate.

use super::PolyOverZq;
use crate::{
    error::MathError, integer::Z, integer_mod_q::Zq, traits::GetCoefficient,
    utils::coordinate::evaluate_coordinate,
};
use flint_sys::fmpz_mod_poly::fmpz_mod_poly_get_coeff_fmpz;
use std::fmt::Display;

impl GetCoefficient<Zq> for PolyOverZq {
    /// Returns the coefficient of a polynomial [`PolyOverZq`] as a [`Zq`].
    ///
    /// If a coordinate is provided which exceeds the highest set coefficient, zero is returned.
    ///
    /// Parameters:
    /// - `coordinate`: the coordinate of the coefficient to get (has to be positive)
    ///
    /// Returns the coefficient as a [`Zq`] or a [`MathError`] if the provided coordinate
    /// is negative and therefore invalid or it does not fit into an [`i64`].
    ///
    /// # Example
    /// ```
    /// use math::traits::GetCoefficient;
    /// use math::integer_mod_q::PolyOverZq;
    /// use math::integer_mod_q::Zq;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZq::from_str("4  0 1 2 3 mod 17").unwrap();
    ///
    /// let coeff_0: Zq = poly.get_coeff(0).unwrap();
    /// let coeff_1: Zq = poly.get_coeff(1).unwrap();
    /// let coeff_4: Zq = poly.get_coeff(4).unwrap(); // This would only return 0
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
    /// either the coordinate is negative or it does not fit into an [`i64`].
    fn get_coeff(&self, coordinate: impl TryInto<i64> + Display + Copy) -> Result<Zq, MathError> {
        let out_z = self.get_coeff(coordinate)?;
        Ok(Zq::from_z_modulus(&out_z, &self.modulus))
    }
}

impl GetCoefficient<Z> for PolyOverZq {
    /// Returns the coefficient of a polynomial [`PolyOverZq`] as a [`Z`].
    ///
    /// If a coordinate is provided which exceeds the highest set coefficient, zero is returned.
    ///
    /// Parameters:
    /// - `coordinate`: the coordinate of the coefficient to get (has to be positive)
    ///
    /// Returns the coefficient as a [`Z`] or a [`MathError`] if the provided coordinate
    /// is negative and therefore invalid or it does not fit into an [`i64`].
    ///
    /// # Example
    /// ```
    /// use math::traits::GetCoefficient;
    /// use math::integer_mod_q::PolyOverZq;
    /// use math::integer::Z;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZq::from_str("4  0 1 2 3 mod 17").unwrap();
    ///
    /// let coeff_0: Z = poly.get_coeff(0).unwrap();
    /// let coeff_1: Z = poly.get_coeff(1).unwrap();
    /// let coeff_4: Z = poly.get_coeff(4).unwrap(); // This would only return 0
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
    /// either the coordinate is negative or it does not fit into an [`i64`].
    fn get_coeff(&self, coordinate: impl TryInto<i64> + Display + Copy) -> Result<Z, MathError> {
        let coordinate = evaluate_coordinate(coordinate)?;
        let mut out = Z::default();
        unsafe {
            fmpz_mod_poly_get_coeff_fmpz(
                &mut out.value,
                &self.poly,
                coordinate,
                self.modulus.get_fmpz_mod_ctx_struct(),
            )
        }
        Ok(out)
    }
}

// we omit the tests for the value of the [`Zq`], and focus on the [`Modulus`] being set correctly
// since get_coefficient for [`Z`] is called, where we will check the value itself
#[cfg(test)]
mod test_get_coeff_zq_modulus {

    use crate::{
        integer_mod_q::{Modulus, PolyOverZq, Zq},
        traits::GetCoefficient,
    };
    use std::str::FromStr;

    /// ensure that the [`Modulus`] is transferred correctly when accessing an index out of bounds
    #[test]
    fn index_out_of_range_modulus() {
        let modulus_str = format!("17{}", u64::MAX);
        let modulus = Modulus::from_str(&modulus_str).unwrap();

        let poly = PolyOverZq::from_str(&format!("4  0 1 2 3 mod {}", modulus_str)).unwrap();

        let zero_coeff: Zq = poly.get_coeff(4).unwrap();

        assert_eq!(modulus, zero_coeff.modulus)
    }

    /// ensure that the [`Modulus`] is transferred correctly when accessing an index in bounds
    #[test]
    fn index_in_range_modulus() {
        let modulus_str = format!("17{}", u64::MAX);
        let modulus = Modulus::from_str(&modulus_str).unwrap();

        let poly = PolyOverZq::from_str(&format!("4  0 1 2 3 mod {}", modulus_str)).unwrap();

        let third_coeff: Zq = poly.get_coeff(3).unwrap();

        assert_eq!(modulus, third_coeff.modulus)
    }
}

#[cfg(test)]
mod test_get_coeff_z {
    use crate::{integer::Z, integer_mod_q::PolyOverZq, traits::GetCoefficient};
    use std::str::FromStr;

    /// ensure that 0 is returned if the provided index is not yet set
    #[test]
    fn index_out_of_range() {
        let modulus_str = format!("17{}", u64::MAX);

        let poly = PolyOverZq::from_str(&format!("4  0 1 2 3 mod {}", modulus_str)).unwrap();

        let zero_coeff = poly.get_coeff(4).unwrap();

        assert_eq!(Z::from(0), zero_coeff)
    }

    /// tests if positive coefficients are returned correctly
    #[test]
    fn positive_coeff() {
        let modulus_str = format!("17{}", u64::MAX);

        let poly = PolyOverZq::from_str(&format!("4  0 1 2 3 mod {}", modulus_str)).unwrap();

        let coeff = poly.get_coeff(2).unwrap();

        assert_eq!(Z::from(2), coeff)
    }

    /// tests if large coefficients are returned correctly
    #[test]
    fn large_coeff() {
        let modulus_str = format!("17{}", u64::MAX);
        let large_string = format!("2  {} {} mod {}", u64::MAX, i64::MAX, modulus_str);
        let poly = PolyOverZq::from_str(&large_string).unwrap();

        assert_eq!(Z::from(u64::MAX), poly.get_coeff(0).unwrap());
        assert_eq!(Z::from(i64::MAX), poly.get_coeff(1).unwrap());
    }

    /// tests if large negative coefficients are returned correctly
    #[test]
    fn large_modulus_applied_negative_large_coefficient() {
        let modulus_str = format!("{}", u64::MAX);
        let large_string = format!("2  -{} {} mod {}", u64::MAX, i64::MAX, modulus_str);
        let poly = PolyOverZq::from_str(&large_string).unwrap();

        assert_eq!(Z::from(0), poly.get_coeff(0).unwrap());
        assert_eq!(Z::from(i64::MAX), poly.get_coeff(1).unwrap());
    }
}
