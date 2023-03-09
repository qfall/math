//! Implementations to evaluate a [`PolyOverZ`].
//! For each reasonable type, an implementation
//! of the [`Evaluate`] trait should be implemented.

use super::PolyOverZ;
use crate::{integer::Z, traits::Evaluate};
use flint_sys::fmpz_poly::fmpz_poly_evaluate_fmpz;

impl Evaluate<Z, Z> for PolyOverZ {
    /// Evaluates a [`PolyOverZ`] on a given input.
    ///
    /// Parameters:
    /// - `value`: the value with which to evaluate the polynomial. Currently supported
    /// are [`i8`],[`i16`],[`i32`],[`i64`],[`u8`],[`u16`],[`u32`],[`u64`] and [`Z`]
    ///
    /// Returns the evaluation of the polynomial as a [`Z`].
    ///
    /// # Examples
    /// ```rust
    /// use math::traits::Evaluate;
    /// use math::integer::Z;
    /// use math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZ::from_str("5  0 1 2 -3 1").unwrap();
    /// let value = Z::from(3);
    /// let res = poly.evaluate(value);
    /// ```
    ///
    /// ```rust
    /// use math::traits::Evaluate;
    /// use math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZ::from_str("5  0 1 2 -3 1").unwrap();
    /// let value = 3;
    /// let res = poly.evaluate(value);
    /// ```
    ///
    /// ```rust
    /// use math::traits::Evaluate;
    /// use math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZ::from_str("5  0 1 2 -3 1").unwrap();
    /// let value = i64::MAX;
    /// let res = poly.evaluate(value);
    /// ```
    fn evaluate<T: Into<Z>>(&self, value: T) -> Z {
        self.evaluate_z_ref(&value.into())
    }
}

impl PolyOverZ {
    /// Evaluates a [`PolyOverZ`] on a given input of [`Z`]. Note that the
    /// [`Z`] in this case is only a reference.
    ///
    /// Parameters:
    /// - `value`: the value with which to evaluate the polynomial.
    ///
    /// Returns the evaluation of the polynomial as a [`Z`].
    ///
    /// # Example
    /// ```rust
    /// use math::traits::Evaluate;
    /// use math::integer::Z;
    /// use math::integer::PolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverZ::from_str("5  0 1 2 -3 1").unwrap();
    /// let value = Z::from(3);
    /// let res = poly.evaluate_z_ref(&value);
    /// ```
    pub fn evaluate_z_ref(&self, value: &Z) -> Z {
        let mut res = Z::from(0);

        unsafe { fmpz_poly_evaluate_fmpz(&mut res.value, &self.poly, &value.value) };

        res
    }
}

#[cfg(test)]
mod test_evaluate {

    use crate::integer::{PolyOverZ, Z};
    use crate::traits::Evaluate;
    use std::str::FromStr;

    /// tests if evaluate works for [`Z`] as input
    #[test]
    fn eval_z() {
        let poly = PolyOverZ::from_str("2  1 2").unwrap();

        let res = poly.evaluate(Z::from(3));

        assert_eq!(Z::from(7), res)
    }

    /// tests if evaluate_z_ref with a reference works
    #[test]
    fn eval_z_ref() {
        let poly = PolyOverZ::from_str("2  1 2").unwrap();

        let res = poly.evaluate_z_ref(&Z::from(3));

        assert_eq!(Z::from(7), res)
    }

    /// tests if evaluate works with negative values
    #[test]
    fn eval_z_negative() {
        let poly = PolyOverZ::from_str("2  1 2").unwrap();

        let res = poly.evaluate_z_ref(&Z::from(-5));

        assert_eq!(Z::from(-9), res)
    }

    /// tests if evaluate works with large integers
    #[test]
    fn eval_z_large() {
        let poly = PolyOverZ::from_str("2  1 2").unwrap();

        let res = poly.evaluate_z_ref(&Z::from_str(&"1".repeat(65)).unwrap());

        let mut res_cmp_str = "2".repeat(64);
        res_cmp_str.push('3');
        assert_eq!(Z::from_str(&res_cmp_str).unwrap(), res)
    }

    /// test if evaluate works with max of i64, i32, ...
    #[test]
    fn eval_max() {
        let poly = PolyOverZ::from_str("2  1 2").unwrap();

        // signed
        let _ = poly.evaluate(i64::MAX);
        let _ = poly.evaluate(i32::MAX);
        let _ = poly.evaluate(i16::MAX);
        let _ = poly.evaluate(i8::MAX);

        //unsigned
        let _ = poly.evaluate(u64::MAX);
        let _ = poly.evaluate(u32::MAX);
        let _ = poly.evaluate(u16::MAX);
        let _ = poly.evaluate(u8::MAX);
    }

    /// test if evaluate works with min of i64, i32, ...
    #[test]
    fn eval_min() {
        let poly = PolyOverZ::from_str("2  1 2").unwrap();

        // signed
        let _ = poly.evaluate(i64::MIN);
        let _ = poly.evaluate(i32::MIN);
        let _ = poly.evaluate(i16::MIN);
        let _ = poly.evaluate(i8::MIN);

        // unsigned
        let _ = poly.evaluate(u64::MIN);
        let _ = poly.evaluate(u32::MIN);
        let _ = poly.evaluate(u16::MIN);
        let _ = poly.evaluate(u8::MIN);
    }
}
