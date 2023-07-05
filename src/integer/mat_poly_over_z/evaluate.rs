//! Implementations to evaluate a [`MatPolyOverZ`].
//! For each reasonable type, an implementation
//! of the [`Evaluate`] trait should be implemented.

use super::MatPolyOverZ;
use crate::{
    integer::{MatZ, Z},
    traits::{Evaluate, GetNumColumns, GetNumRows},
};
use flint_sys::fmpz_poly_mat::fmpz_poly_mat_evaluate_fmpz;

impl<Integer: Into<Z>> Evaluate<Integer, MatZ> for MatPolyOverZ {
    /// Evaluates a [`MatPolyOverZ`] on a given input of [`Z`] entrywise. Note that the
    /// [`Z`] in this case is only a reference.
    ///
    /// Parameters:
    /// - `value`: the value with which to evaluate the matrix of polynomials.
    ///
    /// Returns the evaluation of the polynomial as a [`MatZ`].
    ///
    /// # Examples
    /// ```rust
    /// use qfall_math::traits::*;
    /// use qfall_math::integer::Z;
    /// use qfall_math::integer::MatPolyOverZ;
    /// use std::str::FromStr;
    ///
    /// let poly = MatPolyOverZ::from_str("[[0, 1  17, 2  24 42],[2  24 42, 2  24 42, 2  24 42]]").unwrap();
    /// let value = Z::from(3);
    /// let res = poly.evaluate(&value);
    /// ```
    fn evaluate(&self, value: Integer) -> MatZ {
        let value = value.into();
        // we can unwrap since we know, that the dimensions of our current matrix are positive
        let mut res = MatZ::new(self.get_num_rows(), self.get_num_columns());

        unsafe { fmpz_poly_mat_evaluate_fmpz(&mut res.matrix, &self.matrix, &value.value) };

        res
    }
}

#[cfg(test)]
mod test_evaluate {
    use crate::integer::{MatPolyOverZ, MatZ, Z};
    use crate::traits::Evaluate;
    use std::str::FromStr;

    /// Tests if evaluate works for [`Z`] as input
    #[test]
    fn eval_z() {
        let poly_str = "[[1  17],[2  24 42]]";
        let poly = MatPolyOverZ::from_str(poly_str).unwrap();

        let res = poly.evaluate(Z::from(3));

        assert_eq!(MatZ::from_str("[[17],[150]]").unwrap(), res)
    }

    /// Tests if evaluate_z_ref with a reference works
    #[test]
    fn eval_z_ref() {
        let poly_str = "[[1  17],[2  24 42]]";
        let poly = MatPolyOverZ::from_str(poly_str).unwrap();

        let res = poly.evaluate(&Z::from(3));

        assert_eq!(MatZ::from_str("[[17],[150]]").unwrap(), res)
    }

    /// Tests if evaluate works with negative values
    #[test]
    fn eval_z_negative() {
        let poly_str = "[[1  17],[2  24 42]]";
        let poly = MatPolyOverZ::from_str(poly_str).unwrap();

        let res = poly.evaluate(&Z::from(-5));

        assert_eq!(MatZ::from_str("[[17],[-186]]").unwrap(), res)
    }

    /// Tests if evaluate works with large integers
    #[test]
    fn eval_z_large() {
        let poly_str = "[[1  17],[2  6 2]]";
        let poly = MatPolyOverZ::from_str(poly_str).unwrap();

        let res = poly.evaluate(&Z::from_str(&"1".repeat(65)).unwrap());

        let res_cmp_str = format!("[[17],[{}8]]", "2".repeat(64));
        assert_eq!(MatZ::from_str(&res_cmp_str).unwrap(), res)
    }

    /// Tests whether evaluation of a large entry in the matrix with a large value works
    #[test]
    fn eval_large_with_large() {
        let poly_str = format!("[[2  {} -1, 1  1],[1  {}, 2  0 1]]", u64::MAX, u64::MAX);
        let poly = MatPolyOverZ::from_str(&poly_str).unwrap();
        let res = poly.evaluate(Z::from(u64::MAX));

        let res_cmp_str = format!("[[0, 1],[{}, {}]]", u64::MAX, u64::MAX);
        assert_eq!(MatZ::from_str(&res_cmp_str).unwrap(), res)
    }

    /// Test if evaluate works with max of i64, i32, ...
    #[test]
    fn eval_max() {
        let poly_str = "[[1  17],[2  24 42]]";
        let poly = MatPolyOverZ::from_str(poly_str).unwrap();

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

    /// Test if evaluate works with min of i64, i32, ...
    #[test]
    fn eval_min() {
        let poly_str = "[[1  17],[2  24 42]]";
        let poly = MatPolyOverZ::from_str(poly_str).unwrap();

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
