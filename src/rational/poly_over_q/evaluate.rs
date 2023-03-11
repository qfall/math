//! Implementations to evaluate a [`PolyOverQ`].
//! For each reasonable type, an implementation
//! of the [`Evaluate`] trait should be implemented.

use super::PolyOverQ;
use crate::{integer::Z, rational::Q, traits::Evaluate};
use flint_sys::fmpq_poly::{fmpq_poly_evaluate_fmpq, fmpq_poly_evaluate_fmpz};

impl Evaluate<Q, Q> for PolyOverQ {
    /// Evaluates a [`PolyOverQ`] on a given input. If the provided input could not be converted into a valid [`Q`], [`Q::default`] is returned.
    ///
    /// Parameters:
    /// - `value`: the value with which to evaluate the polynomial. TODO: Currently supported
    /// are ([`i8`], [`i8`]) for all of [`i16`],[`i32`],[`i64`],[`u8`],[`u16`],[`u32`],[`u64`] and separately [`Q`]
    ///
    /// Returns the evaluation of the polynomial as a [`Q`].
    ///
    /// # Examples
    /// ```rust
    /// use math::traits::Evaluate;
    /// use math::rational::Q;
    /// use math::rational::PolyOverQ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverQ::from_str("5  0 1 2/3 -3/2 1").unwrap();
    /// let value = Q::from_str("3/2").unwrap();
    /// let res = poly.evaluate(value);
    /// ```
    fn evaluate(&self, value: impl TryInto<Q>) -> Q {
        let value = match value.try_into() {
            Ok(some) => some,
            Err(_) => return Q::default(),
        };
        self.evaluate_ref_q(&value)
    }
}

impl PolyOverQ {
    /// Evaluates a [`PolyOverQ`] on a given input of [`Q`]. Note that the
    /// [`Q`] in this case is only a reference.
    ///
    /// Parameters:
    /// - `value`: the value with which to evaluate the polynomial.
    ///
    /// Returns the evaluation of the polynomial as a [`Q`].
    ///
    /// # Example
    /// ```rust
    /// use math::traits::Evaluate;
    /// use math::rational::Q;
    /// use math::rational::PolyOverQ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverQ::from_str("5  0 1 2/3 -3/2 1").unwrap();
    /// let value = Q::from_str("3/2").unwrap();
    /// let res = poly.evaluate_ref_q(&value);
    /// ```
    pub fn evaluate_ref_q(&self, value: &Q) -> Q {
        let mut res = Q::default();

        unsafe { fmpq_poly_evaluate_fmpq(&mut res.value, &self.poly, &value.value) };

        res
    }

    /// Evaluates a [`PolyOverQ`] on a given input of [`Z`]. Note that the
    /// [`Z`] in this case is only a reference.
    ///
    /// Parameters:
    /// - `value`: the value with which to evaluate the polynomial.
    ///
    /// Returns the evaluation of the polynomial as a [`Q`].
    ///
    /// # Example
    /// ```rust
    /// use math::traits::Evaluate;
    /// use math::rational::Q;
    /// use math::rational::PolyOverQ;
    /// use std::str::FromStr;
    ///
    /// let poly = PolyOverQ::from_str("5  0 1 2/3 -3/2 1").unwrap();
    /// let value = Q::from_str("3/2").unwrap();
    /// let res = poly.evaluate_ref_q(&value);
    /// ```
    pub fn evaluate_ref_z(&self, value: &Z) -> Q {
        let mut res = Q::default();

        unsafe { fmpq_poly_evaluate_fmpz(&mut res.value, &self.poly, &value.value) };

        res
    }
}

// TODO: add traits for TryInto with other values, once the corresponding functions are
// implemented.
#[cfg(test)]
mod test_evaluate {

    use crate::rational::{PolyOverQ, Q};
    use crate::traits::Evaluate;
    use std::str::FromStr;

    /// tests if evaluate works for [`Q`] as input
    #[test]
    fn eval_q_working() {
        let poly = PolyOverQ::from_str("2  1 2/7").unwrap();

        let res = poly.evaluate(Q::from_str("7/3").unwrap());

        assert_eq!(Q::from_str("5/3").unwrap(), res)
    }

    /// tests if evaluate works with negative values
    #[test]
    fn eval_q_negative() {
        let poly = PolyOverQ::from_str("2  1 2/7").unwrap();

        let res = poly.evaluate(Q::from_str("-7/3").unwrap());

        assert_eq!(Q::from_str("1/3").unwrap(), res)
    }

    /// tests if evaluate works with large rationals
    #[test]
    fn eval_q_large() {
        let q_str = format!("{}/{}", u64::MAX, i64::MIN,);
        let q_str_rev = format!("{}/{}", i64::MIN, u64::MAX);
        let large_string = format!("2  0 {}", q_str);
        let poly = PolyOverQ::from_str(&large_string).unwrap();

        let res = poly.evaluate(Q::from_str(&q_str_rev).unwrap());

        assert_eq!(Q::from_str("1").unwrap(), res)
    }
}

#[cfg(test)]
mod test_evaluate_ref_z {
    use crate::integer::Z;
    use crate::rational::{PolyOverQ, Q};
    use std::str::FromStr;

    /// tests if evaluate works for [`Z`] as input
    #[test]
    fn eval_z_working() {
        let poly = PolyOverQ::from_str("2  1 2/7").unwrap();

        let res = poly.evaluate_ref_z(&Z::from(3));

        assert_eq!(Q::from_str("13/7").unwrap(), res)
    }

    /// tests if evaluate works with negative values
    #[test]
    fn eval_z_negative() {
        let poly = PolyOverQ::from_str("2  1 2/7").unwrap();

        let res = poly.evaluate_ref_z(&Z::from(-5));

        assert_eq!(Q::from_str("-3/7").unwrap(), res)
    }

    /// test if evaluate works with large nominators and denominators
    #[test]
    fn eval_large_nom_denom_large_ref_z() {
        let q_str = format!("{}/{}", u64::MAX, i64::MIN,);
        let large_string = format!("2  -{} {}", u64::MAX, q_str);
        let poly = PolyOverQ::from_str(&large_string).unwrap();

        let res = poly.evaluate_ref_z(&Z::from(i64::MIN));

        assert_eq!(Q::default(), res)
    }
}

#[cfg(test)]
mod test_evaluate_ref_q {
    use crate::rational::{PolyOverQ, Q};
    use std::str::FromStr;

    /// tests if evaluate works for [`Q`] as input
    #[test]
    fn eval_q_working() {
        let poly = PolyOverQ::from_str("2  1 2/7").unwrap();

        let res = poly.evaluate_ref_q(&Q::from_str("7/3").unwrap());

        assert_eq!(Q::from_str("5/3").unwrap(), res)
    }

    /// tests if evaluate works with negative values
    #[test]
    fn eval_q_negative() {
        let poly = PolyOverQ::from_str("2  1 2/7").unwrap();

        let res = poly.evaluate_ref_q(&Q::from_str("-7/3").unwrap());

        assert_eq!(Q::from_str("1/3").unwrap(), res)
    }

    /// tests if evaluate works with large rationals
    #[test]
    fn eval_q_large() {
        let q_str = format!("{}/{}", u64::MAX, i64::MIN,);
        let q_str_rev = format!("{}/{}", i64::MIN, u64::MAX);
        let large_string = format!("2  0 {}", q_str);
        let poly = PolyOverQ::from_str(&large_string).unwrap();

        let res = poly.evaluate_ref_q(&Q::from_str(&q_str_rev).unwrap());

        assert_eq!(Q::from_str("1").unwrap(), res)
    }
}
