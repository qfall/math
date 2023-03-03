use super::PolyZ;
use crate::{integer::Z, traits::Evaluate};
use flint_sys::fmpz_poly::fmpz_poly_evaluate_fmpz;

impl Evaluate<Z, Z> for PolyZ {
    fn evaluate<T: Into<Z>>(&self, value: T) -> Z {
        self.evaluate_z_ref(&value.into())
    }
}

impl PolyZ {
    pub fn evaluate_z_ref(&self, value: &Z) -> Z {
        let mut res = Z::from(0);

        unsafe { fmpz_poly_evaluate_fmpz(&mut res.value, &self.poly, &value.value) };

        res
    }
}

#[cfg(test)]
mod test_evaluate {
    use std::str::FromStr;

    use crate::integer::{PolyZ, Z};
    use crate::traits::Evaluate;

    #[test]
    fn eval_z_positive() {
        let poly = PolyZ::from_str("2  1 2").unwrap();

        let res = poly.evaluate_z_ref(&Z::from(3));

        assert_eq!(Z::from(7), res)
    }

    #[test]
    fn eval_z_negative() {
        let poly = PolyZ::from_str("2  1 2").unwrap();

        let res = poly.evaluate_z_ref(&Z::from(-5));

        assert_eq!(Z::from(-9), res)
    }

    #[test]
    fn eval_z_large() {
        let poly = PolyZ::from_str("2  1 2").unwrap();

        let res = poly.evaluate_z_ref(&Z::from_str(&"1".repeat(65)).unwrap());

        let mut res_cmp_str = "2".repeat(64);
        res_cmp_str.push('3');
        assert_eq!(Z::from_str(&res_cmp_str).unwrap(), res)
    }

    #[test]
    fn eval_max() {
        let poly = PolyZ::from_str("2  1 2").unwrap();

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

    #[test]
    fn eval_min() {
        let poly = PolyZ::from_str("2  1 2").unwrap();

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

    #[test]
    fn eval_z_trait() {
        let poly = PolyZ::from_str("2  1 2").unwrap();

        let res = poly.evaluate(Z::from(3));

        assert_eq!(Z::from(7), res)
    }
}
