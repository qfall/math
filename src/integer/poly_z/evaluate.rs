use flint_sys::fmpz_poly::fmpz_poly_evaluate_fmpz;

use crate::{integer::Z, macros};

use super::PolyZ;

impl PolyZ {
    pub fn evaluate_z(&self, value: &Z) -> Z {
        let mut res = Z::from(0);

        unsafe { fmpz_poly_evaluate_fmpz(&mut res.value, &self.poly, &value.value) };

        res
    }

    macros::evaluate_poly!(i64, Z, Z, evaluate_z);
    macros::evaluate_poly!(i32, Z, Z, evaluate_z);
    macros::evaluate_poly!(i16, Z, Z, evaluate_z);
    macros::evaluate_poly!(i8, Z, Z, evaluate_z);

    macros::evaluate_poly!(u64, Z, Z, evaluate_z);
    macros::evaluate_poly!(u32, Z, Z, evaluate_z);
    macros::evaluate_poly!(u16, Z, Z, evaluate_z);
    macros::evaluate_poly!(u8, Z, Z, evaluate_z);
}

#[cfg(test)]
mod test_evaluate {
    use std::str::FromStr;

    use crate::integer::{PolyZ, Z};

    #[test]
    fn eval_z_positive() {
        let poly = PolyZ::from_str("2  1 2").unwrap();

        let res = poly.evaluate_z(&Z::from(3));

        assert_eq!(Z::from(7), res)
    }

    #[test]
    fn eval_z_negative() {
        let poly = PolyZ::from_str("2  1 2").unwrap();

        let res = poly.evaluate_z(&Z::from(-5));

        assert_eq!(Z::from(-9), res)
    }

    #[test]
    fn eval_z_large() {
        let poly = PolyZ::from_str("2  1 2").unwrap();

        let res = poly.evaluate_z(&Z::from_str(&"1".repeat(65)).unwrap());

        let mut res_cmp_str = "2".repeat(64);
        res_cmp_str.push('3');
        assert_eq!(Z::from_str(&res_cmp_str).unwrap(), res)
    }

    #[test]
    fn eval_max() {
        let poly = PolyZ::from_str("2  1 2").unwrap();

        // signed
        let _ = poly.evaluate_i64(i64::MAX);
        let _ = poly.evaluate_i32(i32::MAX);
        let _ = poly.evaluate_i16(i16::MAX);
        let _ = poly.evaluate_i8(i8::MAX);

        //unsigned
        let _ = poly.evaluate_u64(u64::MAX);
        let _ = poly.evaluate_u32(u32::MAX);
        let _ = poly.evaluate_u16(u16::MAX);
        let _ = poly.evaluate_u8(u8::MAX);
    }

    #[test]
    fn eval_min() {
        let poly = PolyZ::from_str("2  1 2").unwrap();

        // signed
        let _ = poly.evaluate_i64(i64::MIN);
        let _ = poly.evaluate_i32(i32::MIN);
        let _ = poly.evaluate_i16(i16::MIN);
        let _ = poly.evaluate_i8(i8::MIN);

        // unsigned
        let _ = poly.evaluate_u64(u64::MIN);
        let _ = poly.evaluate_u32(u32::MIN);
        let _ = poly.evaluate_u16(u16::MIN);
        let _ = poly.evaluate_u8(u8::MIN);
    }
}
