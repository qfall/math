//! Implementation of the [`Sub`] trait for [`Z`] values.

use super::super::Z;
use crate::macros::arithmetic_trait;
use flint_sys::fmpz::fmpz;
use std::ops::Sub;

arithmetic_trait!(
    doc = "Implements the [`Sub`] trait for two [`Z`] values. \n
[`Sub`] is implemented for any combination of [`Z`] and borrowed [`Z`].\n\n

 Parameters:\n
 - `other`: specifies the value to subtract from `self`\n\n

Returns the result of the subtraction as a [`Z`].\n\n

 # Example\n
 ```rust
 use math::integer::Z;

 let a: Z = Z::from(42);
 let b: Z = Z::from(24);

 let c: Z = &a - &b;
 let d: Z = a - b;
 let e: Z = &c - d;
 let f: Z = c - &e;
 ```",
    Sub,
    sub,
    Z,
    flint_sys::fmpz::fmpz_sub,
    fmpz(0)
);

#[cfg(test)]
mod test_sub {
    use super::Z;

    // testing subtraction for two Z
    #[test]
    fn sub() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = a - b;
        assert!(c == Z::from(18));
    }

    // testing subtraction for two borrowed Z
    #[test]
    fn sub_borrow() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = &a - &b;
        assert!(c == Z::from(18));
    }

    // testing subtraction for borrowed Z and Z
    #[test]
    fn sub_first_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = &a - b;
        assert!(c == Z::from(18));
    }

    // testing subtraction for Z and borrowed Z
    #[test]
    fn sub_second_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = a - &b;
        assert!(c == Z::from(18));
    }

    // testing subtraction for large integers
    #[test]
    fn sub_large() {
        let a: Z = Z::from(u64::MAX - 1);
        let b: Z = Z::from(i64::MAX);
        let c: Z = Z::from(738201034);
        let d: Z = &a - &b;
        let e: Z = &b - a;
        let f: Z = b - c;
        assert!(d == Z::from(i64::MAX));
        assert!(e == Z::from(i64::MIN + 1));
        assert!(f == Z::from(i64::MAX - 738201034));
    }
}
