//! Implementation of the [`Sub`] trait for [`Z`] values.

use flint_sys::fmpz::fmpz;
use std::ops::Sub;

use super::super::Z;
use crate::macros::arithmetic_trait;

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
mod tests {
    use super::Z;

    // testing subtraction for two Z
    #[test]
    fn add() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = a - b;
        assert!(c == Z::from(18));
    }

    // testing subtraction for two borrowed Z
    #[test]
    fn add_borrow() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = &a - &b;
        assert!(c == Z::from(18));
    }

    // testing subtraction for borrowed Z and Z
    #[test]
    fn add_first_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = &a - b;
        assert!(c == Z::from(18));
    }

    // testing subtraction for Z and borrowed Z
    #[test]
    fn add_second_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = a - &b;
        assert!(c == Z::from(18));
    }
}
