//! Implementation of the [`Sub`] trait for [`Q`] values.

use flint_sys::{fmpq::fmpq, fmpz::fmpz};
use std::ops::Sub;

use super::super::Q;
use crate::macros::arithmetic_trait;

arithmetic_trait!(
    doc = "Implements the [`Sub`] trait for two [`Q`] values. \n
[`Sub`] is implemented for any combination of [`Q`] and borrowed [`Q`].\n\n

 Parameters:\n
 - `other`: specifies the value to subtract from `self`\n\n

Returns the result of the subtraction as a [`Q`].\n\n

 # Example\n
 ```rust
 use math::rational::Q;
 use std::str::FromStr;

 let a: Q = Q::from_str(\"42\").unwrap();
 let b: Q = Q::from_str(\"-42/2\").unwrap();

 let c: Q = &a - &b;
 let d: Q = a - b;
 let e: Q = &c - d;
 let f: Q = c - &e;
 ```",
    Sub,
    sub,
    Q,
    flint_sys::fmpq::fmpq_sub,
    fmpq {
        num: fmpz(0),
        den: fmpz(1)
    }
);

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use super::Q;

    // testing subtraction for two Q
    #[test]
    fn sub() {
        let a: Q = Q::from_str("42").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = a - b;
        //assert!(c == Q::from_str("21").unwrap());    todo
    }

    // testing subtraction for two borrowed Q
    #[test]
    fn sub_borrow() {
        let a: Q = Q::from_str("42").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = &a - &b;
        //assert!(c == Q::from_str("21").unwrap());    todo
    }

    // testing subtraction for borrowed Q and Q
    #[test]
    fn sub_first_borrowed() {
        let a: Q = Q::from_str("42/5").unwrap();
        let b: Q = Q::from_str("42/10").unwrap();
        let c: Q = &a - b;
        //assert!(c == Q::from_str("21/5").unwrap());    todo
    }

    // testing subtraction for Q and borrowed Q
    #[test]
    fn sub_second_borrowed() {
        let a: Q = Q::from_str("42").unwrap();
        let b: Q = Q::from_str("42/2").unwrap();
        let c: Q = a - &b;
        //assert!(c == Q::from_str("21").unwrap());    todo
    }
}
