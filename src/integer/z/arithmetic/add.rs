//! Implementation of the [`Add`] trait for [`Z`] values.

use super::super::Z;
use crate::macros::arithmetics::arithmetic_trait;
use flint_sys::fmpz::fmpz;
use std::ops::Add;

arithmetic_trait!(
    doc = "Implements the [`Add`] trait for two [`Z`] values. \n
[`Add`] is implemented for any combination of [`Z`] and borrowed [`Z`].\n\n

 Parameters:\n
 - `other`: specifies the value to add to `self`\n\n

Returns the sum of both numbers as a [`Z`].\n\n

 # Example\n
 ```rust
 use math::integer::Z;

 let a: Z = Z::from(42);
 let b: Z = Z::from(24);

 let c: Z = &a + &b;
 let d: Z = a + b;
 let e: Z = &c + d;
 let f: Z = c + &e;
 ```",
    Add,
    add,
    Z,
    flint_sys::fmpz::fmpz_add,
    fmpz(0)
);

#[cfg(test)]
mod test_add {
    use super::Z;

    // testing addition for two Z
    #[test]
    fn add() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = a + b;
        assert!(c == Z::from(66));
    }

    // testing addition for two borrowed Z
    #[test]
    fn add_borrow() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = &a + &b;
        assert!(c == Z::from(66));
    }

    // testing addition for borrowed Z and Z
    #[test]
    fn add_first_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = &a + b;
        assert!(c == Z::from(66));
    }

    // testing addition for Z and borrowed Z
    #[test]
    fn add_second_borrowed() {
        let a: Z = Z::from(42);
        let b: Z = Z::from(24);
        let c: Z = a + &b;
        assert!(c == Z::from(66));
    }

    // testing addition for big numbers
    #[test]
    fn add_large_numbers() {
        let a: Z = Z::from(u64::MAX);
        let b: Z = Z::from(-221319874);
        let c: Z = Z::from(i64::MIN);
        let d: Z = &a + b;
        let e: Z = a + c;
        assert!(d == Z::from(u64::MAX - 221319874));
        assert!(e == Z::from(i64::MAX));
    }
}
