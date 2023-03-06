//! Implementation of the [`Add`] trait for [`Q`] values.

use flint_sys::{fmpq::fmpq, fmpz::fmpz};
use std::ops::Add;

use super::super::Q;
use crate::macros::arithmetic_trait;

arithmetic_trait!(
    doc = "Implements the [`Add`] trait for two [`Q`] values. \n
[`Add`] is implemented for any combination of [`Q`] and borrowed [`Q`].\n\n

 Parameters:\n
 - `other`: specifies the value to add to `self`\n\n

Returns the sum of both numbers as a [`Q`].\n\n

 # Example\n
 ```rust
 use math::rational::Q;

 let a: Q = Q::from(42);
 let b: Q = Q::from(24);

 let c: Q = &a + &b;
 let d: Q = a + b;
 let e: Q = &c + d;
 let f: Q = c + &e;
 ```",
    Add,
    add,
    Q,
    flint_sys::fmpq::fmpq_add,
    fmpq {fmpz(0),fmpz(1)}
);

#[cfg(test)]
mod tests {
    use super::Q;

    // testing addition for two Q
    #[test]
    fn add() {
        let a: Q = Q::from(42);
        let b: Q = Q::from(24);
        let c: Q = a + b;
        assert!(c == Q::from(66));
    }

    // testing addition for two borrowed Q
    #[test]
    fn add_borrow() {
        let a: Q = Q::from(42);
        let b: Q = Q::from(24);
        let c: Q = &a + &b;
        assert!(c == Q::from(66));
    }

    // testing addition for borrowed Q and Q
    #[test]
    fn add_first_borrowed() {
        let a: Q = Q::from(42);
        let b: Q = Q::from(24);
        let c: Q = &a + b;
        assert!(c == Q::from(66));
    }

    // testing addition for Q and borrowed Q
    #[test]
    fn add_second_borrowed() {
        let a: Q = Q::from(42);
        let b: Q = Q::from(24);
        let c: Q = a + &b;
        assert!(c == Q::from(66));
    }
}
