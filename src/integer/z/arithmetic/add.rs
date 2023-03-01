//! Implementation of the [`Add`] trait for [`Z`] values.

use flint_sys::fmpz::fmpz;
use std::ops::Add;

use super::super::Z;
use crate::macros::arithmetic_trait;

arithmetic_trait!(Add, add, Z, flint_sys::fmpz::fmpz_add, fmpz(0));

#[cfg(test)]
mod tests {
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
}
