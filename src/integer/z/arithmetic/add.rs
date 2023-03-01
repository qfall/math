//! Implementations to add [`Z`] values.
//! 
//! 
//! 


use std::ops::Add;

use flint_sys::fmpz::{fmpz};

use super::super::Z;
use crate::macros;  //TODO MAcro for &a + b (all 2 cases)

macro_rules! arithmetic_trait {
    ($trait:ident, $trait_function:ident, $type:ident, $function:expr) => {
        impl $trait for &$type {
            type Output = $type;

            fn $trait_function(self, other: Self) -> Self::Output {
                let mut out = fmpz(0);  //todo
                unsafe {
                    $function(&mut out, &self.value, &other.value);
                }
                $type { value: out }
            }
        }

        impl $trait<$type> for &$type {
            type Output = $type;

            fn $trait_function(self, other: $type) -> Self::Output {
                self.add(&other)
            }
        }

        impl $trait for $type {
            type Output = $type;

            fn $trait_function(self, other: Self) -> Self::Output {
                (&self).add(&other)
            }
        }

        impl $trait<&$type> for $type {
            type Output = $type;

            fn $trait_function(self, other: &Self) -> Self::Output {
                (&self).add(other)
            }
        }

    };
}






arithmetic_trait!(Add, add, Z, flint_sys::fmpz::fmpz_add);

#[cfg(test)]
mod tests {
    use super::Z;

    #[test]
    fn add() {
        let a: Z = Z::from_i64(42);
        let b: Z = Z::from_i64(24);
        let c: Z = a + b;
        //assert!(c == Z::from(66));
    }

    #[test]
    fn add_borrow() {
        let a: Z = Z::from_i64(42);
        let b: Z = Z::from_i64(24);
        let c: Z = &a + &b;
        //assert!(c == Z::from(66));
    }

    #[test]
    fn add_first_borrowed() {
        let a: Z = Z::from_i64(42);
        let b: Z = Z::from_i64(24);
        let c: Z = &a + b;
        //assert!(c == Z::from(66));
    }

    #[test]
    fn  add_second_borrowed() {
        let a: Z = Z::from_i64(42);
        let b: Z = Z::from_i64(24);
        let c: Z = a + &b;
        //assert!(c == Z::from(66));
    }

}