//! Implementations of the 'From' trait for [PolyZq].
//!
//! This module contains all options to create a polynomial of type [PolyZq].

use std::{mem::MaybeUninit, str::FromStr};

use flint_sys::fmpz_mod_poly::{fmpz_mod_poly_init, fmpz_mod_poly_set_fmpz_poly};

use crate::{error::MathError, integer::poly_z::PolyZ, integer_mod_q::modulus::Modulus};

use super::PolyZq;

impl FromStr for PolyZq {
    type Err = MathError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (poly_s, modulus) = match s.split_once(" mod ") {
            Some((poly_s, modulus)) => (poly_s, modulus),
            None => return Err(todo!()),
        };
        let poly_z = PolyZ::from_str(poly_s)?;
        let modulus = Modulus::from_str(modulus)?;
        let mut poly = MaybeUninit::uninit();
        unsafe {
            fmpz_mod_poly_init(poly.as_mut_ptr(), &modulus.modulus);
            let mut poly = poly.assume_init();
            fmpz_mod_poly_set_fmpz_poly(&mut poly, &poly_z.poly, &modulus.modulus);
            Ok(Self { poly, modulus })
        }
    }
}
