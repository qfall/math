// Copyright © 2023 Marvin Beckmann, Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Implementations to get information about a [`ModulusPolynomialRingZq].

use crate::{integer::Z, integer_mod_q::ModulusPolynomialRingZq};
use flint_sys::{
    fmpz::fmpz_set,
    fq::{fq_ctx_degree, fq_ctx_struct},
};

impl ModulusPolynomialRingZq {
    /// Returns the [`fq_ctx_struct`] of a modulus and is only used internally.
    pub(crate) fn get_fq_ctx_struct(&self) -> &fq_ctx_struct {
        self.modulus.as_ref()
    }

    /// Returns the context integer as a [`Z`].
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let modulus_ring = ModulusPolynomialRingZq::from_str("4  1 0 0 1 mod 17").unwrap();
    ///
    /// let modulus = modulus_ring.get_q();
    ///
    /// let cmp_modulus = Z::from(17);
    /// assert_eq!(cmp_modulus, modulus);
    /// ```
    pub fn get_q(&self) -> Z {
        let mut out = Z::default();
        unsafe {
            fmpz_set(&mut out.value, &self.get_fq_ctx_struct().ctxp[0].n[0]);
        }
        out
    }

    /// Returns the degree of a polynomial [`ModulusPolynomialRingZq`] as a [`i64`].
    /// The zero polynomial has degree '-1'.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer_mod_q::ModulusPolynomialRingZq;
    /// use std::str::FromStr;
    ///
    /// let poly = ModulusPolynomialRingZq::from_str("4  0 1 2 3 mod 7").unwrap();
    ///
    /// let degree = poly.get_degree(); // This would only return 3
    /// ```
    pub fn get_degree(&self) -> i64 {
        unsafe { fq_ctx_degree(self.get_fq_ctx_struct()) }
    }
}

#[cfg(test)]
mod test_get_degree {
    use crate::integer_mod_q::ModulusPolynomialRingZq;
    use std::str::FromStr;

    /// Ensures that degree is working for constant polynomials.
    #[test]
    fn degree_constant() {
        let degrees = [0, 1, 3, 7, 15, 32, 120];
        for degree in degrees {
            let modulus_ring = ModulusPolynomialRingZq::from_str(&format!(
                "{}  {}1 mod 17",
                degree + 1,
                "0 ".repeat(degree)
            ))
            .unwrap();

            assert_eq!(degree as i64, modulus_ring.get_degree());
        }
    }

    /// Ensure that degree is working for polynomials with leading 0 coefficients.
    #[test]
    fn degree_leading_zeros() {
        let poly = ModulusPolynomialRingZq::from_str("4  1 0 0 0 mod 199").unwrap();

        let deg = poly.get_degree();

        assert_eq!(0, deg);
    }

    /// Ensure that degree is working for polynomials with many coefficients
    /// flint does not reduce the exponent due to computational cost.
    #[test]
    fn degree_many_coefficients() {
        let poly_1 = ModulusPolynomialRingZq::from_str("7  1 2 3 4 8 1 3 mod 2").unwrap();
        let poly_2 = ModulusPolynomialRingZq::from_str(&format!(
            "7  1 2 3 4 8 {} {} mod {}",
            u64::MAX,
            i64::MAX,
            u128::MAX
        ))
        .unwrap();

        let deg_1 = poly_1.get_degree();
        let deg_2 = poly_2.get_degree();

        assert_eq!(6, deg_1);
        assert_eq!(6, deg_2);
    }
}

#[cfg(test)]
mod test_get_q {
    use crate::{integer::Z, integer_mod_q::ModulusPolynomialRingZq};
    use std::str::FromStr;

    /// ensure that the same modulus is correctly returned for a large modulus
    #[test]
    fn correct_large() {
        let large_prime = u64::MAX - 58;
        let modulus_ring =
            ModulusPolynomialRingZq::from_str(&format!("4  1 0 0 1 mod {large_prime}")).unwrap();

        let modulus = modulus_ring.get_q();

        let cmp_modulus = Z::from(large_prime);
        assert_eq!(cmp_modulus, modulus);
    }
}
