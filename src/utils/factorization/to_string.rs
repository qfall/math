// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains all options to convert a [`Factorization`]
//! into a [`String`].
//!
//! This includes the [`Display`](std::fmt::Display) trait.

use super::Factorization;
use crate::integer::Z;
use std::fmt;
use string_builder::Builder;

impl fmt::Display for Factorization {
    /// Allows to convert a factorization of type [`Factorization`] into a [`String`].
    ///
    /// Returns the factorization in form of a [`String`]. For factorization `2^3 * 5 * 7^2`
    /// the String looks like this `[(2,3),(5,1),(7,2)]`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::utils::Factorization;
    /// use core::fmt;
    ///
    /// let mut fac = Factorization::from((1200, 20));
    /// fac.refine();
    ///
    /// println!("{}", fac);
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut builder = Builder::default();

        builder.append('[');

        for (num, factor) in Vec::<(Z, u64)>::from(self).iter().enumerate() {
            builder.append(format!("({}, {})", factor.0, factor.1));
            if num < Vec::<(Z, u64)>::from(self).len() - 1 {
                builder.append(", ");
            }
        }
        builder.append(']');

        write!(
            f,
            "{}",
            builder
                .string()
                .expect("Vector string contains invalid bytes.")
        )
    }
}

#[cfg(test)]
mod test_to_string {
    use crate::utils::Factorization;

    /// Tests whether a large positive integer works in a roundtrip.
    #[test]
    fn working_large_positive() {
        let fac = Factorization::from(u64::MAX);

        assert_eq!(format!("[({}, 1)]", u64::MAX), fac.to_string());
    }

    /// Tests whether a large negative integer works in a roundtrip.
    #[test]
    fn working_large_negative() {
        let fac = Factorization::from(i64::MIN);

        assert_eq!(format!("[({}, 1)]", i64::MIN), fac.to_string());
    }

    /// Tests whether a positive integer works in a roundtrip.
    #[test]
    fn working_positive() {
        let fac = Factorization::from(42);

        assert_eq!("[(42, 1)]", fac.to_string());
    }

    /// Tests whether a negative integer works in a roundtrip.
    #[test]
    fn working_negative() {
        let fac = Factorization::from(-42);

        println!("{}", fac);

        assert_eq!("[(-42, 1)]", fac.to_string());
    }

    /// Tests whether to_string works for more than one entry.
    #[test]
    fn working_use_result_of_to_string_as_input() {
        let mut fac = Factorization::from((1200, 20));

        fac.refine();

        assert_eq!("[(3, 1), (20, 3)]", fac.to_string());
    }

    /// Tests whether to_string works for refined negative values.
    #[test]
    fn working_refined_negative() {
        let mut fac = Factorization::from((-1200, 20));

        fac.refine();

        assert_eq!("[(-1, 1), (3, 1), (20, 3)]", fac.to_string());
    }
}
