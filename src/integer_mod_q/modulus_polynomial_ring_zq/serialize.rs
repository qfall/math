// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations of functions
//! important for serialization such as the [`Serialize`] and [`Deserialize`] trait.
//!
//! The explicit functions contain the documentation.

use super::ModulusPolynomialRingZq;
use crate::macros::serialize::{deserialize, serialize};
use core::fmt;
use serde::{
    de::{Error, MapAccess, Unexpected, Visitor},
    ser::SerializeStruct,
    Deserialize, Serialize,
};
use std::str::FromStr;

serialize!("poly", ModulusPolynomialRingZq);
deserialize!("poly", Poly, ModulusPolynomialRingZq);

#[cfg(test)]
mod test_serialize {
    use crate::integer_mod_q::ModulusPolynomialRingZq;
    use std::str::FromStr;

    /// tests whether the serialization of a positive [`ModulusPolynomialRingZq`] works.
    #[test]
    fn serialize_output_positive() {
        let poly_str = "2  17 42 mod 331";
        let poly_z = ModulusPolynomialRingZq::from_str(poly_str).unwrap();
        let cmp_string = format!("{{\"poly\":\"{}\"}}", poly_str);

        assert_eq!(cmp_string, serde_json::to_string(&poly_z).unwrap())
    }

    /// tests whether the serialization of a negative [`ModulusPolynomialRingZq`] works.
    #[test]
    fn serialize_output_negative() {
        let poly_str = "3  -17 -42 1 mod 331";
        let poly_z = ModulusPolynomialRingZq::from_str(poly_str).unwrap();
        let cmp_string = "{\"poly\":\"3  314 289 1 mod 331\"}";

        assert_eq!(cmp_string, serde_json::to_string(&poly_z).unwrap())
    }

    /// tests whether the serialization of a positive large [`ModulusPolynomialRingZq`] works.
    #[test]
    fn serialize_output_positive_large() {
        let poly_str = format!("3  1 {} 1 mod {}", u64::MAX, u64::MAX - 58);
        let poly_z = ModulusPolynomialRingZq::from_str(&poly_str).unwrap();
        let cmp_string = format!("{{\"poly\":\"3  1 58 1 mod {}\"}}", u64::MAX - 58);

        assert_eq!(cmp_string, serde_json::to_string(&poly_z).unwrap())
    }

    /// tests whether the serialization of a negative large [`ModulusPolynomialRingZq`] works.
    #[test]
    fn serialize_output_negative_large() {
        let poly_str = format!("3  1 -{} 1 mod {}", u64::MAX, u64::MAX - 58);
        let poly_z = ModulusPolynomialRingZq::from_str(&poly_str).unwrap();
        let cmp_string = format!(
            "{{\"poly\":\"3  1 {} 1 mod {}\"}}",
            u64::MAX - 2 * 58,
            u64::MAX - 58
        );

        assert_eq!(cmp_string, serde_json::to_string(&poly_z).unwrap())
    }
}

#[cfg(test)]
mod test_deserialize {
    use crate::integer_mod_q::ModulusPolynomialRingZq;
    use std::str::FromStr;

    /// tests whether the deserialization of a positive [`ModulusPolynomialRingZq`] works.
    #[test]
    fn deserialize_positive() {
        let poly_str = "2  17 42 mod 331";
        let cmp_string = format!("{{\"poly\":\"{}\"}}", poly_str);

        let poly_z = ModulusPolynomialRingZq::from_str(poly_str).unwrap();
        assert_eq!(poly_z, serde_json::from_str(&cmp_string).unwrap())
    }

    /// tests whether the deserialization of a negative [`ModulusPolynomialRingZq`] works.
    #[test]
    fn deserialize_negative() {
        let poly_str = "3  -17 -42 1 mod 331";
        let cmp_string = format!("{{\"poly\":\"{}\"}}", poly_str);

        let poly_z = ModulusPolynomialRingZq::from_str(poly_str).unwrap();
        assert_eq!(poly_z, serde_json::from_str(&cmp_string).unwrap())
    }

    /// tests whether the deserialization of a positive large [`ModulusPolynomialRingZq`] works.
    #[test]
    fn deserialize_positive_large() {
        let poly_str = format!("3  -17 {} 1 mod {}", u64::MAX, u64::MAX - 58);
        let cmp_string = format!("{{\"poly\":\"{}\"}}", poly_str);

        let poly_z = ModulusPolynomialRingZq::from_str(&poly_str).unwrap();
        assert_eq!(poly_z, serde_json::from_str(&cmp_string).unwrap())
    }

    /// tests whether the deserialization of a negative large [`ModulusPolynomialRingZq`] works.
    #[test]
    fn deserialize_negative_large() {
        let poly_str = format!("3  -17 -{} 1 mod {}", u64::MAX, u64::MAX - 58);
        let cmp_string = format!("{{\"poly\":\"{}\"}}", poly_str);

        let poly_z = ModulusPolynomialRingZq::from_str(&poly_str).unwrap();
        assert_eq!(poly_z, serde_json::from_str(&cmp_string).unwrap())
    }

    /// tests whether deserialization of a non-prime large `q` [`ModulusPolynomialRingZq`] works.
    #[test]
    fn non_prime_q() {
        let a: Result<ModulusPolynomialRingZq, serde_json::Error> =
            serde_json::from_str(&format!("{{\"poly\":\"2  17 42 mod {}\"}}", u64::MAX));
        assert!(a.is_ok());
    }

    /// tests whether deserialization of a negative `q` [`ModulusPolynomialRingZq`] fails.
    #[test]
    fn negative_q() {
        let a: Result<ModulusPolynomialRingZq, serde_json::Error> =
            serde_json::from_str(&format!("{{\"poly\":\"2  17 42 mod -{}\"}}", u64::MAX));
        assert!(a.is_err());

        let b: Result<ModulusPolynomialRingZq, serde_json::Error> =
            serde_json::from_str("{{\"poly\":\"2  17 42 mod -17\"}}");
        assert!(b.is_err());
    }

    /// tests whether no fields 'poly' provided yield an error [`ModulusPolynomialRingZq`] works.
    #[test]
    fn no_field_value() {
        let a: Result<ModulusPolynomialRingZq, serde_json::Error> =
            serde_json::from_str("{{\"tree\":\"{2  17 42 mod 331}\"}}");
        assert!(a.is_err());

        let b: Result<ModulusPolynomialRingZq, serde_json::Error> = serde_json::from_str("{{}}");
        assert!(b.is_err());
    }

    /// tests whether too many fields yield an error
    #[test]
    fn too_many_fields() {
        let a: Result<ModulusPolynomialRingZq, serde_json::Error> = serde_json::from_str(
            "{{\"tree\":\"{2  17 42 mod 331}\", \"poly\":\"{2  17 42 mod 331}\"}}",
        );
        assert!(a.is_err());

        let b: Result<ModulusPolynomialRingZq, serde_json::Error> =
            serde_json::from_str("{{\"poly\":\"{}\", \"poly\":\"{2  17 42 mod 331}\"}}");
        assert!(b.is_err());
    }
}
