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

use super::PolyOverZq;
use crate::macros::serialize::{deserialize, serialize};
use core::fmt;
use serde::{
    de::{Error, MapAccess, Unexpected, Visitor},
    ser::SerializeStruct,
    Deserialize, Serialize,
};
use std::str::FromStr;

serialize!("poly", PolyOverZq);
deserialize!("poly", Poly, PolyOverZq);

#[cfg(test)]
mod test_serialize {
    use crate::integer_mod_q::PolyOverZq;
    use std::str::FromStr;

    /// tests whether the serialization of a positive [`PolyOverZq`] works.
    #[test]
    fn serialize_output_positive() {
        let poly_str = "2  17 42 mod 81";
        let poly_z = PolyOverZq::from_str(poly_str).unwrap();
        let cmp_string = format!("{{\"poly\":\"{}\"}}", poly_str);

        assert_eq!(cmp_string, serde_json::to_string(&poly_z).unwrap())
    }

    /// tests whether the serialization of a negative [`PolyOverZq`] works.
    #[test]
    fn serialize_output_negative() {
        let poly_str = "3  -17 -42 1 mod 81";
        let poly_z = PolyOverZq::from_str(poly_str).unwrap();
        let cmp_string = "{\"poly\":\"3  64 39 1 mod 81\"}";

        assert_eq!(cmp_string, serde_json::to_string(&poly_z).unwrap())
    }

    /// tests whether the serialization of a positive large [`PolyOverZq`] works.
    #[test]
    fn serialize_output_positive_large() {
        let poly_str = format!("3  1 {} 1 mod {}", u64::MAX, u64::MAX - 58);
        let poly_z = PolyOverZq::from_str(&poly_str).unwrap();
        let cmp_string = format!("{{\"poly\":\"3  1 58 1 mod {}\"}}", u64::MAX - 58);

        assert_eq!(cmp_string, serde_json::to_string(&poly_z).unwrap())
    }

    /// tests whether the serialization of a positive [`PolyOverZq`] works.
    #[test]
    fn serialize_output_negative_large() {
        let poly_str = format!("3  1 -{} 1 mod {}", u64::MAX, u64::MAX - 58);
        let poly_z = PolyOverZq::from_str(&poly_str).unwrap();
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
    use crate::integer_mod_q::PolyOverZq;
    use std::str::FromStr;

    /// tests whether the deserialization of a positive [`PolyOverZq`] works.
    #[test]
    fn deserialize_positive() {
        let poly_str = "2  17 42 mod 81";
        let cmp_string = format!("{{\"poly\":\"{}\"}}", poly_str);

        let poly_z = PolyOverZq::from_str(poly_str).unwrap();
        assert_eq!(poly_z, serde_json::from_str(&cmp_string).unwrap())
    }

    /// tests whether the deserialization of a positive [`PolyOverZq`] works.
    #[test]
    fn deserialize_negative() {
        let poly_str = "3  -17 -42 1 mod 81";
        let cmp_string = format!("{{\"poly\":\"{}\"}}", poly_str);

        let poly_z = PolyOverZq::from_str(poly_str).unwrap();
        assert_eq!(poly_z, serde_json::from_str(&cmp_string).unwrap())
    }

    /// tests whether the deserialization of a positive [`PolyOverZq`] works.
    #[test]
    fn deserialize_positive_large() {
        let poly_str = format!("3  -17 {} 1 mod {}", u64::MAX, u64::MAX - 58);
        let cmp_string = format!("{{\"poly\":\"{}\"}}", poly_str);

        let poly_z = PolyOverZq::from_str(&poly_str).unwrap();
        assert_eq!(poly_z, serde_json::from_str(&cmp_string).unwrap())
    }

    /// tests whether the deserialization of a positive [`PolyOverZq`] works.
    #[test]
    fn deserialize_negative_large() {
        let poly_str = format!("3  -17 -{} 1 mod {}", u64::MAX, u64::MAX - 58);
        let cmp_string = format!("{{\"poly\":\"{}\"}}", poly_str);

        let poly_z = PolyOverZq::from_str(&poly_str).unwrap();
        assert_eq!(poly_z, serde_json::from_str(&cmp_string).unwrap())
    }

    /// tests whether no fields 'poly' provided yield an error
    #[test]
    fn no_field_value() {
        let a: Result<PolyOverZq, serde_json::Error> =
            serde_json::from_str("{{\"tree\":\"{2  17 42 mod 81}\"}}");
        assert!(a.is_err());

        let b: Result<PolyOverZq, serde_json::Error> = serde_json::from_str("{{}}");
        assert!(b.is_err());
    }

    /// tests whether too many fields yield an error
    #[test]
    fn too_many_fields() {
        let a: Result<PolyOverZq, serde_json::Error> = serde_json::from_str(
            "{{\"tree\":\"{2  17 42 mod 81}\", \"poly\":\"{2  17 42 mod 81}\"}}",
        );
        assert!(a.is_err());

        let b: Result<PolyOverZq, serde_json::Error> =
            serde_json::from_str("{{\"poly\":\"{}\", \"poly\":\"{2  17 42 mod 81}\"}}");
        assert!(b.is_err());
    }
}
