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

use super::PolyOverZ;
use crate::macros::serialize::{deserialize, serialize};
use core::fmt;
use serde::{
    de::{Error, MapAccess, Unexpected, Visitor},
    ser::SerializeStruct,
    Deserialize, Serialize,
};
use std::str::FromStr;

serialize!("poly", PolyOverZ);
deserialize!("poly", Poly, PolyOverZ);

#[cfg(test)]
mod test_serialize {
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// tests whether the serialization of a positive [`PolyOverZ`] works.
    #[test]
    fn serialize_output_positive() {
        let poly_str = "2  17 42";
        let poly_z = PolyOverZ::from_str(poly_str).unwrap();
        let cmp_string = format!("{{\"poly\":\"{}\"}}", poly_str);

        assert_eq!(cmp_string, serde_json::to_string(&poly_z).unwrap())
    }

    /// tests whether the serialization of a negative [`PolyOverZ`] works.
    #[test]
    fn serialize_output_negative() {
        let poly_str = "3  -17 -42 1";
        let poly_z = PolyOverZ::from_str(poly_str).unwrap();
        let cmp_string = format!("{{\"poly\":\"{}\"}}", poly_str);

        assert_eq!(cmp_string, serde_json::to_string(&poly_z).unwrap())
    }

    /// tests whether the serialization of a positive large [`PolyOverZ`] works.
    #[test]
    fn serialize_output_positive_large() {
        let poly_str = format!("3  -17 {} 1", u64::MAX);
        let poly_z = PolyOverZ::from_str(&poly_str).unwrap();
        let cmp_string = format!("{{\"poly\":\"{}\"}}", poly_str);

        assert_eq!(cmp_string, serde_json::to_string(&poly_z).unwrap())
    }

    /// tests whether the serialization of a negative [`PolyOverZ`] works.
    #[test]
    fn serialize_output_negative_large() {
        let poly_str = format!("3  -17 -{} 1", u64::MAX);
        let poly_z = PolyOverZ::from_str(&poly_str).unwrap();
        let cmp_string = format!("{{\"poly\":\"{}\"}}", poly_str);

        assert_eq!(cmp_string, serde_json::to_string(&poly_z).unwrap())
    }
}

#[cfg(test)]
mod test_deserialize {
    use crate::integer::PolyOverZ;
    use std::str::FromStr;

    /// tests whether the deserialization of a positive [`PolyOverZ`] works.
    #[test]
    fn deserialize_positive() {
        let poly_str = "2  17 42";
        let cmp_string = format!("{{\"poly\":\"{}\"}}", poly_str);

        let poly_z = PolyOverZ::from_str(poly_str).unwrap();
        assert_eq!(poly_z, serde_json::from_str(&cmp_string).unwrap())
    }

    /// tests whether the deserialization of a negative [`PolyOverZ`] works.
    #[test]
    fn deserialize_negative() {
        let poly_str = "3  -17 -42 1";
        let cmp_string = format!("{{\"poly\":\"{}\"}}", poly_str);

        let poly_z = PolyOverZ::from_str(poly_str).unwrap();
        assert_eq!(poly_z, serde_json::from_str(&cmp_string).unwrap())
    }

    /// tests whether the deserialization of a positive large [`PolyOverZ`] works.
    #[test]
    fn deserialize_positive_large() {
        let poly_str = format!("3  -17 {} 1", u64::MAX);
        let cmp_string = format!("{{\"poly\":\"{}\"}}", poly_str);

        let poly_z = PolyOverZ::from_str(&poly_str).unwrap();
        assert_eq!(poly_z, serde_json::from_str(&cmp_string).unwrap())
    }

    /// tests whether the deserialization of a negative large [`PolyOverZ`] works.
    #[test]
    fn deserialize_negative_large() {
        let poly_str = format!("3  -17 -{} 1", u64::MAX);
        let cmp_string = format!("{{\"poly\":\"{}\"}}", poly_str);

        let poly_z = PolyOverZ::from_str(&poly_str).unwrap();
        assert_eq!(poly_z, serde_json::from_str(&cmp_string).unwrap())
    }

    /// tests whether no fields 'poly' provided yield an error
    #[test]
    fn no_field_value() {
        let a: Result<PolyOverZ, serde_json::Error> =
            serde_json::from_str("{{\"tree\":\"{2  17 42}\"}}");
        assert!(a.is_err());

        let b: Result<PolyOverZ, serde_json::Error> = serde_json::from_str("{{}}");
        assert!(b.is_err());
    }

    /// tests whether too many fields yield an error
    #[test]
    fn too_many_fields() {
        let a: Result<PolyOverZ, serde_json::Error> =
            serde_json::from_str("{{\"tree\":\"{2  17 42}\", \"poly\":\"{2  17 42}\"}}");
        assert!(a.is_err());

        let b: Result<PolyOverZ, serde_json::Error> =
            serde_json::from_str("{{\"poly\":\"{}\", \"poly\":\"{2  17 42}\"}}");
        assert!(b.is_err());
    }
}
