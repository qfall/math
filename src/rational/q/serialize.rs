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

use super::Q;
use crate::macros::serialize::{deserialize, serialize};
use core::fmt;
use serde::{
    de::{Error, MapAccess, Unexpected, Visitor},
    ser::SerializeStruct,
    Deserialize, Serialize,
};
use std::str::FromStr;

serialize!("value", Q);
deserialize!("value", Q);

#[cfg(test)]
mod test_serialize {
    use crate::rational::Q;
    use std::str::FromStr;

    /// tests whether the serialization of a positive [`Q`] works.
    #[test]
    fn serialize_output_positive() {
        let q = Q::from_str("17/3").unwrap();
        let cmp_string = "{\"value\":\"17/3\"}";

        assert_eq!(cmp_string, serde_json::to_string(&q).unwrap())
    }

    /// tests whether the serialization of a negative [`Q`] works.
    #[test]
    fn serialize_output_negative() {
        let q = Q::from_str("-17/3").unwrap();
        let cmp_string = "{\"value\":\"-17/3\"}";

        assert_eq!(cmp_string, serde_json::to_string(&q).unwrap())
    }

    /// tests whether the serialization of a positive large [`Q`] works.
    #[test]
    fn serialize_output_positive_large() {
        let val_str = format!("{}/2", u64::MAX);
        let q = Q::from_str(&val_str).unwrap();
        let cmp_string = format!("{{\"value\":\"{}\"}}", val_str);

        assert_eq!(cmp_string, serde_json::to_string(&q).unwrap())
    }

    /// tests whether the serialization of a positive [`Q`] works.
    #[test]
    fn serialize_output_negative_large() {
        let val_str = format!("-{}/2", u64::MAX);
        let q = Q::from_str(&val_str).unwrap();
        let cmp_string = format!("{{\"value\":\"{}\"}}", val_str);

        assert_eq!(cmp_string, serde_json::to_string(&q).unwrap())
    }
}

#[cfg(test)]
mod test_deserialize {
    use crate::rational::Q;
    use std::str::FromStr;

    /// tests whether the deserialization of a positive [`Q`] works.
    #[test]
    fn deserialize_positive() {
        let q_string = "{\"value\":\"17/3\"}";
        assert_eq!(
            Q::from_str("17/3").unwrap(),
            serde_json::from_str(q_string).unwrap()
        )
    }

    /// tests whether the deserialization of a positive [`Q`] works.
    #[test]
    fn deserialize_negative() {
        let q_string = "{\"value\":\"-17/3\"}";
        assert_eq!(
            Q::from_str("-17/3").unwrap(),
            serde_json::from_str(q_string).unwrap()
        )
    }

    /// tests whether the deserialization of a positive [`Q`] works.
    #[test]
    fn deserialize_positive_large() {
        let val_str = format!("{}/2", u64::MAX);
        let z_string = format!("{{\"value\":\"{}\"}}", val_str);

        assert_eq!(
            Q::from_str(&val_str).unwrap(),
            serde_json::from_str(&z_string).unwrap()
        )
    }

    /// tests whether the deserialization of a positive [`Q`] works.
    #[test]
    fn deserialize_negative_large() {
        let val_str = format!("-{}/2", u64::MAX);
        let z_string = format!("{{\"value\":\"{}\"}}", val_str);

        assert_eq!(
            Q::from_str(&val_str).unwrap(),
            serde_json::from_str(&z_string).unwrap()
        )
    }

    /// tests whether no fields 'value' provided yield an error
    #[test]
    fn no_field_value() {
        let a: Result<Q, serde_json::Error> = serde_json::from_str("{{\"tree\":\"{17}\"}}");
        assert!(a.is_err());

        let b: Result<Q, serde_json::Error> = serde_json::from_str("{{}}");
        assert!(b.is_err());
    }

    /// tests whether too many fields yield an error
    #[test]
    fn too_many_fields() {
        let a: Result<Q, serde_json::Error> =
            serde_json::from_str("{{\"tree\":\"{17/3}\", \"value\":\"{17}\"}}");
        assert!(a.is_err());

        let b: Result<Q, serde_json::Error> =
            serde_json::from_str("{{\"value\":\"{}\", \"value\":\"{17}\"}}");
        assert!(b.is_err());
    }
}
