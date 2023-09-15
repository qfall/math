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

use super::Modulus;
use crate::macros::serialize::{deserialize, serialize};
use core::fmt;
use serde::{
    de::{Error, MapAccess, Unexpected, Visitor},
    ser::SerializeStruct,
    Deserialize, Serialize,
};
use std::str::FromStr;

serialize!("modulus", Modulus);
deserialize!("modulus", Modulus, Modulus);

#[cfg(test)]
mod test_serialize {
    use crate::integer_mod_q::Modulus;
    use std::str::FromStr;

    /// Tests whether the serialization of a positive [`Modulus`] works.
    #[test]
    fn serialize_output_positive() {
        let z = Modulus::from(17);
        let cmp_str = "{\"modulus\":\"17\"}";

        assert_eq!(cmp_str, serde_json::to_string(&z).unwrap());
    }

    /// Tests whether the serialization of a positive large [`Modulus`] works.
    #[test]
    fn serialize_output_positive_large() {
        let val_str = u64::MAX.to_string();
        let z = Modulus::from_str(&val_str).unwrap();
        let cmp_str = format!("{{\"modulus\":\"{val_str}\"}}");

        assert_eq!(cmp_str, serde_json::to_string(&z).unwrap());
    }
}

#[cfg(test)]
mod test_deserialize {
    use crate::integer_mod_q::Modulus;
    use std::str::FromStr;

    /// Tests whether the deserialization of a positive [`Modulus`] works.
    #[test]
    fn deserialize_positive() {
        let z_string = "{\"modulus\":\"17\"}";
        assert_eq!(Modulus::from(17), serde_json::from_str(z_string).unwrap());
    }

    /// Tests whether the deserialization of a negative [`Modulus`] fails.
    #[test]
    fn deserialize_negative() {
        let z_string = "{\"modulus\":\"-17\"}";

        let a: Result<Modulus, serde_json::Error> = serde_json::from_str(z_string);
        assert!(a.is_err());
    }

    /// Tests whether the deserialization of a positive [`Modulus`] works.
    #[test]
    fn deserialize_positive_large() {
        let val_str = u64::MAX.to_string();
        let z_string = format!("{{\"modulus\":\"{val_str}\"}}");

        assert_eq!(
            Modulus::from_str(&val_str).unwrap(),
            serde_json::from_str(&z_string).unwrap()
        )
    }

    /// Tests whether the deserialization of a large negative [`Modulus`] fails.
    #[test]
    fn deserialize_negative_large() {
        let val_str = format!("-{}", u64::MAX);
        let z_string = format!("{{\"modulus\":\"{val_str}\"}}");

        let a: Result<Modulus, serde_json::Error> = serde_json::from_str(&z_string);
        assert!(a.is_err());
    }

    /// Tests whether no fields `modulus` provided yield an error
    #[test]
    fn no_field_value() {
        let a: Result<Modulus, serde_json::Error> = serde_json::from_str("{{\"tree\":\"{17}\"}}");
        assert!(a.is_err());

        let b: Result<Modulus, serde_json::Error> = serde_json::from_str("{{}}");
        assert!(b.is_err());
    }

    /// Tests whether too many fields yield an error
    #[test]
    fn too_many_fields() {
        let a: Result<Modulus, serde_json::Error> =
            serde_json::from_str("{{\"tree\":\"{17}\", \"modulus\":\"{17}\"}}");
        assert!(a.is_err());

        let b: Result<Modulus, serde_json::Error> =
            serde_json::from_str("{{\"modulus\":\"{}\", \"modulus\":\"{17}\"}}");
        assert!(b.is_err());
    }
}
