//! This module contains implementations of functions
//! important for serialization such as the [`Serialize`] and [`Deserialize`] trait.
//!
//! The explicit functions contain the documentation.

use super::Z;
use crate::macros::serialize::{deserialize, serialize};
use core::fmt;
use serde::{
    de::{Error, MapAccess, Unexpected, Visitor},
    ser::SerializeStruct,
    Deserialize, Serialize,
};
use std::str::FromStr;

serialize!("value", Z);
deserialize!("value", Z);

#[cfg(test)]
mod test_serialize {
    use crate::integer::Z;
    use std::str::FromStr;

    /// tests whether the serialization of a positive [`Z`] works.
    #[test]
    fn serialize_output_positive() {
        let z = Z::from(17);
        let cmp_string = "{\"value\":\"17\"}";

        assert_eq!(cmp_string, serde_json::to_string(&z).unwrap())
    }

    /// tests whether the serialization of a negative [`Z`] works.
    #[test]
    fn serialize_output_negative() {
        let z = Z::from(-17);
        let cmp_string = "{\"value\":\"-17\"}";

        assert_eq!(cmp_string, serde_json::to_string(&z).unwrap())
    }

    /// tests whether the serialization of a positive large [`Z`] works.
    #[test]
    fn serialize_output_positive_large() {
        let val_str = u64::MAX.to_string();
        let z = Z::from_str(&val_str).unwrap();
        let cmp_string = format!("{{\"value\":\"{}\"}}", val_str);

        assert_eq!(cmp_string, serde_json::to_string(&z).unwrap())
    }

    /// tests whether the serialization of a positive [`Z`] works.
    #[test]
    fn serialize_output_negative_large() {
        let val_str = format!("-{}", u64::MAX);
        let z = Z::from_str(&val_str).unwrap();
        let cmp_string = format!("{{\"value\":\"{}\"}}", val_str);

        assert_eq!(cmp_string, serde_json::to_string(&z).unwrap())
    }
}

#[cfg(test)]
mod test_deserialize {
    use crate::integer::Z;
    use std::str::FromStr;

    /// tests whether the deserialization of a positive [`Z`] works.
    #[test]
    fn deserialize_positive() {
        let z_string = "{\"value\":\"17\"}";
        assert_eq!(Z::from(17), serde_json::from_str(z_string).unwrap())
    }

    /// tests whether the deserialization of a positive [`Z`] works.
    #[test]
    fn deserialize_negative() {
        let z_string = "{\"value\":\"-17\"}";
        assert_eq!(Z::from(-17), serde_json::from_str(z_string).unwrap())
    }

    /// tests whether the deserialization of a positive [`Z`] works.
    #[test]
    fn deserialize_positive_large() {
        let val_str = u64::MAX.to_string();
        let z_string = format!("{{\"value\":\"{}\"}}", val_str);

        assert_eq!(
            Z::from_str(&val_str).unwrap(),
            serde_json::from_str(&z_string).unwrap()
        )
    }

    /// tests whether the deserialization of a positive [`Z`] works.
    #[test]
    fn deserialize_negative_large() {
        let val_str = format!("-{}", u64::MAX);
        let z_string = format!("{{\"value\":\"{}\"}}", val_str);

        assert_eq!(
            Z::from_str(&val_str).unwrap(),
            serde_json::from_str(&z_string).unwrap()
        )
    }

    /// tests whether no fields 'value' provided yield an error
    #[test]
    fn no_field_value() {
        let a: Result<Z, serde_json::Error> = serde_json::from_str("{{\"tree\":\"{17}\"}}");
        assert!(a.is_err());

        let b: Result<Z, serde_json::Error> = serde_json::from_str("{{}}");
        assert!(b.is_err());
    }

    /// tests whether too many fields yield an error
    #[test]
    fn too_many_fields() {
        let a: Result<Z, serde_json::Error> =
            serde_json::from_str("{{\"tree\":\"{17}\", \"value\":\"{17}\"}}");
        assert!(a.is_err());

        let b: Result<Z, serde_json::Error> =
            serde_json::from_str("{{\"value\":\"{}\", \"value\":\"{17}\"}}");
        assert!(b.is_err());
    }
}
