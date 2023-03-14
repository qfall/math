use super::Z;
use core::fmt;
use serde::{
    de::{self, MapAccess, Visitor},
    ser::SerializeStruct,
    Deserialize, Deserializer, Serialize,
};
use std::str::FromStr;

impl Serialize for Z {
    /// Implements the serialize option. This allows to create a Json-object from a given [`Z`].
    ///
    /// Input parameters:
    /// * `serializer` : the serializer used for serialization
    ///
    /// # Examples
    /// ```
    /// use math::integer::Z;
    ///         
    /// let a = Z::from(42);
    /// let json_string = serde_json::to_string(&a).unwrap();
    /// ```
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("Z", 1)?;
        state.serialize_field("value", &self.to_string())?;
        state.end()
    }
}

#[cfg(test)]
mod test_serialize {
    use std::str::FromStr;

    use crate::integer::Z;

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
