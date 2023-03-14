use super::Z;
use core::fmt;
use serde::{
    de::{self, MapAccess, Unexpected, Visitor},
    ser::SerializeStruct,
    Deserialize, Serialize,
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

impl<'de> Deserialize<'de> for Z {
    /// Implements the deserialize option. This allows to create a [`Z`] from a Json-object.
    ///
    /// Input parameters:
    /// * `deserializer` : the serializer used for deserialization
    ///
    /// # Examples
    /// ```
    /// use math::integer::Z;
    ///         
    /// let input = r#"{"value":"42"}"#;
    /// let deserialized_z: Z = serde_json::from_str(input).unwrap();
    /// ```
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        const FIELDS: &[&str] = &["value"];
        #[derive(Deserialize)]
        #[serde(field_identifier, rename_all = "lowercase")]
        enum Field {
            Value,
        }

        /// This visitor iterates over the strings content and collects all possible fields.
        /// It sets the corresponding values of the struct based on the values found.
        struct ZVisitor;
        impl<'de> Visitor<'de> for ZVisitor {
            type Value = Z;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct Z")
            }

            fn visit_map<V>(self, mut map: V) -> Result<Z, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut value = None;
                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Value => {
                            if value.is_some() {
                                return Err(de::Error::duplicate_field("value"));
                            }
                            value = Some(map.next_value()?);
                        }
                    }
                }
                let value = value.ok_or_else(|| de::Error::missing_field("value"))?;
                Z::from_str(value)
                    .map_err(|_| de::Error::invalid_value(Unexpected::Str(value), &self))
            }
        }

        deserializer.deserialize_struct("Z", FIELDS, ZVisitor)
    }
}

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
