//! This module implements macros which are used to explicitly implement
//! the [`Serialize`](serde::Serialize) and [`Deserialize`](serde::Deserialize) trait for data types.

/// Implements the [`Serialize`](serde::Serialize) for [`*type*`].
///
/// Parameters:
/// - `field_identifier`: the name of the field
/// - `type`: the type for which [`Serialize`](serde::Serialize) is implemented
/// (e.g. [`Z`](crate::integer::Z))
///
/// ```impl Serialize for *type*```
macro_rules! serialize {
    ($field_identifier:tt, $type:ident) => {
        impl Serialize for $type {
            paste::paste! {
                #[doc = "Implements the serialize option. This allows to create a Json-object from a given [`" $type "`]."]
                fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
                where
                    S: serde::Serializer,
                {
                    let mut state = serializer.serialize_struct("$type", 1)?;
                    state.serialize_field($field_identifier, &self.to_string())?;
                    state.end()
                }
            }
        }
    };
}

/// Implements the [`Deserialize`](serde::Deserialize) for [`*type*`].
///
/// Parameters:
/// - `field_identifier`: the name of the field
/// - `type`: the type for which [`Deserialize`](serde::Deserialize) is implemented
/// (e.g. [`Z`](crate::integer::Z))
///
/// ```impl Deserialize for *type*```
macro_rules! deserialize {
    ($field_identifier:tt, $type:ident) => {
        impl<'de> Deserialize<'de> for $type {
        paste::paste! {
            #[doc = "Implements the deserialize option. This allows to create a [`" $type "`] from a given Json-object."]
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                const FIELDS: &[&str] = &[$field_identifier];
                #[derive(Deserialize)]
                #[serde(field_identifier, rename_all = "lowercase")]
                enum Field {
                    Value,
                }

                /// This visitor iterates over the strings content and collects all possible fields.
                /// It sets the corresponding values of the struct based on the values found.
                struct StructVisitor;
                impl<'de> Visitor<'de> for StructVisitor {
                    type Value = $type;

                    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                        formatter.write_str("struct $type")
                    }

                    fn visit_map<V>(self, mut map: V) -> Result<$type, V::Error>
                    where
                        V: MapAccess<'de>,
                    {
                        let mut value = None;
                        while let Some(key) = map.next_key()? {
                            match key {
                                Field::Value => {
                                    if value.is_some() {
                                        return Err(Error::duplicate_field($field_identifier));
                                    }
                                    value = Some(map.next_value()?);
                                }
                            }
                        }
                        let value = value.ok_or_else(|| Error::missing_field($field_identifier))?;
                        $type::from_str(value)
                            .map_err(|_| Error::invalid_value(Unexpected::Str(value), &self))
                    }
                }

                deserializer.deserialize_struct("$type", FIELDS, StructVisitor)

            }
        }
    }
};
}

pub(crate) use serialize;

pub(crate) use deserialize;
