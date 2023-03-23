// Copyright © 2023 Marvin Beckmann, Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module implements macros which are used to explicitly implement
//! traits taking input of one of our types. These types can be constructed
//! from other values. These macros will implement the trait for the other types.
//!
//! Example:
//! [`Z`](crate::integer::Z) implements the [`From`] trait for
//! [`i8`], [`i16`], ... -> hence it is be beneficial if one
//! does not have to first create a [`Z`](crate::integer::Z), but if one can directly
//! pass the value to other functions taking in a [`Z`](crate::integer::Z). These macros
//! shall implement the traits for the other types as well.

/// Implements a specified trait using implicit conversions to a bridge type.
/// Several traits are already supported:
///
/// - [`Evaluate`](crate::traits::Evaluate) with the signature
/// `($bridge_type, $output_type, $type, Evaluate for $source_type:ident)`
/// - [`SetCoefficient`](crate::traits::SetCoefficient) with the signature
/// `($bridge_type, $type, SetCoefficient for $source_type:ident)`
///
/// # Examples
/// ```compile_fail
/// implement_for_others!(Z, Z, PolyOverZ, Evaluate for u8 u16 u32 u64 i8 i16 i32 i64);
/// implement_for_others!(Z, PolyOverZ, SetCoefficient for i8 i16 i32 i64 u8 u16 u32 u64);
/// ```
macro_rules! implement_for_others {
    // [`Evaluate`] trait
    ($bridge_type:ident, $output_type:ident, $type:ident, Evaluate for $($source_type:ident)*) => {
        $(impl Evaluate<$source_type, $output_type> for $type {
            paste::paste! {
                #[doc = "Documentation can be found at [`" $type "::evaluate`]. Implicitly converts [`" $source_type "`] into [`" $bridge_type "`]."]
            fn evaluate(
                &self,
                other: $source_type
            ) -> $output_type {
                self.evaluate(&$bridge_type::from(other))
            }
            }
        })*
    };

    // [`SetCoefficient`] trait
    ($bridge_type:ident, $type:ident, SetCoefficient for $($source_type:ident)*) => {
        $(impl SetCoefficient<$source_type> for $type {
            paste::paste! {
                #[doc = "Documentation can be found at [`" $type "::set_coeff`]. Implicitly converts [`" $source_type "`] into [`" $bridge_type "`]."]
            fn set_coeff(
                &mut self,
                coordinate: impl TryInto<i64> + Display + Copy,
                value: $source_type,
            ) -> Result<(), MathError> {
                self.set_coeff(coordinate, $bridge_type::from(value))
            }
            }
        })*
    };
}

pub(crate) use implement_for_others;

/// Implements [`SetEntry`](crate::traits::SetEntry) for [`*type*`] using the conversions from the
/// [`*bridge_type*`] for [`*type*`].
///
/// Parameters:
/// - `source_type`: the type of the input (e.g. [`i32`], [`i64`])
/// - `bridge_type`: the type in which the input is converted
/// - `type`: the type for which the [`SetEntry`](crate::traits::SetEntry) is implemented (e.g. [`MatZ`](crate::integer::MatZ), [`MatQ`](crate::rational::MatQ))
///
/// Returns the owned Implementation code for the [`SetEntry`](crate::traits::SetEntry)
/// trait with the signature:
///
/// ```impl SetEntry<*&source_type*> for *type*```
macro_rules! implement_for_others_set_entry {
    ($source_type:ident, $bridge_type:ident, $type:ident) => {
        impl SetEntry<$source_type> for $type {
            paste::paste! {
                #[doc = "Documentation can be found at [`" $type "::set_entry`]. Implicitly converts [`" $source_type "`] into [`" $bridge_type "`]."]
            fn set_entry(
                &mut self,
                row: impl TryInto<i64> + Display + Copy,
                column: impl TryInto<i64> + Display + Copy,
                value: $source_type,
            ) -> Result<(), MathError> {
                self.set_entry(row, column, $bridge_type::from(value))
            }
            }
        }
    };
}

pub(crate) use implement_for_others_set_entry;

/// Implements [`SetEntry`](crate::traits::SetEntry) with [`*source_type*`] for [`*type*`].
///
/// Parameters:
/// - `source_type`: the type of the input.
/// - `type`: the type the trait is implemented for.
///
/// Returns the owned Implementation code for the [`SetEntry`](crate::traits::SetEntry)
/// trait with the signature:
///
/// ```impl SetEntry<*source_type*> for *type*```
macro_rules! implement_set_entry_borrowed_to_owned {
    ($source_type:ident, $type:ident) => {
        impl SetEntry<$source_type> for $type {
            paste::paste! {
                #[doc = "Documentation can be found at [`" $type "::set_entry`]."]
            fn set_entry(
                &mut self,
                row: impl TryInto<i64> + Display + Copy,
                column: impl TryInto<i64> + Display + Copy,
                value: $source_type,
            ) -> Result<(), MathError> {
                self.set_entry(row, column, &value)
            }
            }
        }
    };
}

pub(crate) use implement_set_entry_borrowed_to_owned;

/// Implements a specified trait for a owned input using the traits
/// implementation for a borrowed input.
/// Several traits are already supported:
///
/// - [`Evaluate`](crate::traits::Evaluate) with the signature
/// `($bridge_type, $output_type, $type, Evaluate for $source_type:ident)`
/// - [`SetCoefficient`](crate::traits::SetCoefficient) with the signature
/// `($bridge_type, $type, SetCoefficient for $source_type:ident)`
///
/// # Examples
/// ```compile_fail
/// implement_for_owned!(Q, Q, PolyOverQ, Evaluate);
/// implement_for_owned!(Z, PolyOverZ, SetCoefficient);
/// ```
macro_rules! implement_for_owned {
    // [`Evaluate`] trait
    ($source_type:ident, $output_type:ident, $type:ident, Evaluate) => {
        impl Evaluate<$source_type, $output_type> for $type {
            paste::paste! {
                #[doc = "Documentation can be found at [`" $type "::evaluate`]."]
            fn evaluate(
                &self,
                value: $source_type
            ) -> $output_type {
                self.evaluate(&value)
            }
            }
        }
    };

    // [`SetCoefficient`] trait
    ($source_type:ident, $type:ident, SetCoefficient) => {
        impl SetCoefficient<$source_type> for $type {
            paste::paste! {
                #[doc = "Documentation can be found at [`" $type "::set_coeff`]."]
            fn set_coeff(
                &mut self,
                coordinate: impl TryInto<i64> + Display + Copy,
                value: $source_type,
            ) -> Result<(), MathError> {
                self.set_coeff(coordinate, &value)
            }
            }
        }
    };
}

pub(crate) use implement_for_owned;
