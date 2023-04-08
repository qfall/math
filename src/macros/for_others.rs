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
/// - [`SetEntry`](crate::traits::SetEntry) with the signature
/// `($bridge_type, $type, SetEntry for $source_type:ident)`
/// - ['Mul'](std::ops::Mul) with signatures
/// `($bridge_type:ident, $type:ident, Mul Matrix for $source_type:ident)` and
/// `($bridge_type:ident, $type:ident, Mul Scalar for $source_type:ident)`
///
/// # Examples
/// ```compile_fail
/// implement_for_others!(Z, Z, PolyOverZ, Evaluate for u8 u16 u32 u64 i8 i16 i32 i64);
/// implement_for_others!(Z, PolyOverZ, SetCoefficient for i8 i16 i32 i64 u8 u16 u32 u64);
/// implement_for_others!(Z, MatZq, SetEntry for i8 i16 i32 i64 u8 u16 u32 u64);
/// implement_for_others!(Z, MatZ, Mul Matrix for i8 i16 i32 i64 u8 u16 u32 u64);
/// implement_for_others!(Z, i8 i16 i32 i64 u8 u16 u32 u64, Mul Scalar for MatZ);
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
                index: impl TryInto<i64> + Display + Copy,
                value: $source_type,
            ) -> Result<(), MathError> {
                self.set_coeff(index, $bridge_type::from(value))
            }
            }
        })*
    };

    // [`SetEntry`] trait
    ($bridge_type:ident, $type:ident, SetEntry for $($source_type:ident)*) => {
        $(impl SetEntry<$source_type> for $type {
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
        })*
    };

    // [`Mul`] trait scalar
    ($bridge_type:ident, $type:ident, Mul Scalar for $($source_type:ident)*) => {
        $(impl Mul<$source_type> for $type {
            type Output = $type;
            paste::paste! {
                #[doc = "Documentation can be found at [`" $type "::set_entry`]."]
                fn mul(self, scalar: $source_type) -> Self::Output {
                    self.mul($bridge_type::from(scalar))
                }
            }
        })*

        $(impl Mul<$type> for $source_type {
            type Output = $type;
            paste::paste! {
                #[doc = "Documentation can be found at [`" $type "::set_entry`]."]
                fn mul(self, matrix: $type) -> Self::Output {
                    matrix.mul($bridge_type::from(self))
                }
            }
        })*
    };

    // [`Distance`] trait
    ($bridge_type:ident, $type:ident, Distance for $($source_type:ident)*) => {
        $(impl Distance<$source_type> for $type {
            paste::paste! {
                #[doc = "Documentation can be found at [`" $type "::distance`]. Implicitly converts [`" $source_type "`] into [`" $bridge_type "`]."]
            fn distance(
                &self,
                other: $source_type,
            ) -> Self {
                self.distance($bridge_type::from(other))
            }
            }
        })*
    };
}

pub(crate) use implement_for_others;

/// Implements a specified trait for a owned input using the traits
/// implementation for a borrowed input.
/// Several traits are already supported:
///
/// - [`Evaluate`](crate::traits::Evaluate) with the signature
/// `($bridge_type, $output_type, $type, Evaluate for $source_type:ident)`
/// - [`SetCoefficient`](crate::traits::SetCoefficient) with the signature
/// `($bridge_type, $type, SetCoefficient for $source_type:ident)`
/// - [`SetEntry`](crate::traits::SetEntry) with the signature
/// `($bridge_type, $type, SetCoefficient for $source_type:ident)`
///
/// # Examples
/// ```compile_fail
/// implement_for_owned!(Q, Q, PolyOverQ, Evaluate);
/// implement_for_owned!(Z, PolyOverZ, SetCoefficient);
/// implement_for_owned!(Z, MatZq, SetEntry);
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
                index: impl TryInto<i64> + Display + Copy,
                value: $source_type,
            ) -> Result<(), MathError> {
                self.set_coeff(index, &value)
            }
            }
        }
    };

    // [`SetEntry`] trait
    ($source_type:ident, $type:ident, SetEntry) => {
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

    // [`Distance`] trait
    ($source_type:ident, $type:ident, Distance) => {
        impl Distance<$source_type> for $type {
            paste::paste! {
                #[doc = "Documentation can be found at [`" $type "::distance`]."]
            fn distance(
                &self,
                other: $source_type,
            ) -> Self {
                self.distance(&other)
            }
            }
        }
    };
}

pub(crate) use implement_for_owned;
