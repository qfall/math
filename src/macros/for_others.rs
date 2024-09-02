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
//! [`i8`],[`i16`], ... -> hence it is be beneficial if one
//! does not have to first create a [`Z`](crate::integer::Z), but if one can directly
//! pass the value to other functions taking in a [`Z`](crate::integer::Z). These macros
//! shall implement the traits for the other types as well.

/// Implements a specified trait using implicit conversions to a bridge type.
///
/// - ['Mul'](std::ops::Mul) with signature
///     `($bridge_type, $type, Mul Scalar for $source_type)`
///
/// # Examples
/// ```compile_fail
/// implement_for_others!(Z, MatZ, Mul Scalar for i8 i16 i32 i64 u8 u16 u32 u64);
/// ```
macro_rules! implement_for_others {
    // [`Mul`] trait scalar
    ($bridge_type:ident, $type:ident, Mul Scalar for $($source_type:ident)*) => {
        $(#[doc(hidden)] impl Mul<$source_type> for &$type {
            type Output = $type;
            paste::paste! {
                #[doc = "Documentation can be found at [`" $type "::mul`]."]
                fn mul(self, scalar: $source_type) -> Self::Output {
                    self.mul($bridge_type::from(scalar))
                }
            }
        }

        #[doc(hidden)]
        impl Mul<$source_type> for $type {
            type Output = $type;
            paste::paste! {
                #[doc = "Documentation can be found at [`" $type "::mul`]."]
                fn mul(self, scalar: $source_type) -> Self::Output {
                    self.mul($bridge_type::from(scalar))
                }
            }
        }

        #[doc(hidden)]
        impl Mul<&$type> for $source_type {
            type Output = $type;
            paste::paste! {
                #[doc = "Documentation can be found at [`" $type "::mul`]."]
                fn mul(self, matrix: &$type) -> Self::Output {
                    matrix.mul($bridge_type::from(self))
                }
            }
        }

        #[doc(hidden)]
        impl Mul<$type> for $source_type {
            type Output = $type;
            paste::paste! {
                #[doc = "Documentation can be found at [`" $type "::mul`]."]
                fn mul(self, matrix: $type) -> Self::Output {
                    matrix.mul($bridge_type::from(self))
                }
            }
        })*
    };
}

pub(crate) use implement_for_others;

/// Implements a specified trait for an owned input using the traits
/// implementation for a borrowed input.
/// Several traits are already supported:
///
/// - [`Evaluate`](crate::traits::Evaluate) with the signature
///     `($bridge_type, $output_type, $type, Evaluate)`
/// - [`SetCoefficient`](crate::traits::SetCoefficient) with the signature
///     `($bridge_type, $type, SetCoefficient)`
/// - [`SetEntry`](crate::traits::SetEntry) with the signature
///     `($bridge_type, $type, SetCoefficient)`
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
        #[doc(hidden)]
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
        #[doc(hidden)]
        impl SetCoefficient<$source_type> for $type {
            paste::paste! {
                #[doc = "Documentation can be found at [`" $type "::set_coeff`]."]
            fn set_coeff(
                &mut self,
                index: impl TryInto<i64> + Display,
                value: $source_type,
            ) -> Result<(), MathError> {
                self.set_coeff(index, &value)
            }
            }
        }
    };

    // [`SetEntry`] trait
    ($source_type:ident, $type:ident, SetEntry) => {
        #[doc(hidden)]
        impl SetEntry<$source_type> for $type {
            paste::paste! {
                #[doc = "Documentation can be found at [`" $type "::set_entry`]."]
            fn set_entry(
                &mut self,
                row: impl TryInto<i64> + Display,
                column: impl TryInto<i64> + Display,
                value: $source_type,
            ) -> Result<(), MathError> {
                self.set_entry(row, column, &value)
            }
            }
        }
    };
}

pub(crate) use implement_for_owned;

/// Implements a trait with an empty implementation for the specified types
/// and their references.
/// This macro can be used for empty traits or to use just the
/// default implementation of a trait.
///
/// # Examples
/// ```compile_fail
/// implement_empty_trait!(IntoZ for u8 u16 u32 u64 i8 i16 i32 i64);
/// ```
macro_rules! implement_empty_trait_owned_ref {
    ($trait_name:ident for $($type:ty)*) => {
      $(
        impl $trait_name for $type {}
        impl $trait_name for &$type {}
      )*
    };
}
pub(crate) use implement_empty_trait_owned_ref;
