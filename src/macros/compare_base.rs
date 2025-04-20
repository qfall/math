// Copyright © 2025 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module implements macros which are used to implement the compare base trait for data types.

/// Implements the `CompareBase` trait for `*type*` and `&*type*`.
///
/// Parameters:
/// - `type`: the type the trait is implemented for
///   (e.g. [`Zq`](crate::integer_mod_q::Zq)
/// - `source_type`: tthe type for which the basic comparison is implemented
/// - `get_mod_expr`: the expression that returns the modulus of the type for self
///
/// Returns the trait implementations for the provided types just comparing the modulus
/// of both provided inputs.
///
/// # Example
/// ```compile_fail
/// compare_base_impl!(Zq, Zq, |s: &Zq| s.get_mod());
/// ```
macro_rules! compare_base_impl {
    ($type:ident, $source_type:ty, $get_mod_expr:expr) => {
        impl CompareBase<$source_type> for $type {
            paste::paste! {
                /// Compares the moduli of the two elements.
                ///
                /// Parameters:
                /// - `other`: The other object whose base is compared to `self`
                ///
                /// Returns true if the moduli match and false otherwise.
                fn compare_base(&self, other: &$source_type) -> bool {
                    $get_mod_expr(self) == other.get_mod()
                }

                /// Returns an error that gives a small explanation of how the moduli are
                /// incomparable.
                ///
                /// Parameters:
                /// - `other`: The other object whose base is compared to `self`
                ///
                /// Returns a MathError of type [`MismatchingModulus`](MathError::MismatchingModulus).
                fn call_compare_base_error(&self, other: &$source_type) -> Option<MathError> {
                    Some(MathError::MismatchingModulus(format!(
                        "The moduli of the elements mismatch. One of them is {} and the other is {}.
    The desired operation is not defined and an error is returned.",
                        $get_mod_expr(self),
                        other.get_mod()
                    )))
                }
            }
        }

        impl CompareBase<&$source_type> for $type {
            paste::paste! {
                /// Compares the moduli of the two elements.
                ///
                /// Parameters:
                /// - `other`: The other object whose base is compared to `self`
                ///
                /// Returns true if the moduli match and false otherwise.
                fn compare_base(&self, other: &&$source_type) -> bool {
                    $get_mod_expr(self) == other.get_mod()
                }

                /// Returns an error that gives a small explanation of how the moduli are
                /// incomparable.
                ///
                /// Parameters:
                /// - `other`: The other object whose base is compared to `self`
                ///
                /// Returns a MathError of type [`MismatchingModulus`](MathError::MismatchingModulus).
                fn call_compare_base_error(&self, other: &&$source_type) -> Option<MathError> {
                    Some(MathError::MismatchingModulus(format!(
                        "The moduli of the elements mismatch. One of them is {} and the other is {}.
    The desired operation is not defined and an error is returned.",
                        $get_mod_expr(self),
                        other.get_mod()
                    )))
                }
            }
        }
    };
}

/// Implements the `CompareBase` trait for `*type*`, using modulo comparison.
///
/// Parameters:
/// - `type`: the type the trait is implemented for
///   (e.g. [`Zq`](crate::integer_mod_q::Zq)
/// - `source_type`: a list of types for which the basic comparison is implemented
///
/// Returns the trait implementations for the provided types just comparing the modulus
/// of both provided inputs
///
/// # Example
/// ```compile_fail
/// compare_base_get_mod!(Zq for Zq);
/// ```
macro_rules! compare_base_get_mod {
    ($type:ident for $($source_type:ident)*) => {
        $(
            compare_base_impl!($type, $source_type, |s: &$type| s.get_mod());
        )*
    };
}

/// Implements the `CompareBase` trait for `*type*`, using modulo comparison.
/// Here, self and other have different moduli types, and for self, we specifically
/// return the integer modulus possibly contained in polynomial moduli.
///
/// Parameters:
/// - `type`: the type the trait is implemented for
///   (e.g. [`PolynomialRingZq`](crate::integer_mod_q::PolynomialRingZq)
/// - `source_type`: a list of types for which the basic comparison is implemented
///
/// Returns the trait implementations for the provided types just comparing the modulus
/// of both provided inputs
///
/// # Example
/// ```compile_fail
/// compare_base_get_mod_get_q!(PolynomialRingZq for Zq);
/// ```
macro_rules! compare_base_get_mod_get_q {
    ($type:ident for $($source_type:ident)*) => {
        $(
            compare_base_impl!($type, $source_type, |s: &$type| s.get_mod().get_q());
        )*
    };
}

/// Implements the default implementation of the `CompareBase` trait, just returning `true`
/// and no error.
///
/// Parameters:
/// - `type`: the type the trait is implemented for
///   (e.g. [`PolynomialRingZq`](crate::integer_mod_q::PolynomialRingZq)
/// - `source_type`: a list of types for which the basic comparison is implemented
///
/// Returns the default trait implementations for the provided types.
///
/// # Example
/// ```compile_fail
/// compare_base_get_mod_get_q!(Zq for Z);
/// ```
macro_rules! compare_base_default {
    ($type:ident for $($source_type:ident)*) => {
        $(
            impl CompareBase<$source_type> for $type {}
            impl CompareBase<&$source_type> for $type {}
        )*
    };
}

pub(crate) use compare_base_default;
pub(crate) use compare_base_get_mod;
pub(crate) use compare_base_get_mod_get_q;
pub(crate) use compare_base_impl;
