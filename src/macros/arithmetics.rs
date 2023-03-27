// Copyright © 2023 Phil Milewski, Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module implements macros which are used to implement arithmetic traits for data types.

/// Implements the [`*trait*`] for [`*type*`] using the [`*trait*`] for
/// [`&*type*`].
///
/// Parameters:
/// - `trait`: the trait that is implemented (e.g. [`Add`], [`Sub`], ...).
/// - `trait_function`: the function the trait implements
/// (e.g. add for [`Add`], ...).
/// - `type`: the type the trait is implemented for (e.g. [`Z`], [`Q`])
///
/// Returns the owned Implementation code for the [`*trait*`]
/// trait with the signature:
///
/// ```impl *trait* for *type*```
macro_rules! arithmetic_trait_borrowed_to_owned {
    ($trait:ident, $trait_function:ident, $type:ident) => {
        impl $trait for $type {
            type Output = $type;

            paste::paste! {
                #[doc = "Documentation at [`" $type "::" $trait_function "`]."]
                fn $trait_function(self, other: Self) -> Self::Output {
                    (&self).$trait_function(&other)
                }
            }
        }
    };
}

pub(crate) use arithmetic_trait_borrowed_to_owned;

/// Implements the [`*trait*`] for owned [`*type*`] on borrowed [`*type*`] and
/// reverse using the [`*trait*`] for [`&*type*`].
///
/// Parameters:
/// - `trait`: the trait that is implemented (e.g. [`Add`], [`Sub`], ...).
/// - `trait_function`: the function the trait implements
/// (e.g. add for [`Add`], ...).
/// - `type`: the type the trait is implemented for (e.g. [`Z`], [`Q`], ...).
///
/// Returns the mixed owned and borrowed Implementation code for the
/// [`*trait*`] trait with the signatures:
///
/// ```impl *trait*<&*type*> for *type*```
///
/// ```impl *trait*<*type*> for &*type*```
macro_rules! arithmetic_trait_mixed_borrowed_owned {
    ($trait:ident, $trait_function:ident, $type:ident) => {
        impl $trait<$type> for &$type {
            type Output = $type;
            paste::paste! {
                #[doc = "Documentation at [`" $type "::" $trait_function "`]."]
                fn $trait_function(self, other: $type) -> Self::Output {
                    self.$trait_function(&other)
                }
            }
        }

        impl $trait<&$type> for $type {
            type Output = $type;
            paste::paste! {
                #[doc = "Documentation at [`" $type "::" $trait_function "`]."]
                fn $trait_function(self, other: &Self) -> Self::Output {
                    (&self).$trait_function(other)
                }
            }
        }
    };
}

pub(crate) use arithmetic_trait_mixed_borrowed_owned;

/// Implements the [`*trait*`] for [`*type*<*other_type*>`] using the
/// [`*trait<*other_type*>*`] for [`&*type*`].
///
/// Parameters:
/// - `trait`: the trait that is implemented (e.g. [`Add`], [`Sub`], ...).
/// - `trait_function`: the function the trait implements
/// (e.g. add for [`Add`], ...).
/// - `type`: the type the trait is implemented for (e.g. [`Z`], [`Q`])
/// - `other_type`: the other type that the arithm. operation is applied with
/// - `out_type`: the type that the `Output` should have
///
/// Returns the owned Implementation code for the [`*trait*`]
/// trait with the signature:
///
/// ```impl *trait*<*other_type*> for *type*```
macro_rules! arithmetic_trait_cross_types_borrowed_to_owned {
    ($trait:ident, $trait_function:ident, $type:ident, $other_type:ident, $out_type:ident) => {
        impl $trait<$other_type> for $type {
            type Output = $out_type;

            paste::paste! {
                #[doc = "Documentation at [`" $type "::" $trait_function "`]."]
                fn $trait_function(self, other: $other_type) -> Self::Output {
                    (&self).$trait_function(&other)
                }
            }
        }
    };
}

pub(crate) use arithmetic_trait_cross_types_borrowed_to_owned;

/// Implements the [`*trait*<*other_type*>`] for owned [`*type*`] on borrowed [`*type*`] and
/// reverse using the [`*trait*<*other_type*>`] for [`&*type*`].
///
/// Parameters:
/// - `trait`: the trait that is implemented (e.g. [`Add`], [`Sub`], ...).
/// - `trait_function`: the function the trait implements
/// (e.g. add for [`Add`], ...).
/// - `type`: the type the trait is implemented for (e.g. [`Z`], [`Q`], ...).
/// - `other_type`: the other type that the arithm. operation is applied with
/// - `out_type`: the type that the `Output` should have
///
/// Returns the mixed owned and borrowed Implementation code for the
/// [`*trait*`] trait with the signatures:
///
/// ```impl *trait*<&*other_type*> for *type*```
///
/// ```impl *trait*<*other_type*> for &*type*```
macro_rules! arithmetic_trait_cross_types_mixed_borrowed_owned {
    ($trait:ident, $trait_function:ident, $type:ident, $other_type:ident, $out_type:ident) => {
        impl $trait<$other_type> for &$type {
            type Output = $out_type;
            paste::paste! {
                #[doc = "Documentation at [`" $type "::" $trait_function "`]."]
                fn $trait_function(self, other: $other_type) -> Self::Output {
                    self.$trait_function(&other)
                }
            }
        }

        impl $trait<&$other_type> for $type {
            type Output = $out_type;
            paste::paste! {
                #[doc = "Documentation at [`" $type "::" $trait_function "`]."]
                fn $trait_function(self, other: &$other_type) -> Self::Output {
                    (&self).$trait_function(other)
                }
            }
        }
    };
}

pub(crate) use arithmetic_trait_cross_types_mixed_borrowed_owned;
