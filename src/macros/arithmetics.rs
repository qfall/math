// Copyright © 2023 Phil Milewski
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module implements macros which are used to implement arithmetic traits for data types.

use crate::integer_mod_q::Zq;

/// Implements the [`*trait*`] for [`*type*`] using the [`*trait*`] for
/// [`&*type*`].
///
/// Parameters:
/// - `trait`: the trait that is implemented (e.g. [`Add`], [`Sub`], ...).
/// - `trait_function`: the function the trait implements
/// (e.g. add for [`Add`], ...).
/// - `type`: the type the trait is implemented for (e.g. [`Z`], [`Q`])
/// - `other_type`: the type the second part of the computation.
/// - `output_type`: the type of the result.
///
/// Returns the owned Implementation code for the [`*trait*`]
/// trait with the signature:
///
/// ```impl *trait<*other_type*>* for *type*```
macro_rules! arithmetic_trait_borrowed_to_owned {
    ($trait:ident, $trait_function:ident, $type:ident, $other_type:ident, $output_type:ident) => {
        #[doc(hidden)]
        impl $trait<$other_type> for $type {
            type Output = $output_type;

            paste::paste! {
                #[doc = "Documentation at [`" $output_type "::" $trait_function "`]."]
                fn $trait_function(self, other: $other_type) -> Self::Output {
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
/// - `other_type`: the type the second part of the computation.
/// - `output_type`: the type of the result.
///
/// Returns the mixed owned and borrowed Implementation code for the
/// [`*trait*`] trait with the signatures:
///
/// ```impl *trait*<&*other_type*> for *type*```
///
/// ```impl *trait*<*other_type*> for &*type*```
macro_rules! arithmetic_trait_mixed_borrowed_owned {
    ($trait:ident, $trait_function:ident, $type:ident, $other_type:ident, $output_type:ident) => {
        #[doc(hidden)]
        impl $trait<$other_type> for &$type {
            type Output = $output_type;
            paste::paste! {

                #[doc = "Documentation at [`" $output_type "::" $trait_function "`]."]
                fn $trait_function(self, other: $other_type) -> Self::Output {
                    self.$trait_function(&other)
                }
            }
        }

        #[doc(hidden)]
        impl $trait<&$other_type> for $type {
            type Output = $output_type;
            paste::paste! {
                #[doc = "Documentation at [`" $output_type "::" $trait_function "`]."]
                fn $trait_function(self, other: &$other_type) -> Self::Output {
                    (&self).$trait_function(other)
                }
            }
        }
    };
}

pub(crate) use arithmetic_trait_mixed_borrowed_owned;

/// Implements the [`*trait*`] for owned [`*type*`] on borrowed [`*type*`] and
/// reverse using the [`*trait*`] for [`&*type*`].
///
/// Parameters:
/// - `trait`: the trait that is implemented (e.g. [`Add`], [`Sub`], ...).
/// - `trait_function`: the function the trait implements
/// (e.g. add for [`Add`], ...).
/// - `output_type`: one type that is part of the computation and it is the
/// result type (e.g. [`Z`], [`Q`], ...).
/// - `other_type*`: the other types that is part of the computation
/// (e.g. [`Z`], [`Q`], ...).
///
/// Returns the owned and borrowed Implementation code for the
/// [`*trait*`] trait with the signatures:
/// ```impl *trait*<&*other_type*> for &*output_type*```
///
/// ```impl *trait*<*other_type*> for *output_type*```
///
/// ```impl *trait*<&*other_type*> for *output_type*```
///
/// ```impl *trait*<*other_type*> for &*output_type*```
///
/// ```impl *trait*<&*output_type*> for &*other_type*```
///
/// ```impl *trait*<*output_type*> for *other_type*```
///
/// ```impl *trait*<&*output_type*> for *other_type*```
///
/// ```impl *trait*<*output_type*> for &*other_type*```
macro_rules! arithmetic_between_types {
    ($trait:ident, $trait_function:ident, $type:ident, $output_type:ident, $($other_type:ident)*) => {
        $(
            // #[doc(hidden)] //maybe also hide. current state: one doc per type
            impl $trait<&$other_type> for &$type {
                type Output = $output_type;
                paste::paste! {
                    #[doc = "Documentation at [`" $type "::" $trait_function "`]."]
                    fn $trait_function(self, other: &$other_type) -> Self::Output {
                    self.$trait_function($type::from(*other))
                    }
                }
            }

            arithmetic_trait_borrowed_to_owned!($trait,$trait_function,$type,$other_type,$output_type);
            arithmetic_trait_mixed_borrowed_owned!($trait,$trait_function,$type,$other_type,$output_type);

            #[doc(hidden)]
            impl $trait<&$type> for &$other_type {
                type Output = $output_type;
                paste::paste! {
                    #[doc = "Documentation at [`" $type "::" $trait_function "`]."]
                    fn $trait_function(self, other: &$type) -> Self::Output {
                    other.$trait_function($type::from(*self))
                    }
                }
            }
            arithmetic_trait_borrowed_to_owned!($trait,$trait_function,$other_type,$type,$output_type);
            arithmetic_trait_mixed_borrowed_owned!($trait,$trait_function,$other_type,$type,$output_type);

        )*
    };
}

pub(crate) use arithmetic_between_types;

/// Implements the [`*trait*`] for [`*type*`] using the [`*trait*`] for
/// [`&*type*`].
///
/// Parameters:
/// - `trait`: the trait that is implemented (e.g. [`Add`], [`Sub`], ...).
/// - `trait_function`: the function the trait implements
/// (e.g. add for [`Add`], ...).
/// - `type`: the type the trait is implemented for (e.g. [`Z`], [`Q`])
/// - `other_type`: the type the second part of the computation.
/// - `output_type`: the type of the result.
///
/// Returns the owned Implementation code for the [`*trait*`]
/// trait with the signature:
///
/// ```impl *trait<*other_type*>* for *type*```
macro_rules! arithmetic_trait_reverse {
    ($trait:ident, $trait_function:ident, $type:ident, $other_type:ident, $output_type:ident) => {
        #[doc(hidden)]
        impl $trait<&$other_type> for &$type {
            type Output = $output_type;

            paste::paste! {
                #[doc = "Documentation at [`" $output_type "::" $trait_function "`]."]
                fn $trait_function(self, other: &$other_type) -> Self::Output {
                    other.$trait_function(self)
                }
            }
        }
    };
}

pub(crate) use arithmetic_trait_reverse;

/// Implements the [`*trait*`] for owned [`Zq`] on borrowed [`*type*`] and
/// reverse using the [`*trait*`] for [`Zq`].
///
/// Parameters:
/// - `trait`: the trait that is implemented (e.g. [`Add`], [`Sub`], ...).
/// - `trait_function`: the function the trait implements
/// (e.g. add for [`Add`], ...).
/// - `output_type`: one type that is part of the computation and it is the
/// result type (e.g. [`Z`], [`Q`], ...).
/// - `other_type*`: the other types that is part of the computation
/// (e.g. [`Z`], [`Q`], ...).
///
/// Returns the owned and borrowed Implementation code for the
/// [`*trait*`] trait with the signatures:
/// ```impl *trait*<&*other_type*> for &*output_type*```
///
/// ```impl *trait*<*other_type*> for *output_type*```
///
/// ```impl *trait*<&*other_type*> for *output_type*```
///
/// ```impl *trait*<*other_type*> for &*output_type*```
///
/// ```impl *trait*<&*output_type*> for &*other_type*```
///
/// ```impl *trait*<*output_type*> for *other_type*```
///
/// ```impl *trait*<&*output_type*> for *other_type*```
///
/// ```impl *trait*<*output_type*> for &*other_type*```
macro_rules! arithmetic_between_types_zq {
    ($trait:ident, $trait_function:ident, $output_type:ident, $($other_type:ident)*) => {
        $(
            // #[doc(hidden)] //maybe also hide. current state: one doc per type
            impl $trait<&$other_type> for &Zq {
                type Output = $output_type;
                paste::paste! {
                    #[doc = "Documentation at [`Zq::" $trait_function "`]."]
                    fn $trait_function(self, other: &$other_type) -> Self::Output {
                    self.$trait_function(Zq::try_from_z_z(Z::from(*other),self.get_modulus()))
                    }
                }
            }

            arithmetic_trait_borrowed_to_owned!($trait,$trait_function,Zq,$other_type,$output_type);
            arithmetic_trait_mixed_borrowed_owned!($trait,$trait_function,Zq,$other_type,$output_type);

            #[doc(hidden)]
            impl $trait<&$type> for &$other_type {
                type Output = $output_type;
                paste::paste! {
                    #[doc = "Documentation at [`" $type "::" $trait_function "`]."]
                    fn $trait_function(self, other: &$type) -> Self::Output {
                    other.$trait_function(Zq::try_from_z_z(Z::from(*self),other.get_modulus()))
                    }
                }
            }
            arithmetic_trait_borrowed_to_owned!($trait,$trait_function,$other_type,Zq,$output_type);
            arithmetic_trait_mixed_borrowed_owned!($trait,$trait_function,$other_type,Zq,$output_type);

        )*
    };
}

pub(crate) use arithmetic_between_types_zq;
