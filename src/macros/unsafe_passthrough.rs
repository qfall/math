// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module implements macros which are used to implement functions,
//! which provide public access to [`flint_sys`] structs and require to be unsafe.

/// Implements a getter-function for a field in a struct.
///
/// Input parameters:
/// - `struct`: the struct for which the getter is implemented (e.g. [`Z`](crate::integer::Z), ...).
/// - `attribute_name`: the name of the field (e.g. `value`, ...).
/// - `attribute_type`: the struct resp. type of the field (e.g. [`fmpz`](flint_sys::fmpz::fmpz))
///
///  Returns the Implementation code for the given $struct with the signature:
///     ```impl $struct```
macro_rules! unsafe_getter {
    ($struct:ident, $attribute_name:meta, $attribute_type:ident) => {
        impl $struct {
            paste::paste! {
                /// Returns a mutable reference to the field `" $attribute_name "` of type [`" $attribute_type "`].
                ///
                /// **WARNING:** The returned struct is part of [`flint_sys`].
                /// Any changes to this object are unsafe and may introduce memory leaks.
                pub unsafe fn [<get_ $attribute_name>](&mut self) -> &mut $attribute_type {
                    &mut self.$attribute_name
                }
            }
        }
    };
}

pub(crate) use unsafe_getter;
