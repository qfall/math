// Copyright © 2025 Niklas Siemer
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
    ($struct:ident, $attribute_name:meta, $attribute_type:ty) => {
        impl $struct {
            paste::paste! {
                #[doc = "Returns a mutable reference to the field `" $attribute_name "` of type [`" $attribute_type "`]."]
                ///
                /// **WARNING:** The returned struct is part of [`flint_sys`].
                /// Any changes to this object are unsafe and may introduce memory leaks.
                ///
                /// This function is a passthrough to enable users of this library to use [`flint_sys`]
                /// and with that [FLINT](https://flintlib.org/) functions that might not be covered in our library yet.
                /// If this is the case, please consider contributing to this open-source project
                /// by opening a Pull Request at [qfall_math](https://github.com/qfall/math)
                /// to provide this feature in the future.
                ///
                /// # Safety
                /// Any [`flint_sys`] struct and function is part of a FFI to the C-library `FLINT`.
                /// As `FLINT` is a C-library, it does not provide all memory safety features
                /// that Rust and our Wrapper provide.
                /// Thus, using functions of [`flint_sys`] can introduce memory leaks.
                pub unsafe fn [<get_ $attribute_type>](&mut self) -> &mut $attribute_type {
                    &mut self.$attribute_name
                }
            }
        }
    };
}

/// Implements a getter-function for a field in a modulus struct.
/// The Modulus-structs are wrapped in a reference counter. Thus, we require
/// a modified macro for them.
///
/// Input parameters:
/// - `struct`: the struct for which the getter is implemented (e.g. [`Z`](crate::integer::Z), ...).
/// - `attribute_name`: the name of the field (e.g. `value`, ...).
/// - `attribute_type`: the struct resp. type of the field (e.g. [`fmpz`](flint_sys::fmpz::fmpz))
///
///  Returns the Implementation code for the given $struct with the signature:
///     ```impl $struct```
macro_rules! unsafe_getter_mod {
    ($struct:ident, $attribute_name:meta, $attribute_type:ident) => {
        impl $struct {
            paste::paste! {
                #[doc = "Returns a mutable reference to the field `" $attribute_name "` of type [`" $attribute_type "`]."]
                ///
                /// **WARNING:** The returned struct is part of [`flint_sys`].
                /// Any changes to this object are unsafe and may introduce memory leaks.
                /// Please be aware that most moduli are shared across multiple instances and all
                /// modifications of this struct will affect any other instance with a reference to this object.
                ///
                /// This function is a passthrough to enable users of this library to use [`flint_sys`]
                /// and with that [FLINT](https://flintlib.org/) functions that might not be covered in our library yet.
                /// If this is the case, please consider contributing to this open-source project
                /// by opening a Pull Request at [qfall_math](https://github.com/qfall/math)
                /// to provide this feature in the future.
                ///
                /// # Safety
                /// Any [`flint_sys`] struct and function is part of a FFI to the C-library `FLINT`.
                /// As `FLINT` is a C-library, it does not provide all memory safety features
                /// that Rust and our Wrapper provide.
                /// Thus, using functions of [`flint_sys`] can introduce memory leaks.
                pub unsafe fn [<get_ $attribute_type>](&mut self) -> &mut $attribute_type {
                    std::rc::Rc::<$attribute_type>::get_mut(&mut self.$attribute_name).unwrap()
                }
            }
        }
    };
}

/// Implements a getter-function for a field in a struct, which itself has an
/// unsafe getter for an underlying struct.
///
/// Input parameters:
/// - `struct`: the struct for which the getter is implemented (e.g. [`Z`](crate::integer::Z), ...).
/// - `attribute_name`: the name of the field (e.g. `value`, ...).
/// - `function_name`: the name of the function, which is called to gather
///     the [`flint_sys`] struct (e.g. [crate::integer::Z::get_fmpz])
/// - `attribute_type`: the struct resp. type of the field (e.g. [`fmpz`](flint_sys::fmpz::fmpz))
///
///  Returns the Implementation code for the given $struct with the signature:
///     ```impl $struct```
macro_rules! unsafe_getter_indirect {
    ($struct:ident, $attribute_name:meta, $function_name:ident, $attribute_type:ty) => {
        impl $struct {
            paste::paste! {
                #[doc = "Returns a mutable reference to the underlying [`" $attribute_type "`] by calling `" $function_name "` on `" $attribute_name "`."]
                ///
                /// **WARNING:** The returned struct is part of [`flint_sys`].
                /// Any changes to this object are unsafe and may introduce memory leaks.
                /// In case you are calling this function to a modulus struct,
                /// please be aware that most moduli are shared across multiple instances and all
                /// modifications of this struct will affect any other instance with a reference to this object.
                ///
                /// This function is a passthrough to enable users of this library to use [`flint_sys`]
                /// and with that [FLINT](https://flintlib.org/) functions that might not be covered in our library yet.
                /// If this is the case, please consider contributing to this open-source project
                /// by opening a Pull Request at [qfall_math](https://github.com/qfall/math)
                /// to provide this feature in the future.
                ///
                /// # Safety
                /// Any [`flint_sys`] struct and function is part of a FFI to the C-library `FLINT`.
                /// As `FLINT` is a C-library, it does not provide all memory safety features
                /// that Rust and our Wrapper provide.
                /// Thus, using functions of [`flint_sys`] can introduce memory leaks.
                pub unsafe fn [<get_ $attribute_type>](&mut self) -> &mut $attribute_type {
                    self.$attribute_name.$function_name()
                }
            }
        }
    };
}

pub(crate) use unsafe_getter;
pub(crate) use unsafe_getter_indirect;
pub(crate) use unsafe_getter_mod;
