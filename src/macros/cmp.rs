// Copyright © 2025 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module implements macros which are used to implement the [`PartialEq`] and [`PartialOrd`] trait for data types.

/// Implements the [`PartialEq`] trait for mixtures of owned and borrowed values. It requires an already written
/// implementation of the trait between the owned values.
///
/// Input parameters:
/// - `type`: the type for which the trait is implemented.
/// - `source_type`: the value that should be compared.
///
///  Returns the Implementation code for the [`PartialEq`] Trait with the signature:
///     ```impl PartialEq<*source_type*> for *type*```
macro_rules! eq_mixed_borrowed_owned {
    ($type:ident, $source_type:ident) => {
        #[doc(hidden)]
        impl PartialEq<$source_type> for &$type {
            paste::paste! {
                #[doc = "Documentation can be found at [`" $type "::partialEq`]."]
                fn eq(&self, other: &$source_type) -> bool {
                    self.eq(&other)
                }
            }
        }

        #[doc(hidden)]
        impl PartialEq<&$source_type> for $type {
            paste::paste! {
                #[doc = "Documentation can be found at [`" $type "::PartialEq`]."]
                fn eq(&self, other: &&$source_type) -> bool {
                    (&self).eq(other)
                }
            }
        }
    };
}

pub(crate) use eq_mixed_borrowed_owned;
