// Copyright 2026 Jan Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module implements macros which are used to provide an unseeded and a
//! seeded variant of a function from one implementation and one doc-comment.

/// Takes a function `name` whose last parameter is an optional seed `seed: Option<[u8; 32]>`
/// and implements
/// - the function itself as `name_optionally_seeded` with the provided visibility,
/// - the public function `name`, which has the same parameters except for `seed`
///   and forwards `None` as seed, and
/// - the public function `name_seeded`, which takes `seed: [u8; 32]` as its last parameter
///   and forwards `Some(seed)`.
///
/// All three functions share the provided doc-comment. Every doc line (and any other attribute)
/// is added to all three functions, except for the doc lines preceded by
/// - `#[unseeded]`, which are only added to `name`,
/// - `#[seeded]`, which are only added to `name_seeded`, and
/// - `#[optionally_seeded]`, which are only added to `name_optionally_seeded`.
///
/// Calls in examples should be marked with `#[unseeded]` or `#[seeded]`,
/// as doc-tests are also run for non-public functions, but can only access public ones.
///
/// As the input is valid Rust syntax, `rustfmt` formats the provided function as usual
/// if the macro is called with parentheses, i.e. `seedable_function!( ... );`.
///
/// Input parameters:
/// - the shared doc-comment possibly containing marked doc lines
/// - the function `name` with `seed: Option<[u8; 32]>` as its last parameter
///
/// The function may also be a method taking `&self` as its first parameter.
///
/// Returns the code of all three functions, i.e. it needs to be called inside an `impl` block.
///
/// # Examples
/// ```compile_fail
/// impl MatZq {
///     seedable_function!(
///         /// Samples a matrix.
///         ///
///         /// Parameters:
///         /// - `num_rows`: specifies the number of rows
///         #[seeded]
///         /// - `seed`: specifies the 256-bit seed of the PRNG used for sampling
///         #[optionally_seeded]
///         /// - `seed`: specifies an optional 256-bit seed of the PRNG used for sampling
///         pub(crate) fn sample(num_rows: i64, seed: Option<[u8; 32]>) -> MatZq {
///             ...
///         }
///     );
/// }
/// ```
macro_rules! seedable_function {
    // A doc line preceded by `#[unseeded]` is only added to the unseeded function.
    (@attrs [$($unseeded:tt)*] [$($seeded:tt)*] [$($optional:tt)*] #[unseeded] #[$attr:meta] $($rest:tt)*) => {
        $crate::macros::seeded::seedable_function!(
            @attrs [$($unseeded)* #[$attr]] [$($seeded)*] [$($optional)*] $($rest)*
        );
    };
    // A doc line preceded by `#[seeded]` is only added to the seeded function.
    (@attrs [$($unseeded:tt)*] [$($seeded:tt)*] [$($optional:tt)*] #[seeded] #[$attr:meta] $($rest:tt)*) => {
        $crate::macros::seeded::seedable_function!(
            @attrs [$($unseeded)*] [$($seeded)* #[$attr]] [$($optional)*] $($rest)*
        );
    };
    // A doc line preceded by `#[optionally_seeded]` is only added to the optionally seeded function.
    (@attrs [$($unseeded:tt)*] [$($seeded:tt)*] [$($optional:tt)*] #[optionally_seeded] #[$attr:meta] $($rest:tt)*) => {
        $crate::macros::seeded::seedable_function!(
            @attrs [$($unseeded)*] [$($seeded)*] [$($optional)* #[$attr]] $($rest)*
        );
    };
    // Any other doc line or attribute is added to all functions.
    (@attrs [$($unseeded:tt)*] [$($seeded:tt)*] [$($optional:tt)*] #[$attr:meta] $($rest:tt)*) => {
        $crate::macros::seeded::seedable_function!(
            @attrs [$($unseeded)* #[$attr]] [$($seeded)* #[$attr]] [$($optional)* #[$attr]] $($rest)*
        );
    };
    // Once all attributes are sorted, the parameters of a method taking `&self` are processed.
    (
        @attrs $unseeded:tt $seeded:tt $optional:tt
        $vis:vis fn $name:ident (&$receiver:ident, $($params:tt)*) -> $ret:ty $body:block
    ) => {
        $crate::macros::seeded::seedable_function!(
            @params $unseeded $seeded $optional ($vis) $name $ret $body
            [&$receiver,] [$receiver.] [] $($params)*
        );
    };
    // Once all attributes are sorted, the parameters of an associated function are processed.
    (
        @attrs $unseeded:tt $seeded:tt $optional:tt
        $vis:vis fn $name:ident ($($params:tt)*) -> $ret:ty $body:block
    ) => {
        $crate::macros::seeded::seedable_function!(
            @params $unseeded $seeded $optional ($vis) $name $ret $body
            [] [Self::] [] $($params)*
        );
    };
    // The last parameter is the optional seed, i.e. all functions are generated.
    (
        @params [$($unseeded:tt)*] [$($seeded:tt)*] [$($optional:tt)*]
        ($vis:vis) $name:ident $ret:ty $body:block
        [$($receiver:tt)*] [$($call:tt)*]
        [$($arg:ident : $arg_type:ty,)*]
        $seed:ident : Option<[u8; 32]> $(,)?
    ) => {
        paste::paste! {
            $($optional)*
            $vis fn [<$name _optionally_seeded>](
                $($receiver)*
                $($arg: $arg_type,)*
                $seed: Option<[u8; 32]>,
            ) -> $ret $body

            $($unseeded)*
            pub fn $name($($receiver)* $($arg: $arg_type),*) -> $ret {
                $($call)*[<$name _optionally_seeded>]($($arg,)* None)
            }

            $($seeded)*
            pub fn [<$name _seeded>]($($receiver)* $($arg: $arg_type,)* $seed: [u8; 32]) -> $ret {
                $($call)*[<$name _optionally_seeded>]($($arg,)* Some($seed))
            }
        }
    };
    // Any other parameter is collected one at a time, as `macro_rules!` can not
    // match all but the last parameter in one go. `$vis` is wrapped in parentheses,
    // as it may be empty.
    (
        @params $unseeded:tt $seeded:tt $optional:tt $vis:tt $name:tt $ret:tt $body:tt
        $receiver:tt $call:tt [$($collected:tt)*] $arg:ident : $arg_type:ty, $($rest:tt)*
    ) => {
        $crate::macros::seeded::seedable_function!(
            @params $unseeded $seeded $optional $vis $name $ret $body
            $receiver $call [$($collected)* $arg: $arg_type,] $($rest)*
        );
    };
    ($($input:tt)*) => {
        $crate::macros::seeded::seedable_function!(@attrs [] [] [] $($input)*);
    };
}

pub(crate) use seedable_function;
