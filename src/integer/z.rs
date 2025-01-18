// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! `Z` is a type for integers with arbitrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use crate::macros::unsafe_passthrough::unsafe_getter;
use flint_sys::fmpz::fmpz;

mod arithmetic;
mod cmp;
mod default;
mod distance;
pub(crate) mod fmpz_helpers;
mod from;
mod gcd;
mod hash;
mod lcm;
mod ownership;
mod properties;
mod sample;
mod serialize;
mod to_string;

/// [`Z`] is an arbitrary integer value.
///
/// Attributes:
/// - `value`: holds [FLINT](https://flintlib.org/)'s [struct](fmpz)
///     for an integer value
///
/// # Implicit Typecasting
/// Most of our functions take as input values of type [`Into<Z>`].
/// These capture all types that can be turned into a [`Z`] value.
/// The types are [`Z`],[`Modulus`](crate::integer_mod_q::Modulus), [`i8`],
/// [`i16`],[`i32`],[`i64`],[`u8`],[`u16`],[`u32`],[`u64`] and the
/// references of all of these types. These types are then implicitly casted to a [`Z`]
/// before the desired action is performed.
///
/// # Examples
/// ```
/// use qfall_math::integer::Z;
/// use std::str::FromStr;
///
/// // instantiations
/// let a = Z::from_str("-876543")?;
/// let b = Z::from(i64::MIN);
/// let zero = Z::default();
///
/// // arithmetics
/// let _ = &a * b.clone();
/// let _ = &b - zero;
///
/// // comparison
/// assert_ne!(b, a);
///
/// // to_string incl. (de-)serialization
/// assert_eq!("-876543", &a.to_string());
/// assert_eq!(
///     "{\"value\":\"-876543\"}",
///     serde_json::to_string(&a).unwrap()
/// );
/// # Ok::<(), qfall_math::error::MathError>(())
/// ```
#[derive(Debug)]
pub struct Z {
    pub(crate) value: fmpz,
}

unsafe_getter!(Z, value, fmpz);

#[cfg(test)]
mod test_get_value {
    use super::Z;

    /// Checks availability of the getter for [`Z::value`]
    /// and its ability to be modified.
    #[test]
    #[allow(unused_mut)]
    fn availability_and_modification() {
        let mut integer = Z::from(1);

        let mut fmpz_int = unsafe { integer.get_value() };

        fmpz_int.0 = 2;

        assert_eq!(Z::from(2), integer);
    }
}
