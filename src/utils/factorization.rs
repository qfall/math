// Copyright © 2023 Marcel Luca Schmidt
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains the type [`Factorization`], which is a factorized
//! (or partly factorized) representation of integers with arbitrary length.

use flint_sys::fmpz_factor::fmpz_factor_struct;

mod default;
mod from;
mod ownership;
mod refine;
mod to_string;

/// [`Factorization`] represents any integer value as its factorization or
/// partly factorization.
///
/// Attributes:
/// - `factors`: holds [FLINT](https://flintlib.org/)'s [struct](fmpz_factor_struct)
///     for a factorization of an integer value
///
/// # Implicit Typecasting
/// Most of our functions take as input values of type Integer.
/// These capture all types that can be turned into a [`Z`](crate::integer::Z) value.
/// The types are [`Z`](crate::integer::Z), [`Modulus`](crate::integer_mod_q::Modulus), [`i8`],
/// [`i16`], [`i32`], [`i64`], [`u8`], [`u16`], [`u32`], [`u64`] and the
/// references of all of these types. These types are then implicitly casted to a
/// [`Z`](crate::integer::Z) before the desired action is performed.
///
/// # Examples
/// ```
/// use qfall_math::utils::Factorization;
/// use qfall_math::integer::Z;
/// use std::str::FromStr;
/// use core::fmt;
///
/// // instantiations
/// let a = Z::from(1200);
/// let b = Z::from(20);
///
/// let fac1 = Factorization::from(&a);
/// let mut fac2 = Factorization::from((&a, &b));
///
/// // refinement
/// fac2.refine();
///
/// // to_string
/// assert_eq!("[(3, 1), (20, 3)]", &fac2.to_string());
/// ```
#[derive(Debug)]
pub struct Factorization {
    factors: fmpz_factor_struct,
}
