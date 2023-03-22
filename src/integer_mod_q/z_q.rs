//! This module implements [`Zq`].
//!
//! This implementation uses [`fmpz_mod`](https://www.flintlib.org/doc/fmpz_mod.html)
//! from the [FLINT](https://flintlib.org/) library.
//! FLINT uses a `fmpz_mod_ctx_struct` to store functions and data used for
//! optimizing modulo operations.
//! This struct is wrapped in [`Modulus`](super::Modulus) for easy use.
//!
//! For **DEVELOPERS**: The [`PartialEq`] trait expects the [`Zq`] instance to be reduced.
//! Hence, apply `reduce` after every possible `value` change!

use super::Modulus;
use crate::integer::Z;

mod from;
mod reduce;
mod to_string;

#[derive(Debug, Clone, PartialEq, Eq)]
/// [`Zq`] is a type for integers of arbitrary length modulo `q`.
/// This means, integer in `[0..q)` (`0` inclusive, `q` exclusive).
///
/// # Example
/// ```
/// # use math::error::MathError;
/// use math::integer_mod_q::Zq;
///
/// let value = Zq::try_from((5, 10))?;
/// # Ok::<(), MathError>(())
/// ```
///
/// [`Zq`] represents an integer value in a modulus ring.
///
/// Attributes:
/// - `value`: holds a [`Z`] value for an integer value
/// - `modulus`: holds a [`Modulus`] above which the value is reduced
pub struct Zq {
    pub(crate) value: Z,
    pub(crate) modulus: Modulus,
}
