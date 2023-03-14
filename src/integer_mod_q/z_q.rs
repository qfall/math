//! This module implements [`Zq`].
//!
//! This implementation uses [`fmpz_mod`](https://www.flintlib.org/doc/fmpz_mod.html)
//! from the [FLINT](https://flintlib.org/) library.
//! FLINT uses a `fmpz_mod_ctx_struct` to store functions and data used for
//! optimizing modulo operations.
//! This struct is wrapped in [`Modulus`](super::Modulus) for easy use.

use flint_sys::fmpz::fmpz;

mod from;
mod ownership;

/// [`Zq`] is a type for integers of arbitrary length modulo `q`.
/// This means, integer in `[0..q[` (`0` inclusive, `q` exclusive).
///
/// # Example
/// ```
/// # use math::error::MathError;
/// use math::integer_mod_q::Zq;
///
/// let value = Zq::try_from((5, 10))?;
/// # Ok::<(), MathError>(())
/// ```
#[allow(dead_code)]
#[derive(Debug)]
/// [`Zq`] represents an integer value in a modulus ring.
///
/// Attributes:
/// - `value`: holds [FLINT](https://flintlib.org/)'s [struct](fmpz)
///     for an integer value
/// - `ctx`: holds [FLINT](https://flintlib.org/)'s [struct](fmpz_mod_ctx)
///     to specify a modulus
///
/// # Examples
pub struct Zq {
    pub(crate) value: fmpz,
    pub(crate) modulus: super::Modulus,
}
