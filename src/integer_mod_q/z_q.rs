//! `Zq` is a type for integers of arbitrary length modulo `q` with `q` fitting in a single machine word (usually 64 bit).
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz::fmpz;
use flint_sys::fmpz_mod::fmpz_mod_ctx;

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
    pub(crate) ctx: fmpz_mod_ctx,
}
