//! `Zq` is a type for integers of arbitrary length modulo `q` with `q` fitting in a single machine word (usualy 64 bit).
//! This implementation uses the [Flint](https://flintlib.org/) library.

use flint_sys::fmpz::fmpz;
use flint_sys::fmpz_mod::fmpz_mod_ctx;

#[derive(Debug)]
pub struct Zq {
    pub(crate) value: fmpz,
    pub(crate) ctx: fmpz_mod_ctx,
}
