//! `Zq` is a type for arbritrary integers modulo `q` with `q` fitting in a single machine word.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz::fmpz;
use flint_sys::fmpz_mod::fmpz_mod_ctx;

#[derive(Debug)]
pub struct Zq {
    value: fmpz,
    ctx: fmpz_mod_ctx,
}
