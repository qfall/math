//! [Modulus] is a type of a positive nonnegative integer that is used in order to do modulus operations.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_mod::fmpz_mod_ctx;

#[doc(hidden)]
pub mod from;

#[derive(Debug)]
pub struct Modulus {
    pub(crate) modulus: fmpz_mod_ctx,
}
