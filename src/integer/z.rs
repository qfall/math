//! `Z` is a type for integers with arbritrary length.
//! This implementation uses the [Flint](https://flintlib.org/) library.

use flint_sys::fmpz::fmpz;

#[derive(Debug)]
pub struct Z {
    pub(crate) value: fmpz,
}
