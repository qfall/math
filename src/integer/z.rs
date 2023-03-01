//! `Z` is a type for integers with arbritrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz::fmpz;

mod cmp;
mod default;
mod from;

#[allow(dead_code)]
#[derive(Debug)]
pub struct Z {
    pub(crate) value: fmpz,
}
