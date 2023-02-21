//! `Z` is a type for arbritrary integers.
//! This implementation uses the [Flint](https://flintlib.org/) library.

use flint_sys::fmpz::fmpz;

#[derive(Debug)]
pub struct Z {
    value: fmpz,
}
