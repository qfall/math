//! `Q` is a type for arbritrary rationals.
//! This implementation uses the [Flint](https://flintlib.org/) library.

use flint_sys::fmpq::fmpq;

#[derive(Debug)]
pub struct Q {
    value: fmpq,
}
