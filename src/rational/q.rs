//! `Q` is a type for rationals of arbritrary length.
//! This implementation uses the [Flint](https://flintlib.org/) library.

use flint_sys::fmpq::fmpq;

#[derive(Debug)]
pub struct Q {
    pub(crate) value: fmpq,
}
