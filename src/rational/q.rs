//! `Q` is a type for rationals of arbritrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

mod default;

use flint_sys::fmpq::fmpq;

#[allow(dead_code)]
#[derive(Debug)]
pub struct Q {
    pub(crate) value: fmpq,
}
