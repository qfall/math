//! `Zq` is a type for integers of arbitrary length modulo `q` with `q` fitting in a single machine word (usually 64 bit).
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz::fmpz;

mod from;

#[allow(dead_code)]
#[derive(Debug)]
pub struct Zq {
    pub(crate) value: fmpz,
    pub(crate) modulus: super::Modulus,
}
