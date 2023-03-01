//! [`Modulus`] is a type of a positive non-zero integer that is used in order to
//! do modulus operations. The modulus type itself is also used for
//! optimizations.
//!
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_mod::fmpz_mod_ctx;

pub mod from;
pub mod to_string;

#[derive(Debug)]
/// [`Modulus`] is a type of a positive non-zero integer that is used
/// to do modulus operations.
///
// Attributes:
// - `modulus`: holds the value of the modulus
//
/// # Example
/// ```rust
/// use math::integer_mod_q::Modulus;
/// use std::str::FromStr;
///
/// let modulus = Modulus::from_str("42").unwrap();
/// ```
#[allow(dead_code)]
pub struct Modulus {
    pub(crate) modulus: fmpz_mod_ctx,
}
