//! [Modulus] is a type of a positive nonnegative integer that is used in order to do modulus operations.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_mod::fmpz_mod_ctx;

#[doc(hidden)]
pub mod from;

#[derive(Debug)]
/// [Modulus] is a type of a positive nonnegative integer that is used in order to do modulus operations.
///
/// Attributes:
/// - `modulus`: holds the value of the modulus
///
/// # Example
/// ```rust
/// use math::integer_mod_q::Modulus;
/// use std::str::FromStr;
///
/// let modulus = Modulus::from_str("42").unwrap();
/// ```
pub struct Modulus {
    pub(crate) modulus: fmpz_mod_ctx,
}
