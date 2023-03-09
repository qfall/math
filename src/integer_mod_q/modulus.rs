//! [`Modulus`] is a type of a positive non-zero integer that is used in order to
//! do modulus operations. The modulus type itself is also used for
//! optimizations.
//!
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz_mod::fmpz_mod_ctx;

mod from;
mod get;
mod properties;
mod to_string;

#[derive(Debug)]
/// [`Modulus`] is a type of a positive non-zero integer that is used
/// to do modulus operations.
///
/// Attributes:
/// - `modulus`: holds the value of the modulus
///
/// # Examples
/// Create [`Modulus`] from [`str`]:
/// ```rust
/// use math::integer_mod_q::Modulus;
/// use std::str::FromStr;
///
/// let modulus = Modulus::from_str("42").unwrap();
/// ```
///
/// Create [`Modulus`] from [`Z`](crate::integer::Z):
/// ```rust
/// # use math::integer_mod_q::Modulus;
/// # use math::integer::Z;
/// let value = Z::from(10);
///
/// let modulus: Modulus = (&value).try_into().unwrap();
/// let modulus: Modulus = <&Z>::try_into(&value).unwrap();
/// let modulus = Modulus::try_from_z(&value).unwrap();
/// let modulus = Modulus::try_from(&value).unwrap();
/// ```
#[allow(dead_code)]
pub struct Modulus {
    modulus: fmpz_mod_ctx,
}
