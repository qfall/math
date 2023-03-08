//! `Z` is a type for integers with arbritrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpz::fmpz;

mod arithmetic;
mod cmp;
mod default;
mod from;
mod ownership;

#[allow(dead_code)]
#[derive(Debug)]
/// [`Z`] represents any integer value.
///
/// Attributes:
/// - `value`: holds [FLINT](https://flintlib.org/)'s [struct](fmpz)
///     for an integer value
///
/// # Examples
/// ```
/// use math::integer::Z;
/// use std::str::FromStr;
///
/// let a = Z::from_str("-876543")?;
/// let b = Z::from_i64(i64::MIN);
/// let zero = Z::default();
///
/// let result = &a - b.clone() + &zero;
///
/// drop(b);
///
/// assert_ne!(result, zero);
/// # Ok::<(), math::error::MathError>(())
/// ```
pub struct Z {
    pub(crate) value: fmpz,
}
