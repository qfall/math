//! `Q` is a type for rationals of arbritrary length.
//! This implementation uses the [FLINT](https://flintlib.org/) library.

use flint_sys::fmpq::fmpq;

mod cmp;
mod default;
mod from;

#[allow(dead_code)]
#[derive(Debug)]
/// [`Q`] represents any rational value.
///
/// Attributes:
/// - `value`: holds [FLINT](https://flintlib.org/)'s [struct](fmpq)
///     for a rational value
///
/// # Examples
/// ```
/// use math::rational::Q;
/// use std::str::FromStr;
///
/// let a = Q::from_str("-876543/235")?;
/// let zero = Q::default();
/// # Ok::<(), math::error::MathError>(())
/// ```
pub struct Q {
    pub(crate) value: fmpq,
}
