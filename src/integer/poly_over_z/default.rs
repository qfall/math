//! Default value for a [`PolyOverZ`].

use super::PolyOverZ;
use flint_sys::fmpz_poly::fmpz_poly_init;
use std::mem::MaybeUninit;

impl Default for PolyOverZ {
    /// Initializes a [`PolyOverZ`] with the zero polynomial.
    ///
    /// # Example
    /// ```rust
    /// use math::integer::PolyOverZ;
    ///
    /// let poly_over_zero = PolyOverZ::default();
    /// ```
    fn default() -> Self {
        let mut poly = MaybeUninit::uninit();
        unsafe {
            fmpz_poly_init(poly.as_mut_ptr());

            Self {
                poly: poly.assume_init(),
            }
        }
    }
}

// ensure that default initializes an empty polynomial
#[cfg(test)]
mod test_default {
    use std::str::FromStr;

    use crate::integer::PolyOverZ;

    /// Check if [`Default`] initializes the zero polynomial appropriately
    #[test]
    fn init_zero() {
        let poly_over_zero = PolyOverZ::default();

        assert_eq!(PolyOverZ::from_str("0").unwrap(), poly_over_zero)
    }
}
