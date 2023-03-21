//! Default value for a [`PolyOverQ`].

use super::PolyOverQ;
use flint_sys::fmpq_poly::fmpq_poly_init;
use std::mem::MaybeUninit;

impl Default for PolyOverQ {
    /// Initializes a [`PolyOverQ`] as the zero polynomial.
    ///
    /// # Example
    /// ```
    /// use math::rational::PolyOverQ;
    ///
    /// let zero = PolyOverQ::default();
    /// ```
    fn default() -> Self {
        let mut poly = MaybeUninit::uninit();
        unsafe {
            fmpq_poly_init(poly.as_mut_ptr());
            let poly = poly.assume_init();
            Self { poly }
        }
    }
}

/// ensure that default initializes an empty polynomial
#[cfg(test)]
mod test_default {

    use crate::rational::PolyOverQ;
    use std::str::FromStr;

    /// Ensure that [`Default`] initializes the zero polynomial appropriately
    #[test]
    fn init_zero() {
        let poly_over_zero = PolyOverQ::default();

        assert_eq!(PolyOverQ::from_str("0").unwrap(), poly_over_zero)
    }
}
