//! Implementations of the 'From' trait for [MatPolyZ].
//!
//! This module contains all options to create a polynomial of type [MatPolyZ].

use std::mem::MaybeUninit;

use flint_sys::fmpz_poly_mat::fmpz_poly_mat_init;

use super::MatPolyZ;

impl MatPolyZ {
    /// Creates an initialization of a [MatPolyZ] which can not yet be used. It
    /// needs to be assigned coefficients.
    /// This method is used to first construct a [MatPolyZ] and then later
    /// assign the corresponding efficients with methods from FLINT.
    ///
    /// Parameters
    /// - `nrwos`: specifies the number of rows
    /// - `ncols`: specifies the number of columns
    /// Returns an inititialized [MatPolyZ].
    #[allow(dead_code)]
    fn init(nrows: i64, ncols: i64) -> Self {
        let mut mat = MaybeUninit::uninit();
        unsafe {
            fmpz_poly_mat_init(mat.as_mut_ptr(), nrows, ncols);
            let mat = mat.assume_init();
            Self { mat }
        }
    }
}
