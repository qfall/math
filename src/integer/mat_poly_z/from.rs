//! Implementations to create a [MatPolyZ] value from other types..
//! For each reasonable type, an explicit function with the format
//! `from_<type_name>` and the [From] trait should be implemented.
//!
//! The explicit functions contain the documentation.
use std::mem::MaybeUninit;

use flint_sys::fmpz_poly_mat::fmpz_poly_mat_init;

use super::MatPolyZ;

impl MatPolyZ {
    /// Inititializes a [MatPolyZ].
    /// This method is used to internally initialize a [MatPolyZ] with the
    /// provided size.
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
