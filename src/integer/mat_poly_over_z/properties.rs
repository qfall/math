//! Implementations to check certain properties of [`MatPolyOverZ`]
//! This includes checks such as squareness.

use super::MatPolyOverZ;
use crate::traits::{GetNumColumns, GetNumRows};
use flint_sys::fmpz_poly_mat::fmpz_poly_mat_is_one;

impl MatPolyOverZ {
    /// Checks if a [`MatPolyOverZ`] is a identity matrix, i.e.
    /// all entries on the diagonal are the constant polynomial 1 and zero elsewhere.
    ///
    /// Returns `true` if the matrix is the identity and `false` otherwise.
    ///
    /// ```
    /// use std::str::FromStr;
    /// use math::integer::MatPolyOverZ;
    ///
    /// let matrix = MatPolyOverZ::from_str("[[1  1, 0],[0, 1  1]]").unwrap();
    /// let check = matrix.is_identity();
    /// # assert!(check)
    /// ```
    pub fn is_identity(&self) -> bool {
        // we have to test squareness manually, since FLINT does not check this
        // directly with their method
        unsafe { 0 != fmpz_poly_mat_is_one(&self.matrix) && self.is_square() }
    }

    /// Checks if a [`MatPolyOverZ`] is a square matrix, i.e.
    /// the number of rows and columns is identical.
    ///
    /// Returns `true` if the matrix is the square and `false` otherwise.
    ///
    /// ```
    /// use std::str::FromStr;
    /// use math::integer::MatPolyOverZ;
    ///
    /// let matrix = MatPolyOverZ::from_str("[[1  1, 0],[0, 1  1]]").unwrap();
    /// let check = matrix.is_square();
    /// # assert!(check)
    /// ```
    pub fn is_square(&self) -> bool {
        self.get_num_columns() == self.get_num_rows()
    }
}

#[cfg(test)]
mod test_is_identity {
    use crate::integer::MatPolyOverZ;
    use std::str::FromStr;

    /// ensure that true is returned for a 1x1, 2x2, 3x3 identity matrix
    #[test]
    fn identity_true() {
        let matrix_1x1 = MatPolyOverZ::from_str("[[1  1]]").unwrap();
        let matrix_2x2 = MatPolyOverZ::from_str("[[1  1, 0],[0, 1  1]]").unwrap();
        let matrix_3x3 =
            MatPolyOverZ::from_str("[[1  1, 0, 0],[0, 1  1, 0],[0, 0, 1  1]]").unwrap();

        assert!(matrix_1x1.is_identity());
        assert!(matrix_2x2.is_identity());
        assert!(matrix_3x3.is_identity());
    }

    /// ensure that matrices which are not square do not return true
    #[test]
    fn not_square() {
        let matrix_1x2 = MatPolyOverZ::from_str("[[1  1, 0]]").unwrap();
        let matrix_2x1 = MatPolyOverZ::from_str("[[1  1],[0]]").unwrap();
        let matrix_2x3 = MatPolyOverZ::from_str("[[1  1, 0, 0],[0, 1  1, 0]]").unwrap();
        let matrix_3x2 = MatPolyOverZ::from_str("[[1  1, 0],[0, 1  1],[0, 0]]").unwrap();

        assert!(!matrix_1x2.is_identity());
        assert!(!matrix_2x1.is_identity());
        assert!(!matrix_2x3.is_identity());
        assert!(!matrix_3x2.is_identity());
    }

    /// ensure that matrices which are square but are not the identity matrix, return false
    #[test]
    fn not_identity() {
        let matrix_side_entry = MatPolyOverZ::from_str("[[1  1, 1  1],[0, 1  1]]").unwrap();
        let matrix_negative_1 = MatPolyOverZ::from_str("[[1  -1, 0],[0, 1  1]]").unwrap();
        let matrix_negative_2 = MatPolyOverZ::from_str("[[1  -17, 0],[0, 1  1]]").unwrap();
        let matrix_higher_degree = MatPolyOverZ::from_str("[[1  1, 0],[0, 2  1 42]]").unwrap();
        let matrix_matrix_positive = MatPolyOverZ::from_str("[[1  17, 0],[0, 1  1]]").unwrap();
        let matrix_large_negative =
            MatPolyOverZ::from_str(&format!("[[1  -{}, 0],[0, 1  1]]", u64::MAX)).unwrap();
        let matrix_large_positive =
            MatPolyOverZ::from_str(&format!("[[1  {}, 0],[0, 1  1]]", u64::MAX)).unwrap();

        assert!(!matrix_side_entry.is_identity());
        assert!(!matrix_negative_1.is_identity());
        assert!(!matrix_negative_2.is_identity());
        assert!(!matrix_higher_degree.is_identity());
        assert!(!matrix_matrix_positive.is_identity());
        assert!(!matrix_large_negative.is_identity());
        assert!(!matrix_large_positive.is_identity());
    }
}

#[cfg(test)]
mod test_is_square {
    use std::str::FromStr;

    use crate::integer::MatPolyOverZ;

    /// ensure that square matrices return true
    #[test]
    fn square_matrix() {
        let matrix_negative =
            MatPolyOverZ::from_str("[[1  -17, 0, 0],[0, 1  1, 0],[0, 0, 0]]").unwrap();
        let matrix_higher_degree = MatPolyOverZ::from_str("[[1  1, 0],[0, 2  1 42]]").unwrap();
        let matrix_matrix_positive = MatPolyOverZ::from_str("[[1  17]]").unwrap();
        let matrix_large_negative =
            MatPolyOverZ::from_str(&format!("[[1  -{}, 0],[0, 1  1]]", u64::MAX)).unwrap();
        let matrix_large_positive = MatPolyOverZ::from_str(&format!(
            "[[1  {}, 0, 0, 0],[0, 1  1, 0, 0],[0, 1  1, 0, 0],[0, 1  1, 0, 0]]",
            u64::MAX
        ))
        .unwrap();

        assert!(matrix_negative.is_square());
        assert!(matrix_matrix_positive.is_square());
        assert!(matrix_higher_degree.is_square());
        assert!(matrix_large_negative.is_square());
        assert!(matrix_large_positive.is_square());
    }

    /// ensure that non-square matrices return false
    #[test]
    fn not_square_matrix() {
        let matrix_1x2 = MatPolyOverZ::from_str("[[1  1, 0]]").unwrap();
        let matrix_2x1 = MatPolyOverZ::from_str("[[1  1],[0]]").unwrap();
        let matrix_2x3 = MatPolyOverZ::from_str("[[1  1, 0, 0],[0, 1  1, 0]]").unwrap();
        let matrix_3x2 = MatPolyOverZ::from_str("[[1  1, 0],[0, 1  1],[0, 0]]").unwrap();

        assert!(!matrix_1x2.is_square());
        assert!(!matrix_2x1.is_square());
        assert!(!matrix_2x3.is_square());
        assert!(!matrix_3x2.is_square());
    }
}
