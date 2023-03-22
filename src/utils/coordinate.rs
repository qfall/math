//! Implements methods to pre-process coordinates under certain conditions.

use crate::error::MathError;
use crate::traits::{GetNumColumns, GetNumRows};
use std::fmt::Display;

/// Converts coordinate into an [`i64`] that must be greater than `0` and must fit into
/// an [`i64`].
///
/// Parameters:
/// - `coordinate`: the coordinate that has to be converted into an [`i64`].
///
/// Returns an [`i64`] representation of the coordinate or an error, if the
/// coordinate does not fulfill all conditions.
///
/// # Example
/// ```
/// use math::utils::coordinate::evaluate_coordinate;
///
/// let coordinate = evaluate_coordinate(u32::MAX).unwrap();
/// ```
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`OutOfBounds`](MathError::OutOfBounds) if
/// either the coordinate is negative or it does not fit into an [`i64`].
pub fn evaluate_coordinate<S: TryInto<i64> + Display + Copy>(
    coordinate: S,
) -> Result<i64, MathError> {
    // the coordinate must fit into an [`i64`]
    let coordinate: i64 = match coordinate.try_into() {
        Ok(coordinate) => coordinate,
        _ => {
            return Err(MathError::OutOfBounds(
                "fit into a i64".to_owned(),
                coordinate.to_string(),
            ))
        }
    };

    // negative coordinates can not be addressed
    if coordinate < 0 {
        return Err(MathError::OutOfBounds(
            "be at least zero".to_owned(),
            coordinate.to_string(),
        ));
    }
    Ok(coordinate)
}

/// Evaluates whether the provided row and column are referencing an entry in a matrix.
///
/// Parameters:
/// - `matrix`: specifies the matrix in which the entry is located
/// - `row`: specifies the row in which the entry is located
/// - `column`: specifies the column in which the entry is located
///
/// Returns the coordinates as a pair of [`i64`] if they reference an entry and return
/// an error otherwise.
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`MathError::OutOfBounds`]
/// if the number of rows or columns is greater than the matrix or negative.
pub(crate) fn evaluate_coordinates<S: GetNumRows + GetNumColumns>(
    matrix: &S,
    row: impl TryInto<i64> + Display + Copy,
    column: impl TryInto<i64> + Display + Copy,
) -> Result<(i64, i64), MathError> {
    let row_i64 = evaluate_coordinate(row)?;
    let column_i64 = evaluate_coordinate(column)?;

    if matrix.get_num_rows() <= row_i64 || matrix.get_num_columns() <= column_i64 {
        return Err(MathError::OutOfBounds(
            format!(
                "be smaller than ({},{})",
                matrix.get_num_rows(),
                matrix.get_num_columns()
            ),
            format!("({},{})", row_i64, column_i64),
        ));
    }
    Ok((row_i64, column_i64))
}

#[cfg(test)]
mod test_eval_coordinate {

    use super::evaluate_coordinate;

    /// tests that negative coordinates are not accepted
    #[test]
    fn is_err_negative() {
        assert!(evaluate_coordinate(i32::MIN).is_err())
    }

    /// tests that the function can be called with several types
    #[test]
    fn is_ok_several_types() {
        assert!(evaluate_coordinate(i8::MAX).is_ok());
        assert!(evaluate_coordinate(i16::MAX).is_ok());
        assert!(evaluate_coordinate(i32::MAX).is_ok());
        assert!(evaluate_coordinate(i64::MAX).is_ok());
        assert!(evaluate_coordinate(u8::MAX).is_ok());
        assert!(evaluate_coordinate(u16::MAX).is_ok());
        assert!(evaluate_coordinate(u32::MAX).is_ok());
    }

    /// ensure that integers which can not be converted to an [`i64`]
    /// are not accepted
    #[test]
    fn does_not_fit() {
        assert!(evaluate_coordinate(u64::MAX).is_err());
    }
}

#[cfg(test)]
mod test_eval_coordinates {

    use super::evaluate_coordinates;
    use crate::integer::MatZ;

    /// tests that negative coordinates are not accepted
    #[test]
    fn is_err_negative() {
        let matrix = MatZ::new(3, 3).unwrap();
        assert!(evaluate_coordinates(&matrix, i32::MIN, 3).is_err())
    }

    /// tests that the function can be called with several types
    #[test]
    fn is_ok_several_types() {
        let matrix = MatZ::new(i16::MAX, u8::MAX).unwrap();

        assert!(evaluate_coordinates(&matrix, 3i8, 0).is_ok());
        assert!(evaluate_coordinates(&matrix, 3i16, 0).is_ok());
        assert!(evaluate_coordinates(&matrix, 3i32, 0).is_ok());
        assert!(evaluate_coordinates(&matrix, 3i64, 0).is_ok());
        assert!(evaluate_coordinates(&matrix, 3u8, 0).is_ok());
        assert!(evaluate_coordinates(&matrix, 3u16, 0).is_ok());
        assert!(evaluate_coordinates(&matrix, 3u32, 0).is_ok());
        assert!(evaluate_coordinates(&matrix, 3u64, 0).is_ok());

        assert!(evaluate_coordinates(&matrix, 0, 3i8).is_ok());
        assert!(evaluate_coordinates(&matrix, 0, 3i16).is_ok());
        assert!(evaluate_coordinates(&matrix, 0, 3i32).is_ok());
        assert!(evaluate_coordinates(&matrix, 0, 3i64).is_ok());
        assert!(evaluate_coordinates(&matrix, 0, 3u8).is_ok());
        assert!(evaluate_coordinates(&matrix, 0, 3u16).is_ok());
        assert!(evaluate_coordinates(&matrix, 0, 3u32).is_ok());
        assert!(evaluate_coordinates(&matrix, 0, 3u64).is_ok());
    }

    /// ensure that integers which can not be converted to an [`i64`]
    /// are not accepted
    #[test]
    fn does_not_fit() {
        let matrix = MatZ::new(3, 3).unwrap();

        assert!(evaluate_coordinates(&matrix, u64::MAX, 0).is_err());
        assert!(evaluate_coordinates(&matrix, 0, u64::MAX).is_err());
    }
}
