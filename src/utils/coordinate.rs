//! Implements methods to pre-process coordinates under certain conditions.

use crate::error::MathError;
use std::fmt::Display;

/// Converts coordinate into an [`i64`] that must be greater than zero and must fit into
/// an [`i64`].
///
/// Parameters:
/// - `coordinate`: the coordinate that has to be converted into an [`i64`].
///
/// Returns an [`i64`] representation of the coordinate or an error, if the
/// coordinate does not fullfil all conditions.
///
/// # Example
/// ```rust
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
            "must be greater than zero".to_owned(),
            coordinate.to_string(),
        ));
    }
    Ok(coordinate)
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
