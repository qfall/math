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
