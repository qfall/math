//! Implements methods for matrix dimensions.

use crate::error::MathError;

/// Returns the matrix dimensions of a prepared string
/// Takes `1, 2, 3|4, 5, 6` as input and outputs `(2,3)` accordingly.
///
/// Returns an error if the number of rows or columns is too big
/// (must fit into [`i64`]) or if the number of entries in rows is unequal.
///
/// Input parameters:
/// - `string`: the string of the matrix
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`InvalidMatrix`](MathError::InvalidMatrix)
/// if the number of rows or columns is too big (must fit into [`i64`]) or
/// if the number of entries in rows is unequal.
pub(crate) fn find_matrix_dimensions(string: &str) -> Result<(i64, i64), MathError> {
    let mut num_rows: i64 = match string.matches('|').count().try_into() {
        Ok(num_rows) => num_rows,
        _ => {
            return Err(MathError::InvalidMatrix(
                "Number of rows is too big (must fit into [`i64`]).".to_owned(),
            ))
        }
    };
    num_rows += 1;

    let rows = string.split('|');

    let mut num_cols: usize = 0;
    for row in rows {
        if num_cols == 0 {
            num_cols = row.split(',').count();
        } else if num_cols != row.split(',').count() {
            return Err(MathError::InvalidMatrix(
                "Number of entries in rows is unequal.".to_owned(),
            ));
        }
    }
    let num_cols: i64 = match num_cols.try_into() {
        Ok(num_cols) => num_cols,
        _ => {
            return Err(MathError::InvalidMatrix(
                "Number of columns is too big (must fit into [`i64`]).".to_owned(),
            ))
        }
    };

    Ok((num_rows, num_cols))
}

#[cfg(test)]
mod test_find_matrix_dimensions {
    use crate::utils::{dimensions::find_matrix_dimensions, prepare::prepare_matrix_string};

    // Ensure that correct prepared strings of a matrix are accepted.
    #[test]
    fn correct_matrix_works() {
        let mut matrix_string1 = String::from("[[1, 2, 3],[3, 4, 5]]");
        let mut matrix_string2 = String::from("[[1/3, -2/7, 3],[3, 4, -5/-2]]");
        let mut matrix_string3 = String::from("[[4  0 1 2 3, 2  0 1],[1  5, 2  7 8]]");
        let mut matrix_string4 = String::from("[[sdclin, =§&%, +57n4],[+dk<, 37 ffew, 8fh2n]]");

        matrix_string1 = prepare_matrix_string(&matrix_string1).unwrap();
        matrix_string2 = prepare_matrix_string(&matrix_string2).unwrap();
        matrix_string3 = prepare_matrix_string(&matrix_string3).unwrap();
        matrix_string4 = prepare_matrix_string(&matrix_string4).unwrap();

        assert!(find_matrix_dimensions(&matrix_string1).is_ok());
        assert!(find_matrix_dimensions(&matrix_string2).is_ok());
        assert!(find_matrix_dimensions(&matrix_string3).is_ok());
        assert!(find_matrix_dimensions(&matrix_string4).is_ok());
    }

    // Ensure that a matrix with an incorrect number of entries in rows is rejected.
    #[test]
    fn incorrect_rows_error() {
        let matrix_string1 = String::from("1,2|3,4,5");

        assert!(find_matrix_dimensions(&matrix_string1).is_err());
    }

    // Ensure that dimensions can be detected in big matrices.
    #[test]
    fn big_matrix_works() {
        let mut s1 = "[[".to_string();
        s1.push_str(&"1,".repeat(650000));
        s1.push_str(&"1]]");
        let mut s2 = "[".to_string();
        s2.push_str(&"[1,1],".repeat(650000));
        s2.push_str(&"[1,1]]");

        s1 = prepare_matrix_string(&s1).unwrap();
        s2 = prepare_matrix_string(&s2).unwrap();

        assert!(find_matrix_dimensions(&s1).is_ok());
        assert!(find_matrix_dimensions(&s2).is_ok());

        assert_eq!(find_matrix_dimensions(&s1).unwrap().1, 650001);
        assert_eq!(find_matrix_dimensions(&s2).unwrap().0, 650001);
    }
}
