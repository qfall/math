//! Implements methods to prepare a [`String`] for easy use.

use crate::error::MathError;
use regex::Regex;

/// Takes the string of a matrix as input and prepares it for easy use.
///
/// The input should look like `[[1, 2, 3],[4, 5, 6]]` to get `1,2,3|4,5,6` as output.
/// Symbols that are not `-`, `/`, `,`, `[`, `]` or digits between 0 and 9 are
/// automatically deleted.
///
/// Entries of the matrix can contain the symbols `-`, `/` and digits between
/// 0 and 9. They need to have at least one symbol.
///
///
/// If the matrix is not formatted correctly, an error is returned.
///
/// Input parameters:
/// - `string`: a matrix as a string
///
/// # Examples
/// ```rust
/// use math::utils::prepare::prepare_matrix_string;
///
/// let string = String::from("[[1, 2, 3],[3, 4, 5]]");
/// let prepared_string = prepare_matrix_string(&string).unwrap();
/// ```
///
/// ```rust
/// use math::utils::prepare::prepare_matrix_string;
///
/// let string = String::from("[[1/3, -2/7, 3],[3, 4, -5/-2]]");
/// let prepared_string = prepare_matrix_string(&string).unwrap();
/// ```
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`InvalidMatrix`](MathError::InvalidMatrix)
/// if the matrix is not formatted in a suitable way.
/// - Returns a [`MathError`] of type [`RegexError`](MathError::RegexError)
/// if the regular expression inside of the function could not be processed.
pub fn prepare_matrix_string(string: &str) -> Result<String, MathError> {
    // remove any white space, newline or other characters, that should not be included or aren't necessary
    let string: String = string
        .chars()
        .filter(|c| {
            c.is_ascii_digit() || *c == '[' || *c == ']' || *c == ',' || *c == '-' || *c == '/'
        })
        .collect();

    // check if the matrix format is correct
    let regex = match Regex::new(
        r"^\[(\[((\-|/|[0-9])+,)*(\-|/|[0-9])+\],)*(\[((\-|/|[0-9])+,)*(\-|/|[0-9])+\])\]$",
    ) {
        Ok(regex) => regex,
        _ => {
            return Err(MathError::RegexError(
                r"^\[(\[((\-|/|[0-9])+,)*(\-|/|[0-9])+\],)*(\[((\-|/|[0-9])+,)*(\-|/|[0-9])+\])\]$"
                    .to_owned(),
            ));
        }
    };
    // explanation of this regex:
    // it checks whether the string start with a '[' and ends with a ']'
    // we differ between the first/several and the last row (as there is no comma after the last row)
    // each row needs to start with a '[' and end with a ']'
    // we differ between the first/several and the last entry in each row (as there is no comma after the last entry)
    // each entry can contain the symbols `-`, `/` and digits between 0 and 9. It needs to have at least one symbol.
    if !regex.is_match(&string) {
        return Err(MathError::InvalidMatrix(
            "The matrix is not formatted in a suitable way.".to_owned(),
        ));
    }

    let raw_rows = string.split("],[");
    let mut out = String::new();
    for raw_row in raw_rows {
        // remove leading and trailing [[ or ]] in first/last row
        let row = raw_row.replace('[', "");
        let row = row.replace(']', "");
        // push altered value back on string
        out.push_str(&format!("{}|", row));
    }
    // pop last '|'
    out.pop();

    Ok(out)
}

#[cfg(test)]
mod test_prepare_matrix_string {
    use crate::utils::prepare::prepare_matrix_string;

    // Ensure that correct strings of a matrix are accepted.
    #[test]
    fn correct_matrix_work() {
        let matrix_string1 = String::from("[[1, 2, 3],[3, 4, 5]]");
        let matrix_string2 = String::from("[[1/3, -2/7, 3],[3, 4, -5/-2]]");

        assert!(prepare_matrix_string(&matrix_string1).is_ok());
        assert!(prepare_matrix_string(&matrix_string2).is_ok());
    }

    // Ensure that incorrect strings of a matrix are rejected.
    #[test]
    fn incorrect_entries_error() {
        let matrix_string1 = String::from("[1, 2, 3],[3, 4, 5]");
        let matrix_string2 = String::from("[1/3, -2/7, 3,[3, 4, -5/-2]]");

        assert!(prepare_matrix_string(&matrix_string1).is_err());
        assert!(prepare_matrix_string(&matrix_string2).is_err());
    }

    // Ensure that correct strings of a matrix are prepared correctly.
    #[test]
    fn correct_matrix_format() {
        let matrix_string1 = String::from("[[1, 2, 3],[3, 4, 5]]");
        let matrix_string2 = String::from("[[1/3, -2/7, 3],[3, 4, -5/-2]]");

        assert_eq!(
            prepare_matrix_string(&matrix_string1).unwrap(),
            "1,2,3|3,4,5"
        );
        assert_eq!(
            prepare_matrix_string(&matrix_string2).unwrap(),
            "1/3,-2/7,3|3,4,-5/-2"
        );
    }
}
