//! This module contains basic traits for functionalities that are split over
//! different modules.

use std::{
    ops::{Add, Div, Mul, Sub},
    str::FromStr,
};

pub trait Datatype: FromStr
/*
Clone
+ Drop
+ PartialEq
+ ToStr
+ Add<Self, Output = Self>
+ Sub<Self, Output = Self>
+ Mul<Self, Output = Self>
+ Div<Self, Output = Self>
*/
{
    // pub fn gen_rand(lower_bound: &Self, upper_bound: &Self) -> Result<Self, MathError>;
}
/*
pub trait Matrix<T: Datatype>: FromStr<Err = MathError>
/*
Clone
+ Drop
+ PartialEq
+ ToStr
+ Add<Self, Output = Self>
+ Sub<Self, Output = Self>
+ Mul<Self, Output = Self>
+ Div<Self, Output = Self>
*/
{
    fn new(num_rows: u32, num_cols: u32) -> Result<Self, MathError>
    where
        Self: std::marker::Sized,
    {
        if num_rows == 0 || num_cols == 0 {
            return Err(MathError::InvalidStringToZInput(format!(
                "({},{})",
                num_rows, num_cols,
            )));
        }

        // initialize variable with MaybeUn-initialized value to check correctness of initialization later
        let mut matrix = MaybeUninit::uninit();
        unsafe {
            fmpz_mat_init(matrix.as_mut_ptr(), num_rows as i64, num_cols as i64);

            // Construct MatZ from previously initialized fmpz_mat
            Ok(MatZ {
                matrix: matrix.assume_init(),
            })
        }
    }

    fn get_entry(&self, row: u32, column: u32) -> T;

    fn set_entry(&self, row: u32, column: u32, value: T);

    fn get_num_rows(&self) -> u32;

    fn get_num_columns(&self) -> u32;

    /*
    pub fn identity_mat(size: u32) -> Self;

    pub fn get_column_vec(&self, column: u32) -> Result<Self, MathError>;

    pub fn invert(&self) -> Self;

    pub fn transpose(&self) -> Self;

    pub fn norm_l_infinity_2_squared(&self) -> T;

    pub fn dot_product(&self, other: &Self) -> T;

    pub fn order(&mut self);

    fn find_and_control_matrix_dimensions(string: &str) -> (u32, u32);

    fn eq_dimensions(&self, other: &MatZ) -> bool;
    */
}
*/








//! This module contains functions that are used in different modules.

/// Create a [MatZ] matrix from a string
/// The format of that string looks like this `[[1,2,3],[4,5,6]]` for a 2x3 matrix
/// with entries 1, 2, 3 in the first row and 4, 5, 6 in the second row.
///
/// Parameters:
/// - `s`: the matrix
/// Returns a [MatZ] or an error, if the provided string was not formatted
/// correctly.
///
/// # Example:
/// ```rust
/// use std::str::FromStr;
/// use math::integer::mat_z::MatZ;
///  
/// let string = String::from("[[1, -2, 3],[3, 4, 5]]");
/// let matrix = MatZ::from_str(&string).unwrap();
/// ```
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [MathError::InvalidStringToIntInput]
/// if the provided string was not formatted correctly.
fn from_str(s: &str) -> Result<Self, Self::Err> {
    /// Takes a string input of a matrix and prepares it for easy use.
    /// The input should look like `[[1, 2, 3],[4, 5, 6]]` to get `1,2,3|4,5,6` as output.
    ///
    /// Input parameters:
    /// * `string`: of the format of a matrix, that get's prepared
    fn prepare_string(string: &str) -> Result<String, MathError> {
        // remove any white space, newline or other characters, that should not be included or aren't necessary
        let string: String = string
            .chars()
            .filter(|c| c.is_ascii_digit() || *c == '[' || *c == ']' || *c == ',' || *c == '-')
            .collect();

        // check if the format is correct
        // TODO do not unwrap Error here
        let regex = Regex::new(
            r"^\[(\[(\-{0,1}[0-9]+,)*\-{0,1}[0-9]+\],)*(\[(\-{0,1}[0-9]+,)*\-{0,1}[0-9]+\])\]$",
        )?;
        // explanation of this regex:
        // it checks whether the string starts with a '[' and ends with a ']'
        // we differ between the first/several and the last row (as there is no comma after the last row)
        // each row needs to start with a '[' and end with a ']'
        // we differ between the first/several and the last entry in each row (as there is no comma after the last entry)
        // each entry contains at most one '-', then at least one digit and possibly a '.' for entries in Q and ends with a comma if another entry follows
        if !regex.is_match(&string) {
            return Err(MathError::InvalidStringToMatZInput(string));
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

    /// Controls a prepared string on equal entries in each row and returns the matrix dimensions
    /// Takes `1,2,3|4,5,6` as input and outputs `(2,3)` accordingly.
    ///
    /// Input parameters:
    /// `string`: get's controlled and sized up
    fn find_and_control_matrix_dimensions(string: &str) -> Result<(u32, u32), MathError> {
        let mut num_rows: u32 = string.matches('|').count().try_into().unwrap();
        num_rows += 1;
        let rows = string.split('|');

        // define num_cols to be 0
        let mut num_cols: usize = 0;
        for row in rows {
            if num_cols == 0 {
                num_cols = row.split(',').count();
            } else if num_cols != row.split(',').count() {
                return Err(MathError::InvalidStringToMatZInput(string.to_string()));
            }
        }
        let num_cols: u32 = num_cols.try_into().unwrap();
        Ok((num_rows, num_cols))
    }

    let prep_str = prepare_string(s)?;
    let (num_rows, num_cols) = find_and_control_matrix_dimensions(&prep_str)?;
    let matrix = MatZ::new(num_rows, num_cols)?;

    // fill entries of matrix acc to prepared string
    let rows: Vec<&str> = prep_str.split('|').collect();
    for row in 0..num_rows {
        let row_entries: Vec<&str> = rows[row as usize].split(',').collect();
        for col in 0..num_cols {
            let entry = row_entries[col as usize];
            let z_entry = Z::from_str(entry)?;
            matrix.set_entry(row, col, &z_entry)?;
        }
    }
    Ok(matrix)
}







/*
impl FromStr for MatZ {
    type Err = MathError;

    /// Create a [`MatZ`] matrix from a string
    /// The format of that string looks like this `[[1,2,3],[4,5,6]]` for a 2x3
    /// matrix with entries 1, 2, 3 in the first row and 4, 5, 6 in the second row.
    ///
    /// Parameters:
    /// - `s`: the matrix
    /// Returns a [`MatZ`] or an error, if the provided string was not formatted
    /// correctly.
    ///
    /// # Example:
    /// ```rust
    /// use std::str::FromStr;
    /// use math::integer::MatZ;
    ///
    /// let string = String::from("[[1, -2, 3],[3, 4, 5]]");
    /// let matrix = MatZ::from_str(&string).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type
    /// [`InvalidStringToIntInput`](MathError::InvalidStringToIntInput)
    /// if the provided string was not formatted correctly.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        /// Takes a string input of a matrix and prepares it for easy use.
        /// The input should look like `[[1, 2, 3],[4, 5, 6]]` to get `1,2,3|4,5,6` as output.
        ///
        /// Input parameters:
        /// * `string`: of the format of a matrix, that get's prepared
        fn prepare_string(string: &str) -> Result<String, MathError> {
            // remove any white space, newline or other characters, that should not be included or aren't necessary
            let string: String = string
                .chars()
                .filter(|c| c.is_ascii_digit() || *c == '[' || *c == ']' || *c == ',' || *c == '-')
                .collect();

            // check if the format is correct
            let regex = Regex::new(
                r"^\[(\[(\-{0,1}[0-9]+,)*\-{0,1}[0-9]+\],)*(\[(\-{0,1}[0-9]+,)*\-{0,1}[0-9]+\])\]$",
            )
            .expect("Regex for Matrix could not be initialized");
            // explanation of this regex:
            // it checks whether the string starts with a '[' and ends with a ']'
            // we differ between the first/several and the last row (as there is no comma after the last row)
            // each row needs to start with a '[' and end with a ']'
            // we differ between the first/several and the last entry in each row (as there is no comma after the last entry)
            // each entry contains at most one '-', then at least one digit and possibly a '.' for entries in Q and ends with a comma if another entry follows
            if !regex.is_match(&string) {
                return Err(MathError::InvalidStringToMatZInput(string));
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

        /// Controls a prepared string on equal entries in each row and returns the matrix dimensions
        /// Takes `1,2,3|4,5,6` as input and outputs `(2,3)` accordingly.
        ///
        /// Input parameters:
        /// `string`: get's controlled and sized up
        fn find_and_control_matrix_dimensions(string: &str) -> Result<(u32, u32), MathError> {
            let mut num_rows: u32 = string.matches('|').count().try_into().unwrap();
            num_rows += 1;
            let rows = string.split('|');

            // define num_cols to be 0
            let mut num_cols: usize = 0;
            for row in rows {
                if num_cols == 0 {
                    num_cols = row.split(',').count();
                } else if num_cols != row.split(',').count() {
                    return Err(MathError::InvalidStringToMatZInput(string.to_string()));
                }
            }
            let num_cols: u32 = num_cols.try_into().unwrap();
            Ok((num_rows, num_cols))
        }

        let prep_str = prepare_string(s)?;
        let (num_rows, num_cols) = find_and_control_matrix_dimensions(&prep_str)?;
        let mut matrix = MatZ::new(num_rows, num_cols)?;

        // fill entries of matrix acc to prepared string
        let rows: Vec<&str> = prep_str.split('|').collect();
        for row in 0..num_rows {
            let row_entries: Vec<&str> = rows[row as usize].split(',').collect();
            for col in 0..num_cols {
                let entry = row_entries[col as usize];
                let z_entry = Z::from_str(entry)?;
                matrix.set_entry(row, col, &z_entry)?;
            }
        }
        Ok(matrix)
    }
}
*/