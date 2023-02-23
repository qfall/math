use super::Z;

use flint_sys::fmpz::fmpz_cmp;


impl PartialEq for Z {
    /// Checks if two integers are equal.
    ///
    /// Input parameters:
    /// * other: the other value that is used to compare the elements
    ///
    /// # Example
    /// ```rust
    /// use math::integer::Z;
    ///
    /// let a: Z = Z::from_i64(42);
    /// let b: Z = Z::from_i64(24);
    /// let compared: bool = (a == b);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        unsafe { 1 == flint_sys::fmpz::fmpz_equal(&self.value, &other.value) }
    }
}

impl Eq for Z {}

impl PartialOrd for Z {
    /// Compares two [Z] values. Generally returns an ordering that is implicitly used for the <,>,<=,>=,== methods.
    ///
    /// Input parameters:
    /// * other: the other value that is used to compare the elements
    ///
    /// # Example
    /// ```rust
    /// use math::integer::Z;
    ///
    /// let a: Z = Z::from_i64(42);
    /// let b: Z = Z::from_i64(24);
    /// let less: bool = (a < b);
    /// let less_eq: bool = (a <= b);
    /// let greater: bool = (a > b);
    /// let greater_eq: bool = (a >= b);
    /// let eq: bool = (a == b);
    /// ```
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        unsafe { Some(fmpz_cmp(&self.value, &other.value).cmp(&0)) }
    }
}


impl Ord for Z {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}