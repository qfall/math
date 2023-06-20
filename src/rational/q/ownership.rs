// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains implementations of functions
//! important for ownership such as the [`Clone`] and [`Drop`] trait.
//!
//! The explicit functions contain the documentation.

use super::Q;
use flint_sys::fmpq::{fmpq_clear, fmpq_set};

impl Clone for Q {
    /// Clones the given element and returns another cloned reference
    /// to the [`fmpq`](flint_sys::fmpq::fmpq) element.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// let a = Q::from((3, 4));
    /// let b = a.clone();
    /// ```
    fn clone(&self) -> Self {
        let mut clone = Self::default();
        unsafe { fmpq_set(&mut clone.value, &self.value) };
        clone
    }
}

impl Drop for Q {
    /// Drops the given reference to the [`fmpq`](flint_sys::fmpq::fmpq) element
    /// and frees the allocated memory if no references are left.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::rational::Q;
    /// use std::str::FromStr;
    /// {
    ///     let a = Q::from((3, 4));
    /// } // as a's scope ends here, it get's dropped
    /// ```
    ///
    /// ```
    /// use qfall_math::rational::Q;
    /// use std::str::FromStr;
    ///
    /// let a = Q::from((3, 4));
    /// drop(a); // explicitly drops a's value
    /// ```
    fn drop(&mut self) {
        unsafe { fmpq_clear(&mut self.value) }
    }
}

/// Test that the [`Clone`] trait is correctly implemented.
#[cfg(test)]
mod test_clone {
    use super::Q;
    use crate::integer::Z;
    use std::str::FromStr;

    /// check if small positive, negative and zero values are cloned correctly
    /// additionally, check if the values are kept on the stack
    #[test]
    fn clone_equals_small() {
        let values = ["1/2", "-1/2", "0/1"];

        for str_value in values {
            let val = Q::from_str(str_value).unwrap();
            let val_clone = val.clone();

            assert_eq!(
                Z {
                    value: val.value.num
                },
                Z {
                    value: val_clone.value.num
                }
            );
            assert_eq!(
                Z {
                    value: val.value.den
                },
                Z {
                    value: val_clone.value.den
                }
            );
            assert_eq!(val, val_clone);

            // check if cloned values are kept on stack
            assert_eq!(val.value.num.0, val_clone.value.num.0);
            assert_eq!(val.value.den.0, val_clone.value.den.0);
        }
    }

    /// check if large positive, negative and zero values are cloned correctly
    /// additionally check if values are stored at different places in memory
    #[test]
    fn clone_equals_large() {
        let big = "1".repeat(65);
        let signs = ["", "-"];

        for sign in signs {
            let val = Q::from_str(&format!("{}{}/2", sign, &big)).unwrap();
            let val_clone = val.clone();

            assert_eq!(
                Z {
                    value: val.value.num
                },
                Z {
                    value: val_clone.value.num
                }
            );
            assert_eq!(
                Z {
                    value: val.value.den
                },
                Z {
                    value: val_clone.value.den
                }
            );
            assert_eq!(val, val_clone);

            // check if point in memory is different from clone
            assert_ne!(val.value.num.0, val_clone.value.num.0);
        }
    }

    /// check if a cloned value is still alive after the original value ran out of scope
    #[test]
    #[allow(clippy::redundant_clone)]
    fn keep_alive() {
        let a: Q;
        {
            let b = Q::from((5, 1));
            a = b.clone();
        }
        assert_eq!(a, Q::from((5, 1)));
    }
}

/// Test that the [`Drop`] trait is correctly implemented.
#[cfg(test)]
mod test_drop {
    use super::Q;
    use std::str::FromStr;

    /// Check whether freed memory is reused afterwards
    #[test]
    fn free_memory() {
        let string = format!("{}/2", "1".repeat(65));
        let a = Q::from_str(&string).unwrap();
        let num_point_in_memory = a.value.num.0;
        let den_point_in_memory = a.value.den.0;

        drop(a);

        // instantiate different values to check if memory slot is reused for different values
        let c = Q::from_str(&string).unwrap();
        assert_eq!(num_point_in_memory, c.value.num.0);
        assert_eq!(den_point_in_memory, c.value.den.0);

        // memory slots differ due to previously created large integer
        assert_ne!(
            num_point_in_memory,
            Q::from_str(&"1".repeat(65)).unwrap().value.num.0
        );
    }
}
