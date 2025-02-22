// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains public functions that enable access to underlying
//! [FLINT](https://flintlib.org/) structs. Therefore, they require to be unsafe.

use super::Q;
use crate::macros::unsafe_passthrough::unsafe_getter;
use flint_sys::fmpq::fmpq;

unsafe_getter!(Q, value, fmpq);

#[cfg(test)]
mod test_get_value {
    use super::Q;
    use flint_sys::fmpz::fmpz;

    /// Checks availability of the getter for [`Q::value`]
    /// and its ability to be modified.
    #[test]
    #[allow(unused_mut)]
    fn availability_and_modification() {
        let mut rational = Q::from(1);

        let mut fmpq_rat = unsafe { rational.get_value() };

        fmpq_rat.num = fmpz(2);

        assert_eq!(Q::from(2), rational);
    }
}
