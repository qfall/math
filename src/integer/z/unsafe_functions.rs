// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains public functions that enable access to underlying
//! [FLINT](https://flintlib.org/) structs. Therefore, they require to be unsafe.

use crate::{
    integer::Z,
    macros::unsafe_passthrough::{unsafe_getter, unsafe_setter},
};
use flint_sys::fmpz::{fmpz, fmpz_clear};

unsafe_getter!(Z, value, fmpz);
unsafe_setter!(Z, value, fmpz, fmpz_clear);

#[cfg(test)]
mod test_get_fmpz {
    use super::Z;

    /// Checks availability of the getter for [`Z::value`]
    /// and its ability to be modified.
    #[test]
    #[allow(unused_mut)]
    fn availability_and_modification() {
        let mut integer = Z::from(1);

        let mut fmpz_int = unsafe { integer.get_fmpz() };

        fmpz_int.0 = 2;

        assert_eq!(Z::from(2), integer);
    }
}

#[cfg(test)]
mod test_set_fmpz {
    use super::Z;
    use flint_sys::fmpz::fmpz;

    /// Checks availability of the setter for [`Z::value`]
    /// and its ability to modify [`Z`].
    #[test]
    #[allow(unused_mut)]
    fn availability_and_modification() {
        let mut integer = Z::from(1);
        let b = fmpz(2);

        unsafe { integer.set_fmpz(b) };

        assert_eq!(Z::from(2), integer);
    }
}
