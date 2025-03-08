// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains public functions that enable access to underlying
//! [FLINT](https://flintlib.org/) structs. Therefore, they require to be unsafe.

use super::PolyOverQ;
use crate::macros::unsafe_passthrough::unsafe_getter;
use flint_sys::fmpq_poly::fmpq_poly_struct;

unsafe_getter!(PolyOverQ, poly, fmpq_poly_struct);

#[cfg(test)]
mod test_get_fmpq_poly_struct {
    use super::PolyOverQ;
    use crate::rational::Q;
    use flint_sys::fmpq_poly::fmpq_poly_set_coeff_fmpq;

    /// Checks availability of the getter for [`PolyOverQ::poly`]
    /// and its ability to be modified.
    #[test]
    #[allow(unused_mut)]
    fn availability_and_modification() {
        let mut poly = PolyOverQ::from(1);
        let mut value = Q::from(2);

        let mut fmpq_poly = unsafe { poly.get_fmpq_poly_struct() };

        unsafe { fmpq_poly_set_coeff_fmpq(fmpq_poly, 0, value.get_fmpq()) };

        assert_eq!(PolyOverQ::from(2), poly);
    }
}
