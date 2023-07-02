// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module contains algorithms for sampling according to the discrete Gaussian distribution.

use crate::{
    error::MathError,
    integer::{MatPolyOverZ, Z},
    integer_mod_q::{MatPolynomialRingZq, PolynomialRingZq},
    rational::{PolyOverQ, Q},
};

impl MatPolynomialRingZq {
    pub fn sample_d(
        basis: &Self,
        k: i64,
        n: impl Into<Z>,
        center: &PolyOverQ,
        s: impl Into<Q>,
    ) -> Result<PolynomialRingZq, MathError> {
        let sample = MatPolyOverZ::sample_d(&basis.matrix, k, n, center, s)?;
        Ok(PolynomialRingZq::from((&sample, &basis.get_mod())))
    }
}
