// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Create benchmark for basis reductions in this file.

use criterion::*;
use qfall_math::integer::MatZ;

/// Benchmark [`MatZ::lll`].
///
/// We uniformly sample a matrix `A = ZZ_256^{20 x 20}` and execute (0.99, 0.501)-LLL on it.
pub fn bench_lll(c: &mut Criterion) {
    let matrix = MatZ::sample_uniform(20, 20, 0, 256).unwrap();

    c.bench_function("LLL on 20x20 matrix", |b| {
        b.iter(|| matrix.lll(0.99, 0.501))
    });
}

criterion_group!(benches, bench_lll);
