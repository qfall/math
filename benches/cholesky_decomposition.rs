// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Create benchmark for [`MatQ::cholesky_decomposition_flint`] in this file.

use criterion::*;
use qfall_math::rational::MatQ;

/// Benchmark [`MatQ::cholesky_decomposition_flint`].
///
/// We uniformly sampled a matrix `A = ZZ_256^{1000 x 1000}` and
/// computed `A^t * A` to ensure that it's symmetric.
/// This benchmark loads `A^t * A` and computes the Cholesky decomposition.
pub fn bench_cholesky_decomposition(c: &mut Criterion) {
    let string =
        std::fs::read_to_string("benches/matrix_chol_dec.txt").expect("Unable to read file.");
    let matrix: MatQ = serde_json::from_str(&string).expect("Couldn't deserialize matrix.");

    c.bench_function("Cholesky decomposition on 1000x1000 matrix", |b| {
        b.iter(|| matrix.cholesky_decomposition_flint())
    });
}

criterion_group!(benches, bench_cholesky_decomposition);
