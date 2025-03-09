// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Create benchmark for matrix arithmetic in this file.

use criterion::{criterion_group, Criterion};
use qfall_math::rational::MatQ;

/// Benchmark [`MatQ::mul_f64_unchecked`].
///
/// We uniformly sampled a matrix `A = ZZ^{100 x 100}` with
/// values between -256 and 256 and inversed this matrix.
/// This benchmark loads `A^{-1}` and multiplies `A^{-1}` with
/// itself allowing for some loss of precision.
pub fn bench_mat_q_mul_f64_unchecked(c: &mut Criterion) {
    let string =
        std::fs::read_to_string("benches/mat_q_100x100.txt").expect("Unable to read file.");
    let matrix: MatQ = serde_json::from_str(&string).expect("Couldn't deserialize matrix.");

    c.bench_function("MatQ multiplication", |b| {
        b.iter(|| matrix.mul_f64_unchecked(&matrix))
    });
}

criterion_group!(benches, bench_mat_q_mul_f64_unchecked);
