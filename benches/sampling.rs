// Copyright © 2023 Sven Moog
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Create benchmark for sampling in this file.

use criterion::*;
use qfall_math::{integer::*, rational::*};

/// Basically the test [`qfall_math::utils::sample::discrete_gauss::test_sample_d::doc_test`]
/// Sample a [`MatZ`] with `sample_d`.
pub fn sample_d() {
    let basis = MatZ::identity(5, 5);
    let n = Z::from(1024);
    let center = MatQ::new(5, 1);
    let gaussian_parameter = Q::ONE;

    let _ = MatZ::sample_d(&basis, &n, &center, &gaussian_parameter).unwrap();
}

/// benchmark [sample_d]
pub fn bench_sample_d(c: &mut Criterion) {
    c.bench_function("sample_d", |b| b.iter(sample_d));
}

criterion_group!(benches, bench_sample_d);
