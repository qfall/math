// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Create benchmarks for uniform sampling in this file.

use criterion::*;
use qfall_math::{
    integer::Z,
    integer_mod_q::{MatZq, Zq},
};

/// benchmark creating an integer uniformly at random from a super wide interval
pub fn bench_uniform_zq_superwide(c: &mut Criterion) {
    let modulus = Z::from(u64::MAX) * 4 + 4;

    c.bench_function("Uniform superwide single", |b| {
        b.iter(|| Zq::sample_uniform(&modulus))
    });
}

/// benchmark creating an integer uniformly at random from a wide interval
pub fn bench_uniform_zq_wide(c: &mut Criterion) {
    c.bench_function("Uniform wide single", |b| {
        b.iter(|| Zq::sample_uniform(1048576))
    });
}

/// benchmark creating an integer uniformly at random from a narrow interval
pub fn bench_uniform_zq_narrow(c: &mut Criterion) {
    c.bench_function("Uniform narrow single", |b| {
        b.iter(|| Zq::sample_uniform(10))
    });
}

/// benchmark creating a matrix uniformly at random from a super wide interval
pub fn bench_uniform_matzq_superwide(c: &mut Criterion) {
    let modulus = Z::from(u64::MAX) * 4 + 4;

    c.bench_function("Uniform superwide 10,000", |b| {
        b.iter(|| MatZq::sample_uniform(100, 100, &modulus))
    });
}

/// benchmark creating a matrix uniformly at random from a wide interval
pub fn bench_uniform_matzq_wide(c: &mut Criterion) {
    c.bench_function("Uniform wide 10,000", |b| {
        b.iter(|| MatZq::sample_uniform(100, 100, 1048576))
    });
}

/// benchmark creating a matrix uniformly at random from a narrow interval
pub fn bench_uniform_matzq_narrow(c: &mut Criterion) {
    c.bench_function("Uniform narrow 10,000", |b| {
        b.iter(|| MatZq::sample_uniform(100, 100, 10))
    });
}

criterion_group!(
    name = benches;
    config = Criterion::default().significance_level(0.1).sample_size(1000);
    targets = bench_uniform_zq_superwide,
    bench_uniform_zq_wide,
    bench_uniform_zq_narrow,
    bench_uniform_matzq_superwide,
    bench_uniform_matzq_wide,
    bench_uniform_matzq_narrow,
);
