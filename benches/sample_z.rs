// Copyright © 2025 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Create benchmarks for `sample_z` and discrete Gaussian sampling in this file.

use criterion::*;
use qfall_math::{
    integer::{MatZ, Z},
    rational::Q,
};

/// benchmark creating a matrix of size 100x100 sampled by a comparatively wide discrete Gaussian distribution.
pub fn bench_sample_z_wide(c: &mut Criterion) {
    /// Create a matrix of size 100x100 sampled by a comparatively wide discrete Gaussian distribution.
    fn sample_z_wide() {
        let n = Z::from(1000);
        let center = Q::from(0);
        let s = Q::from(100);

        let _ = MatZ::sample_discrete_gauss(100, 100, n, center, s).unwrap();
    }

    c.bench_function("SampleZ wide 10,000", |b| b.iter(sample_z_wide));
}

/// benchmark creating a matrix of size 100x100 sampled by a comparatively narrow discrete Gaussian distribution.
pub fn bench_sample_z_narrow(c: &mut Criterion) {
    /// Create a matrix of size 100x100 sampled by a comparatively narrow discrete Gaussian distribution.
    fn sample_z_narrow() {
        let n = Z::from(100);
        let c = Q::from(0);
        let s = Q::from(2);

        let _ = MatZ::sample_discrete_gauss(100, 100, &n, &c, &s).unwrap();
    }

    c.bench_function("SampleZ narrow 10,000", |b| b.iter(sample_z_narrow));
}

/// benchmark creating a single integer sampled by a comparatively wide discrete Gaussian distribution.
pub fn bench_sample_z_wide_single(c: &mut Criterion) {
    /// Create a single integer sampled by a comparatively wide discrete Gaussian distribution.
    fn sample_z_wide_single() {
        let n = Z::from(1000);
        let c = Q::from(0);
        let s = Q::from(100);

        let _ = Z::sample_discrete_gauss(&n, &c, &s).unwrap();
    }

    c.bench_function("SampleZ wide single", |b| b.iter(sample_z_wide_single));
}

/// benchmark creating a single integer sampled by a comparatively wide discrete Gaussian distribution.
pub fn bench_sample_z_narrow_single(c: &mut Criterion) {
    /// Create a single integer sampled by a comparatively wide discrete Gaussian distribution.
    fn sample_z_narrow_single() {
        let n = Z::from(100);
        let c = Q::from(0);
        let s = Q::from(2);

        let _ = Z::sample_discrete_gauss(&n, &c, &s).unwrap();
    }

    c.bench_function("SampleZ narrow single", |b| b.iter(sample_z_narrow_single));
}

criterion_group!(
    benches,
    bench_sample_z_wide,
    bench_sample_z_narrow,
    bench_sample_z_wide_single,
    bench_sample_z_narrow_single
);
