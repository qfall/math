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
    utils::sample::discrete_gauss::{DiscreteGaussianIntegerSampler, LookupTableSetting},
};

/// benchmark creating a matrix of size 100x100 sampled by a comparatively wide discrete Gaussian distribution.
pub fn bench_sample_z_wide(c: &mut Criterion) {
    let center = Q::from(0);
    let s = Q::from(100);

    c.bench_function("SampleZ wide 10,000", |b| {
        b.iter(|| MatZ::sample_discrete_gauss(100, 100, &center, &s).unwrap())
    });
}

/// benchmark creating a matrix of size 100x100 sampled by a comparatively narrow discrete Gaussian distribution.
pub fn bench_sample_z_narrow(c: &mut Criterion) {
    let center = Q::from(0);
    let s = Q::from(2);

    c.bench_function("SampleZ narrow 10,000", |b| {
        b.iter(|| MatZ::sample_discrete_gauss(100, 100, &center, &s).unwrap())
    });
}

/// benchmark creating a single integer sampled by a comparatively wide discrete Gaussian distribution.
pub fn bench_sample_z_wide_single(c: &mut Criterion) {
    let center = Q::from(0);
    let s = Q::from(100);

    c.bench_function("SampleZ wide single", |b| {
        b.iter(|| Z::sample_discrete_gauss(&center, &s).unwrap())
    });
}

/// benchmark creating a single integer sampled by a comparatively wide discrete Gaussian distribution.
pub fn bench_sample_z_narrow_single(c: &mut Criterion) {
    let center = Q::from(0);
    let s = Q::from(2);

    c.bench_function("SampleZ narrow single", |b| {
        b.iter(|| Z::sample_discrete_gauss(&center, &s).unwrap())
    });
}

/// benchmark discrete Gaussian sampling using [`DiscreteGaussianIntegerSampler::sample_z`] for a variety of widths.
pub fn bench_sample_z(c: &mut Criterion) {
    let center = 0;
    let gaussian_widths = [
        8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768,
    ];

    for s in gaussian_widths {
        let mut dgis =
            DiscreteGaussianIntegerSampler::init(center, s, 6.0, LookupTableSetting::Precompute)
                .unwrap();

        c.bench_function("DiscreteGauss RejectionSampling", |b| {
            b.iter(|| dgis.sample_z())
        });
    }
}

criterion_group!(
    benches,
    bench_sample_z_wide,
    bench_sample_z_narrow,
    bench_sample_z_wide_single,
    bench_sample_z_narrow_single,
    bench_sample_z,
);
