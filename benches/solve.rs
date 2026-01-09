// Copyright © 2023 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Create benchmark for [`MatZq::solve_gaussian_elimination`] in this file.

use criterion::*;
use qfall_math::integer_mod_q::MatZq;
use std::{fs::File, io::Read};

/// Benchmark [`MatZq::solve_gaussian_elimination`]
///
/// We uniformly sampled a matrix `A` and a vector `u`.
/// Then we computed a target `v = A*u` and saved both as matrices.
/// This benchmark loads both strings and runs the solve function to determine
/// the time it takes to produce a solution.
pub fn bench_solve(c: &mut Criterion) {
    let mut matrix = String::new();
    let mut f_matrix = File::open("benches/matrix.txt").expect("Unable to open file");
    f_matrix
        .read_to_string(&mut matrix)
        .expect("Unable to read string");
    let matrix: MatZq = serde_json::from_str(&matrix).unwrap();
    let mut target = String::new();
    let mut f_target = File::open("benches/target.txt").expect("Unable to open file");
    f_target
        .read_to_string(&mut target)
        .expect("Unable to read string");

    let target: MatZq = serde_json::from_str(&target).unwrap();

    c.bench_function("Solve 100x200 mod 4096", |b| {
        b.iter(|| matrix.solve_gaussian_elimination(&target))
    });
}

/// Benchmark [`MatZq::inverse`]
///
/// We uniformly sample a matrix `A` of dimension `300x300` and invert it.
/// Only the inversion time is benchmarked.
pub fn bench_inverse(c: &mut Criterion) {
    let n = 300;
    let q = 7;

    c.bench_function("Inverse Matrix", |b| {
        b.iter_batched(
            || {
                let mut matrix = MatZq::sample_uniform(n, n, q);
                while matrix.get_representative_least_absolute_residue().rank() < n {
                    matrix = MatZq::sample_uniform(n, n, q);
                }
                matrix
            },
            |matrix| matrix.inverse(),
            BatchSize::SmallInput,
        );
    });
}

criterion_group!(benches, bench_solve, bench_inverse);
