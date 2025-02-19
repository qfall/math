// Copyright © 2025 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Contains benchmarks for multiplication with standard FLINT and multiplication using
//! the NTT transform.

use criterion::*;
use qfall_math::{
    integer_mod_q::{ModulusPolynomialRingZq, PolyOverZq, PolynomialRingZq, Zq},
    traits::*,
};

pub fn get_dilithium_setup() -> ModulusPolynomialRingZq {
    let n = 256;
    let modulus = 2_i64.pow(23) - 2_i64.pow(13) + 1;

    let mut mod_poly = PolyOverZq::from(modulus);
    mod_poly.set_coeff(0, 1).unwrap();
    mod_poly.set_coeff(n, 1).unwrap();

    let mut polynomial_modulus = ModulusPolynomialRingZq::from(&mod_poly);
    unsafe {
        polynomial_modulus.set_ntt_unchecked(&Zq::from((1753, modulus)));
    };
    polynomial_modulus
}

pub fn get_hawk1024_setup() -> ModulusPolynomialRingZq {
    let n = 1024;
    let modulus = 12289;

    let mut mod_poly = PolyOverZq::from(modulus);
    mod_poly.set_coeff(0, 1).unwrap();
    mod_poly.set_coeff(n, 1).unwrap();

    let mut polynomial_modulus = ModulusPolynomialRingZq::from(&mod_poly);
    unsafe {
        polynomial_modulus.set_ntt_unchecked(&Zq::from((1945, modulus)));
    };
    polynomial_modulus
}

/// benchmark
pub fn bench_ntt_dilithium_params_with_ntt(c: &mut Criterion) {
    let modulus = get_dilithium_setup();

    let p1 = PolynomialRingZq::sample_uniform(&modulus);
    let p2 = PolynomialRingZq::sample_uniform(&modulus);

    c.bench_function(
        "PolynomialRingZq Multiplication with NTT (Dilithium)",
        |b| {
            b.iter(|| {
                let p1_ntt: Vec<Zq> = p1.ntt().unwrap();
                let p2_ntt: Vec<Zq> = p2.ntt().unwrap();

                let mut p3_ntt = Vec::new();
                for i in 0..256 {
                    p3_ntt.push(&p1_ntt[i] * &p2_ntt[i])
                }

                let _ = PolynomialRingZq::intt(&p3_ntt, &modulus).unwrap();
            })
        },
    );
}

/// benchmark
pub fn bench_ntt_dilithium_params_without_ntt(c: &mut Criterion) {
    let modulus = get_dilithium_setup();

    let p1 = PolynomialRingZq::sample_uniform(&modulus);
    let p2 = PolynomialRingZq::sample_uniform(&modulus);

    c.bench_function(
        "PolynomialRingZq Multiplication without NTT (Dilithium)",
        |b| b.iter(|| &p1 * &p2),
    );
}

/// benchmark
pub fn bench_ntt_hawk1024_params_with_ntt(c: &mut Criterion) {
    let modulus = get_hawk1024_setup();

    let p1 = PolynomialRingZq::sample_uniform(&modulus);
    let p2 = PolynomialRingZq::sample_uniform(&modulus);

    c.bench_function("PolynomialRingZq Multiplication with NTT (HAWK1024)", |b| {
        b.iter(|| {
            let p1_ntt: Vec<Zq> = p1.ntt().unwrap();
            let p2_ntt: Vec<Zq> = p2.ntt().unwrap();

            let mut p3_ntt = Vec::new();
            for i in 0..1024 {
                p3_ntt.push(&p1_ntt[i] * &p2_ntt[i])
            }

            let _ = PolynomialRingZq::intt(&p3_ntt, &modulus).unwrap();
        })
    });
}

/// benchmark
pub fn bench_ntt_hawk1024_params_without_ntt(c: &mut Criterion) {
    let modulus = get_hawk1024_setup();

    let p1 = PolynomialRingZq::sample_uniform(&modulus);
    let p2 = PolynomialRingZq::sample_uniform(&modulus);

    c.bench_function(
        "PolynomialRingZq Multiplication without NTT (HAWK1024)",
        |b| b.iter(|| &p1 * &p2),
    );
}

criterion_group!(
    benches,
    bench_ntt_dilithium_params_with_ntt,
    bench_ntt_dilithium_params_without_ntt,
    bench_ntt_hawk1024_params_with_ntt,
    bench_ntt_hawk1024_params_without_ntt
);
