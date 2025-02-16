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
    integer_mod_q::{MatZq, ModulusPolynomialRingZq, PolyOverZq, PolynomialRingZq, Zq},
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

fn dilithium_params_with_ntt() {
    let modulus = get_dilithium_setup();

    let p1 = PolynomialRingZq::sample_uniform(&modulus);
    let p2 = PolynomialRingZq::sample_uniform(&modulus);

    let p1_ntt: MatZq = p1.ntt().unwrap();
    let p2_ntt: MatZq = p2.ntt().unwrap();

    let mut p3_ntt = MatZq::new(p1.get_degree() + 1, 1, p1_ntt.get_mod());
    for i in 0..256 {
        let p1_i: Zq = p1_ntt.get_entry(i, 0).unwrap();
        let p2_i: Zq = p2_ntt.get_entry(i, 0).unwrap();
        p3_ntt.set_entry(i, 0, p1_i * p2_i).unwrap();
    }

    let _ = PolynomialRingZq::intt(&p3_ntt, &modulus).unwrap();
}

fn dilithium_params_without_ntt() {
    let modulus = get_dilithium_setup();

    let p1 = PolynomialRingZq::sample_uniform(&modulus);
    let p2 = PolynomialRingZq::sample_uniform(&modulus);

    let _ = p1 * p2;
}

/// benchmark
pub fn bench_ntt_dilithium_params_with_ntt(c: &mut Criterion) {
    c.bench_function("PolynomialRingZq Multiplication with NTT", |b| {
        b.iter(dilithium_params_with_ntt)
    });
}

/// benchmark
pub fn bench_ntt_dilithium_params_without_ntt(c: &mut Criterion) {
    c.bench_function("PolynomialRingZq Multiplication without NTT", |b| {
        b.iter(dilithium_params_without_ntt)
    });
}

criterion_group!(
    benches,
    bench_ntt_dilithium_params_with_ntt,
    bench_ntt_dilithium_params_without_ntt
);
