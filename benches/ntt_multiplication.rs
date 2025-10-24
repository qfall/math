// Copyright © 2025 Marvin Beckmann
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Contains benchmarks for multiplication with standard FLINT and multiplication using
//! the NTT .

use criterion::*;
use qfall_math::{
    integer_mod_q::{
        Modulus, ModulusPolynomialRingZq, NTTPolynomialRingZq, PolyOverZq, PolynomialRingZq,
    },
    traits::*,
};

pub fn get_dilithium_setup() -> ModulusPolynomialRingZq {
    let n = 256;
    let modulus = 2_i64.pow(23) - 2_i64.pow(13) + 1;

    let mut mod_poly = PolyOverZq::from(modulus);
    mod_poly.set_coeff(0, 1).unwrap();
    mod_poly.set_coeff(n, 1).unwrap();

    let mut polynomial_modulus = ModulusPolynomialRingZq::from(&mod_poly);

    polynomial_modulus.set_ntt_unchecked(1753);

    polynomial_modulus
}

pub fn get_hawk1024_setup() -> ModulusPolynomialRingZq {
    let n = 1024;
    let modulus = 12289;

    let mut mod_poly = PolyOverZq::from(modulus);
    mod_poly.set_coeff(0, 1).unwrap();
    mod_poly.set_coeff(n, 1).unwrap();

    let mut polynomial_modulus = ModulusPolynomialRingZq::from(&mod_poly);

    polynomial_modulus.set_ntt_unchecked(1945);

    polynomial_modulus
}

/// benchmark multiplication in typical dilithium parameter set with NTT
/// `n=256`, `q = 2^23 - 2^13 + 1` and `zeta = 1753`
pub fn bench_ntt_dilithium_params_with_ntt(c: &mut Criterion) {
    let modulus = get_dilithium_setup();
    let mod_q = Modulus::from(modulus.get_q());

    let p1 = PolynomialRingZq::sample_uniform(&modulus);
    let p2 = PolynomialRingZq::sample_uniform(&modulus);

    let ntt1 = NTTPolynomialRingZq::from(&p1);
    let ntt2 = NTTPolynomialRingZq::from(&p2);

    c.bench_function(
        "PolynomialRingZq Multiplication with NTT (Dilithium)",
        |b| b.iter(|| ntt1.mul(&ntt2, &mod_q)),
    );
}

/// benchmark multiplication in typical dilithium parameter set with NTT & Transforms
/// `n=256`, `q = 2^23 - 2^13 + 1` and `zeta = 1753`
pub fn bench_ntt_dilithium_params_with_ntt_and_transforms(c: &mut Criterion) {
    let modulus = get_dilithium_setup();
    let mod_q = Modulus::from(modulus.get_q());

    let p1 = PolynomialRingZq::sample_uniform(&modulus);
    let p2 = PolynomialRingZq::sample_uniform(&modulus);

    c.bench_function(
        "PolynomialRingZq Multiplication with NTT + Transforms (Dilithium)",
        |b| {
            b.iter(|| {
                let ntt1 = NTTPolynomialRingZq::from(&p1);
                let ntt2 = NTTPolynomialRingZq::from(&p2);

                let ntt_res = ntt1.mul(&ntt2, &mod_q);

                let _ = PolynomialRingZq::from((ntt_res, &modulus));
            })
        },
    );
}

/// benchmark multiplication in typical dilithium parameter set without NTT
/// `n=1024`, `q = 2^23 - 2^13 + 1` and `zeta = 1735`
pub fn bench_ntt_dilithium_params_without_ntt(c: &mut Criterion) {
    let modulus = get_dilithium_setup();

    let p1 = PolynomialRingZq::sample_uniform(&modulus);
    let p2 = PolynomialRingZq::sample_uniform(&modulus);

    c.bench_function(
        "PolynomialRingZq Multiplication without NTT (Dilithium)",
        |b| b.iter(|| &p1 * &p2),
    );
}

/// benchmark multiplication in typical HAWK1024 parameter set with NTT
/// `n=256`, `q = 12289` and `zeta = 1945`
pub fn bench_ntt_hawk1024_params_with_ntt(c: &mut Criterion) {
    let modulus = get_hawk1024_setup();
    let mod_q = Modulus::from(modulus.get_q());

    let p1 = PolynomialRingZq::sample_uniform(&modulus);
    let p2 = PolynomialRingZq::sample_uniform(&modulus);

    let ntt1 = NTTPolynomialRingZq::from(&p1);
    let ntt2 = NTTPolynomialRingZq::from(&p2);

    c.bench_function("PolynomialRingZq Multiplication with NTT (HAWK1024)", |b| {
        b.iter(|| ntt1.mul(&ntt2, &mod_q))
    });
}

/// benchmark multiplication in typical HAWK1024 parameter set with NTT and Transforms
/// `n=256`, `q = 12289` and `zeta = 1945`
pub fn bench_ntt_hawk1024_params_with_ntt_and_transforms(c: &mut Criterion) {
    let modulus = get_hawk1024_setup();
    let mod_q = Modulus::from(modulus.get_q());

    let p1 = PolynomialRingZq::sample_uniform(&modulus);
    let p2 = PolynomialRingZq::sample_uniform(&modulus);

    c.bench_function(
        "PolynomialRingZq Multiplication with NTT + Transforms (HAWK1024)",
        |b| {
            b.iter(|| {
                let ntt1 = NTTPolynomialRingZq::from(&p1);
                let ntt2 = NTTPolynomialRingZq::from(&p2);

                let ntt_res = ntt1.mul(&ntt2, &mod_q);

                let _ = PolynomialRingZq::from((ntt_res, &modulus));
            })
        },
    );
}

/// benchmark multiplication in typical HAWK1024 parameter set without NTT
/// `n=256`, `q = 12289` and `zeta = 1945`
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
    bench_ntt_dilithium_params_with_ntt_and_transforms,
    bench_ntt_dilithium_params_without_ntt,
    bench_ntt_hawk1024_params_with_ntt,
    bench_ntt_hawk1024_params_with_ntt_and_transforms,
    bench_ntt_hawk1024_params_without_ntt,
);
