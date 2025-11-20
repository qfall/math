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
        MatNTTPolynomialRingZq, MatPolynomialRingZq, ModulusPolynomialRingZq, NTTPolynomialRingZq,
        PolyOverZq, PolynomialRingZq,
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

    let p1 = PolynomialRingZq::sample_uniform(&modulus);
    let p2 = PolynomialRingZq::sample_uniform(&modulus);

    let ntt1 = NTTPolynomialRingZq::from(&p1);
    let ntt2 = NTTPolynomialRingZq::from(&p2);

    c.bench_function(
        "PolynomialRingZq Multiplication with NTT (Dilithium)",
        |b| b.iter(|| &ntt1 * &ntt2),
    );
}

/// benchmark multiplication in typical dilithium parameter set with NTT & Transforms
/// `n=256`, `q = 2^23 - 2^13 + 1` and `zeta = 1753`
pub fn bench_ntt_dilithium_params_with_ntt_and_transforms(c: &mut Criterion) {
    let modulus = get_dilithium_setup();

    let p1 = PolynomialRingZq::sample_uniform(&modulus);
    let p2 = PolynomialRingZq::sample_uniform(&modulus);

    c.bench_function(
        "PolynomialRingZq Multiplication with NTT + Transforms (Dilithium)",
        |b| {
            b.iter(|| {
                let ntt1 = NTTPolynomialRingZq::from(&p1);
                let ntt2 = NTTPolynomialRingZq::from(&p2);

                let ntt_res = &ntt1 * &ntt2;

                let _ = PolynomialRingZq::from(ntt_res);
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

    let p1 = PolynomialRingZq::sample_uniform(&modulus);
    let p2 = PolynomialRingZq::sample_uniform(&modulus);

    let ntt1 = NTTPolynomialRingZq::from(&p1);
    let ntt2 = NTTPolynomialRingZq::from(&p2);

    c.bench_function("PolynomialRingZq Multiplication with NTT (HAWK1024)", |b| {
        b.iter(|| &ntt1 * &ntt2)
    });
}

/// benchmark multiplication in typical HAWK1024 parameter set with NTT and Transforms
/// `n=256`, `q = 12289` and `zeta = 1945`
pub fn bench_ntt_hawk1024_params_with_ntt_and_transforms(c: &mut Criterion) {
    let modulus = get_hawk1024_setup();

    let p1 = PolynomialRingZq::sample_uniform(&modulus);
    let p2 = PolynomialRingZq::sample_uniform(&modulus);

    c.bench_function(
        "PolynomialRingZq Multiplication with NTT + Transforms (HAWK1024)",
        |b| {
            b.iter(|| {
                let ntt1 = NTTPolynomialRingZq::from(&p1);
                let ntt2 = NTTPolynomialRingZq::from(&p2);

                let ntt_res = &ntt1 * &ntt2;

                let _ = PolynomialRingZq::from(ntt_res);
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

/// benchmark multiplication in typical dilithium parameter set with NTT
/// `n=256`, `q = 2^23 - 2^13 + 1` and `zeta = 1753`
pub fn bench_mat_ntt_dilithium_params_with_ntt(c: &mut Criterion) {
    let modulus = get_dilithium_setup();

    let p1 = MatPolynomialRingZq::sample_uniform(4, 4, &modulus);
    let p2 = MatPolynomialRingZq::sample_uniform(4, 1, &modulus);

    let ntt1 = MatNTTPolynomialRingZq::from(&p1);
    let ntt2 = MatNTTPolynomialRingZq::from(&p2);

    c.bench_function(
        "MatPolynomialRingZq Multiplication with NTT (Dilithium)",
        |b| b.iter(|| &ntt1 * &ntt2),
    );
}

/// benchmark multiplication in typical dilithium parameter set with NTT & Transforms
/// `n=256`, `q = 2^23 - 2^13 + 1` and `zeta = 1753`
pub fn bench_mat_ntt_dilithium_params_with_ntt_and_transforms(c: &mut Criterion) {
    let modulus = get_dilithium_setup();

    let p1 = MatPolynomialRingZq::sample_uniform(4, 4, &modulus);
    let p2 = MatPolynomialRingZq::sample_uniform(4, 1, &modulus);

    c.bench_function(
        "MatPolynomialRingZq Multiplication with NTT + Transforms (Dilithium)",
        |b| {
            b.iter(|| {
                let ntt1 = MatNTTPolynomialRingZq::from(&p1);
                let ntt2 = MatNTTPolynomialRingZq::from(&p2);

                let ntt_res = &ntt1 * &ntt2;

                let _ = MatPolynomialRingZq::from(ntt_res);
            })
        },
    );
}

/// benchmark multiplication in typical dilithium parameter set without NTT
/// `n=1024`, `q = 2^23 - 2^13 + 1` and `zeta = 1735`
pub fn bench_mat_ntt_dilithium_params_without_ntt(c: &mut Criterion) {
    let modulus = get_dilithium_setup();

    let p1 = MatPolynomialRingZq::sample_uniform(4, 4, &modulus);
    let p2 = MatPolynomialRingZq::sample_uniform(4, 1, &modulus);

    c.bench_function(
        "MatPolynomialRingZq Multiplication without NTT (Dilithium)",
        |b| b.iter(|| &p1 * &p2),
    );
}

/// benchmark multiplication in typical HAWK1024 parameter set with NTT
/// `n=256`, `q = 12289` and `zeta = 1945`
pub fn bench_mat_ntt_hawk1024_params_with_ntt(c: &mut Criterion) {
    let modulus = get_hawk1024_setup();

    let p1 = MatPolynomialRingZq::sample_uniform(1, 2, &modulus);
    let p2 = MatPolynomialRingZq::sample_uniform(2, 2, &modulus);

    let ntt1 = MatNTTPolynomialRingZq::from(&p1);
    let ntt2 = MatNTTPolynomialRingZq::from(&p2);

    c.bench_function(
        "MatPolynomialRingZq Multiplication with NTT (HAWK1024)",
        |b| b.iter(|| &ntt1 * &ntt2),
    );
}

/// benchmark multiplication in typical HAWK1024 parameter set with NTT and Transforms
/// `n=256`, `q = 12289` and `zeta = 1945`
pub fn bench_mat_ntt_hawk1024_params_with_ntt_and_transforms(c: &mut Criterion) {
    let modulus = get_hawk1024_setup();

    let p1 = MatPolynomialRingZq::sample_uniform(2, 2, &modulus);
    let p2 = MatPolynomialRingZq::sample_uniform(2, 1, &modulus);

    c.bench_function(
        "MatPolynomialRingZq Multiplication with NTT + Transforms (HAWK1024)",
        |b| {
            b.iter(|| {
                let ntt1 = MatNTTPolynomialRingZq::from(&p1);
                let ntt2 = MatNTTPolynomialRingZq::from(&p2);

                let ntt_res = &ntt1 * &ntt2;

                let _ = MatPolynomialRingZq::from(ntt_res);
            })
        },
    );
}

/// benchmark multiplication in typical HAWK1024 parameter set without NTT
/// `n=256`, `q = 12289` and `zeta = 1945`
pub fn bench_mat_ntt_hawk1024_params_without_ntt(c: &mut Criterion) {
    let modulus = get_hawk1024_setup();

    let p1 = MatPolynomialRingZq::sample_uniform(2, 2, &modulus);
    let p2 = MatPolynomialRingZq::sample_uniform(2, 1, &modulus);

    c.bench_function(
        "MatPolynomialRingZq Multiplication without NTT (HAWK1024)",
        |b| b.iter(|| &p1 * &p2),
    );
}

pub fn get_rbe_setup() -> ModulusPolynomialRingZq {
    let d: i64 = 256; // Degree of modulus-polynomial (X^d + 1) mod Q
    let q: i64 = 180143985094819841; // Modulus per coefficient
    let root_of_unity: i64 = 121052468536984810;

    let mut mod_poly = PolyOverZq::from(q);
    mod_poly.set_coeff(0, 1).unwrap();
    mod_poly.set_coeff(d, 1).unwrap();

    let mut polynomial_modulus = ModulusPolynomialRingZq::from(&mod_poly);

    polynomial_modulus.set_ntt_unchecked(root_of_unity);

    polynomial_modulus
}

/// benchmark multiplication in typical RBE parameter set with NTT
/// `n=256`, `q = 12289` and `zeta = 1945`
pub fn bench_mat_ntt_rbe_params_with_ntt(c: &mut Criterion) {
    let modulus = get_rbe_setup();

    let p1 = MatPolynomialRingZq::sample_uniform(1, 2, &modulus);
    let p2 = MatPolynomialRingZq::sample_uniform(2, 12, &modulus);

    let ntt1 = MatNTTPolynomialRingZq::from(&p1);
    let ntt2 = MatNTTPolynomialRingZq::from(&p2);

    c.bench_function("MatPolynomialRingZq Multiplication with NTT (RBE)", |b| {
        b.iter(|| &ntt1 * &ntt2)
    });
}

/// benchmark multiplication in typical RBE parameter set with NTT and Transforms
/// `n=256`, `q = 12289` and `zeta = 1945`
pub fn bench_mat_ntt_rbe_params_with_ntt_and_transforms(c: &mut Criterion) {
    let modulus = get_rbe_setup();

    let p1 = MatPolynomialRingZq::sample_uniform(1, 2, &modulus);
    let p2 = MatPolynomialRingZq::sample_uniform(2, 12, &modulus);

    c.bench_function(
        "MatPolynomialRingZq Multiplication with NTT + Transforms (RBE)",
        |b| {
            b.iter(|| {
                let ntt1 = MatNTTPolynomialRingZq::from(&p1);
                let ntt2 = MatNTTPolynomialRingZq::from(&p2);

                let ntt_res = &ntt1 * &ntt2;

                let _ = MatPolynomialRingZq::from(ntt_res);
            })
        },
    );
}

/// benchmark multiplication in typical RBE parameter set without NTT
/// `n=256`, `q = 12289` and `zeta = 1945`
pub fn bench_mat_ntt_rbe_params_without_ntt(c: &mut Criterion) {
    let modulus = get_rbe_setup();

    let p1 = MatPolynomialRingZq::sample_uniform(1, 2, &modulus);
    let p2 = MatPolynomialRingZq::sample_uniform(2, 12, &modulus);

    c.bench_function(
        "MatPolynomialRingZq Multiplication without NTT (RBE)",
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
    bench_mat_ntt_dilithium_params_with_ntt,
    bench_mat_ntt_dilithium_params_with_ntt_and_transforms,
    bench_mat_ntt_dilithium_params_without_ntt,
    bench_mat_ntt_hawk1024_params_with_ntt,
    bench_mat_ntt_hawk1024_params_with_ntt_and_transforms,
    bench_mat_ntt_hawk1024_params_without_ntt,
    bench_mat_ntt_rbe_params_with_ntt,
    bench_mat_ntt_rbe_params_with_ntt_and_transforms,
    bench_mat_ntt_rbe_params_without_ntt,
);
