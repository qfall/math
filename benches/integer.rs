// Copyright © 2023 Sven Moog
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Create benchmark for integers in this file.

use criterion::*;
use std::str::FromStr;

use qfall_math::{
    error::MathError,
    integer::*,
    traits::{GetEntry, SetEntry},
};

/// Create matrices of size 4x4 and vectors of size 4.
/// 1. initialize them.
/// 2. multiply them together resulting in a 1x1 matrix
/// 3. assert that the result is correct.
pub fn mat_z_4_4() -> Result<(), MathError> {
    let mat_small_str = "[[1,2,3,4],[5,6,7,8],[9,10,11,12],[13,14,15,16]]";
    let row_vector = MatZ::from_str("[[1,2,3,4]]")?;
    let col_vector = MatZ::from_str("[[1],[2],[3],[4]]")?;
    let mat_small = MatZ::from_str(mat_small_str)?;
    let mat_large = MatZ::identity(4, 4)? * u64::MAX;

    let mat_res = &mat_small * &mat_large + &mat_large;
    let result: MatZ = &row_vector * (&mat_res * &col_vector);

    assert_eq!(
        // this value was calculated using https://matrixcalc.org/
        Z::from_str("20844820803291793324950")?,
        result.get_entry(0, 0)?
    );
    Ok(())
}

/// Create matrices of size 100x100 and vectors of size 100.
/// 1. initialize them.
/// 2. multiply them together resulting in a 1x1 matrix
/// 3. assert that the result is correct.
pub fn mat_z_100_100() -> Result<(), MathError> {
    let mat_a = 10 * MatZ::identity(100, 100)?;
    let mut mat_b = MatZ::new(100, 100)?;
    let mut row_vec_one = MatZ::new(1, 100)?;
    let mut col_vec_one = MatZ::new(100, 1)?;
    for i in 0..100 {
        col_vec_one.set_entry(i, 0, 1)?;
        row_vec_one.set_entry(0, i, 1)?;
    }

    // set every entry in mat_b to u64::MAX
    for row in 0..100 {
        for col in 0..100 {
            mat_b.set_entry(row, col, u64::MAX)?;
        }
    }

    let mut result: MatZ = &mat_b * &mat_b * 20 * &mat_a;
    result = &row_vec_one * &result * &col_vec_one;

    assert_eq!(
        result.get_entry(0, 0)?,
        // this value was calculated using https://matrixcalc.org/
        Z::from_str("68056473384187692685296223856869821645000000000")?
    );

    Ok(())
}

/// benchmark [mat_z_4_4]
pub fn bench_mat_z_4_4(c: &mut Criterion) {
    c.bench_function("MatZ 4x4", |b| b.iter(|| mat_z_4_4()));
}

/// benchmark [mat_z_100_100]
pub fn bench_mat_z_100_100(c: &mut Criterion) {
    c.bench_function("MatZ 100x100", |b| b.iter(|| mat_z_100_100()));
}

criterion_group!(benches, bench_mat_z_4_4, bench_mat_z_100_100);
