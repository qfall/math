// Copyright © 2023 Sven Moog
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This file collects the benchmarks from other files.

use criterion::criterion_main;

pub mod classic_crypto;
pub mod integer;

criterion_main! {integer::benches, classic_crypto::benches}
