// Copyright 2023 Jan Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes core functionality to sample according to random distributions.

pub mod binomial;
pub mod discrete_gauss;
pub mod uniform;

/// Returns a fresh seed for every call within the same thread, starting from the
/// same sequence of seeds for every test, which allows to test seeded functions
/// repeatedly, e.g. in loops, without receiving the same sample in every iteration.
#[cfg(test)]
pub(crate) fn test_seed() -> [u8; 32] {
    use std::cell::Cell;

    thread_local!(static COUNTER: Cell<u64> = const { Cell::new(0) });
    let counter = COUNTER.with(|counter| {
        let value = counter.get();
        counter.set(value + 1);
        value
    });

    let mut seed = [0; 32];
    seed[..8].copy_from_slice(&counter.to_le_bytes());
    seed
}
