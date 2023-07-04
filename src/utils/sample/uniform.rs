// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! This module includes core functionality to sample according to the
//! uniform random distribution.

use crate::{error::MathError, integer::Z};
use rand::RngCore;

/// Computes a uniform at random chosen [`Z`] sample in `[0, interval_size)`.
///
/// Parameters:
/// - `interval_size`: specifies the size of the interval
/// over which the samples are drawn
///
/// Returns a uniform at random chosen [`Z`] instance in `[0, interval_size)`.
///
/// # Examples
/// ```compile_fail
/// use qfall_math::utils::sample::sample_uniform_rejection;
/// use qfall_math::integer::Z;
/// let interval_size = Z::from(20);
///
/// let sample = sample_uniform_rejection(&interval_size).unwrap();
///
/// assert!(Z::ZERO <= sample);
/// assert!(sample < interval_size);
/// ```
///
/// # Errors and Failures
/// - Returns a [`MathError`] of type [`InvalidInterval`](MathError::InvalidInterval)
/// if the interval is chosen smaller than or equal to `1`.
#[allow(dead_code)]
pub(crate) fn sample_uniform_rejection(interval_size: &Z) -> Result<Z, MathError> {
    if interval_size <= &Z::ONE {
        return Err(MathError::InvalidInterval(format!(
            "An invalid interval size {} was provided.",
            interval_size
        )));
    }

    let bit_size = interval_size.bits() as usize;

    let mut random = Z::from(&sample_bits_uniform(bit_size));
    while &random >= interval_size {
        random = Z::from(&sample_bits_uniform(bit_size));
    }
    Ok(random)
}

/// Computes `nr_bits` many uniform at random chosen bits.
///
/// Parameters:
/// - `nr_bits`: specifies the number of bits to be chosen uniform at random
///
/// Returns a [`Vec<u8>`] including `nr_bits` many uniform at random chosen bits,
/// filled with `0` bits if needed for the last byte resp. [`u8`].
///
/// # Examples
/// ```compile_fail
/// use qfall_math::utils::sample::sample_bits_uniform;
/// let nr_bits = 14;
///
/// let byte_vector = sample_bits_uniform(nr_bits);
///
/// assert_eq!(byte_vector[1] < 64);
/// assert_eq!(2, byte_vector.len());
/// ```
#[allow(dead_code)]
fn sample_bits_uniform(nr_bits: usize) -> Vec<u8> {
    let mut rng = rand::thread_rng();

    // sample ⌈ nr_bits / 8 ⌉ bytes
    let mut byte_vector;
    if nr_bits % 8 == 0 {
        byte_vector = vec![0u8; nr_bits / 8];
    } else {
        byte_vector = vec![0u8; nr_bits / 8 + 1];
    }
    let mut res = rng.try_fill_bytes(&mut byte_vector);
    while res.is_err() {
        // Continue filling bytes at first zero byte found by binary search.
        // This may potentially discard previously sampled values, but stays uniform in the distribution
        let first_unfilled_byte = find_first_unfilled_byte(&byte_vector);
        res = rng.try_fill_bytes(&mut byte_vector[first_unfilled_byte..]);
    }

    // set superfluous bits at the end to `0`
    if nr_bits % 8 != 0 {
        let last_index = byte_vector.len() - 1;
        byte_vector[last_index] %= 2u8.pow(nr_bits as u32 % 8);
    }

    byte_vector
}

/// Binary search to find the first zero byte.
///
/// As we do not mark the filled bytes, the first zero byte is our
/// best guess to identify a not yet randomly/ unfiilled byte.
///
/// Parameters:
/// - `byte_arr`: specifies the slice whose first zero byte is looked for
///
/// Returns the position of the first zero byte acc. to binary search.
/// If no zero byte exists, the length of the slice is returned.
///
/// # Examples
/// ```compile_fail
/// use qfall_math::utils::sample::{find_first_unfilled_byte, sample_bits_uniform};
/// let nr_bits = 256;
/// let byte_vector = sample_bits_uniform(nr_bits);
///
/// let first_zero_byte = find_first_unfilled_byte(&byte_vector);
/// ```
fn find_first_unfilled_byte(byte_arr: &[u8]) -> usize {
    let mut lower_bound = 0;
    let mut upper_bound = byte_arr.len();
    while upper_bound - lower_bound > 1 {
        let index = lower_bound + (upper_bound - lower_bound) / 2;
        if byte_arr[index] == 0x0 {
            upper_bound = index;
        } else {
            lower_bound = index;
        }
    }
    if byte_arr[lower_bound] == 0x0 {
        lower_bound
    } else {
        upper_bound
    }
}

#[cfg(test)]
mod test_sample_uniform_rejection {
    use super::{sample_uniform_rejection, Z};

    /// Ensures that the doc tests works correctly.
    #[test]
    fn doc_test() {
        let interval_size = Z::from(20);

        let sample = sample_uniform_rejection(&interval_size).unwrap();

        assert!(Z::ZERO <= sample);
        assert!(sample < interval_size);
    }

    /// Checks whether sampling works fine for small interval sizes
    #[test]
    fn small_interval() {
        let size_2 = Z::from(2);
        let size_7 = Z::from(7);

        let sample_0 = sample_uniform_rejection(&size_2).unwrap();
        let sample_1 = sample_uniform_rejection(&size_2).unwrap();
        let sample_2 = sample_uniform_rejection(&size_2).unwrap();
        let sample_3 = sample_uniform_rejection(&size_7).unwrap();
        let sample_4 = sample_uniform_rejection(&size_7).unwrap();
        let sample_5 = sample_uniform_rejection(&size_7).unwrap();

        assert!(sample_0 >= Z::ZERO);
        assert!(sample_0 < size_2);
        assert!(sample_1 >= Z::ZERO);
        assert!(sample_1 < size_2);
        assert!(sample_2 >= Z::ZERO);
        assert!(sample_2 < size_2);
        assert!(sample_3 >= Z::ZERO);
        assert!(sample_3 < size_7);
        assert!(sample_4 >= Z::ZERO);
        assert!(sample_4 < size_7);
        assert!(sample_5 >= Z::ZERO);
        assert!(sample_5 < size_7);
    }

    /// Checks whether sampling works fine for large interval sizes
    #[test]
    fn large_interval() {
        let size = Z::from(i64::MAX);

        for _i in 0..u8::MAX {
            let sample = sample_uniform_rejection(&size).unwrap();

            assert!(sample >= Z::ZERO);
            assert!(sample < size);
        }
    }

    /// Checks whether interval sizes smaller than 2 result in an error
    #[test]
    fn invalid_interval() {
        assert!(sample_uniform_rejection(&Z::ONE).is_err());
        assert!(sample_uniform_rejection(&Z::ZERO).is_err());
        assert!(sample_uniform_rejection(&Z::MINUS_ONE).is_err());
    }
}

#[cfg(test)]
mod test_sample_bits_uniform {
    use super::sample_bits_uniform;

    /// Ensures that the doc tests works correctly.
    #[test]
    fn doc_test() {
        let nr_bits = 14;

        let byte_vector = sample_bits_uniform(nr_bits);

        assert!(byte_vector[1] < 64);
        assert_eq!(2, byte_vector.len());
    }

    /// Checks whether random bit sampling works appropriate for full byte orders
    #[test]
    fn full_bytes() {
        let bits_0 = sample_bits_uniform(8);
        let bits_1 = sample_bits_uniform(16);
        let bits_2 = sample_bits_uniform(256);

        assert_eq!(1, bits_0.len());
        assert_eq!(2, bits_1.len());
        assert_eq!(32, bits_2.len());
    }

    /// Checks whether random bit sampling works appropriate for partial bytes
    /// and that superfluous bits are cutoff appropriately
    #[test]
    fn partial_bytes() {
        let bits_0 = sample_bits_uniform(7);
        let bits_1 = sample_bits_uniform(14);
        let bits_2 = sample_bits_uniform(250);

        assert_eq!(1, bits_0.len());
        assert!(128 > bits_0[0]);
        assert_eq!(2, bits_1.len());
        assert!(64 > bits_1[1]);
        assert_eq!(32, bits_2.len());
        assert!(4 > bits_2[31])
    }

    /// Check whether all necessary bits are chosen uniform at random.
    /// This test could possibly fail with probability 2^-64
    #[test]
    fn random_bits() {
        let mut samples: Vec<u8> = vec![];
        for _i in 0..64 {
            samples.push(sample_bits_uniform(7)[0]);
        }

        for position in 0..7 {
            let mut found_1 = false;
            // check for all 64 samples whether the `position`-th bit is `1`
            for sample in &samples {
                if (sample >> position & 1) % 2 == 1 {
                    found_1 = true;
                    break;
                }
            }

            if !found_1 {
                panic!(
                    "None of the inspected 64 random bits at position {} was 1. 
                    This seems suspicious.",
                    position
                );
            }
        }
    }
}

#[cfg(test)]
mod test_find_first_unfilled_byte {
    use super::{find_first_unfilled_byte, sample_bits_uniform};

    /// Ensures that the doc test works properly and that
    /// the boundaries of the slice length are respected
    #[test]
    fn doc_test() {
        let nr_bits = 256;
        let byte_vector = sample_bits_uniform(nr_bits);

        let first_zero_byte = find_first_unfilled_byte(&byte_vector);

        assert!(first_zero_byte <= 256);
    }

    /// Ensures correct computation of the first
    /// detectable zero bytes via binary search for static examples
    #[test]
    fn static_cases() {
        let mut vec_0 = vec![0x1; 5];
        let mut vec_1 = vec![0x0; 4];
        let arr_0: [u8; 8] = [0, 1, 2, 3, 4, 5, 6, 0];
        let arr_1: [u8; 7] = [1, 2, 0, 0, 0, 0, 0];

        let res_0 = find_first_unfilled_byte(&vec_0);
        let res_1 = find_first_unfilled_byte(&vec_1);
        vec_0.append(&mut vec_1);
        let res_2 = find_first_unfilled_byte(&vec_0);
        let res_3 = find_first_unfilled_byte(&arr_0);
        let res_4 = find_first_unfilled_byte(&arr_1);

        assert_eq!(5, res_0);
        assert_eq!(0, res_1);
        assert_eq!(5, res_2);
        assert_eq!(7, res_3);
        assert_eq!(2, res_4);
    }
}
