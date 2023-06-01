// Copyright © 2023 Niklas Siemer
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.

//! Contains benchmarks for some classic cryptographic schemes.

use criterion::*;
use qfall_math::{
    integer::Z,
    integer_mod_q::{Modulus, Zq},
    traits::*,
};

/// This was previously generated by [`gen_prime_order_group_plus_generator`]
/// with a 1024 bit security level and is a generator of a prime order group given
/// by its modulus.
const GEN_PRIME_ORDER_GROUP: &str = "6699169310659235470225047447246035339577556238993322352393397681703675533291305168752108540160627484197919777651312939723365761438699736642357805668125639 mod 18400681887370733277111033107635204264308519065621966282426615876457082834857578485285974739251754512147175264691046473507777607318533584903054155533044823";

/// Outputs a prime in `[lower_bound, upper_bound)` if one exists.
///
/// This is done via naive uniform rejection sampling by checking
/// whether a uniform sample is prime.
fn sample_prime_naive(lower_bound: &Z, upper_bound: &Z) -> Z {
    let mut sample = Z::sample_uniform(lower_bound, upper_bound).unwrap();
    while !sample.is_prime() {
        sample = Z::sample_uniform(lower_bound, upper_bound).unwrap();
    }
    sample
}

#[allow(dead_code)]
/// Generates a prime [`Modulus`] (i.e. a prime order group) and a `generator` for that group.
pub fn gen_prime_order_group_plus_generator(security_lvl: u32) -> (Modulus, Zq) {
    let two = Z::from(2);
    let lower_bound = two.pow(security_lvl / 2).unwrap();
    let upper_bound = two.pow(security_lvl / 2 + 1).unwrap();

    // sampling according to
    // https://de.wikipedia.org/wiki/Diffie-Hellman-Schl%C3%BCsselaustausch#Prime_Restklassengruppe_und_Primitivwurzel
    // sample prime modulus where `p - 1 = q * 2` for prime `q`
    let mut modulus = sample_prime_naive(&lower_bound, &upper_bound);
    let mut q = (&modulus - Z::ONE).div_exact(&two).unwrap();
    while !q.is_prime() {
        modulus = sample_prime_naive(&lower_bound, &upper_bound);
        q = (&modulus - Z::ONE).div_exact(&two).unwrap();
    }

    // choose generator s.t. `g^2 != 1 mod p` and `g^q != 1 mod p`
    let mut generator = Zq::sample_uniform(&modulus).unwrap();
    while generator.pow(&two).unwrap().get_value() == Z::ONE
        || generator.pow(&q).unwrap().get_value() == Z::ONE
        || generator.clone().get_value() == Z::ZERO
    {
        generator = Zq::sample_uniform(&modulus).unwrap();
    }

    (Modulus::try_from_z(&modulus).unwrap(), generator)
}

mod rsa_textbook {
    use super::sample_prime_naive;
    use qfall_math::{
        integer::Z,
        integer_mod_q::{Modulus, Zq},
        traits::*,
    };
    use std::str::FromStr;

    /// These constants were previously generated by [`rsa_textbook::gen(1024)`]
    const RSA_N: &str = "432529019456174073628056731021899753880199292843627050477235451320968504136109996834942250928981978445989472551473247465106240932979604095669286519963140687101286153803154189345553920544182137022020540002491541180583190915417665399496578760830730904289091934652022809043462927391234535724121396575445021309223";
    const RSA_PK: &str = "272636431233265956354044639799116206612921445708076864293675274944980833816969100954445036939076331379279263791466802764599215907676388073791876743514004914016502795361305034353643235925659883900363706630095745283005183368525178846360740971098036527594113502421475552957731655910068081721705039500289221854513";

    /// Naively generates an RSA key pair `(N, pk, sk)` with the provided `security_lvl`,
    /// where `N` is the [`Modulus`] and `pk` and `sk` integer s.t. `(m^(pk * sk)) = m mod N`.
    ///
    /// This algorithm is naive, because it samples primes in a naive way,
    /// i.e. rejection sampling uniformly at random and checking whether that sample is prime.
    ///
    /// The following steps are made:
    /// 1. Generate two unequal primes `p` and `q` roughly of bit size `security_lvl / 2`
    /// (s.t. `N` is roughly of bit size `security_lvl`).
    /// 2. Compute `N = p * q`.
    /// 3. Compute Euler's Phi function `phi(N) = (p-1) * (q-1)`.
    /// 4. Choose `pk = 65537 = 0x10000000000000001` statically as public key (common as `enc` is very
    /// efficient with this key, has sufficient size, and guarantees to have an inverse).
    /// 5. Calculate `sk = pk^(-1) mod phi(N)`.
    /// 6. Output `(N, pk, sk)`.
    pub fn gen(security_lvl: u32) -> (Modulus, Z, Z) {
        let lower_bound = Z::from(2).pow(security_lvl / 2).unwrap();
        let upper_bound = Z::from(2).pow(security_lvl / 2 + 1).unwrap();

        let p = sample_prime_naive(&lower_bound, &upper_bound);
        let q = sample_prime_naive(&lower_bound, &upper_bound);
        assert_ne!(
            p, q,
            "Primes used for modulus N calculation shouldn't be equal."
        );

        let modulus = Modulus::try_from(&(&p * &q)).unwrap();
        let phi_mod = (&p - Z::ONE) * (&q - Z::ONE);

        // standard prime value chosen as public key
        // to remove necessity of choosing it at random
        let pk = Z::from(65537);
        let sk = Zq::try_from_z_z(&pk, &phi_mod)
            .unwrap()
            .inverse()
            .expect("There must an inverse of this element as pk is prime.")
            .get_value();

        (modulus, pk, sk)
    }

    /// Returns a pre-computed RSA key pair that was computed with `gen(1024)`.
    pub fn static_gen() -> (Modulus, Z, Z) {
        let modulus = Modulus::from_str(RSA_N).unwrap();
        let pk = Z::from(65537);
        let sk = Z::from_str(RSA_PK).unwrap();
        (modulus, pk, sk)
    }

    /// Encrypts a `msg` assumed to be smaller than `modulus` via RSA's `pk`.
    ///
    /// `rsa_textbook.enc(N, pk, msg) = msg^pk mod N`
    pub fn enc(modulus: &Modulus, pk: &Z, msg: &Z) -> Zq {
        let msg = Zq::from_z_modulus(msg, modulus);
        msg.pow(pk).unwrap()
    }

    /// Decrypts a `cipher` via RSA's `sk`.
    ///
    /// `rsa_textbook.dec(N, sk, cipher) = cipher^sk mod N`
    pub fn dec(sk: &Z, cipher: &Zq) -> Z {
        cipher.pow(sk).unwrap().get_value()
    }

    /// Run textbook RSA encryption with 1024 bit security.
    /// 1. get (N, pk, sk) from a previously generated key pair with `gen(1024)`
    /// 2. run cycle of `dec(sk, enc(pk, msg)) == msg`,
    /// where `msg` is sampled uniformly at random in `[0, u64::MAX)`
    pub fn rsa_run_enc_dec() {
        let (modulus, pk, sk) = static_gen();
        let msg = Z::sample_uniform(&0, &u64::MAX).unwrap();

        let cipher = enc(&modulus, &pk, &msg);
        let cmp = dec(&sk, &cipher);
        assert_eq!(msg, cmp);
    }
}

/// benchmark [`rsa enc+dec`]
pub fn bench_rsa_enc_dec(c: &mut Criterion) {
    c.bench_function("RSA enc+dec", |b| {
        b.iter(|| rsa_textbook::rsa_run_enc_dec())
    });
}

/// benchmark [`rsa gen`] for 1024 bit security
pub fn bench_rsa_gen(c: &mut Criterion) {
    c.bench_function("RSA gen", |b| b.iter(|| rsa_textbook::gen(1024)));
}

mod dh_ke {
    use super::GEN_PRIME_ORDER_GROUP;
    use qfall_math::{
        integer::Z,
        integer_mod_q::{Modulus, Zq},
        traits::*,
    };
    use std::str::FromStr;

    /// Returns a pre-computed set of public parameters that was
    /// pre-computed with `gen_prime_order_group_plus_generator(1024)`.
    pub fn static_gen_pp() -> (Modulus, Zq) {
        let generator = Zq::from_str(GEN_PRIME_ORDER_GROUP).unwrap();
        let modulus = generator.get_mod();
        (modulus, generator)
    }

    /// Computes all values needed for the initialization of the DH key exchange
    ///
    /// `dh_ke::gen_key_pair(modulus, generator) -> (pk, sk)`,
    /// where `pk = g^sk mod modulus` and `sk` uniformly random
    pub fn gen_key_pair(modulus: &Modulus, generator: &Zq) -> (Zq, Z) {
        let sk = Z::sample_uniform(&0, &Z::from(modulus)).unwrap();
        let pk = generator.pow(&sk).unwrap();
        (pk, sk)
    }

    /// Combines the others public key and own secret key to the commonly shared secret key `k`
    ///
    /// `dh_ke::combine_to_shared_sk(sk, pk) -> k`, where `k = pk^sk mod p`
    pub fn combine_to_shared_sk(sk: &Z, other_pk: &Zq) -> Zq {
        other_pk.pow(sk).unwrap()
    }

    /// Run a Diffie-Hellman key exchange with precomputed public parameters with 1024 bit security.
    /// 1. get (p, g) from previously generated public parameters
    /// 2. run one cycle of `gen_key_pair` and `combine_to_shared_sk` on each end (2 times),
    /// i.e. one key exchange at both ends and compare the computed shared secrets
    pub fn dh_run() {
        let (modulus, generator) = static_gen_pp();

        let (pk_0, sk_0) = gen_key_pair(&modulus, &generator);
        let (pk_1, sk_1) = gen_key_pair(&modulus, &generator);

        let shared_secret_0 = combine_to_shared_sk(&sk_0, &pk_1);
        let shared_secret_1 = combine_to_shared_sk(&sk_1, &pk_0);

        assert_eq!(shared_secret_0, shared_secret_1);
    }
}

/// benchmark [`dh`] key exchange for both communication partners
pub fn bench_dh(c: &mut Criterion) {
    c.bench_function("DH key exchange", |b| b.iter(|| dh_ke::dh_run()));
}

mod el_gamal_enc {
    use super::GEN_PRIME_ORDER_GROUP;
    use qfall_math::{
        integer::Z,
        integer_mod_q::{Modulus, Zq},
        traits::*,
    };
    use std::str::FromStr;

    /// Returns a pre-computed set of public parameters that was
    /// computed with `gen_prime_order_group_plus_generator(1024)`.
    pub fn static_gen_pp() -> (Modulus, Zq) {
        let generator = Zq::from_str(GEN_PRIME_ORDER_GROUP).unwrap();
        let modulus = generator.get_mod();
        (modulus, generator)
    }

    /// Generates a (pk, sk) key pair for ElGamal's encryption scheme
    ///
    /// `gen_key_pair(p, g) -> (pk, sk)`,
    /// where `pk = g^sk mod p` and `sk` uniformly random
    pub fn gen_key_pair(modulus: &Modulus, generator: &Zq) -> (Zq, Z) {
        let sk = Z::sample_uniform(&0, &Z::from(modulus)).unwrap();
        let pk = generator.pow(&sk).unwrap();
        (pk, sk)
    }

    /// Encrypts a message `m` according to ElGamal's encryption scheme by outputting
    /// `(c_0, c_1) = (g^r, pk^r * m) mod p`
    pub fn enc(generator: &Zq, pk: &Zq, msg: &Zq) -> (Zq, Zq) {
        let r = Z::sample_uniform(&0, &generator.get_mod()).unwrap();
        let c_0 = generator.pow(&r).unwrap();
        let c_1 = pk.pow(&r).unwrap() * msg;
        (c_0, c_1)
    }

    /// Decrypts a `cipher = (c_0, c_1)` according to ElGamal's encryption scheme by outputting
    /// `m = c_0^(-sk) * c_1`.
    pub fn dec(sk: &Z, c_0: &Zq, c_1: &Zq) -> Zq {
        c_0.inverse().unwrap().pow(sk).unwrap() * c_1
    }

    /// Run ElGamal gen+enc+dec with precomputed public parameters with 1024 bit security.
    /// 1. get (p, g) from previously generated public parameters
    /// 2. run one cycle of `gen_key_pair`, `enc`, `dec`, and compare the `msg` to the result
    pub fn el_gamal_run() {
        let (modulus, generator) = static_gen_pp();

        let (pk, sk) = gen_key_pair(&modulus, &generator);

        let msg = Zq::from_z_modulus(&Z::sample_uniform(&0, &modulus).unwrap(), &modulus);

        let (c_0, c_1) = enc(&generator, &pk, &msg);
        let cmp = dec(&sk, &c_0, &c_1);

        assert_eq!(msg, cmp);
    }
}

/// benchmark [`el_gamal`]
pub fn bench_el_gamal(c: &mut Criterion) {
    c.bench_function("El Gamal gen+enc+dec", |b| {
        b.iter(|| el_gamal_enc::el_gamal_run())
    });
}

criterion_group!(
    benches,
    bench_rsa_enc_dec,
    bench_rsa_gen,
    bench_dh,
    bench_el_gamal,
);
