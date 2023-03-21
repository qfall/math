# qFALL-math
[![made-with-rust](https://img.shields.io/badge/Made%20with-Rust-1f425f.svg)](https://www.rust-lang.org/)
[![CI](https://github.com/qfall/math/actions/workflows/pull_request.yml/badge.svg?branch=dev)](https://github.com/qfall/math/actions/workflows/pull_request.yml)
[![License: MPL 2.0](https://img.shields.io/badge/License-MPL_2.0-brightgreen.svg)](https://opensource.org/licenses/MPL-2.0)
<TODO Badge for Documentation>
<TODO Badge for Code Coverage>
<TODO Badge for Website>

This repository is being developed by the project group [qFALL - quantum resistant fast lattice library](https://cs.uni-paderborn.de/cuk/lehre/veranstaltungen/ws-2022-23/project-group-qfall) in the winter term 2022 and summer term 2023 in Paderborn.

The main objective of this project is to develop a memory safe and efficient usage of
[FLINT](https://flintlib.org/) in [Rust](https://www.rust-lang.org/). The main purpose
is to use this library as a building block to build other projects on top of it.

## Disclaimer
As of right now we are in the development phase and interfaces might change.
Feel free to check out the current progress, but be aware, that the content will
change in the upcoming weeks and months. An official release will be published in the second half of 2023.

## Installation
In order to use this project one needs to have an [installation of Rust](https://www.rust-lang.org/tools/install). Since we are using flint-sys
which itself uses [gmp](https://gmplib.org/manual/), we are currently restricted to usage on Mac, Linux and Linux subsystems under Windows. For a subsystem under Windows, one additionally is required to have installed m4 and a C-compiler.

Since our project isn't yet published there is no option to find it on crates.io.
If you want to include this project in your own Rust project, you can 
include a link to our version on the `dev` branch in your `cargo.toml`. 

```text
math = { git = "https://github.com/qfall/math", branch="dev" }
```

Be aware that the external libraries in our project have to be compiled at the first installation,
which may take about 30 minutes. After the first installation all should be working fine.


## What does qFALL-math offer?

An extensive documentation can be generated using

```bash
cargo doc               # suffix with --open to directly open the documentation
```
once the project is cloned. Following, find a small overview which general types [qFALL-math](https://github.com/qfall/math).

```bash
.math
├── ...
├── src                 
│   ├── integer         # src folder containing implementations of integers
│   ├── integer_mod_q   # src folder containing implementations of integers
│   │                   # for which a certain modulus is applied 
│   └── rational        # src folder containing implementations of rationals
└── ...
```

### Integers

- [`Z`](https://github.com/qfall/math/blob/dev/src/integer/z.rs): Represents $\mathbb Z$
- [`MatZ`](https://github.com/qfall/math/blob/dev/src/integer/mat_z.rs): Represents matrices of $\mathbb Z$
- [`PolyOverZ`]((https://github.com/qfall/math/blob/dev/src/integer/poly_over_z.rs)): Represents polynomials with coefficients over $\mathbb Z$
- [`MatPolyOverZ`]((https://github.com/qfall/math/blob/dev/src/integer/mat_poly_over_z.rs)): Represents matrices of polynomials with coefficients over $\mathbb Z$


```rust
use math::integer::Z;

let a = Z::from(24);
let b = Z::from(42);

let res_add: Z = a + b;
let res_sub: Z = a - b;
let res_mul: Z = a * b;
```

### Integers mod q

- [`Zq`]((https://github.com/qfall/math/blob/dev/src/integer_mod_q/zq.rs)): Represents $\mathbb Z_q$
- [`MatZq`]((https://github.com/qfall/math/blob/dev/src/integer_mod_q/mat_zq.rs)): Represents matrices of $\mathbb Z_q$
- [`PolyOverZq`]((https://github.com/qfall/math/blob/dev/src/integer_mod_q/poly_over_zq.rs)): Represents polynomials with coefficients over $\mathbb Z_q$
- [`PolynomialRingZq`]((https://github.com/qfall/math/blob/dev/src/integer_mod_q/polynomial_ring_zq.rs)): Represents quotient rings of $\mathbb Z_q[X]/f(X)$ where $q$ is prime and $f(X)$ is a [`PolyOverZq`]((https://github.com/qfall/math/blob/dev/src/integer_mod_q/poly_over_zq.rs)).

```rust
use math::integer_mod_q::Zq;
use math::integer_mod_q::Modulus;

let modulus = Modulus::try_from(24).unwrap();
let a = Zq::from((&Z::from(42), &modulus));
let b = Zq::from((&Z::from(17), &modulus));

let res_add: Z = a + b;
let res_sub: Z = a - b;
let res_mul: Z = a * b;
```

### Rational

- [`Q`]((https://github.com/qfall/math/blob/dev/src/rational/q.rs)): Represents $\mathbb Q$
- [`MatQ`]((https://github.com/qfall/math/blob/dev/src/rational/mat.rs)): Represents matrices of $\mathbb Q$
- [`PolyOverQ`]((https://github.com/qfall/math/blob/dev/src/rational/poly_over_q.rs)): Represents polynomials with coefficients over $\mathbb Q$

```rust
use math::rational::Q;

let a = Q::try_from((17, 19)).unwrap();
let b = Q::try_from((42, 24)).unwrap();

let res_add: Z = a + b;
let res_sub: Z = a - b;
let res_mul: Z = a * b;
```

## External Libraries
This project includes the C-library [FLINT](https://flintlib.org/) as a math library. In order to use a C-library in Rust, there has to be an FFI (Foreign Function Interface) which allows to call the methods from FLINT in Rust. We used the crate [flint-sys](https://github.com/alex-ozdemir/flint-rs/tree/master/flint-sys) as bindings for FLINT.
Last, but not least, we utilized [serde](https://crates.io/crates/serde) and [serde_json](https://crates.io/crates/serde_json) to (de-)serialize objects to and from JSON. An extensive list can be found in our `Cargo.toml` file.

## License
This library is distributed under the **Mozilla Public License Version 2.0**.
Permissions of this weak copyleft license are conditioned on making available source code of licensed files and modifications of those files under the same license (or in certain cases, one of the GNU licenses). Copyright and license notices must be preserved. Contributors provide an express grant of patent rights. However, a larger work using the licensed work may be distributed under different terms and without source code for files added in the larger work.

## Citing

Please use the following bibtex entry to cite [qFALL-math](https://github.com/qfall/math):

```text
@misc{qFALL-math,
    author = {Porzenheim, Laurens and Beckmann, Marvin and Kramer, Paul and Milewski, Phil and Moog, Sven and Schmidt, Marcel and Siemer, Niklas}
    title = {qFALL-math v0.0},
    howpublished = {Online: \url{https://github.com/qfall/math}},
    month = Mar,
    year = 2023,
    note = {University Paderborn, C&K Paderborn}
}
```

## Get in Touch
One can contact the members of the project group with our mailing list `pg-qfall@lists.upb.de`.