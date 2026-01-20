# qFALL-math
[<img alt="github" src="https://img.shields.io/badge/qfall--math-github?style=for-the-badge&logo=github&label=github&color=8da0cb" height="20">](https://github.com/qfall/math)
[<img alt="crates.io" src="https://img.shields.io/badge/qfall--math-cratesio?style=for-the-badge&logo=rust&label=crates&color=fc8d62" height="20">](https://crates.io/crates/qfall-math)
[<img alt="docs.rs" src="https://img.shields.io/badge/qfall--math-docs?style=for-the-badge&logo=docs.rs&label=docs.rs&color=66c2a5" height="20">](https://docs.rs/qfall-math)
[<img alt="tutorial" src="https://img.shields.io/badge/book-tutorial?style=for-the-badge&logo=mdBook&label=Tutorial&color=ffd92f" height="20">](https://qfall.github.io/book)
[<img alt="build" src="https://img.shields.io/github/actions/workflow/status/qfall/math/main.yml?branch=main&style=for-the-badge" height="20">](https://github.com/qfall/math/actions/workflows/main.yml)
[<img alt="license" src="https://img.shields.io/badge/License-MPL_2.0-blue.svg?style=for-the-badge" height="20">](https://github.com/qfall/math/blob/dev/LICENSE)

`qFALL` is a prototyping library for lattice-based cryptography.
This `math`-crate is a memory-safe wrapper of [FLINT](https://flintlib.org/) in Rust, which provides several additional features often used in lattice-based cryptography. This crate is the foundation of the [qFALL project](https://qfall.github.io) containing further crates for prototyping of lattice-based cryptography.

## Quick-Start
First, ensure that you use a Unix-like distribution (Linux or MacOS). Setup [WSL](https://learn.microsoft.com/en-us/windows/wsl/install) if you're using Windows. This is required due to this crate's dependency on FLINT.
Then, make sure your `rustc --version` is `1.85` or newer. 

Furthermore, it's required that `m4`, a C-compiler such as `gcc`, and `make` are installed.
```bash
sudo apt-get install m4 gcc make
```
Then, add you can add this crate to your project by executing the following command.
```bash
cargo add qfall-math
```
- Find further information on [our website](https://qfall.github.io/). Also check out [`qfall-tools`](https://crates.io/crates/qfall-tools) and [`qfall-schemes`](https://crates.io/crates/qfall-schemes).
- Read the [documentation of this crate](https://docs.rs/qfall-math).
- We recommend [our tutorial](https://qfall.github.io/book) to start working with qFALL.

## What does qFALL-math offer?
We would like to point out a few supported features which are specifically important for lattice-based cryptography.
- Uniform, discrete Gaussian, and binomial sampling
- Support of several norms
- Solving systems of linear equations
- Support of the Number-Theoretic Transform (NTT)

Furthermore, this crate simplifies the implementation of your prototype by supporting a wide range of functions such as tensor multiplication, serialisation, matrix concatenations and many more.
Arithmetic operations, comparisons, and conversions are supported across several types. You can find all supported data-types below.

### Integers
- [`Z`](https://docs.rs/qfall-math/latest/qfall_math/integer/struct.Z.html): Represents $\mathbb Z$.
- [`MatZ`](https://docs.rs/qfall-math/latest/qfall_math/integer/struct.MatZ.html): Represents matrices over $\mathbb Z$.
- [`PolyOverZ`](https://docs.rs/qfall-math/latest/qfall_math/integer/struct.PolyOverZ.html): Represents polynomials with coefficients over $\mathbb Z$.
- [`MatPolyOverZ`](https://docs.rs/qfall-math/latest/qfall_math/integer/struct.MatPolyOverZ.html): Represents matrices of polynomials with coefficients over $\mathbb Z$.

### Integers mod q
- [`Zq`](https://docs.rs/qfall-math/latest/qfall_math/integer_mod_q/struct.Zq.html): Represents $\mathbb Z_q$.
- [`MatZq`](https://docs.rs/qfall-math/latest/qfall_math/integer_mod_q/struct.MatZq.html): Represents matrices over $\mathbb Z_q$.
- [`PolyOverZq`](https://docs.rs/qfall-math/latest/qfall_math/integer_mod_q/struct.PolyOverZq.html): Represents polynomials with coefficients over $\mathbb Z_q$.
- [`PolynomialRingZq`](https://docs.rs/qfall-math/latest/qfall_math/integer_mod_q/struct.PolynomialRingZq.html): Represents quotient rings $\mathbb Z_q[X]/f(X)$.
- [`MatPolynomialRingZq`](https://docs.rs/qfall-math/latest/qfall_math/integer_mod_q/struct.MatPolynomialRingZq.html): Represents matrices over quotient rings $\mathbb Z_q[X]/f(X)$.
- [`NTTPolynomialRingZq`](https://docs.rs/qfall-math/latest/qfall_math/integer_mod_q/struct.NTTPolynomialRingZq.html): Represents quotient rings $\mathbb Z_q[X]/f(X)$ in NTT form.
- [`MatNTTPolynomialRingZq`](https://docs.rs/qfall-math/latest/qfall_math/integer_mod_q/struct.MatNTTPolynomialRingZq.html): Represents matrices over quotient rings $\mathbb Z_q[X]/f(X)$ in NTT form.

### Rationals
- [`Q`](https://docs.rs/qfall-math/latest/qfall_math/rational/struct.Q.html): Represents $\mathbb Q$.
- [`MatQ`](https://docs.rs/qfall-math/latest/qfall_math/rational/struct.MatQ.html): Represents matrices over $\mathbb Q$.
- [`PolyOverQ`](https://docs.rs/qfall-math/latest/qfall_math/rational/struct.PolyOverQ.html): Represents polynomials with coefficients over $\mathbb Q$.

## Quick Example
```rust
use qfall_math::{integer_mod_q::MatZq, integer::MatZ};

let (n, m, q) = (256, 1024, 3329);
let (center, sigma) = (0.0, 8.0);

let mat_a = MatZq::sample_uniform(n, m, q);
let vec_s = MatZ::sample_uniform(n, 1, 0, 2).unwrap();
let vec_e = MatZ::sample_discrete_gauss(m, 1, center, sigma).unwrap();

// SIS-Instance: t = A * e mod q
let vec_t = &mat_a * &vec_e;

// LWE-Instance: b^T = s^T * A + e^T mod q
let vec_b = vec_s.transpose() * mat_a + vec_e.transpose();
```

## Bugs
Please report bugs through the [GitHub issue tracker](https://github.com/qfall/math/issues).

## Contributions
Contributors are:
- Marvin Beckmann
- Phil Milewski
- Sven Moog
- Marcel Luca Schmidt
- Jan Niklas Siemer

See [Contributing](https://github.com/qfall/math/blob/dev/CONTRIBUTING.md) for details on how to contribute.

## Citing

Please use the following bibtex entry to cite [qFALL](https://qfall.github.io).

```bibtex
@misc{qfall,
      author = {Marvin Beckmann and Phil Milewski and Laurens Porzenheim and Marcel Luca Schmidt and Jan Niklas Siemer},
      title = {{qFALL} – {Rapid Prototyping of Lattice-based Cryptography}},
      howpublished = {Cryptology {ePrint} Archive, Paper 2026/069},
      year = {2026},
      url = {https://eprint.iacr.org/2026/069}
}
```

## Dependencies
This project uses the C-based, optimised math-library [FLINT](https://flintlib.org/). We tested our use of FLINT extensively to ensure that you can not introduce memory-leaks by using our crate.
If you need a function supported by FLINT that is not supported by this crate, this crate offers an `unsafe` passthrough to access and operate on FLINT's structs directly.

Furthermore, we utilise [serde](https://crates.io/crates/serde) and [serde_json](https://crates.io/crates/serde_json) to (de-)serialize objects to and from JSON. This crate relies on [criterion](https://crates.io/crates/criterion) for benchmarking purposes. Last, but not least, our sampling algorithms use the [rand](https://crates.io/crates/rand)-crate to generate uniformly random bits. An extensive list can be found in our `Cargo.toml` file.

## License

This library is distributed under the [Mozilla Public License Version 2.0](https://github.com/qfall/math/blob/dev/LICENSE).
Permissions of this weak copyleft license are conditioned on making the source code of licensed files and modifications of those files available under the same license (or in certain cases, under one of the GNU licenses). Copyright and license notices must be preserved. Contributors provide an express grant of patent rights. However, a larger work using the licensed work may be distributed under different terms and without source code for files added to the larger work.
