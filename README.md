# qFALL-math
[<img alt="github" src="https://img.shields.io/badge/qfall--math-github?style=for-the-badge&logo=github&label=github&color=8da0cb" height="20">](https://github.com/qfall/math)
[<img alt="crates.io" src="https://img.shields.io/badge/qfall--math-cratesio?style=for-the-badge&logo=rust&label=crates&color=fc8d62" height="20">](https://crates.io/crates/qfall-math)
[<img alt="docs.rs" src="https://img.shields.io/badge/qfall--math-docs?style=for-the-badge&logo=docs.rs&label=docs.rs&color=66c2a5" height="20">](https://docs.rs/qfall-math)
[<img alt="tutorial" src="https://img.shields.io/badge/book-tutorial?style=for-the-badge&logo=mdBook&label=Tutorial&color=ffd92f" height="20">](https://qfall.github.io/book)
[<img alt="build" src="https://img.shields.io/github/actions/workflow/status/qfall/math/push.yml?style=for-the-badge" height="20">](https://github.com/qfall/math/actions/workflows/push.yml)
[<img alt="license" src="https://img.shields.io/badge/License-MPL_2.0-blue.svg?style=for-the-badge" height="20">](https://opensource.org/licenses/MPL-2.0)

`qFALL` is a prototyping library for lattice-based constructions.
The `math`-crate is a memory-safe wrapper of [FLINT](https://flintlib.org/) in Rust, which provides several additional features often used in lattice-based cryptography.

## Quick-Start
To use this crate, make sure that `m4`, a C-compiler such as `gcc`, and `make` are installed by running
```bash
sudo apt-get install m4 gcc make
```
Then, add you can add this crate to your project by executing the following command.
```bash
cargo add qfall-math
```
This crate requires `rustc --version >= 1.85`. As it depends on FLINT, this crate requires a Linux or Mac operating system to compile.
- Find further information on [our website](https://qfall.github.io/).
- We recommend [our tutorial](https://qfall.github.io/book) to start working with qFALL.
- Read the [documentation of this crate](https://docs.rs/qfall-math).

## What does qFALL-math offer?
We would like to point out a few supported features which are specifically important for lattice-based cryptography.
- Uniform, discrete Gaussian, and binomial sampling
- Support of several norms
- Solving systems of linear equations
- Support of the Number-Theoretic Transform (NTT)

Furthermore, this crate simplifies the implementation of your prototype by supporting a wide range of functions such as tensor multiplication, serialisation, matrix concatenations and many more.
Arithmetic operations, comparisons, and conversions are supported across several types. You can find all supported data-types below.

### Integers
- [`Z`](TODO_Link_to_documentation): Represents $\mathbb Z$.
- [`MatZ`](TODO_Link_to_documentation): Represents matrices over $\mathbb Z$.
- [`PolyOverZ`](TODO_Link_to_documentation): Represents polynomials with coefficients over $\mathbb Z$.
- [`MatPolyOverZ`](TODO_Link_to_documentation): Represents matrices of polynomials with coefficients over $\mathbb Z$.

### Integers mod q
- [`Zq`](TODO_Link_to_documentation): Represents $\mathbb Z_q$.
- [`MatZq`](TODO_Link_to_documentation): Represents matrices over $\mathbb Z_q$.
- [`PolyOverZq`](TODO_Link_to_documentation): Represents polynomials with coefficients over $\mathbb Z_q$.
- [`PolynomialRingZq`](TODO_Link_to_documentation): Represents quotient rings $\mathbb Z_q[X]/f(X)$.
- [`MatPolynomialRingZq`](TODO_Link_to_documentation): Represents matrices over quotient rings $\mathbb Z_q[X]/f(X)$.
- [`NTTPolynomialRingZq`](TODO_Link_to_documentation): Represents quotient rings $\mathbb Z_q[X]/f(X)$ in NTT form.
- [`MatNTTPolynomialRingZq`](TODO_Link_to_documentation): Represents matrices over quotient rings $\mathbb Z_q[X]/f(X)$ in NTT form.

### Rationals
- [`Q`](TODO_Link_to_documentation): Represents $\mathbb Q$.
- [`MatQ`](TODO_Link_to_documentation): Represents matrices over $\mathbb Q$.
- [`PolyOverQ`](TODO_Link_to_documentation): Represents polynomials with coefficients over $\mathbb Q$.

## Quick Example
```rust
use qfall_math::{integer_mod_q::MatZq, integer::MatZ};

# parameters: nr_rows, nr_columns, modulus
let mat_a = MatZq::sample_uniform(2, 3, 257);
# parameters: nr_rows, nr_columns, lower_bound, upper_bound
let vec_s = MatZ::sample_uniform(1, 2, 0, 2);
# parameters: nr_rows, nr_columns, center, Gaussian parameter
let vec_e = MatZ::sample_discrete_gauss(1, 3, 0, 4.0);

# SIS-instance: t = A * e^T mod 257
let vec_t = mat_a * vec_e.transpose();

# LWE-instance: b = s * A + e mod 257
let vec_b = vec_s * mat_a + vec_e;
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

See [Contributing](TODO_Contribute_file) for details on how to contribute.

## Citing

Please use the following bibtex entry to cite [qFALL](https://qfall.github.io).

```text
Update to eprint
```

## Dependencies
This project uses the C-based, optimized math-library [FLINT](https://flintlib.org/). We tested our use of FLINT extensively to ensure that you can not introduce memory-leaks by using our library.
If you need a function supported by FLINT that is not supported by this crate, we have created an `unsafe` passthrough to access and operate on FLINT's structs directly.

Furthermore, we utilized [serde](https://crates.io/crates/serde) and [serde_json](https://crates.io/crates/serde_json) to (de-)serialize objects to and from JSON. Last, but not least, our sampling algorithms use the [rand](https://crates.io/crates/rand)-crate to generate uniformly random bits. An extensive list can be found in our `Cargo.toml` file.

## License

This library is distributed under the [Mozilla Public License Version 2.0]((https://github.com/qfall/math/blob/dev/LICENSE)).
Permissions of this weak copyleft license are conditioned on making the source code of licensed files and modifications of those files available under the same license (or in certain cases, under one of the GNU licenses). Copyright and license notices must be preserved. Contributors provide an express grant of patent rights. However, a larger work using the licensed work may be distributed under different terms and without source code for files added to the larger work.
