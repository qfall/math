# qFALL-math
[![made-with-rust](https://img.shields.io/badge/Made%20with-Rust-1f425f.svg)](https://www.rust-lang.org/)
[![Pipeline](https://github.com/qfall/math/actions/workflows/push.yml/badge.svg)](https://github.com/qfall/math/actions/workflows/push.yml)
[![License: MPL 2.0](https://img.shields.io/badge/License-MPL_2.0-blue.svg)](https://opensource.org/licenses/MPL-2.0)

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
- Find further information on [our website](https://qfall.github.io/).
- We recommend [our tutorial](https://qfall.github.io/book) to start working with qFALL.
- Read the [documentation of this crate](TODO).

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

This library is distributed under the **Mozilla Public License Version 2.0** which can be found [here](https://github.com/qfall/math/blob/dev/LICENSE).
Permissions of this weak copyleft license are conditioned on making the source code of licensed files and modifications of those files available under the same license (or in certain cases, under one of the GNU licenses). Copyright and license notices must be preserved. Contributors provide an express grant of patent rights. However, a larger work using the licensed work may be distributed under different terms and without source code for files added to the larger work.
