# Contributing

This library has been designed for prototyping lattice-based cryptography. Do you miss a common function for your own prototype or did you design your own scheme and want it added to this library? You are welcome to add it and we are happy help you. 

More generally, all contributions such as bugfixes, documentation and tests are welcome. Please go ahead and submit your pull requests.

## Choosing the right location

The qfall library is divided into thre different repositories: [qFALL-math](https://github.com/qfall/math), [qFALL-tools](https://github.com/qfall/tools) and [qFALL-schemes](https://github.com/qfall/schemes).

To decide where ro add your code, ask the following questions:

 - Is your code a general mathematical function, e.g. addition or LLL?   -> add your code to [qFALL-math](https://github.com/qfall/math).
 - Is your code a construction that is commonly used in the construction of lattice based schemes, e.g. g-trapdoors?     -> add your code to [qFALL-tools](https://github.com/qfall/tools).
 - Is your code one specific scheme or prototype, e.g. 'scheme XY of paper Z'?    -> add your code to [qFALL-schemes](https://github.com/qfall/schemes).

When in doubt, just submit your pull request to the repository you feel is best suited for your code.

##  Style Guide


## Pull request template

Every pull request will use this template by default:

> **Description**
> 
> <!-- 
> Please include a summary of the changes and which issue is fixed or which feature it added.
> Please also include relevant motivation and context. List any dependencies that are required for this change.
> -->
> 
> This PR implements...
> - [ ] feature/ revision/ hotfix/ optimisation/ ...
> 
> for/ of `Component`.
> 
> <!--
> If Connected to an issue, include:
> Closes #(issue number)
> -->
> 
> **Testing**
> 
> <!-- Please shortly describe how you tested your code and mark all you have done after -->
> 
> <!-- exclude any of the following if they do not apply -->
> - [ ] I added basic working examples (possibly in doc-comment)
> - [ ] I added tests for large (pointer representation) values
> - [ ] I triggered all possible errors in my test in every possible way
> - [ ] I included tests for all reasonable edge cases
> <!-- Please add other tests if any other have been performed -->
> 
> **Checklist:**
> 
> <!-- This is a short summary of the things the programmer should always consider before merging-->
> 
> - [ ] I have performed a self-review of my own code
>   - [ ] The code provides good readability and maintainability s.t. it fulfills best practices like talking code, modularity, ...
>     - [ ] The chosen implementation is not more complex than it has to be
>   - [ ] My code should work as intended and no side effects occur (e.g. memory leaks)
>   - [ ] The doc comments fit our style guide
>   - [ ] I have credited related sources if needed


## Disclaimer

Currently, we are in the development phase and interfaces might change.
Feel free to check out the current progress, but be aware, that the content will
change in the upcoming weeks and months. An official release will most likely be published in the second half of 2024.

## Quick-Start

Please refer to [our website](https://qfall.github.io/) as a central information point.

To install and add our library to your project, please refer to [our tutorial](https://qfall.github.io/book/index.html).
It provides a step-by-step guide to install the required libraries and gives further insights into the usage of our crates.

## What does qFALL-math offer?

Extensive documentation can be generated using

```bash
cargo doc               # suffix with --open to directly open the documentation
```

once the project is cloned. Following, there is a small overview containing the general types of our library [qFALL-math](https://github.com/qfall/math).

```bash
math
├── ...
├── src
│   ├── integer         # src folder containing implementations of integers
│   ├── integer_mod_q   # src folder containing implementations of integers
│   │                   # for which a certain modulus is applied
│   └── rational        # src folder containing implementations of rationals
└── ...
```

### Integers

- [`Z`](https://github.com/qfall/math/blob/dev/src/integer/z.rs): Represents $\mathbb Z$.
- [`MatZ`](https://github.com/qfall/math/blob/dev/src/integer/mat_z.rs): Represents matrices of $\mathbb Z$.
- [`PolyOverZ`](https://github.com/qfall/math/blob/dev/src/integer/poly_over_z.rs): Represents polynomials with coefficients over $\mathbb Z$.
- [`MatPolyOverZ`](https://github.com/qfall/math/blob/dev/src/integer/mat_poly_over_z.rs): Represents matrices of polynomials with coefficients over $\mathbb Z$.

```rust
use qfall_math::integer::Z;

let a = Z::from(24);
let b = Z::from(42);

let res_add: Z = &a + &b;
let res_sub: Z = a - 10;
let res_mul: Z = 3 * b;
```

### Integers mod q

- [`Zq`](https://github.com/qfall/math/blob/dev/src/integer_mod_q/zq.rs): Represents $\mathbb Z_q$.
- [`MatZq`](https://github.com/qfall/math/blob/dev/src/integer_mod_q/mat_zq.rs): Represents matrices of $\mathbb Z_q$.
- [`PolyOverZq`](https://github.com/qfall/math/blob/dev/src/integer_mod_q/poly_over_zq.rs): Represents polynomials with coefficients over $\mathbb Z_q$.
- [`PolynomialRingZq`](https://github.com/qfall/math/blob/dev/src/integer_mod_q/polynomial_ring_zq.rs): Represents quotient rings of $\mathbb Z_q[X]/f(X)$ where $q$ is an integer modulus and $f(X)$ is a [`PolyOverZq`](https://github.com/qfall/math/blob/dev/src/integer_mod_q/poly_over_zq.rs).
- [`MatPolynomialRingZq`](https://github.com/qfall/math/blob/dev/src/integer_mod_q/mat_polynomial_ring_zq.rs): Represents matrices of quotient rings of $\mathbb Z_q[X]/f(X)$ where $q$ is an integer modulus and $f(X)$ is a [`PolyOverZq`](https://github.com/qfall/math/blob/dev/src/integer_mod_q/poly_over_zq.rs).

```rust
use qfall_math::integer_mod_q::Zq;
use qfall_math::integer_mod_q::Modulus;

let modulus = Modulus::from(24);
let a = Zq::from((42, &modulus));
let b = Zq::from((17, &modulus));

let res_add: Zq = &a + &b;
let res_sub: Zq = a - 10;
let res_mul: Zq = 3 * b;
```

### Rationals

- [`Q`](https://github.com/qfall/math/blob/dev/src/rational/q.rs): Represents $\mathbb Q$.
- [`MatQ`](https://github.com/qfall/math/blob/dev/src/rational/mat.rs): Represents matrices of $\mathbb Q$.
- [`PolyOverQ`](https://github.com/qfall/math/blob/dev/src/rational/poly_over_q.rs): Represents polynomials with coefficients over $\mathbb Q$.

```rust
use qfall_math::rational::Q;

let a = Q::from((17, 19));
let b = Q::from(0.5);

let res_add: Q = &a + &b;
let res_sub: Q = a - 10.5;
let res_mul: Q = 3 * b;
```

## External Libraries

This project uses the C-based, optimized math library [FLINT](https://flintlib.org/). To use a C-library in Rust, there has to be an FFI (Foreign Function Interface) which allows to call the methods from [FLINT](https://flintlib.org/) in Rust. This project uses the crate [flint-sys](https://github.com/alex-ozdemir/flint-rs/tree/master/flint-sys) as a binding for [FLINT](https://flintlib.org/).
Furthermore, we utilized [serde](https://crates.io/crates/serde) and [serde_json](https://crates.io/crates/serde_json) to (de-)serialize objects to and from JSON. Last, but not least, our sampling algorithms heavily rely on the [rand-crate](https://crates.io/crates/rand). An extensive list can be found in our `Cargo.toml` file.

## License

This library is distributed under the **Mozilla Public License Version 2.0** which can be found here [License](https://github.com/qfall/math/blob/dev/LICENSE).
Permissions of this weak copyleft license are conditioned on making available the source code of licensed files and modifications of those files under the same license (or in certain cases, one of the GNU licenses). Copyright and license notices must be preserved. Contributors provide an express grant of patent rights. However, a larger work using the licensed work may be distributed under different terms and without source code for files added to the larger work.


## Get in Touch

To contact us, please refer to our mailing list `pg-qfall(at)lists.upb.de`.
