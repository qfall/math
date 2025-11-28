# Contributing
This library is designed to prototype lattice-based cryptography. Our intent for this library is to be maintained by the community. We encourage anyone to add missing, frequently used features for lattice-based prototyping to this library, and we are happy to help with that process.

More generally, all contributions such as bugfixes, documentation and tests are welcome. Please go ahead and submit your pull requests.

## Choosing the right location
The qFALL library is divided into three repositories: [qFALL-math](https://github.com/qfall/math), [qFALL-tools](https://github.com/qfall/tools) and [qFALL-schemes](https://github.com/qfall/schemes).

Please add new features to one of these repositories, roughly following these guidelines.
- If your feature implements a general mathematical function, then add your code to [qFALL-math](https://github.com/qfall/math).
- If your feature implements a fundamental primitive or shortcut that is commonly used in the construction of lattice-based schemes, e.g., G-trapdoors, then add your code to [qFALL-tools](https://github.com/qfall/tools).
- If you implement a construction, e.g., Kyber, then add your code to [qFALL-schemes](https://github.com/qfall/schemes).

When in doubt, just submit your pull request to the repository you feel is best suited for your code. We will sort it.

## Style Guide
Our style guide is based on the [rust standard](https://github.com/rust-lang/rfcs/blob/master/text/0505-api-comment-conventions.md). These rules summarise our style guidelines.
- Every function should be documented. A doc-comment includes a concise description of the function and an example. In case it receives parameters other than `self`, it also includes a description of every parameter, the output type, and behavior. If applicable, it also includes Error and Panic behavior and references to scientific literature.
- If the code of your function is not self-explanatory from your doc-comment, use inline-comments `//` to briefly describe the steps.
- A file should always have the copyright notice at the top, followed by a very brief inner doc-comment to summarise the purpose of this file, grouped up imports, implementations of all features, and finally tests of each feature in a separate test-module with a brief doc-comment for each test.
- Overall, any feature should get a descriptive but concise name s.t. it can be discovered intuitively.
- Code in our library needs to be formatted using `cargo fmt` and satisfy `clippy`'s standards.
- We aim for multiple tests per function, its unforeseen behavior, panic or error-cases to boost confidence in our implementations and ensure that modifications of a function only introduce intended changes of behavior.
- Last but not least, we would like to minimise the number of dependencies of all crates to keep them as slim and quickly compilable as possible.

## Documentation
The documentation for each crate is available online and it can be generated locally by running the following command in the root directory of this repository.
```bash
cargo doc --open
```

Furthermore, here is an example of a doc-comment of a function that follows our guidelines.
```rust
impl Z {
    /// Chooses a [`Z`] instance according to the discrete Gaussian distribution
    /// in `[center - ⌈6 * s⌉ , center + ⌊6 * s⌋ ]`.
    ///
    /// This function samples discrete Gaussians according to the definition of
    /// SampleZ in [GPV08](https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=d9f54077d568784c786f7b1d030b00493eb3ae35).
    ///
    /// Parameters:
    /// - `n`: specifies the range from which is sampled
    /// - `center`: specifies the position of the center with peak probability
    /// - `s`: specifies the Gaussian parameter, which is proportional
    ///   to the standard deviation `sigma * sqrt(2 * pi) = s`
    ///
    /// Returns new [`Z`] sample chosen according to the specified discrete Gaussian
    /// distribution or a [`MathError`] if the specified parameters were not chosen
    /// appropriately, i.e. `s < 0`.
    ///
    /// # Examples
    /// ```
    /// use qfall_math::integer::Z;
    ///
    /// let sample = Z::sample_discrete_gauss(0, 1).unwrap();
    /// ```
    ///
    /// # Errors and Failures
    /// - Returns a [`MathError`] of type [`InvalidIntegerInput`](MathError::InvalidIntegerInput)
    ///   if `s < 0`.
    ///
    /// This function implements SampleZ according to:
    /// - \[1\] Gentry, Craig and Peikert, Chris and Vaikuntanathan, Vinod (2008).
    ///   Trapdoors for hard lattices and new cryptographic constructions.
    ///   In: Proceedings of the fortieth annual ACM symposium on Theory of computing.
    ///   <https://dl.acm.org/doi/pdf/10.1145/1374376.1374407>
    pub fn sample_discrete_gauss(center: impl Into<Q>, s: impl Into<Q>) -> Result<Self, MathError> {...}
}
```
