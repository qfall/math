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
Our Style guide is based on the [rust standard](https://github.com/rust-lang/rfcs/blob/master/text/0505-api-comment-conventions.md).

Every function should have a documentation. A documentation includes a description of the function, a description of every parameter, the output behavior and an example. If applicable it also includes, Error and Panic behavior and references to scientific literature. 

Here is an example documentation:

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
    pub fn sample_discrete_gauss(center: impl Into<Q>, s: impl Into<Q>) -> Result<Self, MathError> {
        let center: Q = center.into();
        let s: Q = s.into();

        let mut dgis = DiscreteGaussianIntegerSampler::init(
            &center,
            &s,
            unsafe { TAILCUT },
            LookupTableSetting::NoLookup,
        )?;

        Ok(dgis.sample_z())
    }
}
```

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


### Formating

All code has to comply with *clippy* format.
This can be ensured by running 
```bash
cargo clippy
```
## Get in Touch

To contact us, please refer to our mailing list `pg-qfall(at)lists.upb.de`.
