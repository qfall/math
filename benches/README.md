// Copyright © 2023 Sven Moog
//
// This file is part of qFALL-math.
//
// qFALL-math is free software: you can redistribute it and/or modify it under
// the terms of the Mozilla Public License Version 2.0 as published by the
// Mozilla Foundation. See <https://mozilla.org/en-US/MPL/2.0/>.


# How to run benchmarks:
## Criterion
We use criterion for statistical analysis. A plotting library has to be installed to generate graphs. You can find more information and help here: 
- [Criterion-rs GitHub](https://github.com/bheisler/criterion.rs)
- [Cargo-criterion GitHub](https://github.com/bheisler/cargo-criterion)
- [Criterion Book](https://bheisler.github.io/criterion.rs/book/criterion_rs.html)(!Watchout for the criterion version, as of writing this the book is not on the latest version!)


### Commands
a) ```cargo criterion <benchmark name regex>```  
Has to be installed with `cargo install criterion`.  
Pros:
- You can remove `features = ["html_reports"]` from the `Cargo.toml` leading to a (slightly) faster compile times.
- Criterion aims to move to just using cargo criterion
- The large Probability Density Function graph shows the samples and marks the outlier categorization boarders.

b) ```cargo bench <benchmark name regex>```  
Pros:
- Can visualize the change in performance compared to previous run or other baseline

## Flamegraph
You can also run the benchmarks using the profiler flamegraph. Details can be found here:
- [Flamegraph GitHub](https://github.com/flamegraph-rs/flamegraph).
This provides insights on the where execution time is spent.

### Command
```cargo flamegraph --freq 63300 --bench benchmarks -- --bench --profile-time 5 <benchmark name regex>```  
Generates a flamegraph that allows to approximate how long each function executes. The accuracy of the approximation is better the more samples are produced. This can be improved by 
- increasing the sample frequency (`--freq 63300`), This frequency is throttled to the highest possible frequency which depends on the cpu, cpu-temperature, power settings and much more...
- increasing `profile-time` (in seconds). This is how long the benchmark code will be executed.
This parameter also disables the statistical analysis of criterion which prevents it from showing up in the graph.
This parameter is optional, but suggested.

The flamegraph can be overwhelming since it exposes a lot of internal workings of rust, criterion, and more.
The easiest way to find the function you are looking for is to search for it with `Ctrl + F`.
You have to enter a part of the rust function name or regex (not the benchmark name).

# How to create benchmarks
 
## No appropriate file exists so far:
   1. create the file
   2. Insert in new file:
        ``` rust 
        use criterion::*;

        criterion_group!(benches);
        ```
   3. Insert in [benchmarks.rs](/benches/benchmarks.rs):
        ``` rust 
        pub mod <new_file_name>;
        ```
      and `<new_file_name>::benches` in the `criterion_main!` macro.

## Appropriately named benchmark file exists in `/benches` (e.g. `integer.rs`)
   1. Create a function that performs the functionality that should be benchmarked (called `do_stuff` below).
   2. Add a function to handle the interaction with criterion.
      e.g.:
      ``` rust
      pub fn bench_do_stuff(c: &mut Criterion) {
          c.bench_function("<benchmark name here>", |b| b.iter(|| do_stuff()));
      }
      ```
      The benchmark name specified here is later used to select which benchmark to run and also displayed in the output.
      This function can also look differently, for example, because it uses [criterion groups](https://docs.rs/criterion/latest/criterion/struct.BenchmarkGroup.html).
   3. Add function created in step 2 in the `criterion_group!` macro (bottom of file).

