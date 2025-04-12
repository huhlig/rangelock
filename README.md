# Rangelock

[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)
[![Actions Status](https://github.com/huhlig/rangelock/actions/workflows/rust.yml/badge.svg)](https://github.com/huhlig/rangelock/actions)

([API Docs])

> A Rust library providing concurrent access to ranges within data structures. Features range-based read-write locks 
> and mutexes, allowing multiple threads to safely access non-overlapping ranges simultaneously. Ideal for parallel 
> processing of contiguous data.

## Project Structure

* `.github` - GitHub Actions Workflows and Issue Templates
* `benches` - Project Benchmarks
* `src` - The Source Code

## License

This project is licensed under [Apache License, Version 2.0](http://www.apache.org/licenses/LICENSE-2.0).

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you, as 
defined in the Apache-2.0 license, shall be licensed as above, without any additional terms or conditions.

[API Docs]: https://huhlig.github.io/rangelock/