# 🐎 daachorse

Daac Horse: Double-Array Aho-Corasick

[![Crates.io](https://img.shields.io/crates/v/daachorse)](https://crates.io/crates/daachorse)
[![Documentation](https://docs.rs/daachorse/badge.svg)](https://docs.rs/daachorse)
![Build Status](https://github.com/legalforce-research/daachorse/actions/workflows/rust.yml/badge.svg)

## Overview

A fast implementation of the Aho-Corasick algorithm using Double-Array Trie.

### Examples

```rust
use daachorse::DoubleArrayAhoCorasick;

let patterns = vec!["bcd", "ab", "a"];
let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();

let mut it = pma.find_overlapping_iter("abcd");

let m = it.next().unwrap();
assert_eq!((0, 1, 2), (m.start(), m.end(), m.pattern()));

let m = it.next().unwrap();
assert_eq!((0, 2, 1), (m.start(), m.end(), m.pattern()));

let m = it.next().unwrap();
assert_eq!((1, 4, 0), (m.start(), m.end(), m.pattern()));

assert_eq!(None, it.next());
```

## Disclaimer

This software is developed by LegalForce, Inc.,
but not an officially supported LegalForce product.

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
