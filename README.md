# 🐎 daachorse: Double-Array Aho-Corasick

A fast implementation of the Aho-Corasick algorithm using the compact double-array data structure.

[![Crates.io](https://img.shields.io/crates/v/daachorse)](https://crates.io/crates/daachorse)
[![Documentation](https://docs.rs/daachorse/badge.svg)](https://docs.rs/daachorse)
[![Rust](https://img.shields.io/badge/rust-1.77%2B-blue.svg?maxAge=3600)](https://github.com/daac-tools/daachorse)
[![Build Status](https://github.com/daac-tools/daachorse/actions/workflows/rust.yml/badge.svg)](https://github.com/daac-tools/daachorse/actions)
[![Slack](https://img.shields.io/badge/join-chat-brightgreen?logo=slack)](https://join.slack.com/t/daac-tools/shared_invite/zt-1pwwqbcz4-KxL95Nam9VinpPlzUpEGyA)

The main technical ideas behind this library appear in the following paper:

> Shunsuke Kanda, Koichi Akabe, and Yusuke Oda.
> [Engineering faster double-array Aho-Corasick automata](https://doi.org/10.1002/spe.3190).
> *Software: Practice and Experience (SPE)*,
> 53(6): 1332–1361, 2023
> ([arXiv](https://arxiv.org/abs/2207.13870))

A Python wrapper is also available [here](https://github.com/daac-tools/python-daachorse).

## Overview

Daachorse (pronounced "dark horse") is a crate for fast multiple pattern matching using the
[Aho-Corasick algorithm](https://dl.acm.org/doi/10.1145/360825.360855), running in linear time over
the length of the input text. This crate uses the
[compact double-array data structure](https://doi.org/10.1016/j.ipm.2006.04.004) for implementing
the pattern match automaton for time and memory efficiency. The data structure not only supports
constant-time state-to-state traversal but also represents each state in the space of only 12
bytes.

## Performance comparison

![](./figures/comparison.svg)

Details are available on
[Wiki](https://github.com/daac-tools/daachorse/wiki/Performance-Comparison).

## Requirements

Rust 1.77 or higher is required to build this crate.

## Example usage

Daachorse contains some search options, ranging from standard matching with the Aho-Corasick
algorithm to more advanced matching. All of them run efficiently, powered by the double-array data
structure, and can be easily plugged into your application, as shown below.

### Finding overlapping occurrences

To search for all occurrences of registered patterns that allow for positional overlap in the input
text, use `find_overlapping_iter()`. When you use `new()` for construction, the library assigns a
unique identifier to each pattern in the input order. The match result has the byte positions of
the occurrence and its identifier.

```rust
use daachorse::DoubleArrayAhoCorasick;

let patterns = vec!["bcd", "ab", "a"];
let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();

let mut it = pma.find_overlapping_iter("abcd");

let m = it.next().unwrap();
assert_eq!((0, 1, 2), (m.start(), m.end(), m.value()));

let m = it.next().unwrap();
assert_eq!((0, 2, 1), (m.start(), m.end(), m.value()));

let m = it.next().unwrap();
assert_eq!((1, 4, 0), (m.start(), m.end(), m.value()));

assert_eq!(None, it.next());
```

### Finding non-overlapping occurrences with standard matching

To disallow positional overlap, use `find_iter()` instead. It performs the search on the
Aho-Corasick automaton and reports the first matching pattern found at each search position.

```rust
use daachorse::DoubleArrayAhoCorasick;

let patterns = vec!["bcd", "ab", "a"];
let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();

let mut it = pma.find_iter("abcd");

let m = it.next().unwrap();
assert_eq!((0, 1, 2), (m.start(), m.end(), m.value()));

let m = it.next().unwrap();
assert_eq!((1, 4, 0), (m.start(), m.end(), m.value()));

assert_eq!(None, it.next());
```

### Finding non-overlapping occurrences with longest matching

To search for the longest pattern without positional overlap in each iteration, specify
`MatchKind::LeftmostLongest` during construction and use `leftmost_find_iter()`.

```rust
use daachorse::{DoubleArrayAhoCorasickBuilder, MatchKind};

let patterns = vec!["ab", "a", "abcd"];
let pma = DoubleArrayAhoCorasickBuilder::new()
    .match_kind(MatchKind::LeftmostLongest)
    .build(&patterns)
    .unwrap();

let mut it = pma.leftmost_find_iter("abcd");

let m = it.next().unwrap();
assert_eq!((0, 4, 2), (m.start(), m.end(), m.value()));

assert_eq!(None, it.next());
```

### Finding non-overlapping occurrences with leftmost-first matching

To search for the earliest registered pattern among those starting from the search position,
specify `MatchKind::LeftmostFirst` during construction and use `leftmost_find_iter()`.

This semantics is the so-called *leftmost first match*, a tricky search option supported in the
[aho-corasick](https://github.com/BurntSushi/aho-corasick) crate. For example, in the following
code, `ab` is reported because it is the earliest registered one.

```rust
use daachorse::{DoubleArrayAhoCorasickBuilder, MatchKind};

let patterns = vec!["ab", "a", "abcd"];
let pma = DoubleArrayAhoCorasickBuilder::new()
    .match_kind(MatchKind::LeftmostFirst)
    .build(&patterns)
    .unwrap();

let mut it = pma.leftmost_find_iter("abcd");

let m = it.next().unwrap();
assert_eq!((0, 2, 0), (m.start(), m.end(), m.value()));

assert_eq!(None, it.next());
```

### Associating arbitrary values with patterns

To build the automaton from pairs of a pattern and user-defined value, instead of assigning
identifiers automatically, use `with_values()`.

```rust
use daachorse::DoubleArrayAhoCorasick;

let patvals = vec![("bcd", 0), ("ab", 10), ("a", 20)];
let pma = DoubleArrayAhoCorasick::with_values(patvals).unwrap();

let mut it = pma.find_overlapping_iter("abcd");

let m = it.next().unwrap();
assert_eq!((0, 1, 20), (m.start(), m.end(), m.value()));

let m = it.next().unwrap();
assert_eq!((0, 2, 10), (m.start(), m.end(), m.value()));

let m = it.next().unwrap();
assert_eq!((1, 4, 0), (m.start(), m.end(), m.value()));

assert_eq!(None, it.next());
```

### Building faster automata on multibyte characters

To build a faster automaton on multibyte characters, use `CharwiseDoubleArrayAhoCorasick` instead.

The standard version `DoubleArrayAhoCorasick` handles strings as UTF-8 sequences and defines
transition labels using byte values. In contrast, `CharwiseDoubleArrayAhoCorasick` uses Unicode code
point values, reducing the number of transitions and enabling faster matching on multibyte
characters.

```rust
use daachorse::CharwiseDoubleArrayAhoCorasick;

let patterns = vec!["全世界", "世界", "に"];
let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();

let mut it = pma.find_iter("全世界中に");

let m = it.next().unwrap();
assert_eq!((0, 9, 0), (m.start(), m.end(), m.value()));

let m = it.next().unwrap();
assert_eq!((12, 15, 2), (m.start(), m.end(), m.value()));

assert_eq!(None, it.next());
```

## `no_std`

Daachorse has no dependency on `std` (but requires a global allocator with the `alloc` crate).

## CLI

This repository contains a command-line interface named `daacfind` for searching patterns in text
files.

```
% cat ./pat.txt
fn
const fn
pub fn
unsafe fn
% find . -name "*.rs" | xargs cargo run --release -p daacfind -- --color=auto -nf ./pat.txt
...
...
./src/errors.rs:67:    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
./src/errors.rs:81:    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
./src/lib.rs:115:    fn default() -> Self {
./src/lib.rs:126:    pub fn base(&self) -> Option<u32> {
./src/lib.rs:131:    pub const fn check(&self) -> u8 {
./src/lib.rs:136:    pub const fn fail(&self) -> u32 {
...
...
```

## FAQ

* **Does this library support data types other than `str` and `[u8]`?
  (e.g., structures implementing `Eq`.)**

  Not supported. This library uses Aho-Corasick automata built with a
  data structure called *double-array trie*. The algorithm on this data
  structure works with XOR operations on the input haystack. Therefore,
  the haystack must be a sequence of integers. This library is specifically
  optimized for `str` and `[u8]` among integer sequences.

* **Does this library support case-insensitive matching?**

  Not supported. As a matter of policy, this library prioritizes implementation
  simplicity. Case-insensitive matching is a language-specific concept, and a different
  normalization process is required for non-Western text. If you want to treat
  multiple characters identically, you can achieve this by lowercasing or applying
  NFKC normalization to both the patterns and the haystack outside of this library.

* **Does this library provide bindings to programming languages other
  than Rust?**

  While we provide [a Python binding](https://github.com/daac-tools/python-daachorse),
  there are currently no plans to support other languages.
  If you are interested in writing bindings, you are welcome to do so.
  *daachorse* is free software.

## Slack

We have a Slack workspace for developers and users to ask questions and discuss a variety of topics.

 * https://daac-tools.slack.com/
 * Please get an invitation from [here](https://join.slack.com/t/daac-tools/shared_invite/zt-1pwwqbcz4-KxL95Nam9VinpPlzUpEGyA).

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

If you use this library in academic papers, please cite the following paper.

```
@article{10.1002/spe.3190,
    author = {Kanda, Shunsuke and Akabe, Koichi and Oda, Yusuke},
    title = {Engineering faster double-array {Aho--Corasick} automata},
    journal = {Software: Practice and Experience},
    volume={53},
    number={6},
    pages={1332--1361},
    year={2023},
    keywords = {Aho–Corasick automata, code optimization, double-array, multiple pattern matching},
    doi = {https://doi.org/10.1002/spe.3190},
    url = {https://onlinelibrary.wiley.com/doi/abs/10.1002/spe.3190},
    eprint = {https://onlinelibrary.wiley.com/doi/pdf/10.1002/spe.3190}
}
```

## Contribution

See [the guidelines](./CONTRIBUTING.md).
