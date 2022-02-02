use crate::*;

use std::collections::{HashMap, HashSet};

use rand::seq::SliceRandom;
use rand::Rng;

/// Generates a random string consisting of `size` characters from `"random"`.
fn generate_random_string(size: usize) -> String {
    const CHARSET: &[u8] = b"random";
    let mut rng = rand::thread_rng();
    (0..size)
        .map(|_| CHARSET[rng.gen_range(0..CHARSET.len())] as char)
        .collect()
}

/// Generates a random byte string consisting of `size` characters from `0..256`.
fn generate_random_binary_string(size: usize) -> Vec<u8> {
    let mut rng = rand::thread_rng();
    (0..size)
        .map(|_| rng.gen_range(u8::MIN..=u8::MAX))
        .collect()
}

/// Generates a set of random patterns mapping random values.
/// The argument `props = [(num, len)]` specifies to generate `num` strings of length `len`.
/// Random mapped values are from `0..100`.
fn generate_random_patvals<F, T>(props: &[(usize, usize)], gen: F) -> HashMap<T, u32>
where
    F: Fn(usize) -> T,
    T: std::cmp::Eq + std::hash::Hash,
{
    let mut value_gen = rand::thread_rng();
    let mut patvals = HashMap::<_, _>::new();
    for &(num, len) in props {
        for _ in 0..num {
            patvals.insert(gen(len), value_gen.gen_range(0..100));
        }
    }
    patvals
}

#[test]
fn test_dump_states_random() {
    for _ in 0..100 {
        let mut patterns = HashSet::new();
        for _ in 0..100 {
            patterns.insert(generate_random_string(8));
        }
        let patterns_vec: Vec<_> = patterns.into_iter().collect();
        let pma = DoubleArrayAhoCorasick::new(&patterns_vec).unwrap();

        let mut visitor = vec![0u32];
        let mut visited = vec![false; pma.states.len()];

        while let Some(idx) = visitor.pop() {
            assert!(!visited[idx as usize]);
            assert!(
                pma.states[idx as usize].base().is_some()
                    || pma.states[idx as usize].output_pos().is_some()
            );
            visited[idx as usize] = true;
            for c in 0..=255 {
                if let Some(child_idx) = pma.get_child_index(idx, c) {
                    visitor.push(child_idx);
                }
            }
        }
    }
}

#[test]
fn test_input_order_random() {
    let mut rng = rand::thread_rng();
    for _ in 0..100 {
        let patvals = generate_random_patvals(&[(100, 4)], generate_random_string);
        let mut patvals: Vec<_> = patvals.into_iter().collect();
        patvals.sort_by(|(s1, _), (s2, _)| s1.cmp(s2));
        let pma_sorted = DoubleArrayAhoCorasick::with_values(patvals.clone()).unwrap();
        for _ in 0..10 {
            patvals.shuffle(&mut rng);
            let pma_unsorted = DoubleArrayAhoCorasick::with_values(patvals.clone()).unwrap();
            assert_eq!(pma_sorted.states, pma_unsorted.states);
            assert_eq!(pma_sorted.outputs, pma_unsorted.outputs);
        }
    }
}

#[test]
fn test_input_order_binary_random() {
    let mut rng = rand::thread_rng();
    for _ in 0..100 {
        let patvals = generate_random_patvals(&[(100, 4)], generate_random_binary_string);
        let mut patvals: Vec<_> = patvals.into_iter().collect();
        patvals.sort_by(|(s1, _), (s2, _)| s1.cmp(s2));
        let pma_sorted = DoubleArrayAhoCorasick::with_values(patvals.clone()).unwrap();
        for _ in 0..10 {
            patvals.shuffle(&mut rng);
            let pma_unsorted = DoubleArrayAhoCorasick::with_values(patvals.clone()).unwrap();
            assert_eq!(pma_sorted.states, pma_unsorted.states);
            assert_eq!(pma_sorted.outputs, pma_unsorted.outputs);
        }
    }
}
