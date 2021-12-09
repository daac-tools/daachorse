use super::*;

use std::collections::{HashMap, HashSet};

use rand::Rng;

fn generate_random_string(size: usize) -> String {
    const CHARSET: &[u8] = b"random";
    let mut rng = rand::thread_rng();

    (0..size)
        .map(|_| {
            let idx = rng.gen_range(0..CHARSET.len());
            CHARSET[idx] as char
        })
        .collect()
}

fn generate_random_binary_string(size: usize) -> Vec<u8> {
    let mut rng = rand::thread_rng();
    (0..size).map(|_| rng.gen_range(0..=255)).collect()
}

// props are a sequence of (num, length) to generate.
fn generate_random_patterns<F, T>(props: &[(usize, usize)], gen: F) -> HashSet<T>
where
    F: Fn(usize) -> T,
    T: std::cmp::Eq + std::hash::Hash,
{
    let mut patterns = HashSet::<T>::new();
    for &(num, len) in props {
        for _ in 0..num {
            patterns.insert(gen(len));
        }
    }
    patterns
}

// props are a sequence of (num, length) to generate.
fn generate_random_patvals<F, T>(props: &[(usize, usize)], gen: F) -> HashMap<T, u32>
where
    F: Fn(usize) -> T,
    T: std::cmp::Eq + std::hash::Hash,
{
    let mut value_gen = rand::thread_rng();
    let mut patvals = HashMap::<T, u32>::new();
    for &(num, len) in props {
        for _ in 0..num {
            patvals.insert(gen(len), value_gen.gen_range(0..100));
        }
    }
    patvals
}

#[test]
fn test_double_array() {
    /*
     *          a--> 4
     *         /
     *   a--> 1 --c--> 5
     *  /
     * 0 --b--> 2 --c--> 6
     *  \
     *   c--> 3
     *
     *   a = 0
     *   b = 1
     *   c = 2
     */
    let patterns = vec![vec![0, 0], vec![0, 2], vec![1, 2], vec![2]];
    let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();

    let base_expected = vec![
        4,            // 0  (state=0)
        BASE_INVALID, // 1
        BASE_INVALID, // 2  (state=6)
        BASE_INVALID, // 3
        8,            // 4  (state=1)
        0,            // 5  (state=2)
        BASE_INVALID, // 6  (state=3)
        BASE_INVALID, // 7
        BASE_INVALID, // 8  (state=4)
        BASE_INVALID, // 9
        BASE_INVALID, // 10 (state=5)
    ];
    let check_expected = vec![
        1, // 0  (state=0)
        0, // 1
        2, // 2  (state=6)
        2, // 3
        0, // 4  (state=1)
        1, // 5  (state=2)
        2, // 6  (state=3)
        6, // 7
        0, // 8  (state=4)
        8, // 9
        2, // 10 (state=5)
    ];
    let fail_expected = vec![
        ROOT_STATE_IDX, // 0  (state=0)
        ROOT_STATE_IDX, // 1
        6,              // 2  (state=6)
        ROOT_STATE_IDX, // 3
        ROOT_STATE_IDX, // 4  (state=1)
        ROOT_STATE_IDX, // 5  (state=2)
        ROOT_STATE_IDX, // 6  (state=3)
        ROOT_STATE_IDX, // 7
        4,              // 8  (state=4)
        ROOT_STATE_IDX, // 9
        6,              // 10 (state=5)
    ];

    let pma_base: Vec<_> = pma.states[0..11]
        .iter()
        .map(|state| state.base().unwrap_or(BASE_INVALID))
        .collect();
    let pma_check: Vec<_> = pma.states[0..11]
        .iter()
        .map(|state| state.check())
        .collect();
    let pma_fail: Vec<_> = pma.states[0..11]
        .iter()
        .map(|state| state.fail() as usize)
        .collect();

    assert_eq!(base_expected, pma_base);
    assert_eq!(check_expected, pma_check);
    assert_eq!(fail_expected, pma_fail);
}

#[test]
fn test_find_iter_random() {
    for _ in 0..100 {
        let patterns = generate_random_patterns(&[(100, 4)], generate_random_string);
        let haystack = generate_random_string(100);

        // naive pattern match
        let mut expected = HashSet::new();
        let mut pos = 0;
        while pos <= haystack.len() - 4 {
            if patterns.contains(&haystack[pos..pos + 4]) {
                expected.insert((pos, pos + 4, haystack[pos..pos + 4].to_string()));
                pos += 3;
            }
            pos += 1;
        }

        // daachorse
        let mut actual = HashSet::new();
        let patterns_vec: Vec<_> = patterns.into_iter().collect();
        let pma = DoubleArrayAhoCorasick::new(&patterns_vec).unwrap();
        for m in pma.find_iter(&haystack) {
            actual.insert((m.start(), m.end(), patterns_vec[m.value()].clone()));
        }
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_find_iter_random_with_values() {
    for _ in 0..100 {
        let patvals = generate_random_patvals(&[(100, 4)], generate_random_string);
        let haystack = generate_random_string(100);

        // naive pattern match
        let mut expected = HashMap::new();
        let mut pos = 0;
        while pos <= haystack.len() - 4 {
            if let Some(&v) = patvals.get(&haystack[pos..pos + 4]) {
                expected.insert((pos, pos + 4), v as usize);
                pos += 3;
            }
            pos += 1;
        }

        // daachorse
        let mut actual = HashMap::new();
        let patvals_vec: Vec<_> = patvals.into_iter().collect();
        let pma = DoubleArrayAhoCorasick::with_values(patvals_vec).unwrap();
        for m in pma.find_iter(&haystack) {
            actual.insert((m.start(), m.end()), m.value());
        }
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_find_iter_binary_random() {
    for _ in 0..100 {
        let patterns = generate_random_patterns(&[(100, 4)], generate_random_binary_string);
        let haystack = generate_random_binary_string(100);

        // naive pattern match
        let mut expected = HashSet::new();
        let mut pos = 0;
        while pos <= haystack.len() - 4 {
            if patterns.contains(&haystack[pos..pos + 4]) {
                expected.insert((pos, pos + 4, haystack[pos..pos + 4].to_vec()));
                pos += 3;
            }
            pos += 1;
        }

        // daachorse
        let mut actual = HashSet::new();
        let patterns_vec: Vec<_> = patterns.into_iter().collect();
        let pma = DoubleArrayAhoCorasick::new(&patterns_vec).unwrap();
        for m in pma.find_iter(&haystack) {
            actual.insert((m.start(), m.end(), patterns_vec[m.value()].clone()));
        }
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_find_iter_binary_random_with_values() {
    for _ in 0..100 {
        let patvals = generate_random_patvals(&[(100, 4)], generate_random_binary_string);
        let haystack = generate_random_binary_string(100);

        // naive pattern match
        let mut expected = HashMap::new();
        let mut pos = 0;
        while pos <= haystack.len() - 4 {
            if let Some(&v) = patvals.get(&haystack[pos..pos + 4]) {
                expected.insert((pos, pos + 4), v as usize);
                pos += 3;
            }
            pos += 1;
        }

        // daachorse
        let mut actual = HashMap::new();
        let patvals_vec: Vec<_> = patvals.into_iter().collect();
        let pma = DoubleArrayAhoCorasick::with_values(patvals_vec).unwrap();
        for m in pma.find_iter(&haystack) {
            actual.insert((m.start(), m.end()), m.value());
        }
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_find_overlapping_iter_random() {
    for _ in 0..100 {
        let patterns = generate_random_patterns(
            &[(6, 1), (20, 2), (50, 3), (100, 4)],
            generate_random_string,
        );
        let haystack = generate_random_string(100);

        // naive pattern match
        let mut expected = HashSet::new();
        for i in 0..4 {
            for pos in 0..haystack.len() - i {
                if patterns.contains(&haystack[pos..pos + i + 1]) {
                    expected.insert((pos, pos + i + 1, haystack[pos..pos + i + 1].to_string()));
                }
            }
        }

        // daachorse
        let mut actual = HashSet::new();
        let patterns_vec: Vec<_> = patterns.into_iter().collect();
        let pma = DoubleArrayAhoCorasick::new(&patterns_vec).unwrap();
        for m in pma.find_overlapping_iter(&haystack) {
            actual.insert((m.start(), m.end(), patterns_vec[m.value()].clone()));
        }
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_find_overlapping_iter_random_with_values() {
    for _ in 0..100 {
        let patvals = generate_random_patvals(
            &[(6, 1), (20, 2), (50, 3), (100, 4)],
            generate_random_string,
        );
        let haystack = generate_random_string(100);

        // naive pattern match
        let mut expected = HashMap::new();
        for i in 0..4 {
            for pos in 0..haystack.len() - i {
                if let Some(&v) = patvals.get(&haystack[pos..pos + i + 1]) {
                    expected.insert((pos, pos + i + 1), v as usize);
                }
            }
        }

        // daachorse
        let mut actual = HashMap::new();
        let patvals_vec: Vec<_> = patvals.into_iter().collect();
        let pma = DoubleArrayAhoCorasick::with_values(patvals_vec).unwrap();
        for m in pma.find_overlapping_iter(&haystack) {
            actual.insert((m.start(), m.end()), m.value());
        }
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_find_overlapping_iter_binary_random() {
    for _ in 0..100 {
        let patterns = generate_random_patterns(
            &[(6, 1), (20, 2), (50, 3), (100, 4)],
            generate_random_binary_string,
        );
        let haystack = generate_random_binary_string(100);

        // naive pattern match
        let mut expected = HashSet::new();
        for i in 0..4 {
            for pos in 0..haystack.len() - i {
                if patterns.contains(&haystack[pos..pos + i + 1]) {
                    expected.insert((pos, pos + i + 1, haystack[pos..pos + i + 1].to_vec()));
                }
            }
        }

        // daachorse
        let mut actual = HashSet::new();
        let patterns_vec: Vec<_> = patterns.into_iter().collect();
        let pma = DoubleArrayAhoCorasick::new(&patterns_vec).unwrap();
        for m in pma.find_overlapping_iter(&haystack) {
            actual.insert((m.start(), m.end(), patterns_vec[m.value()].clone()));
        }
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_find_overlapping_iter_binary_random_with_values() {
    for _ in 0..100 {
        let patvals = generate_random_patvals(
            &[(6, 1), (20, 2), (50, 3), (100, 4)],
            generate_random_binary_string,
        );
        let haystack = generate_random_binary_string(100);

        // naive pattern match
        let mut expected = HashMap::new();
        for i in 0..4 {
            for pos in 0..haystack.len() - i {
                if let Some(&v) = patvals.get(&haystack[pos..pos + i + 1]) {
                    expected.insert((pos, pos + i + 1), v as usize);
                }
            }
        }

        // daachorse
        let mut actual = HashMap::new();
        let patvals_vec: Vec<_> = patvals.into_iter().collect();
        let pma = DoubleArrayAhoCorasick::with_values(patvals_vec).unwrap();
        for m in pma.find_overlapping_iter(&haystack) {
            actual.insert((m.start(), m.end()), m.value());
        }
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_leftmost_longest_find_iter_random() {
    for _ in 0..100 {
        let patterns = generate_random_patterns(
            &[(6, 1), (20, 2), (50, 3), (100, 4)],
            generate_random_string,
        );
        let haystack = generate_random_string(100);

        // naive pattern match
        let mut expected = HashSet::new();
        let mut pos = 0;
        while pos < haystack.len() {
            for i in (0..4).rev() {
                if pos + i >= haystack.len() {
                    continue;
                }
                if patterns.contains(&haystack[pos..pos + i + 1]) {
                    expected.insert((pos, pos + i + 1, haystack[pos..pos + i + 1].to_string()));
                    pos += i;
                    break;
                }
            }
            pos += 1;
        }

        // daachorse
        let mut actual = HashSet::new();
        let patterns_vec: Vec<_> = patterns.into_iter().collect();
        let pma = DoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostLongest)
            .build(&patterns_vec)
            .unwrap();
        for m in pma.leftmost_find_iter(&haystack) {
            actual.insert((m.start(), m.end(), patterns_vec[m.value()].clone()));
        }
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_leftmost_longest_find_iter_random_with_values() {
    for _ in 0..100 {
        let patvals = generate_random_patvals(
            &[(6, 1), (20, 2), (50, 3), (100, 4)],
            generate_random_string,
        );
        let haystack = generate_random_string(100);

        // naive pattern match
        let mut expected = HashMap::new();
        let mut pos = 0;
        while pos < haystack.len() {
            for i in (0..4).rev() {
                if pos + i >= haystack.len() {
                    continue;
                }
                if let Some(&v) = patvals.get(&haystack[pos..pos + i + 1]) {
                    expected.insert((pos, pos + i + 1), v as usize);
                    pos += i;
                    break;
                }
            }
            pos += 1;
        }

        // daachorse
        let mut actual = HashMap::new();
        let patvals_vec: Vec<_> = patvals.into_iter().collect();
        let pma = DoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostLongest)
            .build_with_values(patvals_vec)
            .unwrap();
        for m in pma.leftmost_find_iter(&haystack) {
            actual.insert((m.start(), m.end()), m.value());
        }
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_leftmost_longest_find_iter_binary_random() {
    for _ in 0..100 {
        let patterns = generate_random_patterns(
            &[(6, 1), (20, 2), (50, 3), (100, 4)],
            generate_random_binary_string,
        );
        let haystack = generate_random_binary_string(100);

        // naive pattern match
        let mut expected = HashSet::new();
        let mut pos = 0;
        while pos < haystack.len() {
            for i in (0..4).rev() {
                if pos + i >= haystack.len() {
                    continue;
                }
                if patterns.contains(&haystack[pos..pos + i + 1]) {
                    expected.insert((pos, pos + i + 1, haystack[pos..pos + i + 1].to_vec()));
                    pos += i;
                    break;
                }
            }
            pos += 1;
        }

        // daachorse
        let mut actual = HashSet::new();
        let patterns_vec: Vec<_> = patterns.into_iter().collect();
        let pma = DoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostLongest)
            .build(&patterns_vec)
            .unwrap();
        for m in pma.leftmost_find_iter(&haystack) {
            actual.insert((m.start(), m.end(), patterns_vec[m.value()].clone()));
        }
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_leftmost_longest_find_iter_binary_random_with_values() {
    for _ in 0..100 {
        let patvals = generate_random_patvals(
            &[(6, 1), (20, 2), (50, 3), (100, 4)],
            generate_random_binary_string,
        );
        let haystack = generate_random_binary_string(100);

        // naive pattern match
        let mut expected = HashMap::new();
        let mut pos = 0;
        while pos < haystack.len() {
            for i in (0..4).rev() {
                if pos + i >= haystack.len() {
                    continue;
                }
                if let Some(&v) = patvals.get(&haystack[pos..pos + i + 1]) {
                    expected.insert((pos, pos + i + 1), v as usize);
                    pos += i;
                    break;
                }
            }
            pos += 1;
        }

        // daachorse
        let mut actual = HashMap::new();
        let patvals_vec: Vec<_> = patvals.into_iter().collect();
        let pma = DoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostLongest)
            .build_with_values(patvals_vec)
            .unwrap();
        for m in pma.leftmost_find_iter(&haystack) {
            actual.insert((m.start(), m.end()), m.value());
        }
        assert_eq!(expected, actual);
    }
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

        let mut visitor = vec![0 as usize];
        let mut visited = vec![false; pma.states.len()];

        while let Some(idx) = visitor.pop() {
            assert!(!visited[idx]);
            assert!(pma.states[idx].base().is_some() || pma.states[idx].output_pos().is_some());
            visited[idx] = true;
            for c in 0..=255 {
                if let Some(child_idx) = pma.get_child_index(idx, c) {
                    visitor.push(child_idx);
                }
            }
        }
    }
}

#[test]
#[should_panic]
fn test_to_create_find_iter_with_leftmost_longest() {
    let pma = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build([""])
        .unwrap();
    pma.find_iter("");
}

#[test]
#[should_panic]
fn test_to_create_find_iter_with_leftmost_first() {
    let pma = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build([""])
        .unwrap();
    pma.find_iter("");
}

#[test]
#[should_panic]
fn test_to_create_find_overlapping_iter_with_leftmost_longest() {
    let pma = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build([""])
        .unwrap();
    pma.find_overlapping_iter("");
}

#[test]
#[should_panic]
fn test_to_create_find_overlapping_iter_with_leftmost_first() {
    let pma = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build([""])
        .unwrap();
    pma.find_overlapping_iter("");
}

#[test]
#[should_panic]
fn test_to_create_find_overlapping_no_suffix_iter_with_leftmost_longest() {
    let pma = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build([""])
        .unwrap();
    pma.find_overlapping_no_suffix_iter("");
}

#[test]
#[should_panic]
fn test_to_create_find_overlapping_no_suffix_iter_with_leftmost_first() {
    let pma = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build([""])
        .unwrap();
    pma.find_overlapping_no_suffix_iter("");
}

#[test]
#[should_panic]
fn test_to_create_leftmost_find_iter_with_standard() {
    let pma = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::Standard)
        .build([""])
        .unwrap();
    pma.leftmost_find_iter("");
}
