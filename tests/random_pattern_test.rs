use std::collections::{HashMap, HashSet};

use rand::Rng;

use daachorse::{DoubleArrayAhoCorasick, DoubleArrayAhoCorasickBuilder, MatchKind};

/// Creates a mapping from patterns to values.
/// Also, returns the maximum and minimum lengthes of patterns.
fn make_naive_map<I, P>(patvals: I) -> (HashMap<Vec<u8>, u32>, usize, usize)
where
    I: IntoIterator<Item = (P, u32)>,
    P: AsRef<[u8]>,
{
    let mut map = HashMap::new();
    let (mut min_len, mut max_len) = (std::usize::MAX, 0);
    for (pat, val) in patvals {
        let pat = pat.as_ref();
        assert_ne!(pat.len(), 0);
        let found = map.insert(pat.to_vec(), val);
        assert_eq!(found, None);
        min_len = min_len.min(pat.len());
        max_len = max_len.max(pat.len());
    }
    (map, min_len, max_len)
}

/// Finds non-overlapped occurrences with shortest matching in a naive manner,
/// returning answers consisting of `(start, end) => value` mappings.
fn naive_find<I, P>(patvals: I, haystack: P) -> HashMap<(usize, usize), usize>
where
    I: IntoIterator<Item = (P, u32)>,
    P: AsRef<[u8]>,
{
    let (map, min_len, max_len) = make_naive_map(patvals);
    assert_ne!(min_len, 0);

    let haystack = haystack.as_ref();
    let mut answers = HashMap::new();

    let mut pos = 0;
    while pos < haystack.len() {
        // The forward search simulates traversals with child pointers.
        'forward: for l in min_len..max_len + 1 {
            if let Some(subject) = haystack.get(pos..pos + l) {
                if let Some(&v) = map.get(subject) {
                    answers.insert((pos, pos + l), v as usize);
                    pos += l - 1;
                    break;
                }
                // The backward search simulates traversals with failure pointers.
                for m in (min_len..l).rev() {
                    if let Some(&v) = map.get(&haystack[pos + l - m..pos + l]) {
                        answers.insert((pos + l - m, pos + l), v as usize);
                        pos += l - 1;
                        break 'forward;
                    }
                }
            } else {
                break;
            }
        }
        pos += 1;
    }
    answers
}

/// Finds all overlapped occurrences in a naive manner,
/// returning answers consisting of `(start, end) => value` mappings.
fn naive_find_overlapping<I, P>(patvals: I, haystack: P) -> HashMap<(usize, usize), usize>
where
    I: IntoIterator<Item = (P, u32)>,
    P: AsRef<[u8]>,
{
    let (map, min_len, max_len) = make_naive_map(patvals);
    assert_ne!(min_len, 0);

    let haystack = haystack.as_ref();
    let mut answers = HashMap::new();

    let mut pos = 0;
    while pos < haystack.len() {
        for l in min_len..max_len + 1 {
            if let Some(subject) = haystack.get(pos..pos + l) {
                if let Some(&v) = map.get(subject) {
                    answers.insert((pos, pos + l), v as usize);
                }
            } else {
                break;
            }
        }
        pos += 1;
    }
    answers
}

/// Finds non-overlapped occurrences with longest matching in a naive manner,
/// returning answers consisting of `(start, end) => value` mappings.
fn naive_leftmost_longest_find<I, P>(patvals: I, haystack: P) -> HashMap<(usize, usize), usize>
where
    I: IntoIterator<Item = (P, u32)>,
    P: AsRef<[u8]>,
{
    let (map, min_len, max_len) = make_naive_map(patvals);
    assert_ne!(min_len, 0);

    let haystack = haystack.as_ref();
    let mut answers = HashMap::new();

    let mut pos = 0;
    while pos < haystack.len() {
        for l in (min_len..max_len + 1).rev() {
            if let Some(subject) = haystack.get(pos..pos + l) {
                if let Some(&v) = map.get(subject) {
                    answers.insert((pos, pos + l), v as usize);
                    pos += l - 1;
                    break;
                }
            }
        }
        pos += 1;
    }
    answers
}

/// Finds non-overlapped occurrences with leftmost-first matching in a naive manner,
/// returning answers consisting of `(start, end) => value` mappings.
fn naive_leftmost_first_find<I, P>(patvals: I, haystack: P) -> HashMap<(usize, usize), usize>
where
    I: IntoIterator<Item = (P, u32)>,
    P: AsRef<[u8]>,
{
    let list: Vec<_> = patvals
        .into_iter()
        .map(|(p, v)| (p.as_ref().to_vec(), v))
        .collect();

    let haystack = haystack.as_ref();
    let mut answers = HashMap::new();

    let mut pos = 0;
    while pos < haystack.len() {
        for (p, v) in &list {
            let l = p.len();
            if let Some(subject) = haystack.get(pos..pos + l) {
                if p == subject {
                    answers.insert((pos, pos + l), *v as usize);
                    pos += l - 1;
                    break;
                }
            }
        }
        pos += 1;
    }
    answers
}

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

/// Generates a set of random patterns.
/// The argument `props = [(num, len)]` specifies to generate `num` strings of length `len`.
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
fn test_find_iter_random() {
    for _ in 0..100 {
        let patterns = generate_random_patterns(
            &[(6, 1), (20, 2), (50, 3), (100, 4)],
            generate_random_string,
        );
        let haystack = generate_random_string(100);

        // naive pattern match
        let expected = naive_find(
            patterns.iter().enumerate().map(|(i, p)| (p, i as u32)),
            &haystack,
        );

        // daachorse
        let mut actual = HashMap::new();
        let pma = DoubleArrayAhoCorasick::new(patterns.iter()).unwrap();
        for m in pma.find_iter(&haystack) {
            actual.insert((m.start(), m.end()), m.value());
        }
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_find_iter_random_with_values() {
    for _ in 0..100 {
        let patvals = generate_random_patvals(
            &[(6, 1), (20, 2), (50, 3), (100, 4)],
            generate_random_string,
        );
        let haystack = generate_random_string(100);

        // naive pattern match
        let expected = naive_find(patvals.iter().map(|(p, &v)| (p, v)), &haystack);

        // daachorse
        let mut actual = HashMap::new();
        let pma = DoubleArrayAhoCorasick::with_values(patvals).unwrap();
        for m in pma.find_iter(&haystack) {
            actual.insert((m.start(), m.end()), m.value());
        }
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_find_iter_binary_random() {
    for _ in 0..100 {
        let patterns = generate_random_patterns(
            &[(6, 1), (20, 2), (50, 3), (100, 4)],
            generate_random_binary_string,
        );
        let haystack = generate_random_binary_string(100);

        // naive pattern match
        let expected = naive_find(
            patterns.iter().enumerate().map(|(i, p)| (p, i as u32)),
            &haystack,
        );

        // daachorse
        let mut actual = HashMap::new();
        let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
        for m in pma.find_iter(&haystack) {
            actual.insert((m.start(), m.end()), m.value());
        }
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_find_iter_binary_random_with_values() {
    for _ in 0..100 {
        let patvals = generate_random_patvals(
            &[(6, 1), (20, 2), (50, 3), (100, 4)],
            generate_random_binary_string,
        );
        let haystack = generate_random_binary_string(100);

        // naive pattern match
        let expected = naive_find(patvals.iter().map(|(p, &v)| (p, v)), &haystack);

        // daachorse
        let mut actual = HashMap::new();
        let pma = DoubleArrayAhoCorasick::with_values(patvals).unwrap();
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
        let expected = naive_find_overlapping(
            patterns.iter().enumerate().map(|(i, p)| (p, i as u32)),
            &haystack,
        );

        // daachorse
        let mut actual = HashMap::new();
        let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
        for m in pma.find_overlapping_iter(&haystack) {
            actual.insert((m.start(), m.end()), m.value());
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
        let expected = naive_find_overlapping(patvals.iter().map(|(p, &v)| (p, v)), &haystack);

        // daachorse
        let mut actual = HashMap::new();
        let pma = DoubleArrayAhoCorasick::with_values(patvals).unwrap();
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
        let expected = naive_find_overlapping(
            patterns.iter().enumerate().map(|(i, p)| (p, i as u32)),
            &haystack,
        );

        // daachorse
        let mut actual = HashMap::new();
        let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
        for m in pma.find_overlapping_iter(&haystack) {
            actual.insert((m.start(), m.end()), m.value());
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
        let expected = naive_find_overlapping(patvals.iter().map(|(p, &v)| (p, v)), &haystack);

        // daachorse
        let mut actual = HashMap::new();
        let pma = DoubleArrayAhoCorasick::with_values(patvals).unwrap();
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
        let expected = naive_leftmost_longest_find(
            patterns.iter().enumerate().map(|(i, p)| (p, i as u32)),
            &haystack,
        );

        // daachorse
        let mut actual = HashMap::new();
        let pma = DoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostLongest)
            .build(patterns)
            .unwrap();
        for m in pma.leftmost_find_iter(&haystack) {
            actual.insert((m.start(), m.end()), m.value());
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
        let expected = naive_leftmost_longest_find(patvals.iter().map(|(p, &v)| (p, v)), &haystack);

        // daachorse
        let mut actual = HashMap::new();
        let pma = DoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostLongest)
            .build_with_values(patvals)
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
        let expected = naive_leftmost_longest_find(
            patterns.iter().enumerate().map(|(i, p)| (p, i as u32)),
            &haystack,
        );

        // daachorse
        let mut actual = HashMap::new();
        let pma = DoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostLongest)
            .build(patterns)
            .unwrap();
        for m in pma.leftmost_find_iter(&haystack) {
            actual.insert((m.start(), m.end()), m.value());
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
        let expected = naive_leftmost_longest_find(patvals.iter().map(|(p, &v)| (p, v)), &haystack);

        // daachorse
        let mut actual = HashMap::new();
        let pma = DoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostLongest)
            .build_with_values(patvals)
            .unwrap();
        for m in pma.leftmost_find_iter(&haystack) {
            actual.insert((m.start(), m.end()), m.value());
        }
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_leftmost_first_find_iter_random() {
    for _ in 0..100 {
        let patterns = generate_random_patterns(
            &[(6, 1), (20, 2), (50, 3), (100, 4)],
            generate_random_string,
        );
        let haystack = generate_random_string(100);

        // naive pattern match
        let expected = naive_leftmost_first_find(
            patterns.iter().enumerate().map(|(i, p)| (p, i as u32)),
            &haystack,
        );

        // daachorse
        let mut actual = HashMap::new();
        let pma = DoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostFirst)
            .build(patterns)
            .unwrap();
        for m in pma.leftmost_find_iter(&haystack) {
            actual.insert((m.start(), m.end()), m.value());
        }
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_leftmost_first_find_iter_random_with_values() {
    for _ in 0..100 {
        let patvals = generate_random_patvals(
            &[(6, 1), (20, 2), (50, 3), (100, 4)],
            generate_random_string,
        );
        let haystack = generate_random_string(100);

        // naive pattern match
        let expected = naive_leftmost_first_find(patvals.iter().map(|(p, &v)| (p, v)), &haystack);

        // daachorse
        let mut actual = HashMap::new();
        let pma = DoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostFirst)
            .build_with_values(patvals)
            .unwrap();
        for m in pma.leftmost_find_iter(&haystack) {
            actual.insert((m.start(), m.end()), m.value());
        }
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_leftmost_first_find_iter_binary_random() {
    for _ in 0..100 {
        let patterns = generate_random_patterns(
            &[(6, 1), (20, 2), (50, 3), (100, 4)],
            generate_random_binary_string,
        );
        let haystack = generate_random_binary_string(100);

        // naive pattern match
        let expected = naive_leftmost_first_find(
            patterns.iter().enumerate().map(|(i, p)| (p, i as u32)),
            &haystack,
        );

        // daachorse
        let mut actual = HashMap::new();
        let pma = DoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostFirst)
            .build(patterns)
            .unwrap();
        for m in pma.leftmost_find_iter(&haystack) {
            actual.insert((m.start(), m.end()), m.value());
        }
        assert_eq!(expected, actual);
    }
}

#[test]
fn test_leftmost_first_find_iter_binary_random_with_values() {
    for _ in 0..100 {
        let patvals = generate_random_patvals(
            &[(6, 1), (20, 2), (50, 3), (100, 4)],
            generate_random_binary_string,
        );
        let haystack = generate_random_binary_string(100);

        // naive pattern match
        let expected = naive_leftmost_first_find(patvals.iter().map(|(p, &v)| (p, v)), &haystack);

        // daachorse
        let mut actual = HashMap::new();
        let pma = DoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostFirst)
            .build_with_values(patvals)
            .unwrap();
        for m in pma.leftmost_find_iter(&haystack) {
            actual.insert((m.start(), m.end()), m.value());
        }
        assert_eq!(expected, actual);
    }
}
