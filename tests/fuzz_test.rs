use daachorse::{CharwiseDoubleArrayAhoCorasick, CharwiseDoubleArrayAhoCorasickBuilder, MatchKind};

// Simple zero-dependency XorShift64 PRNG for deterministic, reproducible fuzzing.
struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self {
            state: if seed == 0 { 0xdead_beef_cafe } else { seed },
        }
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }

    fn gen_range(&mut self, low: usize, high: usize) -> usize {
        assert!(low <= high);
        if low == high {
            return low;
        }
        low + (self.next_u64() as usize % (high - low))
    }

    fn gen_string(&mut self, alphabet: &[char], min_len: usize, max_len: usize) -> String {
        let len = self.gen_range(min_len, max_len);
        let mut s = String::with_capacity(len * 4);
        for _ in 0..len {
            let idx = self.gen_range(0, alphabet.len());
            s.push(alphabet[idx]);
        }
        s
    }
}

fn differential_fuzz_round(patterns: &[String], haystack: &str, round: usize) {
    if patterns.is_empty() {
        return;
    }

    let pma_legacy: CharwiseDoubleArrayAhoCorasick<usize> =
        match CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostLongest)
            .build(patterns)
        {
            Ok(pma) => pma,
            Err(_) => return, // Duplicate pattern error or empty
        };

    let pma_linear: CharwiseDoubleArrayAhoCorasick<usize> =
        match CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostLongestExperimental)
            .build(patterns)
        {
            Ok(pma) => pma,
            Err(e) => panic!("Linear builder failed when legacy succeeded: {:?}", e),
        };

    let matches_legacy: Vec<_> = pma_legacy
        .leftmost_find_iter(haystack)
        .map(|m| (m.start(), m.end(), m.value()))
        .collect();

    let matches_linear: Vec<_> = pma_linear
        .leftmost_find_iter_experimental(haystack)
        .map(|m| (m.start(), m.end(), m.value()))
        .collect();

    if matches_legacy != matches_linear {
        eprintln!("=== MISMATCH in Round {} ===", round);
        eprintln!("Patterns ({}): {:?}", patterns.len(), patterns);
        eprintln!("Haystack (len {}): {:?}", haystack.len(), haystack);
        let max_len = matches_legacy.len().max(matches_linear.len());
        for i in 0..max_len {
            let leg = matches_legacy.get(i);
            let lin = matches_linear.get(i);
            if leg != lin {
                eprintln!(
                    "First diff at match index {}: Legacy={:?}, Linear={:?}",
                    i, leg, lin
                );
                let start_idx = i.saturating_sub(5);
                let end_idx = (i + 5).min(max_len);
                eprintln!("--- Legacy matches [{}..{}] ---", start_idx, end_idx);
                for k in start_idx..end_idx {
                    if let Some(m) = matches_legacy.get(k) {
                        eprintln!("  {}: [{}..{}] = {:?}", k, m.0, m.1, patterns[m.2]);
                    }
                }
                eprintln!("--- Linear matches [{}..{}] ---", start_idx, end_idx);
                for k in start_idx..end_idx {
                    if let Some(m) = matches_linear.get(k) {
                        eprintln!("  {}: [{}..{}] = {:?}", k, m.0, m.1, patterns[m.2]);
                    }
                }
                break;
            }
        }
        panic!("Mismatch detected!");
    }
}

#[test]
fn test_repro_round_28() {
    let patterns = vec![
        "da".to_string(),
        "dbacbc".to_string(),
        "a".to_string(),
        "bbdadd".to_string(),
        "d".to_string(),
        "dbc".to_string(),
        "dbacbd".to_string(),
        "bad".to_string(),
        "cbac".to_string(),
        "cc".to_string(),
        "ddacad".to_string(),
        "b".to_string(),
    ];
    let haystack = "abbccdbdadbaacbcaacccbdbcbbcccdddbcabdbdbcbdbaaaaaabbddbaccabbddabbcabacaccabbccaddbbaadbbdadbcacbbcbcdabbaccdddbcacaccdccdacbbccbacaddbbcbbaacccacaacadcccbcccbbcdccaaacbcbcddddbabccbbbabbbdbdccdddcabdadbaaacadbdccadbbbdbbadcbaabaddaabddabcbbcbaadbbcdcdadadccccaadaabdddbacbbcdbbdcaabcbbcaaddbddcccbcccaddbdbbbaccdcabcccdbbdddddacbddacaddadcbdaabacdcabababbdbbadaaabbddcbadbbaaaabcccdcdadccddcabcdabbdbaacbaccabaccbbbaacbcdaadacbdbbddcdcacdcacdbbbdbbdddbacbdcccadabccbacaaadbccacbcccdbaacbcaabdabcbbbcdbccdcaadaadbbaddbaaddbcdbbabdbbbdabdabdbdcccccbbcadabaaddbdaadaaaacdddccddcbddcdbaaababdaaddacccbccddadadcdbdabdddccadcccccdcdbccbaabbabdacdabaccdbbbdccbcaaaabdcdacdbbbaadaacadaccbadcdcaddacbacbccbadccbbacbddcbbcbbbddccaabaacbbdccdadaddabdcbbcdcdadddaacacbbcddadbcbcdddcbaabcababbacdcdabbccacbddcbccdcbbcbacdcdaccba";
    differential_fuzz_round(&patterns, haystack, 28);
}

#[test]
fn test_parent_and_candidate_matches() {
    // Verifies that when an intermediate state on a long pattern branch (e.g. "xybacelong")
    // experiences candidate failure on transition 'e' (where suffix candidate "bac" breaks),
    // both ancestor matches ("xy") and broken candidate matches ("b", "a") are correctly
    // spliced and preserved when matching text that diverges (e.g. "xybacex").
    let patterns = vec![
        "xy".to_string(),
        "b".to_string(),
        "a".to_string(),
        "bacd".to_string(),
        "xybacelong".to_string(),
    ];
    let haystack = "xybacex";
    differential_fuzz_round(&patterns, haystack, 1);
}

#[test]
fn test_fuzz_binary_alphabet() {
    let mut rng = Rng::new(0x1234_5678);
    let alphabet = ['a', 'b'];

    for round in 0..200 {
        let num_pats = rng.gen_range(2, 20);
        let mut patterns = Vec::with_capacity(num_pats);
        for _ in 0..num_pats {
            let pat = rng.gen_string(&alphabet, 1, 6);
            if !patterns.contains(&pat) {
                patterns.push(pat);
            }
        }
        let haystack = rng.gen_string(&alphabet, 10, 500);
        differential_fuzz_round(&patterns, &haystack, round);
    }
}

#[test]
fn test_fuzz_small_alphabet() {
    let mut rng = Rng::new(0x8765_4321);
    let alphabet = ['a', 'b', 'c', 'd'];

    for round in 0..200 {
        let num_pats = rng.gen_range(2, 30);
        let mut patterns = Vec::with_capacity(num_pats);
        for _ in 0..num_pats {
            let pat = rng.gen_string(&alphabet, 1, 8);
            if !patterns.contains(&pat) {
                patterns.push(pat);
            }
        }
        let haystack = rng.gen_string(&alphabet, 20, 1000);
        differential_fuzz_round(&patterns, &haystack, round);
    }
}

#[test]
fn test_fuzz_unicode_chinese() {
    let mut rng = Rng::new(0xfeed_face);
    let alphabet = ['中', '文', '分', '词', '测', '试', '长', '短', '匹', '配'];

    for round in 0..100 {
        let num_pats = rng.gen_range(2, 25);
        let mut patterns = Vec::with_capacity(num_pats);
        for _ in 0..num_pats {
            let pat = rng.gen_string(&alphabet, 1, 5);
            if !patterns.contains(&pat) {
                patterns.push(pat);
            }
        }
        let haystack = rng.gen_string(&alphabet, 10, 800);
        differential_fuzz_round(&patterns, &haystack, round);
    }
}

#[test]
fn test_fuzz_heavy_nested_prefixes() {
    let mut rng = Rng::new(0xabcd_ef01);
    let alphabet = ['a', 'b', 'c'];

    for round in 0..100 {
        // Generate patterns where prefixes are intentionally injected
        let num_base = rng.gen_range(2, 6);
        let mut patterns = Vec::new();
        for _ in 0..num_base {
            let base = rng.gen_string(&alphabet, 3, 10);
            for k in 1..=base.len() {
                let prefix = base[..k].to_string();
                if !patterns.contains(&prefix) {
                    patterns.push(prefix);
                }
            }
        }
        let haystack = rng.gen_string(&alphabet, 50, 2000);
        differential_fuzz_round(&patterns, &haystack, round);
    }
}

#[test]
fn test_fuzz_adversarial_near_miss() {
    let mut rng = Rng::new(0x9999_9999);

    for round in 0..100 {
        let l = rng.gen_range(10, 100);
        let pat_long = format!("{}b", "a".repeat(l));
        let pat_short = "a".repeat(l / 2);
        let pat_single = "a".to_string();
        let patterns = vec![pat_long, pat_short, pat_single];

        // Haystack with near misses: a^(l-1) c
        let reps = rng.gen_range(10, 50);
        let block = format!("{}c", "a".repeat(l - 1));
        let haystack = block.repeat(reps);

        differential_fuzz_round(&patterns, &haystack, round);
    }
}

#[test]
fn test_fuzz_stress_large_corpus() {
    let mut rng = Rng::new(0x5555_5555);
    let alphabet = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'];

    for round in 0..50 {
        let num_pats = rng.gen_range(50, 200);
        let mut patterns = Vec::with_capacity(num_pats);
        for _ in 0..num_pats {
            let pat = rng.gen_string(&alphabet, 1, 15);
            if !patterns.contains(&pat) {
                patterns.push(pat);
            }
        }
        let haystack = rng.gen_string(&alphabet, 1000, 10000);
        differential_fuzz_round(&patterns, &haystack, round);
    }
}

fn differential_fuzz_round_leftmost_first(patterns: &[String], haystack: &str, round: usize) {
    if patterns.is_empty() {
        return;
    }

    let pma_legacy: CharwiseDoubleArrayAhoCorasick<usize> =
        match CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostFirst)
            .build(patterns)
        {
            Ok(pma) => pma,
            Err(_) => return,
        };

    let pma_linear: CharwiseDoubleArrayAhoCorasick<usize> =
        match CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostFirstExperimental)
            .build(patterns)
        {
            Ok(pma) => pma,
            Err(e) => panic!("Linear builder failed when legacy succeeded: {:?}", e),
        };

    let matches_legacy: Vec<_> = pma_legacy
        .leftmost_find_iter(haystack)
        .map(|m| (m.start(), m.end(), m.value()))
        .collect();

    let matches_linear: Vec<_> = pma_linear
        .leftmost_find_iter_experimental(haystack)
        .map(|m| (m.start(), m.end(), m.value()))
        .collect();

    if matches_legacy != matches_linear {
        eprintln!("=== MISMATCH in Round {} (LeftmostFirst) ===", round);
        eprintln!("Patterns ({}): {:?}", patterns.len(), patterns);
        eprintln!("Haystack (len {}): {:?}", haystack.len(), haystack);
        panic!("LeftmostFirst mismatch detected!");
    }
}

#[test]
fn test_fuzz_leftmost_first_equivalence() {
    let mut rng = Rng::new(0xdead_beef_1234_5678);
    let alphabet = ['a', 'b', 'c', 'd'];

    for round in 0..200 {
        let num_pats = rng.gen_range(2, 20);
        let mut patterns = Vec::with_capacity(num_pats);
        for _ in 0..num_pats {
            let pat = rng.gen_string(&alphabet, 1, 8);
            if !patterns.contains(&pat) {
                patterns.push(pat);
            }
        }
        let haystack = rng.gen_string(&alphabet, 20, 1000);
        differential_fuzz_round_leftmost_first(&patterns, &haystack, round);
    }
}

/// Patterns are built from a *sub*alphabet while the haystack uses a larger
/// one, so a controlled fraction of haystack characters are absent from the
/// mapper. The experimental matcher treats unmapped characters specially (it
/// must still flush pending emits), and the other fuzzers never generate this
/// case: they draw patterns and haystacks from the same alphabet, so every
/// character is mapped.
#[test]
fn test_fuzz_unmapped_characters() {
    let mut rng = Rng::new(0x5eed_1234);

    // Separators appear only in the haystack, never in patterns.
    let sep = [' ', '.', '-', '/', '\n', '\t', 'X', 'Z', '0', '9'];
    let word = ['a', 'b', 'c', 'd', 'e'];

    for round in 0..100 {
        let num_pats = rng.gen_range(1, 40);
        let mut patterns = Vec::new();
        for _ in 0..num_pats {
            let p = rng.gen_string(&word, 1, 5);
            patterns.push(p);
        }
        patterns.sort();
        patterns.dedup();

        // Haystack interleaves words with separators (unmapped characters).
        let mut haystack = String::new();
        let parts = rng.gen_range(5, 60);
        for _ in 0..parts {
            haystack.push_str(&rng.gen_string(&word, 0, 6));
            let s = sep[rng.gen_range(0, sep.len())];
            haystack.push(s);
            if rng.gen_range(0, 4) == 0 {
                haystack.push(s);
            }
        }

        differential_fuzz_round(&patterns, &haystack, round);
        differential_fuzz_round_leftmost_first(&patterns, &haystack, round);
    }
}

/// Fuzz tests leftmost matching when the dictionary contains the empty pattern `""`.
///
/// Under leftmost matching semantics:
/// 1. A dictionary containing only `[""]` matches at every UTF-8 character boundary (offset 0 to EOF).
/// 2. For `LeftmostLongest`, every non-empty pattern has length >= 1 and strictly longer than `""`.
///    Therefore, under `LeftmostLongest`, non-empty patterns strictly take precedence over `""`,
///    so the sequence of non-empty matches must be identical whether `""` is in the dictionary or not.
/// 3. For `LeftmostFirst`:
///    - If `""` is at index 0 (highest priority), it matches at every character boundary across the text.
#[test]
fn test_fuzz_with_empty_pattern() {
    let mut rng = Rng::new(0xee91_1001);
    let alphabet = ['a', 'b', 'c', '中', '文'];

    // 1. Edge Case: Dictionary with ONLY the empty pattern.
    {
        let patterns = vec![String::new()];
        for haystack in ["", "a", "abc", "中文测试", "a中b文c"] {
            differential_fuzz_round(&patterns, haystack, 0);
            differential_fuzz_round_leftmost_first(&patterns, haystack, 0);

            let pma: CharwiseDoubleArrayAhoCorasick<usize> =
                CharwiseDoubleArrayAhoCorasickBuilder::new()
                    .match_kind(MatchKind::LeftmostLongestExperimental)
                    .build(&patterns)
                    .unwrap();
            let boundaries: Vec<usize> = haystack
                .char_indices()
                .map(|(i, _)| i)
                .chain(core::iter::once(haystack.len()))
                .collect();
            let matches: Vec<(usize, usize, usize)> = pma
                .leftmost_find_iter_experimental(haystack)
                .map(|m| (m.start(), m.end(), m.value()))
                .collect();
            assert_eq!(matches.len(), boundaries.len());
            for (&b, &m) in boundaries.iter().zip(matches.iter()) {
                assert_eq!(m, (b, b, 0));
            }
        }
    }

    // 2. Invariant Fuzzing: Empty pattern combined with random patterns.
    for _round in 0..500 {
        let num_pats = rng.gen_range(1, 15);
        let mut pats = Vec::with_capacity(num_pats);
        for _ in 0..num_pats {
            let p = rng.gen_string(&alphabet, 1, 6);
            if !pats.contains(&p) {
                pats.push(p);
            }
        }

        let haystack = rng.gen_string(&alphabet, 0, 200);

        // A. LeftmostLongest Invariant:
        // Adding "" must not change the sequence of non-empty matches:
        let pma_no_empty: CharwiseDoubleArrayAhoCorasick<usize> =
            CharwiseDoubleArrayAhoCorasickBuilder::new()
                .match_kind(MatchKind::LeftmostLongestExperimental)
                .build(&pats)
                .unwrap();
        let expected_non_empty: Vec<(usize, usize, usize)> = pma_no_empty
            .leftmost_find_iter_experimental(&haystack)
            .map(|m| (m.start(), m.end(), m.value()))
            .collect();

        let mut pats_with_empty = vec![String::new()];
        pats_with_empty.extend(pats.clone());

        let pma_with_empty: CharwiseDoubleArrayAhoCorasick<usize> =
            CharwiseDoubleArrayAhoCorasickBuilder::new()
                .match_kind(MatchKind::LeftmostLongestExperimental)
                .build(&pats_with_empty)
                .unwrap();
        let all_matches: Vec<(usize, usize, usize)> = pma_with_empty
            .leftmost_find_iter_experimental(&haystack)
            .map(|m| (m.start(), m.end(), m.value()))
            .collect();

        // 1. Matches must be monotonically ordered and non-overlapping:
        let mut last_end = 0;
        for &m in &all_matches {
            assert!(m.0 <= m.1, "match start <= end");
            assert!(m.0 >= last_end, "non-overlapping order");
            if m.0 < m.1 {
                assert_eq!(&haystack[m.0..m.1], &pats_with_empty[m.2]);
            } else {
                assert_eq!(m.2, 0);
            }
            last_end = m.1;
        }

        // 2. Non-empty matches must match the non-empty run exactly:
        let actual_non_empty: Vec<(usize, usize, usize)> = all_matches
            .iter()
            .copied()
            .filter(|m| m.0 < m.1)
            .map(|(s, e, v)| (s, e, v - 1))
            .collect();
        assert_eq!(actual_non_empty, expected_non_empty);

        // B. LeftmostFirst Invariant:
        // If "" is at index 0, it has highest priority and matches every char boundary:
        let pma_first_empty: CharwiseDoubleArrayAhoCorasick<usize> =
            CharwiseDoubleArrayAhoCorasickBuilder::new()
                .match_kind(MatchKind::LeftmostFirstExperimental)
                .build(&pats_with_empty)
                .unwrap();
        let first_empty_matches: Vec<(usize, usize, usize)> = pma_first_empty
            .leftmost_find_iter_experimental(&haystack)
            .map(|m| (m.start(), m.end(), m.value()))
            .collect();
        let all_boundaries: Vec<usize> = haystack
            .char_indices()
            .map(|(i, _)| i)
            .chain(core::iter::once(haystack.len()))
            .collect();
        assert_eq!(first_empty_matches.len(), all_boundaries.len());
        for (&b, &m) in all_boundaries.iter().zip(first_empty_matches.iter()) {
            assert_eq!(m, (b, b, 0));
        }
    }
}

#[test]
fn test_fuzz_iter_pattern_reconstruction() {
    let alphabets: &[(&str, &[char])] = &[
        ("binary", &['a', 'b']),
        ("small_ascii", &['a', 'b', 'c', 'd', 'e']),
        ("cjk_emoji", &['中', '文', '字', '符', '🦀', '🚀']),
        (
            "unicode_boundaries",
            &[
                '\u{0}',
                'a',
                '\u{7f}',
                '\u{80}',
                '\u{7ff}',
                '\u{800}',
                '\u{ffff}',
                '\u{10000}',
                '\u{10ffff}',
            ],
        ),
    ];

    let mut rng = Rng::new(0x1337_c0de_cafe_babe);

    for (name, alphabet) in alphabets {
        for round in 0..50 {
            let num_pats = rng.gen_range(0, 30);
            let mut patvals: Vec<(String, u32)> = Vec::with_capacity(num_pats);

            for v in 0..num_pats {
                // Generate pattern, with occasional empty string or duplicate strings
                let p = if v == 0 && rng.gen_range(0, 5) == 0 {
                    String::new()
                } else if !patvals.is_empty() && rng.gen_range(0, 6) == 0 {
                    // Introduce deliberate duplicate with distinct value
                    let idx = rng.gen_range(0, patvals.len());
                    patvals[idx].0.clone()
                } else {
                    rng.gen_string(alphabet, 0, 10)
                };
                patvals.push((p, u32::try_from(v).unwrap()));
            }

            // Ground truth for LeftmostLongestExperimental:
            // Deduplicated by pattern string (first registered value wins), sorted lexicographically.
            let mut expected_longest: Vec<(String, u32)> = Vec::new();
            for (p, val) in &patvals {
                if !expected_longest.iter().any(|(x, _)| x == p) {
                    expected_longest.push((p.clone(), *val));
                }
            }
            expected_longest.sort_by(|a, b| a.0.cmp(&b.0));

            // 1. Invariant: LeftmostLongestExperimental iter() matches deduplicated ground truth
            let pma_exp_longest: CharwiseDoubleArrayAhoCorasick<u32> =
                CharwiseDoubleArrayAhoCorasickBuilder::new()
                    .match_kind(MatchKind::LeftmostLongestExperimental)
                    .build_with_values(patvals.clone())
                    .unwrap();

            let actual_longest: Vec<(String, u32)> = pma_exp_longest.iter().collect();
            assert_eq!(
                actual_longest, expected_longest,
                "[{}] Round {}: LeftmostLongestExperimental iter() mismatch against ground truth",
                name, round
            );

            // 2. Invariant: Serialization roundtrip preserves iter()
            let bytes = pma_exp_longest.serialize();
            let (pma_deser, _) =
                CharwiseDoubleArrayAhoCorasick::<u32>::deserialize(&bytes).unwrap();
            let actual_deser: Vec<(String, u32)> = pma_deser.iter().collect();
            assert_eq!(
                actual_deser, expected_longest,
                "[{}] Round {}: Deserialized iter() mismatch against ground truth",
                name, round
            );

            // 3. Invariant: Prefilter on vs off yields identical iter()
            let pma_prefiltered: CharwiseDoubleArrayAhoCorasick<u32> =
                CharwiseDoubleArrayAhoCorasickBuilder::new()
                    .match_kind(MatchKind::LeftmostLongestExperimental)
                    .use_prefilter(true)
                    .build_with_values(patvals.clone())
                    .unwrap();
            let actual_prefiltered: Vec<(String, u32)> = pma_prefiltered.iter().collect();
            assert_eq!(
                actual_prefiltered, expected_longest,
                "[{}] Round {}: Prefiltered iter() mismatch",
                name, round
            );

            // 4. Invariant: When there are no duplicate patterns, experimental matches legacy exactly
            let has_duplicates = patvals.len() != expected_longest.len();
            if !has_duplicates {
                // A. LeftmostLongest: Legacy vs Experimental
                let pma_legacy_longest: CharwiseDoubleArrayAhoCorasick<u32> =
                    CharwiseDoubleArrayAhoCorasickBuilder::new()
                        .match_kind(MatchKind::LeftmostLongest)
                        .build_with_values(patvals.clone())
                        .unwrap();
                let legacy_longest: Vec<(String, u32)> = pma_legacy_longest.iter().collect();
                assert_eq!(
                    actual_longest, legacy_longest,
                    "[{}] Round {}: LeftmostLongestExperimental vs legacy iter() mismatch",
                    name, round
                );

                // B. LeftmostFirst: Legacy vs Experimental
                let pma_legacy_first: CharwiseDoubleArrayAhoCorasick<u32> =
                    CharwiseDoubleArrayAhoCorasickBuilder::new()
                        .match_kind(MatchKind::LeftmostFirst)
                        .build_with_values(patvals.clone())
                        .unwrap();
                let pma_exp_first: CharwiseDoubleArrayAhoCorasick<u32> =
                    CharwiseDoubleArrayAhoCorasickBuilder::new()
                        .match_kind(MatchKind::LeftmostFirstExperimental)
                        .build_with_values(patvals.clone())
                        .unwrap();

                let legacy_first: Vec<(String, u32)> = pma_legacy_first.iter().collect();
                let exp_first: Vec<(String, u32)> = pma_exp_first.iter().collect();
                assert_eq!(
                    exp_first, legacy_first,
                    "[{}] Round {}: LeftmostFirstExperimental vs legacy iter() mismatch",
                    name, round
                );
            }
        }
    }
}
