use daachorse::{
    CharwiseDoubleArrayAhoCorasick, CharwiseDoubleArrayAhoCorasickBuilder, DoubleArrayAhoCorasick,
    DoubleArrayAhoCorasickBuilder, MatchKind,
};
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

fn random_string(rng: &mut SmallRng, alphabet: &[char], max_len: usize) -> String {
    let len = rng.random_range(1..=max_len);
    (0..len)
        .map(|_| alphabet[rng.random_range(0..alphabet.len())])
        .collect()
}

macro_rules! corpus_test {
    ($name:ident, $builder:ident, $pma:ty, $kind:expr, $find:ident) => {
        #[test]
        fn $name() {
            let alphabet: Vec<char> = "abc火星猫".chars().collect();
            for trial in 0..100 {
                let trial_seed: u64 = rand::random();
                let mut rng = SmallRng::seed_from_u64(trial_seed);
                let mut patterns: Vec<String> = (0..20)
                    .map(|_| random_string(&mut rng, &alphabet, 6))
                    .collect();
                patterns.sort();
                patterns.dedup();
                let corpus: Vec<String> = (0..5)
                    .map(|_| random_string(&mut rng, &alphabet, 200))
                    .collect();
                let haystack = random_string(&mut rng, &alphabet, 300);

                let plain: $pma = $builder::new().match_kind($kind).build(&patterns).unwrap();
                let tuned: $pma = $builder::new()
                    .match_kind($kind)
                    .corpus(&corpus)
                    .build(&patterns)
                    .unwrap();
                let expected: Vec<_> = plain
                    .$find(&haystack)
                    .map(|m| (m.start(), m.end(), m.value()))
                    .collect();
                let actual: Vec<_> = tuned
                    .$find(&haystack)
                    .map(|m| (m.start(), m.end(), m.value()))
                    .collect();
                assert_eq!(expected, actual, "trial {trial}, seed 0x{trial_seed:016x}");
            }
        }
    };
}

corpus_test!(
    bytewise_standard,
    DoubleArrayAhoCorasickBuilder,
    DoubleArrayAhoCorasick<u32>,
    MatchKind::Standard,
    find_overlapping_iter
);

corpus_test!(
    bytewise_leftmost_longest,
    DoubleArrayAhoCorasickBuilder,
    DoubleArrayAhoCorasick<u32>,
    MatchKind::LeftmostLongest,
    leftmost_find_iter
);

corpus_test!(
    bytewise_leftmost_first,
    DoubleArrayAhoCorasickBuilder,
    DoubleArrayAhoCorasick<u32>,
    MatchKind::LeftmostFirst,
    leftmost_find_iter
);

corpus_test!(
    charwise_standard,
    CharwiseDoubleArrayAhoCorasickBuilder,
    CharwiseDoubleArrayAhoCorasick<u32>,
    MatchKind::Standard,
    find_overlapping_iter
);

corpus_test!(
    charwise_leftmost_longest,
    CharwiseDoubleArrayAhoCorasickBuilder,
    CharwiseDoubleArrayAhoCorasick<u32>,
    MatchKind::LeftmostLongest,
    leftmost_find_iter
);

corpus_test!(
    charwise_leftmost_first,
    CharwiseDoubleArrayAhoCorasickBuilder,
    CharwiseDoubleArrayAhoCorasick<u32>,
    MatchKind::LeftmostFirst,
    leftmost_find_iter
);
