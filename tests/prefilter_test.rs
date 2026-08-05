use daachorse::{
    CharwiseDoubleArrayAhoCorasick, CharwiseDoubleArrayAhoCorasickBuilder, DoubleArrayAhoCorasick,
    DoubleArrayAhoCorasickBuilder, MatchKind,
};
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

fn random_string(rng: &mut SmallRng, alphabet: &[char], min_len: usize, max_len: usize) -> String {
    let len = rng.random_range(min_len..=max_len);
    (0..len)
        .map(|_| alphabet[rng.random_range(0..alphabet.len())])
        .collect()
}

/// Compares search results between automatons built with and without the prefilter. Pattern
/// lengths range from 2 bytes, so both prefiltered and prefilter-less automatons are exercised.
macro_rules! prefilter_equivalence_test {
    ($name:ident, $builder:ident, $pma:ty, $kind:expr, $find:ident) => {
        #[test]
        fn $name() {
            let alphabet: Vec<char> = "ari火星猫".chars().collect();
            for trial in 0..100 {
                let trial_seed: u64 = rand::random();
                let mut rng = SmallRng::seed_from_u64(trial_seed);
                let mut patterns: Vec<String> = (0..20)
                    .map(|_| random_string(&mut rng, &alphabet, 2, 6))
                    .collect();
                patterns.sort();
                patterns.dedup();
                let haystack = random_string(&mut rng, &alphabet, 1, 300);

                let filtered: $pma = $builder::new().match_kind($kind).build(&patterns).unwrap();
                let plain: $pma = $builder::new()
                    .match_kind($kind)
                    .use_prefilter(false)
                    .build(&patterns)
                    .unwrap();
                let expected: Vec<_> = plain
                    .$find(&haystack)
                    .map(|m| (m.start(), m.end(), m.value()))
                    .collect();
                let actual: Vec<_> = filtered
                    .$find(&haystack)
                    .map(|m| (m.start(), m.end(), m.value()))
                    .collect();
                assert_eq!(expected, actual, "trial {trial}, seed 0x{trial_seed:016x}");
            }
        }
    };
}

prefilter_equivalence_test!(
    bytewise_standard_find,
    DoubleArrayAhoCorasickBuilder,
    DoubleArrayAhoCorasick<u32>,
    MatchKind::Standard,
    find_iter
);

prefilter_equivalence_test!(
    bytewise_standard_overlapping,
    DoubleArrayAhoCorasickBuilder,
    DoubleArrayAhoCorasick<u32>,
    MatchKind::Standard,
    find_overlapping_iter
);

prefilter_equivalence_test!(
    bytewise_standard_no_suffix,
    DoubleArrayAhoCorasickBuilder,
    DoubleArrayAhoCorasick<u32>,
    MatchKind::Standard,
    find_overlapping_no_suffix_iter
);

prefilter_equivalence_test!(
    bytewise_leftmost_longest,
    DoubleArrayAhoCorasickBuilder,
    DoubleArrayAhoCorasick<u32>,
    MatchKind::LeftmostLongest,
    leftmost_find_iter
);

prefilter_equivalence_test!(
    bytewise_leftmost_first,
    DoubleArrayAhoCorasickBuilder,
    DoubleArrayAhoCorasick<u32>,
    MatchKind::LeftmostFirst,
    leftmost_find_iter
);

prefilter_equivalence_test!(
    charwise_standard_find,
    CharwiseDoubleArrayAhoCorasickBuilder,
    CharwiseDoubleArrayAhoCorasick<u32>,
    MatchKind::Standard,
    find_iter
);

prefilter_equivalence_test!(
    charwise_standard_overlapping,
    CharwiseDoubleArrayAhoCorasickBuilder,
    CharwiseDoubleArrayAhoCorasick<u32>,
    MatchKind::Standard,
    find_overlapping_iter
);

prefilter_equivalence_test!(
    charwise_standard_no_suffix,
    CharwiseDoubleArrayAhoCorasickBuilder,
    CharwiseDoubleArrayAhoCorasick<u32>,
    MatchKind::Standard,
    find_overlapping_no_suffix_iter
);

prefilter_equivalence_test!(
    charwise_leftmost_longest,
    CharwiseDoubleArrayAhoCorasickBuilder,
    CharwiseDoubleArrayAhoCorasick<u32>,
    MatchKind::LeftmostLongest,
    leftmost_find_iter
);

prefilter_equivalence_test!(
    charwise_leftmost_first,
    CharwiseDoubleArrayAhoCorasickBuilder,
    CharwiseDoubleArrayAhoCorasick<u32>,
    MatchKind::LeftmostFirst,
    leftmost_find_iter
);

/// A pattern occurrence every few bytes gives the prefilter almost no gain, so the gate closes
/// mid-search and the iterators must fall back to plain scanning without changing the results.
macro_rules! gate_close_test {
    ($name:ident, $builder:ident, $pma:ty, $kind:expr, $find:ident) => {
        #[test]
        fn $name() {
            let patterns = ["ぷいにゅ", "アリア社長"];
            let haystack = "ぷいにゅ、".repeat(200);

            let filtered: $pma = $builder::new().match_kind($kind).build(&patterns).unwrap();
            let plain: $pma = $builder::new()
                .match_kind($kind)
                .use_prefilter(false)
                .build(&patterns)
                .unwrap();
            let expected: Vec<_> = plain
                .$find(&haystack)
                .map(|m| (m.start(), m.end(), m.value()))
                .collect();
            let actual: Vec<_> = filtered
                .$find(&haystack)
                .map(|m| (m.start(), m.end(), m.value()))
                .collect();
            assert_eq!(expected, actual);
        }
    };
}

gate_close_test!(
    bytewise_gate_close_find,
    DoubleArrayAhoCorasickBuilder,
    DoubleArrayAhoCorasick<u32>,
    MatchKind::Standard,
    find_iter
);

gate_close_test!(
    bytewise_gate_close_overlapping,
    DoubleArrayAhoCorasickBuilder,
    DoubleArrayAhoCorasick<u32>,
    MatchKind::Standard,
    find_overlapping_iter
);

gate_close_test!(
    bytewise_gate_close_leftmost,
    DoubleArrayAhoCorasickBuilder,
    DoubleArrayAhoCorasick<u32>,
    MatchKind::LeftmostLongest,
    leftmost_find_iter
);

gate_close_test!(
    charwise_gate_close_find,
    CharwiseDoubleArrayAhoCorasickBuilder,
    CharwiseDoubleArrayAhoCorasick<u32>,
    MatchKind::Standard,
    find_iter
);

gate_close_test!(
    charwise_gate_close_overlapping,
    CharwiseDoubleArrayAhoCorasickBuilder,
    CharwiseDoubleArrayAhoCorasick<u32>,
    MatchKind::Standard,
    find_overlapping_iter
);

gate_close_test!(
    charwise_gate_close_leftmost,
    CharwiseDoubleArrayAhoCorasickBuilder,
    CharwiseDoubleArrayAhoCorasick<u32>,
    MatchKind::LeftmostLongest,
    leftmost_find_iter
);

#[test]
fn bytewise_serialization_roundtrip_with_prefilter() {
    let patterns = ["AriaCompany", "OrangePlanet", "HimeyaCompany"];
    let haystack =
        "Akari rows for AriaCompany, Aika for HimeyaCompany, and Alice for OrangePlanet.";
    let pma = DoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
    let bytes = pma.serialize();

    let expected: Vec<_> = pma
        .find_iter(haystack)
        .map(|m| (m.start(), m.end(), m.value()))
        .collect();
    assert_eq!(expected.len(), 3);

    let (other, rest) = DoubleArrayAhoCorasick::<u32>::deserialize(&bytes).unwrap();
    assert!(rest.is_empty());
    let actual: Vec<_> = other
        .find_iter(haystack)
        .map(|m| (m.start(), m.end(), m.value()))
        .collect();
    assert_eq!(expected, actual);

    let (other, _) = unsafe { DoubleArrayAhoCorasick::<u32>::deserialize_unchecked(&bytes) };
    let actual: Vec<_> = other
        .find_iter(haystack)
        .map(|m| (m.start(), m.end(), m.value()))
        .collect();
    assert_eq!(expected, actual);

    // The serialized data ends with the prefilter section:
    // [presence flag (1), window_len (1), table (65536)].
    let flag_pos = bytes.len() - 65536 - 2;
    assert_eq!(bytes[flag_pos], 1);
    let mut corrupted = bytes.clone();
    corrupted[flag_pos + 1] = 100; // window_len out of range
    assert!(DoubleArrayAhoCorasick::<u32>::deserialize(&corrupted).is_err());
    let mut corrupted = bytes.clone();
    corrupted[flag_pos] = 2; // invalid presence flag
    assert!(DoubleArrayAhoCorasick::<u32>::deserialize(&corrupted).is_err());
}

#[test]
fn charwise_serialization_roundtrip_with_prefilter() {
    let patterns = ["灯里", "アリス", "藍華"];
    let haystack = "ARIAカンパニーには灯里が、姫屋に藍華が、オレンジぷらねっとにはアリスがいる。";
    let pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
    let bytes = pma.serialize();

    let expected: Vec<_> = pma
        .find_iter(haystack)
        .map(|m| (m.start(), m.end(), m.value()))
        .collect();
    assert_eq!(expected.len(), 3);

    let (other, rest) = CharwiseDoubleArrayAhoCorasick::<u32>::deserialize(&bytes).unwrap();
    assert!(rest.is_empty());
    let actual: Vec<_> = other
        .find_iter(haystack)
        .map(|m| (m.start(), m.end(), m.value()))
        .collect();
    assert_eq!(expected, actual);

    let (other, _) =
        unsafe { CharwiseDoubleArrayAhoCorasick::<u32>::deserialize_unchecked(&bytes) };
    let actual: Vec<_> = other
        .find_iter(haystack)
        .map(|m| (m.start(), m.end(), m.value()))
        .collect();
    assert_eq!(expected, actual);
}

#[test]
fn bytewise_serialization_roundtrip_without_prefilter() {
    // The shortest pattern has one byte, so no prefilter is built, and the presence flag must
    // round-trip as 0.
    let pma = DoubleArrayAhoCorasick::<u32>::new(["a", "aqua"]).unwrap();
    let bytes = pma.serialize();
    let (other, rest) = DoubleArrayAhoCorasick::<u32>::deserialize(&bytes).unwrap();
    assert!(rest.is_empty());
    assert_eq!(
        pma.find_iter("the gondola floats on aqua")
            .map(|m| (m.start(), m.end(), m.value()))
            .collect::<Vec<_>>(),
        other
            .find_iter("the gondola floats on aqua")
            .map(|m| (m.start(), m.end(), m.value()))
            .collect::<Vec<_>>()
    );
}
