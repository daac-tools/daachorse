use daachorse::{
    CharwiseDoubleArrayAhoCorasick, CharwiseDoubleArrayAhoCorasickBuilder, DoubleArrayAhoCorasick,
    DoubleArrayAhoCorasickBuilder, MatchKind,
};

const PATTERN_SETS: &[&[&str]] = &[
    &["aria", "ariacompany", "ria", "ia"],
    &["ai", "aika", "aikagranzchesta"],
    &["ariacompan", "ariacompany", "orangeplanet"],
    &["にゅにゅ", "にゅにゅにゅ", "ぷいにゅ"],
    &["アリア", "アリシア", "アイカ"],
    &["undine", "アクア", "gondola"],
    &["の", "アリア社長", "姫屋"],
];

fn haystacks(patterns: &[&str]) -> Vec<String> {
    let p0 = patterns[0];
    let longest = patterns.iter().max_by_key(|p| p.len()).unwrap();
    let head: String = p0.chars().take(p0.chars().count() - 1).collect();
    let long_head: String = longest.chars().take(longest.chars().count() - 1).collect();
    let tail: String = p0.chars().skip(1).collect();
    let pad = "水の都ネオヴェネツィアを漕ぐ".repeat(8);
    vec![
        String::new(),
        p0.chars().next().unwrap().to_string(),
        head.clone(),
        p0.to_string(),
        format!("{p0}{pad}"),
        format!("{pad}{p0}"),
        format!("{pad}{longest}"),
        format!("{pad}{head}"),
        format!("{pad}{long_head}"),
        format!("{long_head}、{p0}"),
        patterns.concat(),
        patterns.join("、"),
        format!("{head}{tail}{head}{tail}"),
        format!("{head}{p0}{tail}"),
        p0.repeat(80),
        format!("{}{pad}{p0}", p0.repeat(80)),
    ]
}

macro_rules! prefilter_equivalence_test {
    ($name:ident, $builder:ident, $pma:ty, $kind:expr, $find:ident) => {
        #[test]
        fn $name() {
            for (set_idx, patterns) in PATTERN_SETS.iter().enumerate() {
                let filtered: $pma = $builder::new().match_kind($kind).build(*patterns).unwrap();
                let plain: $pma = $builder::new()
                    .match_kind($kind)
                    .use_prefilter(false)
                    .build(*patterns)
                    .unwrap();
                for (hay_idx, haystack) in haystacks(patterns).iter().enumerate() {
                    let expected: Vec<_> = plain
                        .$find(haystack)
                        .map(|m| (m.start(), m.end(), m.value()))
                        .collect();
                    let actual: Vec<_> = filtered
                        .$find(haystack)
                        .map(|m| (m.start(), m.end(), m.value()))
                        .collect();
                    assert_eq!(
                        expected, actual,
                        "pattern set {set_idx}, haystack {hay_idx}"
                    );
                }
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
fn charwise_prefilter_candidates_inside_characters_are_skipped() {
    let patterns = ["アリア", "アリシア"];
    let pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(patterns).unwrap();
    let mut bytes = pma.serialize();
    let table_pos = bytes.len() - 65536;
    assert_eq!(bytes[table_pos - 2], 1);
    for (ngram, ngram_pos) in [
        (0xB3E3, 0),
        (0xE382, 1),
        (0x82A2, 2),
        (0xA2E3, 3),
        (0xE383, 4),
        (0x83AA, 5),
        (0xAAE3, 6),
        (0xE382, 7),
    ] {
        bytes[table_pos + ngram] &= !(1u8 << ngram_pos);
    }
    let (forged, _) = CharwiseDoubleArrayAhoCorasick::<u32>::deserialize(&bytes).unwrap();
    let haystack = "ンンンンンアリアのアリシア、ンンアリア";
    let expected: Vec<_> = pma
        .find_overlapping_iter(haystack)
        .map(|m| (m.start(), m.end(), m.value()))
        .collect();
    assert!(!expected.is_empty());
    let actual: Vec<_> = forged
        .find_overlapping_iter(haystack)
        .map(|m| (m.start(), m.end(), m.value()))
        .collect();
    assert_eq!(expected, actual);
}

#[test]
fn bytewise_serialization_roundtrip_without_prefilter() {
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
