use daachorse::{
    CharwiseDoubleArrayAhoCorasick, CharwiseDoubleArrayAhoCorasickBuilder, DoubleArrayAhoCorasick,
    DoubleArrayAhoCorasickBuilder, MatchKind,
};

const PATTERN_SETS: &[&[&str]] = &[
    &["aria", "ariacompany", "ria", "ia"],
    &["ai", "aika", "aikagranzchesta"],
    &["にゅにゅ", "にゅにゅにゅ", "ぷいにゅ"],
    &["アリア", "アリシア", "アイカ"],
    &["undine", "アクア", "gondola"],
    &["の", "アリア社長", "姫屋"],
];

fn corpora(patterns: &[&str]) -> Vec<Vec<String>> {
    let p0 = patterns[0];
    let longest = patterns.iter().max_by_key(|p| p.len()).unwrap();
    let long_head: String = longest.chars().take(longest.chars().count() - 1).collect();
    vec![
        vec![],
        vec![String::new()],
        patterns.iter().map(|p| (*p).to_string()).collect(),
        vec![p0.repeat(50)],
        vec![long_head],
        vec!["水の都ネオヴェネツィアを漕ぐ".to_string()],
        vec![patterns.join("、"), p0.to_string()],
    ]
}

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

macro_rules! corpus_test {
    ($name:ident, $builder:ident, $pma:ty, $kind:expr, $find:ident) => {
        #[test]
        fn $name() {
            for (set_idx, patterns) in PATTERN_SETS.iter().enumerate() {
                let plain: $pma = $builder::new().match_kind($kind).build(*patterns).unwrap();
                for (corpus_idx, corpus) in corpora(patterns).iter().enumerate() {
                    let tuned: $pma = $builder::new()
                        .match_kind($kind)
                        .corpus(corpus)
                        .build(*patterns)
                        .unwrap();
                    for (hay_idx, haystack) in haystacks(patterns).iter().enumerate() {
                        let expected: Vec<_> = plain
                            .$find(haystack)
                            .map(|m| (m.start(), m.end(), m.value()))
                            .collect();
                        let actual: Vec<_> = tuned
                            .$find(haystack)
                            .map(|m| (m.start(), m.end(), m.value()))
                            .collect();
                        assert_eq!(
                            expected, actual,
                            "pattern set {set_idx}, corpus {corpus_idx}, haystack {hay_idx}"
                        );
                    }
                }
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
