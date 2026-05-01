use daachorse::{CharwiseDoubleArrayAhoCorasick, CharwiseDoubleArrayAhoCorasickBuilder, MatchKind};

#[test]
fn test_empty_pattern() {
    assert!(CharwiseDoubleArrayAhoCorasick::<usize>::new([""]).is_err());
}

#[test]
fn test_empty_pattern_with_matchkind_leftmost_longest() {
    let pma: Result<CharwiseDoubleArrayAhoCorasick<usize>, _> =
        CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostLongest)
            .build([""]);
    assert!(pma.is_err());
}

#[test]
fn test_empty_pattern_with_matchkind_leftmost_first() {
    let pma: Result<CharwiseDoubleArrayAhoCorasick<usize>, _> =
        CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostFirst)
            .build([""]);
    assert!(pma.is_err());
}

#[test]
fn test_empty_pattern_with_matchkind_standard() {
    let pma: Result<CharwiseDoubleArrayAhoCorasick<usize>, _> =
        CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::Standard)
            .build([""]);
    assert!(pma.is_err());
}
