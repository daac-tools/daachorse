use daachorse::{DoubleArrayAhoCorasick, DoubleArrayAhoCorasickBuilder, MatchKind};

#[test]
fn test_empty_pattern() {
    assert!(DoubleArrayAhoCorasick::<usize>::new([""]).is_err());
}

#[test]
fn test_empty_pattern_with_matchkind_leftmost_longest() {
    let pma: Result<DoubleArrayAhoCorasick<usize>, _> = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build([""]);
    assert!(pma.is_err());
}

#[test]
fn test_empty_pattern_with_matchkind_leftmost_first() {
    let pma: Result<DoubleArrayAhoCorasick<usize>, _> = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build([""]);
    assert!(pma.is_err());
}

#[test]
fn test_empty_pattern_with_matchkind_standard() {
    let pma: Result<DoubleArrayAhoCorasick<usize>, _> = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::Standard)
        .build([""]);
    assert!(pma.is_err());
}
