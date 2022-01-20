use daachorse::{DoubleArrayAhoCorasick, DoubleArrayAhoCorasickBuilder, MatchKind};

#[test]
fn test_empty_pattern() {
    assert!(DoubleArrayAhoCorasick::new([""]).is_err());
}

#[test]
fn test_empty_set() {
    assert!(DoubleArrayAhoCorasick::new(Vec::<String>::new()).is_err());
}

#[test]
fn test_empty_pattern_with_matchkind_leftmost_longest() {
    assert!(DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build([""])
        .is_err());
}

#[test]
fn test_empty_set_with_matchkind_leftmost_longest() {
    assert!(DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build(Vec::<String>::new())
        .is_err());
}

#[test]
fn test_empty_pattern_with_matchkind_leftmost_first() {
    assert!(DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build([""])
        .is_err());
}

#[test]
fn test_empty_set_with_matchkind_leftmost_first() {
    assert!(DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build(Vec::<String>::new())
        .is_err());
}

#[test]
fn test_empty_pattern_with_matchkind_standard() {
    assert!(DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::Standard)
        .build([""])
        .is_err());
}

#[test]
fn test_empty_set_with_matchkind_standard() {
    assert!(DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::Standard)
        .build(Vec::<String>::new())
        .is_err());
}
