use daachorse::charwise::{CharwiseDoubleArrayAhoCorasick, CharwiseDoubleArrayAhoCorasickBuilder};
use daachorse::MatchKind;

#[test]
fn test_empty_pattern() {
    assert!(CharwiseDoubleArrayAhoCorasick::new([""]).is_err());
}

#[test]
fn test_empty_set() {
    assert!(CharwiseDoubleArrayAhoCorasick::new(Vec::<String>::new()).is_err());
}

#[test]
fn test_duplicate_patterns() {
    assert!(CharwiseDoubleArrayAhoCorasick::new(["abc", "123", "abc",]).is_err());
}

#[test]
fn test_empty_pattern_with_matchkind_leftmost_longest() {
    assert!(CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build([""])
        .is_err());
}

#[test]
fn test_empty_set_with_matchkind_leftmost_longest() {
    assert!(CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build(Vec::<String>::new())
        .is_err());
}

#[test]
fn test_duplicate_patterns_with_matchkind_leftmost_longest() {
    assert!(CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build(["abc", "123", "abc",])
        .is_err());
}

#[test]
fn test_empty_pattern_with_matchkind_leftmost_first() {
    assert!(CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build([""])
        .is_err());
}

#[test]
fn test_empty_set_with_matchkind_leftmost_first() {
    assert!(CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build(Vec::<String>::new())
        .is_err());
}

#[test]
fn test_duplicate_patterns_with_matchkind_leftmost_first() {
    assert!(CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build(["abc", "123", "abc",])
        .is_err());
}

#[test]
fn test_empty_pattern_with_matchkind_standard() {
    assert!(CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::Standard)
        .build([""])
        .is_err());
}

#[test]
fn test_empty_set_with_matchkind_standard() {
    assert!(CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::Standard)
        .build(Vec::<String>::new())
        .is_err());
}

#[test]
fn test_duplicate_patterns_with_matchkind_standard() {
    assert!(CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::Standard)
        .build(["abc", "123", "abc"])
        .is_err());
}
