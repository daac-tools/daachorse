use daachorse::{CharwiseDoubleArrayAhoCorasick, CharwiseDoubleArrayAhoCorasickBuilder, MatchKind};

#[test]
#[should_panic]
fn test_find_iter_with_leftmost_longest() {
    let pma: CharwiseDoubleArrayAhoCorasick<usize> = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build(["pattern"])
        .unwrap();
    pma.find_iter("");
}

#[test]
#[should_panic]
fn test_find_iter_with_leftmost_first() {
    let pma: CharwiseDoubleArrayAhoCorasick<usize> = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build(["pattern"])
        .unwrap();
    pma.find_iter("");
}

#[test]
#[should_panic]
fn test_find_overlapping_iter_with_leftmost_longest() {
    let pma: CharwiseDoubleArrayAhoCorasick<usize> = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build(["pattern"])
        .unwrap();
    pma.find_overlapping_iter("");
}

#[test]
#[should_panic]
fn test_find_overlapping_iter_with_leftmost_first() {
    let pma: CharwiseDoubleArrayAhoCorasick<usize> = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build(["pattern"])
        .unwrap();
    pma.find_overlapping_iter("");
}

#[test]
#[should_panic]
fn test_find_overlapping_no_suffix_iter_with_leftmost_longest() {
    let pma: CharwiseDoubleArrayAhoCorasick<usize> = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build(["pattern"])
        .unwrap();
    pma.find_overlapping_no_suffix_iter("");
}

#[test]
#[should_panic]
fn test_find_overlapping_no_suffix_iter_with_leftmost_first() {
    let pma: CharwiseDoubleArrayAhoCorasick<usize> = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build(["pattern"])
        .unwrap();
    pma.find_overlapping_no_suffix_iter("");
}

#[test]
#[should_panic]
fn test_leftmost_find_iter_with_standard() {
    let pma: CharwiseDoubleArrayAhoCorasick<usize> = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::Standard)
        .build(["pattern"])
        .unwrap();
    pma.leftmost_find_iter("");
}

#[test]
#[should_panic]
fn test_cache_depth_with_leftmost_longest() {
    let mut pma: CharwiseDoubleArrayAhoCorasick<usize> =
        CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostLongest)
            .build(["pattern"])
            .unwrap();
    let _ = pma.cache_depths();
}

#[test]
#[should_panic]
fn test_cache_depth_with_leftmost_first() {
    let mut pma: CharwiseDoubleArrayAhoCorasick<usize> =
        CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostFirst)
            .build(["pattern"])
            .unwrap();
    let _ = pma.cache_depths();
}

#[test]
#[should_panic]
fn test_leftmost_find_iter_experimental_with_standard() {
    let pma: CharwiseDoubleArrayAhoCorasick<usize> = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::Standard)
        .build(["pattern"])
        .unwrap();
    pma.leftmost_find_iter_experimental("");
}

#[test]
#[should_panic]
fn test_leftmost_find_iter_experimental_with_leftmost_first() {
    let pma: CharwiseDoubleArrayAhoCorasick<usize> = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build(["pattern"])
        .unwrap();
    pma.leftmost_find_iter_experimental("");
}

#[test]
#[should_panic]
fn test_leftmost_find_iter_experimental_with_leftmost_longest() {
    let pma: CharwiseDoubleArrayAhoCorasick<usize> = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build(["pattern"])
        .unwrap();
    pma.leftmost_find_iter_experimental("");
}

#[test]
#[should_panic]
fn test_leftmost_finder_experimental_with_leftmost_first() {
    let pma: CharwiseDoubleArrayAhoCorasick<usize> = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build(["pattern"])
        .unwrap();
    let _ = pma.leftmost_finder_experimental();
}

#[test]
#[should_panic]
fn test_leftmost_finder_experimental_with_leftmost_longest() {
    let pma: CharwiseDoubleArrayAhoCorasick<usize> = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build(["pattern"])
        .unwrap();
    let _ = pma.leftmost_finder_experimental();
}

#[test]
#[should_panic]
fn test_leftmost_find_iter_with_leftmost_longest_experimental() {
    let pma: CharwiseDoubleArrayAhoCorasick<usize> = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongestExperimental)
        .build(["pattern"])
        .unwrap();
    pma.leftmost_find_iter("");
}

#[test]
#[should_panic]
fn test_leftmost_find_iter_with_leftmost_first_experimental() {
    let pma: CharwiseDoubleArrayAhoCorasick<usize> = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirstExperimental)
        .build(["pattern"])
        .unwrap();
    pma.leftmost_find_iter("");
}

#[test]
fn test_leftmost_longest_experimental_with_empty_pattern() {
    let pma: CharwiseDoubleArrayAhoCorasick<usize> = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongestExperimental)
        .build(["", "pattern"])
        .unwrap();
    let matches: Vec<_> = pma.leftmost_find_iter_experimental("pattern").collect();
    assert_eq!(matches.len(), 1);
    assert_eq!(
        (matches[0].start(), matches[0].end(), matches[0].value()),
        (0, 7, 1)
    );
}

#[test]
fn test_leftmost_first_experimental_with_empty_pattern() {
    let pma: CharwiseDoubleArrayAhoCorasick<usize> = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirstExperimental)
        .build(["", "pattern"])
        .unwrap();
    let matches: Vec<_> = pma.leftmost_find_iter_experimental("pattern").collect();
    assert!(!matches.is_empty());
}

#[test]
#[should_panic]
fn test_cache_depth_with_leftmost_longest_experimental() {
    let mut pma: CharwiseDoubleArrayAhoCorasick<usize> =
        CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostLongestExperimental)
            .build(["pattern"])
            .unwrap();
    let _ = pma.cache_depths();
}

#[test]
#[should_panic]
fn test_cache_depth_with_leftmost_first_experimental() {
    let mut pma: CharwiseDoubleArrayAhoCorasick<usize> =
        CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(MatchKind::LeftmostFirstExperimental)
            .build(["pattern"])
            .unwrap();
    let _ = pma.cache_depths();
}
