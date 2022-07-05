use daachorse::{DoubleArrayAhoCorasick, DoubleArrayAhoCorasickBuilder, MatchKind};

#[test]
#[should_panic]
fn test_find_iter_with_leftmost_longest() {
    let pma: DoubleArrayAhoCorasick<u32> = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build(["pattern"])
        .unwrap();
    pma.find_iter("");
}

#[test]
#[should_panic]
fn test_find_iter_with_leftmost_first() {
    let pma: DoubleArrayAhoCorasick<u32> = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build(["pattern"])
        .unwrap();
    pma.find_iter("");
}

#[test]
#[should_panic]
fn test_find_overlapping_iter_with_leftmost_longest() {
    let pma: DoubleArrayAhoCorasick<u32> = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build(["pattern"])
        .unwrap();
    pma.find_overlapping_iter("");
}

#[test]
#[should_panic]
fn test_find_overlapping_iter_with_leftmost_first() {
    let pma: DoubleArrayAhoCorasick<u32> = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build(["pattern"])
        .unwrap();
    pma.find_overlapping_iter("");
}

#[test]
#[should_panic]
fn test_find_overlapping_no_suffix_iter_with_leftmost_longest() {
    let pma: DoubleArrayAhoCorasick<u32> = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build(["pattern"])
        .unwrap();
    pma.find_overlapping_no_suffix_iter("");
}

#[test]
#[should_panic]
fn test_find_overlapping_no_suffix_iter_with_leftmost_first() {
    let pma: DoubleArrayAhoCorasick<u32> = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build(["pattern"])
        .unwrap();
    pma.find_overlapping_no_suffix_iter("");
}

#[test]
#[should_panic]
fn test_leftmost_find_iter_with_standard() {
    let pma: DoubleArrayAhoCorasick<u32> = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::Standard)
        .build(["pattern"])
        .unwrap();
    pma.leftmost_find_iter("");
}
