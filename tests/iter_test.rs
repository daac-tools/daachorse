use daachorse::{
    CharwiseDoubleArrayAhoCorasick, CharwiseDoubleArrayAhoCorasickBuilder, DoubleArrayAhoCorasick,
    DoubleArrayAhoCorasickBuilder, MatchKind,
};

fn bytewise_pairs(pma: &DoubleArrayAhoCorasick<u32>) -> Vec<(Vec<u8>, u32)> {
    pma.iter().collect()
}

fn charwise_pairs(pma: &CharwiseDoubleArrayAhoCorasick<u32>) -> Vec<(String, u32)> {
    pma.iter().collect()
}

fn to_bytes(pairs: &[(&str, u32)]) -> Vec<(Vec<u8>, u32)> {
    pairs
        .iter()
        .map(|&(p, v)| (p.as_bytes().to_vec(), v))
        .collect()
}

fn to_strings(pairs: &[(&str, u32)]) -> Vec<(String, u32)> {
    pairs.iter().map(|&(p, v)| (p.to_string(), v)).collect()
}

#[test]
fn test_iter_basic() {
    let patterns = ["bcd", "ab", "a"];
    let expected = [("a", 2), ("ab", 1), ("bcd", 0)];

    let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    assert_eq!(to_bytes(&expected), bytewise_pairs(&pma));
    let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    assert_eq!(to_strings(&expected), charwise_pairs(&pma));
}

#[test]
fn test_iter_with_values() {
    let patvals = [("bcd", 10), ("ab", 20), ("a", 30)];
    let expected = [("a", 30), ("ab", 20), ("bcd", 10)];

    let pma = DoubleArrayAhoCorasick::with_values(patvals).unwrap();
    assert_eq!(to_bytes(&expected), bytewise_pairs(&pma));
    let pma = CharwiseDoubleArrayAhoCorasick::with_values(patvals).unwrap();
    assert_eq!(to_strings(&expected), charwise_pairs(&pma));
}

#[test]
fn test_iter_multibyte() {
    let patterns = ["全世界", "世界", "に"];
    let expected = [("に", 2), ("世界", 1), ("全世界", 0)];

    let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    assert_eq!(to_bytes(&expected), bytewise_pairs(&pma));
    let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    assert_eq!(to_strings(&expected), charwise_pairs(&pma));
}

#[test]
fn test_iter_empty_pattern_set() {
    let patterns: [&str; 0] = [];

    let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    assert!(bytewise_pairs(&pma).is_empty());
    let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    assert!(charwise_pairs(&pma).is_empty());
}

#[test]
fn test_iter_empty_pattern() {
    let patterns = ["a", ""];
    let expected = [("", 1), ("a", 0)];

    let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    assert_eq!(to_bytes(&expected), bytewise_pairs(&pma));
    let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    assert_eq!(to_strings(&expected), charwise_pairs(&pma));
}

#[test]
fn test_iter_suffix_outputs() {
    let patterns = ["aria", "ria", "ia", "a"];
    let expected = [("a", 3), ("aria", 0), ("ia", 2), ("ria", 1)];

    let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    assert_eq!(to_bytes(&expected), bytewise_pairs(&pma));
    let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    assert_eq!(to_strings(&expected), charwise_pairs(&pma));
}

#[test]
fn test_iter_duplicate_patterns() {
    let patvals = [("ab", 0), ("a", 1), ("ab", 2)];
    let expected = [("a", 1), ("ab", 0), ("ab", 2)];

    let pma = DoubleArrayAhoCorasick::with_values(patvals).unwrap();
    assert_eq!(to_bytes(&expected), bytewise_pairs(&pma));
    let pma = CharwiseDoubleArrayAhoCorasick::with_values(patvals).unwrap();
    assert_eq!(to_strings(&expected), charwise_pairs(&pma));
}

#[test]
fn test_iter_leftmost_longest() {
    let patterns = ["ab", "abc", "b"];
    let expected = [("ab", 0), ("abc", 1), ("b", 2)];

    let pma = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build(patterns)
        .unwrap();
    assert_eq!(to_bytes(&expected), bytewise_pairs(&pma));
    let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build(patterns)
        .unwrap();
    assert_eq!(to_strings(&expected), charwise_pairs(&pma));
    let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongestExperimental)
        .build(patterns)
        .unwrap();
    assert_eq!(to_strings(&expected), charwise_pairs(&pma));
}

#[test]
fn test_iter_experimental_duplicates_and_suffixes() {
    // 1. Duplicate patterns: leftmost matching keeps the first-registered value.
    let patvals = [("ab", 10), ("a", 20), ("ab", 30), ("abc", 40)];
    let expected = [("a", 20), ("ab", 10), ("abc", 40)];

    let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongestExperimental)
        .build_with_values(patvals)
        .unwrap();
    assert_eq!(to_strings(&expected), charwise_pairs(&pma));

    // 2. Suffixes and leaf matches
    let patterns = ["aria", "ria", "ia", "a", ""];
    let expected = [("", 4), ("a", 3), ("aria", 0), ("ia", 2), ("ria", 1)];
    let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongestExperimental)
        .build(patterns)
        .unwrap();
    assert_eq!(to_strings(&expected), charwise_pairs(&pma));

    // 3. Prefiltered experimental automaton
    let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongestExperimental)
        .use_prefilter(true)
        .build(patterns)
        .unwrap();
    assert_eq!(to_strings(&expected), charwise_pairs(&pma));
}

#[test]
fn test_iter_leftmost_first() {
    let patterns = ["ab", "abc", "xy", "x"];
    let expected = [("ab", 0), ("x", 3), ("xy", 2)];

    let pma = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build(patterns)
        .unwrap();
    assert_eq!(to_bytes(&expected), bytewise_pairs(&pma));
    let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build(patterns)
        .unwrap();
    assert_eq!(to_strings(&expected), charwise_pairs(&pma));
    let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirstExperimental)
        .build(patterns)
        .unwrap();
    assert_eq!(to_strings(&expected), charwise_pairs(&pma));
}

#[test]
fn test_iter_bytewise_boundary_bytes() {
    let patterns: [&[u8]; 4] = [b"\xff", b"a\x00", b"\x00", b"\x00\xff"];
    let expected: Vec<(Vec<u8>, u32)> = vec![
        (b"\x00".to_vec(), 2),
        (b"\x00\xff".to_vec(), 3),
        (b"a\x00".to_vec(), 1),
        (b"\xff".to_vec(), 0),
    ];

    let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();
    assert_eq!(expected, bytewise_pairs(&pma));
}

#[test]
fn test_iter_charwise_boundary_chars() {
    let patterns = ["\u{10ffff}", "あ", "a\u{0}", "\u{0}"];
    let expected = [("\u{0}", 3), ("a\u{0}", 2), ("あ", 1), ("\u{10ffff}", 0)];

    let pma = CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
    assert_eq!(to_strings(&expected), charwise_pairs(&pma));
}

#[test]
fn test_iter_multiple_blocks() {
    let mut patterns = vec![];
    for c1 in 'a'..='z' {
        for c2 in 'a'..='z' {
            patterns.push(format!("{c2}{c1}"));
        }
    }
    let mut expected: Vec<(String, u32)> = patterns
        .iter()
        .enumerate()
        .map(|(i, p)| (p.clone(), u32::try_from(i).unwrap()))
        .collect();
    expected.sort();

    let pma = DoubleArrayAhoCorasick::new(&patterns).unwrap();
    let expected_bytes: Vec<(Vec<u8>, u32)> = expected
        .iter()
        .map(|(p, v)| (p.as_bytes().to_vec(), *v))
        .collect();
    assert_eq!(expected_bytes, bytewise_pairs(&pma));
    let pma = CharwiseDoubleArrayAhoCorasick::new(&patterns).unwrap();
    assert_eq!(expected, charwise_pairs(&pma));
}

#[test]
fn test_iter_deserialized() {
    let patterns = ["bcd", "ab", "a", ""];
    let expected = [("", 3), ("a", 2), ("ab", 1), ("bcd", 0)];

    for match_kind in [
        MatchKind::Standard,
        MatchKind::LeftmostLongest,
        MatchKind::LeftmostFirst,
    ] {
        let pma: DoubleArrayAhoCorasick<u32> = DoubleArrayAhoCorasickBuilder::new()
            .match_kind(match_kind)
            .build(patterns)
            .unwrap();
        let bytes = pma.serialize();
        let (pma, _) = DoubleArrayAhoCorasick::<u32>::deserialize(&bytes).unwrap();
        assert_eq!(to_bytes(&expected), bytewise_pairs(&pma));

        let pma: CharwiseDoubleArrayAhoCorasick<u32> = CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(match_kind)
            .build(patterns)
            .unwrap();
        let bytes = pma.serialize();
        let (pma, _) = CharwiseDoubleArrayAhoCorasick::<u32>::deserialize(&bytes).unwrap();
        assert_eq!(to_strings(&expected), charwise_pairs(&pma));
    }

    for match_kind in [
        MatchKind::LeftmostLongestExperimental,
        MatchKind::LeftmostFirstExperimental,
    ] {
        let pma: CharwiseDoubleArrayAhoCorasick<u32> = CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(match_kind)
            .build(patterns)
            .unwrap();
        let bytes = pma.serialize();
        let (pma, _) = CharwiseDoubleArrayAhoCorasick::<u32>::deserialize(&bytes).unwrap();
        assert_eq!(to_strings(&expected), charwise_pairs(&pma));
    }
}

#[test]
fn test_iter_exhausted() {
    let pma = DoubleArrayAhoCorasick::<u32>::new(["a"]).unwrap();
    let mut it = pma.iter();
    assert_eq!(Some((b"a".to_vec(), 0)), it.next());
    assert_eq!(None, it.next());
    assert_eq!(None, it.next());

    let pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(["a"]).unwrap();
    let mut it = pma.iter();
    assert_eq!(Some(("a".to_string(), 0)), it.next());
    assert_eq!(None, it.next());
    assert_eq!(None, it.next());
}

fn set_bytewise_element(bytes: &mut [u8], idx: u32, base: u32, check: u8) {
    let off = 4 + usize::try_from(idx).unwrap() * 12;
    bytes[off..off + 4].copy_from_slice(&base.to_le_bytes());
    bytes[off + 4..off + 8].copy_from_slice(&0u32.to_le_bytes());
    bytes[off + 8..off + 12].copy_from_slice(&u32::from(check).to_le_bytes());
}

#[test]
fn test_iter_bytewise_malformed_cycle() {
    let pma = DoubleArrayAhoCorasick::<u32>::new(["a", "b"]).unwrap();
    let mut bytes = pma.serialize();
    let root_base = u32::from_le_bytes(bytes[4..8].try_into().unwrap());
    for c in *b"ab" {
        let off = 4 + usize::try_from(root_base ^ u32::from(c)).unwrap() * 12;
        bytes[off..off + 4].copy_from_slice(&root_base.to_le_bytes());
    }
    let (pma, _) = DoubleArrayAhoCorasick::<u32>::deserialize(&bytes).unwrap();
    assert_eq!(to_bytes(&[("a", 0), ("b", 1)]), bytewise_pairs(&pma));
}

#[test]
fn test_iter_bytewise_malformed_dag() {
    let pma = DoubleArrayAhoCorasick::<u32>::new(["a"]).unwrap();
    let mut bytes = pma.serialize();
    for idx in 0..256u32 {
        set_bytewise_element(&mut bytes, idx, 0, u8::try_from(idx ^ 255).unwrap());
    }
    set_bytewise_element(&mut bytes, 0, 2, 0);
    for level in 1..=100u32 {
        let next_base = if level < 100 { 2 * level + 2 } else { 0 };
        set_bytewise_element(&mut bytes, 2 * level, next_base, 0);
        set_bytewise_element(&mut bytes, 2 * level + 1, next_base, 1);
    }
    let (pma, _) = DoubleArrayAhoCorasick::<u32>::deserialize(&bytes).unwrap();
    assert_eq!(0, pma.iter().count());
}

#[test]
fn test_iter_charwise_malformed_cycle() {
    let pma = CharwiseDoubleArrayAhoCorasick::<u32>::new(["ab"]).unwrap();
    let mut bytes = pma.serialize();
    let num_states = u32::from_le_bytes(bytes[..4].try_into().unwrap());
    let field = |bytes: &[u8], idx: u32, i: usize| {
        let off = 4 + usize::try_from(idx).unwrap() * 16 + i * 4;
        u32::from_le_bytes(bytes[off..off + 4].try_into().unwrap())
    };
    let child = (1..num_states)
        .find(|&idx| field(&bytes, idx, 1) == 0 && field(&bytes, idx, 0) != 0)
        .unwrap();
    let grandchild = (1..num_states)
        .find(|&idx| field(&bytes, idx, 1) == child)
        .unwrap();
    let off = 4 + usize::try_from(child).unwrap() * 16 + 4;
    bytes[off..off + 4].copy_from_slice(&grandchild.to_le_bytes());
    let (pma, _) = CharwiseDoubleArrayAhoCorasick::<u32>::deserialize(&bytes).unwrap();
    assert_eq!(0, pma.iter().count());
}
