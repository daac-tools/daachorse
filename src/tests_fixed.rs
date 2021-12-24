use super::*;

#[test]
fn test_double_array() {
    /*
     *          a--> 4
     *         /
     *   a--> 1 --c--> 5
     *  /
     * 0 --b--> 2 --c--> 6
     *  \
     *   c--> 3
     *
     *   a = 0
     *   b = 1
     *   c = 2
     */
    let patterns = vec![vec![0, 0], vec![0, 2], vec![1, 2], vec![2]];
    let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();

    let base_expected = vec![
        4,            // 0  (state=0)
        BASE_INVALID, // 1
        BASE_INVALID, // 2  (state=6)
        BASE_INVALID, // 3
        8,            // 4  (state=1)
        0,            // 5  (state=2)
        BASE_INVALID, // 6  (state=3)
        BASE_INVALID, // 7
        BASE_INVALID, // 8  (state=4)
        BASE_INVALID, // 9
        BASE_INVALID, // 10 (state=5)
    ];
    let check_expected = vec![
        1, // 0  (state=0)
        0, // 1
        2, // 2  (state=6)
        2, // 3
        0, // 4  (state=1)
        1, // 5  (state=2)
        2, // 6  (state=3)
        6, // 7
        0, // 8  (state=4)
        8, // 9
        2, // 10 (state=5)
    ];
    let fail_expected = vec![
        ROOT_STATE_IDX, // 0  (state=0)
        ROOT_STATE_IDX, // 1
        6,              // 2  (state=6)
        ROOT_STATE_IDX, // 3
        ROOT_STATE_IDX, // 4  (state=1)
        ROOT_STATE_IDX, // 5  (state=2)
        ROOT_STATE_IDX, // 6  (state=3)
        ROOT_STATE_IDX, // 7
        4,              // 8  (state=4)
        ROOT_STATE_IDX, // 9
        6,              // 10 (state=5)
    ];

    let pma_base: Vec<_> = pma.states[0..11]
        .iter()
        .map(|state| state.base().unwrap_or(BASE_INVALID))
        .collect();
    let pma_check: Vec<_> = pma.states[0..11]
        .iter()
        .map(|state| state.check())
        .collect();
    let pma_fail: Vec<_> = pma.states[0..11].iter().map(|state| state.fail()).collect();

    assert_eq!(base_expected, pma_base);
    assert_eq!(check_expected, pma_check);
    assert_eq!(fail_expected, pma_fail);
}

#[test]
fn test_num_states() {
    /*
     *   b-*-a-*-a-*-b-*-a-*
     *  /
     * *-a-*-b-*-b-*-a-*
     *          \
     *           a-*-b-*-a-*
     */
    let patterns = vec!["abba", "baaba", "ababa"];
    let pma = DoubleArrayAhoCorasick::new(patterns).unwrap();

    assert_eq!(13, pma.num_states());
}

#[test]
fn test_empty_pattern() {
    let patterns = vec![""];
    assert!(DoubleArrayAhoCorasick::new(patterns).is_err());
}

#[test]
fn test_empty_pattern_set() {
    let patterns = Vec::<String>::new();
    assert!(DoubleArrayAhoCorasick::new(patterns).is_err());
}

#[test]
#[should_panic]
fn test_to_create_find_iter_with_leftmost_longest() {
    let pma = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build([""])
        .unwrap();
    pma.find_iter("");
}

#[test]
#[should_panic]
fn test_to_create_find_iter_with_leftmost_first() {
    let pma = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build([""])
        .unwrap();
    pma.find_iter("");
}

#[test]
#[should_panic]
fn test_to_create_find_overlapping_iter_with_leftmost_longest() {
    let pma = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build([""])
        .unwrap();
    pma.find_overlapping_iter("");
}

#[test]
#[should_panic]
fn test_to_create_find_overlapping_iter_with_leftmost_first() {
    let pma = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build([""])
        .unwrap();
    pma.find_overlapping_iter("");
}

#[test]
#[should_panic]
fn test_to_create_find_overlapping_no_suffix_iter_with_leftmost_longest() {
    let pma = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build([""])
        .unwrap();
    pma.find_overlapping_no_suffix_iter("");
}

#[test]
#[should_panic]
fn test_to_create_find_overlapping_no_suffix_iter_with_leftmost_first() {
    let pma = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostFirst)
        .build([""])
        .unwrap();
    pma.find_overlapping_no_suffix_iter("");
}

#[test]
#[should_panic]
fn test_to_create_leftmost_find_iter_with_standard() {
    let pma = DoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::Standard)
        .build([""])
        .unwrap();
    pma.leftmost_find_iter("");
}

/// The following test suites are copied from
/// [aho-corasick crate](https://github.com/BurntSushi/aho-corasick/blob/master/src/tests.rs),
/// although duplicate and empty patterns are removed.

/// A description of a single test against an Aho-Corasick automaton.
///
/// A single test may not necessarily pass on every configuration of an
/// Aho-Corasick automaton. The tests are categorized and grouped appropriately
/// below.
#[derive(Clone, Debug, Eq, PartialEq)]
struct SearchTest {
    /// The name of this test, for debugging.
    name: &'static str,
    /// The patterns to search for.
    patterns: &'static [&'static str],
    /// The text to search.
    haystack: &'static str,
    /// Each match is a triple of (value, start, end), where
    /// value is an associated value and `start`/`end` are indices
    /// into `haystack`.
    matches: &'static [(usize, usize, usize)],
}

/// Short-hand constructor for SearchTest.
macro_rules! t {
    ($name:ident, $patterns:expr, $haystack:expr, $matches:expr) => {
        SearchTest {
            name: stringify!($name),
            patterns: $patterns,
            haystack: $haystack,
            matches: $matches,
        }
    };
}

/// A collection of test groups.
type TestCollection = &'static [&'static [SearchTest]];

// Define several collections corresponding to the different type of match
// semantics supported by Aho-Corasick. These collections have some overlap,
// but each collection should have some tests that no other collection has.

/// Tests for Aho-Corasick's standard non-overlapping match semantics.
const AC_STANDARD_NON_OVERLAPPING: TestCollection = &[BASICS, NON_OVERLAPPING, STANDARD];

/// Tests for Aho-Corasick's standard overlapping match semantics.
const AC_STANDARD_OVERLAPPING: TestCollection = &[BASICS, OVERLAPPING];

/// Tests for Aho-Corasick's leftmost-longest match semantics.
const AC_LEFTMOST_LONGEST: TestCollection = &[BASICS, NON_OVERLAPPING, LEFTMOST, LEFTMOST_LONGEST];

/// Tests for Aho-Corasick's leftmost-first match semantics.
const AC_LEFTMOST_FIRST: TestCollection = &[BASICS, NON_OVERLAPPING, LEFTMOST, LEFTMOST_FIRST];

/// A collection of tests for the Aho-Corasick algorithm that should always be true.
/// That is, all iterators should produce the same answer.
const BASICS: &'static [SearchTest] = &[
    t!(basic001, &["a"], "", &[]),
    t!(basic010, &["a"], "a", &[(0, 0, 1)]),
    t!(basic020, &["a"], "aa", &[(0, 0, 1), (0, 1, 2)]),
    t!(basic030, &["a"], "aaa", &[(0, 0, 1), (0, 1, 2), (0, 2, 3)]),
    t!(basic040, &["a"], "aba", &[(0, 0, 1), (0, 2, 3)]),
    t!(basic050, &["a"], "bba", &[(0, 2, 3)]),
    t!(basic060, &["a"], "bbb", &[]),
    t!(
        basic070,
        &["a"],
        "bababbbba",
        &[(0, 1, 2), (0, 3, 4), (0, 8, 9)]
    ),
    t!(basic100, &["aa"], "", &[]),
    t!(basic110, &["aa"], "aa", &[(0, 0, 2)]),
    t!(basic120, &["aa"], "aabbaa", &[(0, 0, 2), (0, 4, 6)]),
    t!(basic130, &["aa"], "abbab", &[]),
    t!(basic140, &["aa"], "abbabaa", &[(0, 5, 7)]),
    t!(basic200, &["abc"], "abc", &[(0, 0, 3)]),
    t!(basic210, &["abc"], "zazabzabcz", &[(0, 6, 9)]),
    t!(basic220, &["abc"], "zazabczabcz", &[(0, 3, 6), (0, 7, 10)]),
    t!(basic300, &["a", "b"], "", &[]),
    t!(basic310, &["a", "b"], "z", &[]),
    t!(basic320, &["a", "b"], "b", &[(1, 0, 1)]),
    t!(basic330, &["a", "b"], "a", &[(0, 0, 1)]),
    t!(
        basic340,
        &["a", "b"],
        "abba",
        &[(0, 0, 1), (1, 1, 2), (1, 2, 3), (0, 3, 4),]
    ),
    t!(
        basic350,
        &["b", "a"],
        "abba",
        &[(1, 0, 1), (0, 1, 2), (0, 2, 3), (1, 3, 4),]
    ),
    t!(basic360, &["abc", "bc"], "xbc", &[(1, 1, 3),]),
    t!(basic400, &["foo", "bar"], "", &[]),
    t!(
        basic410,
        &["foo", "bar"],
        "foobar",
        &[(0, 0, 3), (1, 3, 6),]
    ),
    t!(
        basic420,
        &["foo", "bar"],
        "barfoo",
        &[(1, 0, 3), (0, 3, 6),]
    ),
    t!(
        basic430,
        &["foo", "bar"],
        "foofoo",
        &[(0, 0, 3), (0, 3, 6),]
    ),
    t!(
        basic440,
        &["foo", "bar"],
        "barbar",
        &[(1, 0, 3), (1, 3, 6),]
    ),
    t!(basic450, &["foo", "bar"], "bafofoo", &[(0, 4, 7),]),
    t!(basic460, &["bar", "foo"], "bafofoo", &[(1, 4, 7),]),
    t!(basic470, &["foo", "bar"], "fobabar", &[(1, 4, 7),]),
    t!(basic480, &["bar", "foo"], "fobabar", &[(0, 4, 7),]),
    t!(
        basic700,
        &["yabcdef", "abcdezghi"],
        "yabcdefghi",
        &[(0, 0, 7),]
    ),
    t!(
        basic710,
        &["yabcdef", "abcdezghi"],
        "yabcdezghi",
        &[(1, 1, 10),]
    ),
    t!(
        basic720,
        &["yabcdef", "bcdeyabc", "abcdezghi"],
        "yabcdezghi",
        &[(2, 1, 10),]
    ),
];

/// Tests for non-overlapping standard match semantics.
///
/// These tests generally shouldn't pass for leftmost-{first,longest}, although
/// some do in order to write clearer tests. For example, standard000 will
/// pass with leftmost-first semantics, but standard010 will not. We write
/// both to emphasize how the match semantics work.
const STANDARD: &'static [SearchTest] = &[
    t!(standard000, &["ab", "abcd"], "abcd", &[(0, 0, 2)]),
    t!(standard010, &["abcd", "ab"], "abcd", &[(1, 0, 2)]),
    t!(standard020, &["abcd", "ab", "abc"], "abcd", &[(1, 0, 2)]),
    t!(standard030, &["abcd", "abc", "ab"], "abcd", &[(2, 0, 2)]),
    t!(
        standard400,
        &["abcd", "bcd", "cd", "b"],
        "abcd",
        &[(3, 1, 2), (2, 2, 4),]
    ),
];

/// Tests for non-overlapping leftmost match semantics. These should pass for
/// both leftmost-first and leftmost-longest match kinds. Stated differently,
/// among ambiguous matches, the longest match and the match that appeared
/// first when constructing the automaton should always be the same.
const LEFTMOST: &'static [SearchTest] = &[
    t!(leftmost030, &["a", "ab"], "aa", &[(0, 0, 1), (0, 1, 2)]),
    t!(leftmost031, &["ab", "a"], "aa", &[(1, 0, 1), (1, 1, 2)]),
    t!(
        leftmost032,
        &["ab", "a"],
        "xayabbbz",
        &[(1, 1, 2), (0, 3, 5)]
    ),
    t!(leftmost300, &["abcd", "bce", "b"], "abce", &[(1, 1, 4)]),
    t!(leftmost310, &["abcd", "ce", "bc"], "abce", &[(2, 1, 3)]),
    t!(
        leftmost320,
        &["abcd", "bce", "ce", "b"],
        "abce",
        &[(1, 1, 4)]
    ),
    t!(
        leftmost330,
        &["abcd", "bce", "cz", "bc"],
        "abcz",
        &[(3, 1, 3)]
    ),
    t!(leftmost340, &["bce", "cz", "bc"], "bcz", &[(2, 0, 2)]),
    t!(leftmost350, &["abc", "bd", "ab"], "abd", &[(2, 0, 2)]),
    t!(
        leftmost360,
        &["abcdefghi", "hz", "abcdefgh"],
        "abcdefghz",
        &[(2, 0, 8),]
    ),
    t!(
        leftmost370,
        &["abcdefghi", "cde", "hz", "abcdefgh"],
        "abcdefghz",
        &[(3, 0, 8),]
    ),
    t!(
        leftmost380,
        &["abcdefghi", "hz", "abcdefgh", "a"],
        "abcdefghz",
        &[(2, 0, 8),]
    ),
    t!(
        leftmost390,
        &["b", "abcdefghi", "hz", "abcdefgh"],
        "abcdefghz",
        &[(3, 0, 8),]
    ),
    t!(
        leftmost400,
        &["h", "abcdefghi", "hz", "abcdefgh"],
        "abcdefghz",
        &[(3, 0, 8),]
    ),
    t!(
        leftmost410,
        &["z", "abcdefghi", "hz", "abcdefgh"],
        "abcdefghz",
        &[(3, 0, 8), (0, 8, 9),]
    ),
];

/// Tests for non-overlapping leftmost-first match semantics. These tests
/// should generally be specific to leftmost-first, which means they should
/// generally fail under leftmost-longest semantics.
const LEFTMOST_FIRST: &'static [SearchTest] = &[
    t!(leftfirst000, &["ab", "abcd"], "abcd", &[(0, 0, 2)]),
    t!(leftfirst020, &["abcd", "ab"], "abcd", &[(0, 0, 4)]),
    t!(
        leftfirst040,
        &["a", "ab"],
        "xayabbbz",
        &[(0, 1, 2), (0, 3, 4)]
    ),
    t!(
        leftfirst100,
        &["abcdefg", "bcde", "bcdef"],
        "abcdef",
        &[(1, 1, 5)]
    ),
    t!(
        leftfirst110,
        &["abcdefg", "bcdef", "bcde"],
        "abcdef",
        &[(1, 1, 6)]
    ),
    t!(leftfirst300, &["abcd", "b", "bce"], "abce", &[(1, 1, 2)]),
    t!(
        leftfirst310,
        &["abcd", "b", "bce", "ce"],
        "abce",
        &[(1, 1, 2), (3, 2, 4),]
    ),
    t!(
        leftfirst320,
        &["a", "abcdefghi", "hz", "abcdefgh"],
        "abcdefghz",
        &[(0, 0, 1), (2, 7, 9),]
    ),
    t!(
        leftfirst330,
        &["a", "abab"],
        "abab",
        &[(0, 0, 1), (0, 2, 3)]
    ),
];

/// Tests for non-overlapping leftmost-longest match semantics. These tests
/// should generally be specific to leftmost-longest, which means they should
/// generally fail under leftmost-first semantics.
const LEFTMOST_LONGEST: &'static [SearchTest] = &[
    t!(leftlong000, &["ab", "abcd"], "abcd", &[(1, 0, 4)]),
    t!(
        leftlong010,
        &["abcd", "bcd", "cd", "b"],
        "abcd",
        &[(0, 0, 4),]
    ),
    t!(leftlong040, &["a", "ab"], "a", &[(0, 0, 1)]),
    t!(leftlong050, &["a", "ab"], "ab", &[(1, 0, 2)]),
    t!(leftlong060, &["ab", "a"], "a", &[(1, 0, 1)]),
    t!(leftlong070, &["ab", "a"], "ab", &[(0, 0, 2)]),
    t!(
        leftlong100,
        &["abcdefg", "bcde", "bcdef"],
        "abcdef",
        &[(2, 1, 6)]
    ),
    t!(
        leftlong110,
        &["abcdefg", "bcdef", "bcde"],
        "abcdef",
        &[(1, 1, 6)]
    ),
    t!(leftlong300, &["abcd", "b", "bce"], "abce", &[(2, 1, 4)]),
    t!(
        leftlong310,
        &["a", "abcdefghi", "hz", "abcdefgh"],
        "abcdefghz",
        &[(3, 0, 8),]
    ),
    t!(leftlong320, &["a", "abab"], "abab", &[(1, 0, 4)]),
    t!(
        leftlong330,
        &["abcd", "b", "ce"],
        "abce",
        &[(1, 1, 2), (2, 2, 4),]
    ),
    t!(
        leftlong340,
        &["a", "ab"],
        "xayabbbz",
        &[(0, 1, 2), (1, 3, 5)]
    ),
];

/// Tests for non-overlapping match semantics.
///
/// Generally these tests shouldn't pass when using overlapping semantics.
/// These should pass for both standard and leftmost match semantics.
const NON_OVERLAPPING: &'static [SearchTest] = &[
    t!(nover010, &["abcd", "bcd", "cd"], "abcd", &[(0, 0, 4),]),
    t!(nover020, &["bcd", "cd", "abcd"], "abcd", &[(2, 0, 4),]),
    t!(nover030, &["abc", "bc"], "zazabcz", &[(0, 3, 6),]),
    t!(
        nover100,
        &["ab", "ba"],
        "abababa",
        &[(0, 0, 2), (0, 2, 4), (0, 4, 6),]
    ),
];

/// Tests for overlapping match semantics.
///
/// This only supports standard match semantics, since leftmost-{first,longest}
/// do not support overlapping matches.
const OVERLAPPING: &'static [SearchTest] = &[
    t!(
        over000,
        &["abcd", "bcd", "cd", "b"],
        "abcd",
        &[(3, 1, 2), (0, 0, 4), (1, 1, 4), (2, 2, 4),]
    ),
    t!(
        over010,
        &["bcd", "cd", "b", "abcd"],
        "abcd",
        &[(2, 1, 2), (3, 0, 4), (0, 1, 4), (1, 2, 4),]
    ),
    t!(
        over020,
        &["abcd", "bcd", "cd"],
        "abcd",
        &[(0, 0, 4), (1, 1, 4), (2, 2, 4),]
    ),
    t!(
        over030,
        &["bcd", "abcd", "cd"],
        "abcd",
        &[(1, 0, 4), (0, 1, 4), (2, 2, 4),]
    ),
    t!(
        over040,
        &["bcd", "cd", "abcd"],
        "abcd",
        &[(2, 0, 4), (0, 1, 4), (1, 2, 4),]
    ),
    t!(over050, &["abc", "bc"], "zazabcz", &[(0, 3, 6), (1, 4, 6),]),
    t!(
        over100,
        &["ab", "ba"],
        "abababa",
        &[
            (0, 0, 2),
            (1, 1, 3),
            (0, 2, 4),
            (1, 3, 5),
            (0, 4, 6),
            (1, 5, 7),
        ]
    ),
    t!(
        over360,
        &["foo", "foofoo"],
        "foofoo",
        &[(0, 0, 3), (1, 0, 6), (0, 3, 6)]
    ),
];

#[test]
fn search_tests_have_unique_names() {
    let assert = |constname, tests: &[SearchTest]| {
        let mut seen = std::collections::HashMap::new(); // map from test name to position
        for (i, test) in tests.iter().enumerate() {
            if !seen.contains_key(test.name) {
                seen.insert(test.name, i);
            } else {
                let last = seen[test.name];
                panic!(
                    "{} tests have duplicate names at positions {} and {}",
                    constname, last, i
                );
            }
        }
    };
    assert("BASICS", BASICS);
    assert("STANDARD", STANDARD);
    assert("LEFTMOST", LEFTMOST);
    assert("LEFTMOST_FIRST", LEFTMOST_FIRST);
    assert("LEFTMOST_LONGEST", LEFTMOST_LONGEST);
    assert("NON_OVERLAPPING", NON_OVERLAPPING);
    assert("OVERLAPPING", OVERLAPPING);
}

macro_rules! testconfig {
    (non_overlapping, $name:ident, $collection:expr, $kind:ident, $with:expr) => {
        #[test]
        fn $name() {
            run_search_tests($collection, |test| {
                let pma = DoubleArrayAhoCorasickBuilder::new()
                    .match_kind(MatchKind::$kind)
                    .build(test.patterns)
                    .unwrap();
                pma.find_iter(test.haystack).collect()
            });
        }
    };
    (overlapping, $name:ident, $collection:expr, $kind:ident, $with:expr) => {
        #[test]
        fn $name() {
            run_search_tests($collection, |test| {
                let pma = DoubleArrayAhoCorasickBuilder::new()
                    .match_kind(MatchKind::$kind)
                    .build(test.patterns)
                    .unwrap();
                pma.find_overlapping_iter(test.haystack).collect()
            });
        }
    };
    (leftmost, $name:ident, $collection:expr, $kind:ident, $with:expr) => {
        #[test]
        fn $name() {
            run_search_tests($collection, |test| {
                let pma = DoubleArrayAhoCorasickBuilder::new()
                    .match_kind(MatchKind::$kind)
                    .build(test.patterns)
                    .unwrap();
                pma.leftmost_find_iter(test.haystack).collect()
            });
        }
    };
}

testconfig!(
    non_overlapping,
    search_standard_non_overlapping,
    AC_STANDARD_NON_OVERLAPPING,
    Standard,
    |_| ()
);

testconfig!(
    overlapping,
    search_standard_overlapping,
    AC_STANDARD_OVERLAPPING,
    Standard,
    |_| ()
);

testconfig!(
    leftmost,
    search_leftmost_longest,
    AC_LEFTMOST_LONGEST,
    LeftmostLongest,
    |_| ()
);

testconfig!(
    leftmost,
    search_leftmost_first,
    AC_LEFTMOST_FIRST,
    LeftmostFirst,
    |_| ()
);

fn run_search_tests<F: FnMut(&SearchTest) -> Vec<Match>>(which: TestCollection, mut f: F) {
    let get_match_triples = |matches: Vec<Match>| -> Vec<(usize, usize, usize)> {
        matches
            .into_iter()
            .map(|m| (m.value(), m.start(), m.end()))
            .collect()
    };
    for &tests in which {
        for test in tests {
            assert_eq!(
                test.matches,
                get_match_triples(f(&test)).as_slice(),
                "test: {}, patterns: {:?}, haystack: {:?}",
                test.name,
                test.patterns,
                test.haystack
            );
        }
    }
}
