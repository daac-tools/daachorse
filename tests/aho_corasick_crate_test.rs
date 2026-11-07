#![cfg_attr(rustfmt, rustfmt_skip)]

use daachorse::{
    CharwiseDoubleArrayAhoCorasickBuilder, DoubleArrayAhoCorasickBuilder, Match, MatchKind,
};

/// Most of the following tests were copied from,
/// [the aho-corasick crate](https://github.com/BurntSushi/aho-corasick/blob/master/src/tests.rs),
/// but we have also included some of our own tests.
///
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
    t!(basic000, &[], "", &[]),
    t!(basic_daachorse001, &[], "a", &[]),
    t!(basic_daachorse002, &[], "abc", &[]),
    t!(basic001, &[""], "a", &[(0, 0, 0), (0, 1, 1)]),
    t!(basic002, &["a"], "", &[]),
    t!(basic010, &["a"], "a", &[(0, 0, 1)]),
    t!(basic020, &["a"], "aa", &[(0, 0, 1), (0, 1, 2)]),
    t!(basic030, &["a"], "aaa", &[(0, 0, 1), (0, 1, 2), (0, 2, 3)]),
    t!(basic040, &["a"], "aba", &[(0, 0, 1), (0, 2, 3)]),
    t!(basic050, &["a"], "bba", &[(0, 2, 3)]),
    t!(basic060, &["a"], "bbb", &[]),
    t!(basic070, &["a"], "bababbbba", &[(0, 1, 2), (0, 3, 4), (0, 8, 9)]),
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
    t!(basic410, &["foo", "bar"], "foobar", &[(0, 0, 3), (1, 3, 6),]),
    t!(basic420, &["foo", "bar"], "barfoo", &[(1, 0, 3), (0, 3, 6),]),
    t!(basic430, &["foo", "bar"], "foofoo", &[(0, 0, 3), (0, 3, 6),]),
    t!(basic440, &["foo", "bar"], "barbar", &[(1, 0, 3), (1, 3, 6),]),
    t!(basic450, &["foo", "bar"], "bafofoo", &[(0, 4, 7),]),
    t!(basic460, &["bar", "foo"], "bafofoo", &[(1, 4, 7),]),
    t!(basic470, &["foo", "bar"], "fobabar", &[(1, 4, 7),]),
    t!(basic480, &["bar", "foo"], "fobabar", &[(0, 4, 7),]),
    t!(basic600, &[""], "", &[(0, 0, 0)]),
    t!(basic610, &[""], "a", &[(0, 0, 0), (0, 1, 1)]),
    t!(basic620, &[""], "abc", &[(0, 0, 0), (0, 1, 1), (0, 2, 2), (0, 3, 3)]),
    t!(basic700, &["yabcdef", "abcdezghi"], "yabcdefghi", &[(0, 0, 7),]),
    t!(basic710, &["yabcdef", "abcdezghi"], "yabcdezghi", &[(1, 1, 10),]),
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
    t!(standard040, &["a", ""], "a", &[(1, 0, 0), (1, 1, 1)]),
    t!(
        standard400,
        &["abcd", "bcd", "cd", "b"],
        "abcd",
        &[(3, 1, 2), (2, 2, 4),]
    ),
    t!(standard410, &["", "a"], "a", &[(0, 0, 0), (0, 1, 1),]),
    t!(standard420, &["", "a"], "aa", &[(0, 0, 0), (0, 1, 1), (0, 2, 2),]),
    t!(standard430, &["", "a", ""], "a", &[(0, 0, 0), (0, 1, 1),]),
    t!(standard440, &["a", "", ""], "a", &[(1, 0, 0), (1, 1, 1),]),
    t!(standard450, &["", "", "a"], "a", &[(0, 0, 0), (0, 1, 1),]),
];

/// Tests for non-overlapping leftmost match semantics. These should pass for
/// both leftmost-first and leftmost-longest match kinds. Stated differently,
/// among ambiguous matches, the longest match and the match that appeared
/// first when constructing the automaton should always be the same.
const LEFTMOST: &'static [SearchTest] = &[
    t!(leftmost000, &["ab", "ab"], "abcd", &[(0, 0, 2)]),
    t!(leftmost010, &["a", ""], "a", &[(0, 0, 1)]),
    t!(leftmost011, &["a", ""], "ab", &[(0, 0, 1), (1, 2, 2)]),
    t!(leftmost_daachorse001, &["a", ""], "ba", &[(1, 0, 0), (0, 1, 2)]),
    t!(leftmost_daachorse002, &["a", ""], "abab", &[(0, 0, 1), (0, 2, 3), (1, 4, 4)]),
    t!(leftmost_daachorse003, &["a", "a"], "abab", &[(0, 0, 1), (0, 2, 3)]),
    t!(leftmost020, &["", ""], "a", &[(0, 0, 0), (0, 1, 1)]),
    t!(leftmost030, &["a", "ab"], "aa", &[(0, 0, 1), (0, 1, 2)]),
    t!(leftmost031, &["ab", "a"], "aa", &[(1, 0, 1), (1, 1, 2)]),
    t!(leftmost032, &["ab", "a"], "xayabbbz", &[(1, 1, 2), (0, 3, 5)]),
    t!(leftmost300, &["abcd", "bce", "b"], "abce", &[(1, 1, 4)]),
    t!(leftmost310, &["abcd", "ce", "bc"], "abce", &[(2, 1, 3)]),
    t!(leftmost320, &["abcd", "bce", "ce", "b"], "abce", &[(1, 1, 4)]),
    t!(leftmost330, &["abcd", "bce", "cz", "bc"], "abcz", &[(3, 1, 3)]),
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
    t!(
        leftmost_daachorse500,
        &["a", "xyz", ""],
        "axyw",
        &[(0, 0, 1), (2, 2, 2), (2, 3, 3), (2, 4, 4)]
    ),
    t!(
        leftmost_daachorse501,
        &["a", "xyz", ""],
        "axywa",
        &[(0, 0, 1), (2, 2, 2), (2, 3, 3), (0, 4, 5)]
    ),
];

/// Tests for non-overlapping leftmost-first match semantics. These tests
/// should generally be specific to leftmost-first, which means they should
/// generally fail under leftmost-longest semantics.
const LEFTMOST_FIRST: &'static [SearchTest] = &[
    t!(leftfirst000, &["ab", "abcd"], "abcd", &[(0, 0, 2)]),
    t!(leftfirst010, &["", "a"], "a", &[(0, 0, 0), (0, 1, 1)]),
    t!(leftfirst011, &["", "a", ""], "a", &[(0, 0, 0), (0, 1, 1),]),
    t!(leftfirst012, &["a", "", ""], "a", &[(0, 0, 1)]),
    t!(leftfirst013, &["", "", "a"], "a", &[(0, 0, 0), (0, 1, 1)]),
    t!(leftfirst014, &["a", ""], "a", &[(0, 0, 1)]),
    t!(leftfirst015, &["a", ""], "ab", &[(0, 0, 1), (1, 2, 2)]),
    t!(leftfirst020, &["abcd", "ab"], "abcd", &[(0, 0, 4)]),
    t!(leftfirst030, &["ab", "ab"], "abcd", &[(0, 0, 2)]),
    t!(leftfirst040, &["a", "ab"], "xayabbbz", &[(0, 1, 2), (0, 3, 4)]),
    t!(leftfirst100, &["abcdefg", "bcde", "bcdef"], "abcdef", &[(1, 1, 5)]),
    t!(leftfirst110, &["abcdefg", "bcdef", "bcde"], "abcdef", &[(1, 1, 6)]),
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
    t!(leftfirst330, &["a", "abab"], "abab", &[(0, 0, 1), (0, 2, 3)]),
    t!(leftfirst400, &["amwix", "samwise", "sam"], "Zsamwix", &[(2, 1, 4)]),
];

/// Tests for non-overlapping leftmost-longest match semantics. These tests
/// should generally be specific to leftmost-longest, which means they should
/// generally fail under leftmost-first semantics.
const LEFTMOST_LONGEST: &'static [SearchTest] = &[
    t!(leftlong000, &["ab", "abcd"], "abcd", &[(1, 0, 4)]),
    t!(leftlong010, &["abcd", "bcd", "cd", "b"], "abcd", &[(0, 0, 4),]),
    t!(leftlong020, &["", "a"], "a", &[(1, 0, 1)]),
    t!(leftlong021, &["", "a", ""], "a", &[(1, 0, 1)]),
    t!(leftlong022, &["a", "", ""], "a", &[(0, 0, 1)]),
    t!(leftlong023, &["", "", "a"], "a", &[(2, 0, 1)]),
    t!(leftlong024, &["", "a"], "ab", &[(1, 0, 1), (0, 2, 2)]),
    t!(leftlong030, &["", "a"], "aa", &[(1, 0, 1), (1, 1, 2)]),
    t!(leftlong040, &["a", "ab"], "a", &[(0, 0, 1)]),
    t!(leftlong050, &["a", "ab"], "ab", &[(1, 0, 2)]),
    t!(leftlong060, &["ab", "a"], "a", &[(1, 0, 1)]),
    t!(leftlong070, &["ab", "a"], "ab", &[(0, 0, 2)]),
    t!(leftlong100, &["abcdefg", "bcde", "bcdef"], "abcdef", &[(2, 1, 6)]),
    t!(leftlong110, &["abcdefg", "bcdef", "bcde"], "abcdef", &[(1, 1, 6)]),
    t!(leftlong300, &["abcd", "b", "bce"], "abce", &[(2, 1, 4)]),
    t!(
        leftlong310,
        &["a", "abcdefghi", "hz", "abcdefgh"],
        "abcdefghz",
        &[(3, 0, 8),]
    ),
    t!(leftlong320, &["a", "abab"], "abab", &[(1, 0, 4)]),
    t!(leftlong330, &["abcd", "b", "ce"], "abce", &[(1, 1, 2), (2, 2, 4),]),
    t!(leftlong340, &["a", "ab"], "xayabbbz", &[(0, 1, 2), (1, 3, 5)]),
];

/// Tests for non-overlapping match semantics.
///
/// Generally these tests shouldn't pass when using overlapping semantics.
/// These should pass for both standard and leftmost match semantics.
const NON_OVERLAPPING: &'static [SearchTest] = &[
    t!(nover010, &["abcd", "bcd", "cd"], "abcd", &[(0, 0, 4),]),
    t!(nover020, &["bcd", "cd", "abcd"], "abcd", &[(2, 0, 4),]),
    t!(nover030, &["abc", "bc"], "zazabcz", &[(0, 3, 6),]),
    t!(nover_daachorse001, &["abc", "abc"], "abcabc", &[(0, 0, 3), (0, 3, 6)]),
    t!(
        nover100,
        &["ab", "ba"],
        "abababa",
        &[(0, 0, 2), (0, 2, 4), (0, 4, 6),]
    ),
    t!(nover200, &["foo", "foo"], "foobarfoo", &[(0, 0, 3), (0, 6, 9),]),
    t!(nover300, &["", ""], "", &[(0, 0, 0),]),
    t!(nover310, &["", ""], "a", &[(0, 0, 0), (0, 1, 1),]),
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
        &[(0, 0, 2), (1, 1, 3), (0, 2, 4), (1, 3, 5), (0, 4, 6), (1, 5, 7),]
    ),
    t!(
        over200,
        &["foo", "foo"],
        "foobarfoo",
        &[(0, 0, 3), (1, 0, 3), (0, 6, 9), (1, 6, 9),]
    ),
    t!(over300, &["", ""], "", &[(0, 0, 0), (1, 0, 0),]),
    t!(
        over310,
        &["", ""],
        "a",
        &[(0, 0, 0), (1, 0, 0), (0, 1, 1), (1, 1, 1),]
    ),
    t!(over320, &["", "a"], "a", &[(0, 0, 0), (1, 0, 1), (0, 1, 1),]),
    t!(
        over330,
        &["", "a", ""],
        "a",
        &[(0, 0, 0), (2, 0, 0), (1, 0, 1), (0, 1, 1), (2, 1, 1),]
    ),
    t!(
        over340,
        &["a", "", ""],
        "a",
        &[(1, 0, 0), (2, 0, 0), (0, 0, 1), (1, 1, 1), (2, 1, 1),]
    ),
    t!(
        over350,
        &["", "", "a"],
        "a",
        &[(0, 0, 0), (1, 0, 0), (2, 0, 1), (0, 1, 1), (1, 1, 1),]
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
    (non_overlapping, $name:ident, $builder:ident, $collection:expr, $kind:ident, $with:expr) => {
        #[test]
        fn $name() {
            run_search_tests($collection, |test| {
                let pma = $builder::new()
                    .match_kind(MatchKind::$kind)
                    .build(test.patterns)
                    .unwrap();
                pma.find_iter(test.haystack).collect()
            });
        }
    };
    (non_overlapping_stepper_bytes, $name:ident, $builder:ident, $collection:expr, $kind:ident, $with:expr) => {
        #[test]
        fn $name() {
            run_search_tests($collection, |test| {
                let pma = $builder::new()
                    .match_kind(MatchKind::$kind)
                    .build(test.patterns)
                    .unwrap();
                let mut stepper = pma.find_stepper();
                let m = stepper.matches();
                m.into_iter()
                    .chain(
                        test.haystack
                            .as_bytes()
                            .iter()
                            .flat_map(|&b| {
                                stepper.consume(b);
                                stepper.matches()
                            }),
                    )
                    .collect()
            });
        }
    };
    (non_overlapping_stepper_chars, $name:ident, $builder:ident, $collection:expr, $kind:ident, $with:expr) => {
        #[test]
        fn $name() {
            run_search_tests($collection, |test| {
                let pma = $builder::new()
                    .match_kind(MatchKind::$kind)
                    .build(test.patterns)
                    .unwrap();
                let mut stepper = pma.find_stepper();
                let m = stepper.matches();
                m.into_iter()
                    .chain(test.haystack.chars().flat_map(|c| {
                        stepper.consume(c);
                        stepper.matches()
                    }))
                    .collect()
            });
        }
    };
    (overlapping, $name:ident, $builder:ident, $collection:expr, $kind:ident, $with:expr) => {
        #[test]
        fn $name() {
            run_search_tests($collection, |test| {
                let pma = $builder::new()
                    .match_kind(MatchKind::$kind)
                    .build(test.patterns)
                    .unwrap();
                pma.find_overlapping_iter(test.haystack).collect()
            });
        }
    };
    (overlapping_stepper_bytes, $name:ident, $builder:ident, $collection:expr, $kind:ident, $with:expr) => {
        #[test]
        fn $name() {
            run_search_tests($collection, |test| {
                let pma = $builder::new()
                    .match_kind(MatchKind::$kind)
                    .build(test.patterns)
                    .unwrap();
                let mut stepper = pma.find_overlapping_stepper();
                let m = stepper.matches();
                m.chain(
                    test.haystack
                        .as_bytes()
                        .iter()
                        .flat_map(|&b| {
                            stepper.consume(b);
                            stepper.matches().collect::<Vec<_>>()
                        }),
                )
                .collect()
            });
        }
    };
    (overlapping_stepper_chars, $name:ident, $builder:ident, $collection:expr, $kind:ident, $with:expr) => {
        #[test]
        fn $name() {
            run_search_tests($collection, |test| {
                let pma = $builder::new()
                    .match_kind(MatchKind::$kind)
                    .build(test.patterns)
                    .unwrap();
                let mut stepper = pma.find_overlapping_stepper();
                let m = stepper.matches();
                m.chain(
                    test.haystack
                        .chars()
                        .flat_map(|c| {
                            stepper.consume(c);
                            stepper.matches().collect::<Vec<_>>()
                        }),
                )
                .collect()
            });
        }
    };
    (leftmost, $name:ident, $builder:ident, $collection:expr, $kind:ident, $with:expr) => {
        #[test]
        fn $name() {
            run_search_tests($collection, |test| {
                let pma = $builder::new()
                    .match_kind(MatchKind::$kind)
                    .build(test.patterns)
                    .unwrap();
                pma.leftmost_find_iter(test.haystack).collect()
            });
        }
    };
}

// Bytewise Daachorse tests
testconfig!(
    non_overlapping,
    search_standard_non_overlapping,
    DoubleArrayAhoCorasickBuilder,
    AC_STANDARD_NON_OVERLAPPING,
    Standard,
    |_| ()
);

testconfig!(
    non_overlapping_stepper_bytes,
    search_standard_non_overlapping_stepper,
    DoubleArrayAhoCorasickBuilder,
    AC_STANDARD_NON_OVERLAPPING,
    Standard,
    |_| ()
);

testconfig!(
    overlapping,
    search_standard_overlapping,
    DoubleArrayAhoCorasickBuilder,
    AC_STANDARD_OVERLAPPING,
    Standard,
    |_| ()
);

testconfig!(
    overlapping_stepper_bytes,
    search_standard_overlapping_stepper,
    DoubleArrayAhoCorasickBuilder,
    AC_STANDARD_OVERLAPPING,
    Standard,
    |_| ()
);

testconfig!(
    leftmost,
    search_leftmost_longest,
    DoubleArrayAhoCorasickBuilder,
    AC_LEFTMOST_LONGEST,
    LeftmostLongest,
    |_| ()
);

testconfig!(
    leftmost,
    search_leftmost_first,
    DoubleArrayAhoCorasickBuilder,
    AC_LEFTMOST_FIRST,
    LeftmostFirst,
    |_| ()
);

// Charwise Daachorse tests
testconfig!(
    non_overlapping,
    search_standard_non_overlapping_charwise,
    CharwiseDoubleArrayAhoCorasickBuilder,
    AC_STANDARD_NON_OVERLAPPING,
    Standard,
    |_| ()
);

// Charwise Daachorse tests
testconfig!(
    non_overlapping_stepper_chars,
    search_standard_non_overlapping_charwise_stepper,
    CharwiseDoubleArrayAhoCorasickBuilder,
    AC_STANDARD_NON_OVERLAPPING,
    Standard,
    |_| ()
);

testconfig!(
    overlapping,
    search_standard_overlapping_charwise,
    CharwiseDoubleArrayAhoCorasickBuilder,
    AC_STANDARD_OVERLAPPING,
    Standard,
    |_| ()
);

testconfig!(
    overlapping_stepper_chars,
    search_standard_overlapping_charwise_stepper,
    CharwiseDoubleArrayAhoCorasickBuilder,
    AC_STANDARD_OVERLAPPING,
    Standard,
    |_| ()
);

testconfig!(
    leftmost,
    search_leftmost_longest_charwise,
    CharwiseDoubleArrayAhoCorasickBuilder,
    AC_LEFTMOST_LONGEST,
    LeftmostLongest,
    |_| ()
);

testconfig!(
    leftmost,
    search_leftmost_first_charwise,
    CharwiseDoubleArrayAhoCorasickBuilder,
    AC_LEFTMOST_FIRST,
    LeftmostFirst,
    |_| ()
);

fn run_search_tests<F: FnMut(&SearchTest) -> Vec<Match<usize>>>(which: TestCollection, mut f: F) {
    let get_match_triples = |matches: Vec<Match<usize>>| -> Vec<(usize, usize, usize)> {
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


fn to_match_triples(matches: impl IntoIterator<Item = Match<usize>>) -> Vec<(usize, usize, usize)> {
    matches
        .into_iter()
        .map(|m| (m.value(), m.start(), m.end()))
        .collect()
}

#[test]
fn search_leftmost_longest_experimental_charwise() {
    for &collection in AC_LEFTMOST_LONGEST {
        for test in collection {
            let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
                .match_kind(MatchKind::LeftmostLongestExperimental)
                .build(test.patterns)
                .unwrap();
            let matches: Vec<Match<usize>> =
                pma.leftmost_find_iter_experimental(test.haystack).collect();
            assert_eq!(
                test.matches,
                to_match_triples(matches).as_slice(),
                "test: {}, patterns: {:?}, haystack: {:?}",
                test.name,
                test.patterns,
                test.haystack
            );
        }
    }
}

#[test]
fn search_leftmost_first_experimental_charwise() {
    for &collection in AC_LEFTMOST_FIRST {
        for test in collection {
            let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
                .match_kind(MatchKind::LeftmostFirstExperimental)
                .build(test.patterns)
                .unwrap();
            let matches: Vec<Match<usize>> =
                pma.leftmost_find_iter_experimental(test.haystack).collect();
            assert_eq!(
                test.matches,
                to_match_triples(matches).as_slice(),
                "test: {}, patterns: {:?}, haystack: {:?}",
                test.name,
                test.patterns,
                test.haystack
            );
        }
    }
}

#[test]
fn test_experimental_empty_pattern_with_prefixes() {
    for match_kind in [
        MatchKind::LeftmostLongestExperimental,
        MatchKind::LeftmostFirstExperimental,
    ] {
        let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(match_kind)
            .build(["", "ab"])
            .unwrap();
        let matches = to_match_triples(pma.leftmost_find_iter_experimental(""));
        assert_eq!(matches, &[(0, 0, 0)]);

        let matches = to_match_triples(pma.leftmost_find_iter_experimental("a"));
        assert_eq!(matches, &[(0, 0, 0), (0, 1, 1)]);

        let matches = to_match_triples(pma.leftmost_find_iter_experimental("ab"));
        if match_kind == MatchKind::LeftmostLongestExperimental {
            assert_eq!(matches, &[(1, 0, 2)]);
        } else {
            assert_eq!(matches, &[(0, 0, 0), (0, 1, 1), (0, 2, 2)]);
        }

        let pma_rev = CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(match_kind)
            .build(["ab", ""])
            .unwrap();
        let matches = to_match_triples(pma_rev.leftmost_find_iter_experimental("ab"));
        assert_eq!(matches, &[(0, 0, 2)]);

        // 3-char prefix with mismatch halfway
        let pma_abc = CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(match_kind)
            .build(["", "abc"])
            .unwrap();
        let matches = to_match_triples(pma_abc.leftmost_find_iter_experimental("ab"));
        assert_eq!(matches, &[(0, 0, 0), (0, 1, 1), (0, 2, 2)]);

        // Multi-byte UTF-8 test
        let pma_utf8 = CharwiseDoubleArrayAhoCorasickBuilder::new()
            .match_kind(match_kind)
            .build(["", "你好"])
            .unwrap();
        let matches = to_match_triples(pma_utf8.leftmost_find_iter_experimental("你"));
        assert_eq!(matches, &[(0, 0, 0), (0, 3, 3)]);
    }
}

#[test]
fn test_experimental_regression_interleaved_fail_links() {
    let patterns = [
        "da", "dbacbc", "a", "bbdadd", "d", "dbc", "dbacbd", "bad", "cbac", "cc", "ddacad", "b",
    ];
    let haystack = "abbccdbdadbaacbcaacccbdbcbbcccdddbcabdbdbcbdbaaaaaabbddbaccabbddabbcabacaccabbccaddbbaadbbdadbcacbbcbcdabbaccdddbcacaccdccdacbbccbacaddbbcbbaacccacaacadcccbcccbbcdccaaacbcbcddddbabccbbbabbbdbdccdddcabdadbaaacadbdccadbbbdbbadcbaabaddaabddabcbbcbaadbbcdcdadadccccaadaabdddbacbbcdbbdcaabcbbcaaddbddcccbcccaddbdbbbaccdcabcccdbbdddddacbddacaddadcbdaabacdcabababbdbbadaaabbddcbadbbaaaabcccdcdadccddcabcdabbdbaacbaccabaccbbbaacbcdaadacbdbbddcdcacdcacdbbbdbbdddbacbdcccadabccbacaaadbccacbcccdbaacbcaabdabcbbbcdbccdcaadaadbbaddbaaddbcdbbabdbbbdabdabdbdcccccbbcadabaaddbdaadaaaacdddccddcbddcdbaaababdaaddacccbccddadadcdbdabdddccadcccccdcdbccbaabbabdacdabaccdbbbdccbcaaaabdcdacdbbbaadaacadaccbadcdcaddacbacbccbadccbbacbddcbbcbbbddccaabaacbbdccdadaddabdcbbcdcdadddaacacbbcddadbcbcdddcbaabcababbacdcdabbccacbddcbccdcbbcbacdcdaccba";

    let pma_legacy = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build::<_, _, usize>(patterns)
        .unwrap();
    let pma_experimental = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongestExperimental)
        .build::<_, _, usize>(patterns)
        .unwrap();

    let expected: Vec<_> = pma_legacy.leftmost_find_iter(haystack).collect();
    let actual: Vec<_> = pma_experimental
        .leftmost_find_iter_experimental(haystack)
        .collect();
    assert_eq!(expected, actual);
}

#[test]
fn test_experimental_parent_and_candidate_matches() {
    // Verifies that when an intermediate state on a long pattern branch (e.g. "xybacelong")
    // experiences candidate failure on transition 'e' (where suffix candidate "bac" breaks),
    // ancestor matches ("xy") and broken candidate matches ("b", "a") are correctly
    // spliced and preserved when matching text that diverges (e.g. "xybacex").
    let patterns = ["xy", "b", "a", "bacd", "xybacelong"];
    let haystack = "xybacex";

    let pma_legacy = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongest)
        .build::<_, _, usize>(patterns)
        .unwrap();
    let pma_experimental = CharwiseDoubleArrayAhoCorasickBuilder::new()
        .match_kind(MatchKind::LeftmostLongestExperimental)
        .build::<_, _, usize>(patterns)
        .unwrap();

    let expected: Vec<_> = pma_legacy.leftmost_find_iter(haystack).collect();
    let actual: Vec<_> = pma_experimental
        .leftmost_find_iter_experimental(haystack)
        .collect();
    assert_eq!(expected, actual);
}

#[test]
fn test_leftmost_finder_experimental_buffer_reuse() {
    let patterns_sets: &[&[&str]] = &[
        &["xy", "b", "a", "bacd", "xybacelong"],
        &["", "xy", "b", "a", "bacd", "xybacelong"],
    ];
    let haystacks = [
        "xybacex",
        "no match here",
        "b",
        "xybacelong",
        "xy and b and a",
    ];

    for patterns in patterns_sets {
        for match_kind in [
            MatchKind::LeftmostLongestExperimental,
            MatchKind::LeftmostFirstExperimental,
        ] {
            let pma = CharwiseDoubleArrayAhoCorasickBuilder::new()
                .match_kind(match_kind)
                .build::<_, _, usize>(*patterns)
                .unwrap();

            let mut finder = pma.leftmost_finder_experimental();
            for h in haystacks {
                let expected: Vec<_> = pma.leftmost_find_iter_experimental(h).collect();
                let actual: Vec<_> = finder.find_iter(h).collect();
                assert_eq!(expected, actual, "Mismatch on haystack: {h}");
            }

            // Test early termination leaving leftover matches in buffer:
            // "xybacex" yields multiple matches. Consuming only 1 leaves leftover matches buffered.
            let mut it = finder.find_iter("xybacex");
            assert!(it.next().is_some());
            #[allow(clippy::drop_non_drop)]
            drop(it);
            let actual: Vec<_> = finder.find_iter("b").collect();
            let expected: Vec<_> = pma.leftmost_find_iter_experimental("b").collect();
            assert_eq!(expected, actual);
        }
    }
}
