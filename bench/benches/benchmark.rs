use std::fs::File;
use std::io::BufRead;
use std::io::BufReader;
use std::path::Path;
use std::time::Duration;

use criterion::{
    criterion_group, criterion_main, measurement::WallTime, BenchmarkGroup, Criterion, SamplingMode,
};

const BUILD_SAMPLE_SIZE: usize = 10;
const BUILD_WARM_UP_TIME: Duration = Duration::from_millis(500);
const BUILD_MEASURE_TIME: Duration = Duration::from_secs(2);

const SEARCH_SAMPLE_SIZE: usize = 30;
const SEARCH_WARM_UP_TIME: Duration = Duration::from_millis(500);
const SEARCH_MEASURE_TIME: Duration = Duration::from_secs(2);

macro_rules! define_build_bench {
    ( $func_name:ident, $group:literal, $corpus:literal ) => {
        fn $func_name(c: &mut Criterion) {
            let mut group = c.benchmark_group($group);
            group.sample_size(BUILD_SAMPLE_SIZE);
            group.warm_up_time(BUILD_WARM_UP_TIME);
            group.measurement_time(BUILD_MEASURE_TIME);
            group.sampling_mode(SamplingMode::Flat);
            let mut patterns = load_file($corpus);
            patterns.sort_unstable();
            add_build_benches(&mut group, &patterns);
        }
    };
}

macro_rules! define_find_bench {
    ( $func_name:ident, $bench:ident, $group:literal, $corpus:literal, $haystack:literal ) => {
        fn $func_name(c: &mut Criterion) {
            let mut group = c.benchmark_group($group);
            group.sample_size(SEARCH_SAMPLE_SIZE);
            group.warm_up_time(SEARCH_WARM_UP_TIME);
            group.measurement_time(SEARCH_MEASURE_TIME);
            group.sampling_mode(SamplingMode::Flat);
            let mut patterns = load_file($corpus);
            patterns.sort_unstable();
            let haystacks = load_file($haystack);
            $bench(&mut group, &patterns, &haystacks);
        }
    };
}

define_build_bench!(criterion_unidic_build, "unidic/build", "data/unidic/unidic");
define_build_bench!(
    criterion_words_100_build,
    "words_100/build",
    "data/words_100"
);
define_build_bench!(
    criterion_words_5000_build,
    "words_5000/build",
    "data/words_5000"
);
define_build_bench!(
    criterion_words_15000_build,
    "words_15000/build",
    "data/words_15000"
);
define_build_bench!(
    criterion_words_100000_build,
    "words_100000/build",
    "data/words_100000"
);

define_find_bench!(
    criterion_unidic_find,
    add_find_benches,
    "unidic/find",
    "data/unidic/unidic",
    "data/wagahaiwa_nekodearu.txt"
);
define_find_bench!(
    criterion_words_100_find,
    add_find_benches,
    "words_100/find",
    "data/words_100",
    "data/sherlock.txt"
);
define_find_bench!(
    criterion_words_5000_find,
    add_find_benches,
    "words_5000/find",
    "data/words_5000",
    "data/sherlock.txt"
);
define_find_bench!(
    criterion_words_15000_find,
    add_find_benches,
    "words_15000/find",
    "data/words_15000",
    "data/sherlock.txt"
);
define_find_bench!(
    criterion_words_100000_find,
    add_find_benches,
    "words_100000/find",
    "data/words_100000",
    "data/sherlock.txt"
);

define_find_bench!(
    criterion_unidic_find_overlapping,
    add_find_overlapping_benches,
    "unidic/find_overlapping",
    "data/unidic/unidic",
    "data/wagahaiwa_nekodearu.txt"
);
define_find_bench!(
    criterion_words_100_find_overlapping,
    add_find_overlapping_benches,
    "words_100/find_overlapping",
    "data/words_100",
    "data/sherlock.txt"
);
define_find_bench!(
    criterion_words_5000_find_overlapping,
    add_find_overlapping_benches,
    "words_5000/find_overlapping",
    "data/words_5000",
    "data/sherlock.txt"
);
define_find_bench!(
    criterion_words_15000_find_overlapping,
    add_find_overlapping_benches,
    "words_15000/find_overlapping",
    "data/words_15000",
    "data/sherlock.txt"
);
define_find_bench!(
    criterion_words_100000_find_overlapping,
    add_find_overlapping_benches,
    "words_100000/find_overlapping",
    "data/words_100000",
    "data/sherlock.txt"
);

define_find_bench!(
    criterion_unidic_find_leftmost_longest,
    add_find_leftmost_longest_benches,
    "unidic/find_leftmost_longest",
    "data/unidic/unidic",
    "data/wagahaiwa_nekodearu.txt"
);
define_find_bench!(
    criterion_words_100_find_leftmost_longest,
    add_find_leftmost_longest_benches,
    "words_100/find_leftmost_longest",
    "data/words_100",
    "data/sherlock.txt"
);
define_find_bench!(
    criterion_words_5000_find_leftmost_longest,
    add_find_leftmost_longest_benches,
    "words_5000/find_leftmost_longest",
    "data/words_5000",
    "data/sherlock.txt"
);
define_find_bench!(
    criterion_words_15000_find_leftmost_longest,
    add_find_leftmost_longest_benches,
    "words_15000/find_leftmost_longest",
    "data/words_15000",
    "data/sherlock.txt"
);
define_find_bench!(
    criterion_words_100000_find_leftmost_longest,
    add_find_leftmost_longest_benches,
    "words_100000/find_leftmost_longest",
    "data/words_100000",
    "data/sherlock.txt"
);

define_find_bench!(
    criterion_unidic_find_leftmost_first,
    add_find_leftmost_first_benches,
    "unidic/find_leftmost_first",
    "data/unidic/unidic",
    "data/wagahaiwa_nekodearu.txt"
);
define_find_bench!(
    criterion_words_100_find_leftmost_first,
    add_find_leftmost_first_benches,
    "words_100/find_leftmost_first",
    "data/words_100",
    "data/sherlock.txt"
);
define_find_bench!(
    criterion_words_5000_find_leftmost_first,
    add_find_leftmost_first_benches,
    "words_5000/find_leftmost_first",
    "data/words_5000",
    "data/sherlock.txt"
);
define_find_bench!(
    criterion_words_15000_find_leftmost_first,
    add_find_leftmost_first_benches,
    "words_15000/find_leftmost_first",
    "data/words_15000",
    "data/sherlock.txt"
);
define_find_bench!(
    criterion_words_100000_find_leftmost_first,
    add_find_leftmost_first_benches,
    "words_100000/find_leftmost_first",
    "data/words_100000",
    "data/sherlock.txt"
);

fn add_build_benches(group: &mut BenchmarkGroup<WallTime>, patterns: &[String]) {
    group.bench_function("daachorse", |b| {
        b.iter(|| daachorse::DoubleArrayAhoCorasick::<usize>::new(patterns).unwrap());
    });

    group.bench_function("daachorse/charwise", |b| {
        b.iter(|| {
            daachorse::charwise::CharwiseDoubleArrayAhoCorasick::<usize>::new(patterns).unwrap()
        });
    });

    group.bench_function("aho_corasick/nfa", |b| {
        b.iter(|| aho_corasick::AhoCorasick::new(patterns));
    });

    group.bench_function("aho_corasick/dfa", |b| {
        b.iter(|| {
            aho_corasick::AhoCorasickBuilder::new()
                .dfa(true)
                .build(patterns)
        });
    });

    group.bench_function("yada", |b| {
        b.iter(|| {
            yada::builder::DoubleArrayBuilder::build(
                &patterns
                    .iter()
                    .cloned()
                    .enumerate()
                    .map(|(i, pattern)| (pattern, i.try_into().unwrap()))
                    .collect::<Vec<_>>(),
            )
            .unwrap()
        });
    });

    group.bench_function("fst/map", |b| {
        b.iter(|| {
            fst::raw::Fst::from_iter_map(
                patterns
                    .iter()
                    .cloned()
                    .enumerate()
                    .map(|(i, pattern)| (pattern, i.try_into().unwrap())),
            )
            .unwrap()
        });
    });
}

fn add_find_benches(
    group: &mut BenchmarkGroup<WallTime>,
    patterns: &[String],
    haystacks: &[String],
) {
    group.bench_function("daachorse", |b| {
        let pma = daachorse::DoubleArrayAhoCorasick::<usize>::new(patterns).unwrap();
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                for m in pma.find_iter(haystack) {
                    sum += m.start() + m.end() + m.value();
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });

    group.bench_function("daachorse/charwise", |b| {
        let pma =
            daachorse::charwise::CharwiseDoubleArrayAhoCorasick::<usize>::new(patterns).unwrap();
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                for m in pma.find_iter(haystack) {
                    sum += m.start() + m.end() + m.value();
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });

    group.bench_function("aho_corasick/nfa", |b| {
        let pma = aho_corasick::AhoCorasick::new(patterns);
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                for m in pma.find_iter(haystack) {
                    sum += m.start() + m.end() + m.pattern();
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });

    group.bench_function("aho_corasick/dfa", |b| {
        let pma = aho_corasick::AhoCorasickBuilder::new()
            .dfa(true)
            .build(patterns);
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                for m in pma.find_iter(haystack) {
                    sum += m.start() + m.end() + m.pattern();
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });
}

fn add_find_overlapping_benches(
    group: &mut BenchmarkGroup<WallTime>,
    patterns: &[String],
    haystacks: &[String],
) {
    group.bench_function("daachorse", |b| {
        let pma = daachorse::DoubleArrayAhoCorasick::<usize>::new(patterns).unwrap();
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                for m in pma.find_overlapping_iter(haystack) {
                    sum += m.start() + m.end() + m.value();
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });

    group.bench_function("daachorse/no_suffix", |b| {
        let pma = daachorse::DoubleArrayAhoCorasick::<usize>::new(patterns).unwrap();
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                for m in pma.find_overlapping_no_suffix_iter(haystack) {
                    sum += m.start() + m.end() + m.value();
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });

    group.bench_function("daachorse/charwise", |b| {
        let pma =
            daachorse::charwise::CharwiseDoubleArrayAhoCorasick::<usize>::new(patterns).unwrap();
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                for m in pma.find_overlapping_iter(haystack) {
                    sum += m.start() + m.end() + m.value();
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });

    group.bench_function("daachorse/charwise/no_suffix", |b| {
        let pma =
            daachorse::charwise::CharwiseDoubleArrayAhoCorasick::<usize>::new(patterns).unwrap();
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                for m in pma.find_overlapping_no_suffix_iter(haystack) {
                    sum += m.start() + m.end() + m.value();
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });

    group.bench_function("aho_corasick/nfa", |b| {
        let pma = aho_corasick::AhoCorasick::new(patterns);
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                for m in pma.find_overlapping_iter(haystack) {
                    sum += m.start() + m.end() + m.pattern();
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });

    group.bench_function("aho_corasick/dfa", |b| {
        let pma = aho_corasick::AhoCorasickBuilder::new()
            .dfa(true)
            .build(patterns);
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                for m in pma.find_overlapping_iter(haystack) {
                    sum += m.start() + m.end() + m.pattern();
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });

    group.bench_function("yada", |b| {
        let data = yada::builder::DoubleArrayBuilder::build(
            &patterns
                .iter()
                .cloned()
                .enumerate()
                .map(|(i, pattern)| (pattern, i as u32))
                .collect::<Vec<_>>(),
        )
        .unwrap();
        let da = yada::DoubleArray::new(data);
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                let haystack_bytes = haystack.as_bytes();
                for i in 0..haystack_bytes.len() {
                    for (id, length) in da.common_prefix_search(&haystack_bytes[i..]) {
                        sum += i + length + id as usize;
                    }
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });

    group.bench_function("fst/map", |b| {
        let fst = fst::raw::Fst::from_iter_map(
            patterns
                .iter()
                .cloned()
                .enumerate()
                .map(|(i, pattern)| (pattern, i as u64)),
        )
        .unwrap();
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                let haystack_bytes = haystack.as_bytes();
                for i in 0..haystack_bytes.len() {
                    for (id, length) in fst_common_prefix_search(&fst, &haystack_bytes[i..]) {
                        sum += i + length as usize + id as usize;
                    }
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });
}

fn add_find_leftmost_longest_benches(
    group: &mut BenchmarkGroup<WallTime>,
    patterns: &[String],
    haystacks: &[String],
) {
    group.bench_function("daachorse", |b| {
        let pma: daachorse::DoubleArrayAhoCorasick<usize> =
            daachorse::DoubleArrayAhoCorasickBuilder::new()
                .match_kind(daachorse::MatchKind::LeftmostLongest)
                .build(patterns)
                .unwrap();
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                for m in pma.leftmost_find_iter(haystack) {
                    sum += m.start() + m.end() + m.value();
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });

    group.bench_function("daachorse/charwise", |b| {
        let pma: daachorse::CharwiseDoubleArrayAhoCorasick<usize> =
            daachorse::charwise::CharwiseDoubleArrayAhoCorasickBuilder::new()
                .match_kind(daachorse::MatchKind::LeftmostLongest)
                .build(patterns)
                .unwrap();
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                for m in pma.leftmost_find_iter(haystack) {
                    sum += m.start() + m.end() + m.value();
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });

    group.bench_function("aho_corasick/nfa", |b| {
        let pma = aho_corasick::AhoCorasickBuilder::new()
            .match_kind(aho_corasick::MatchKind::LeftmostLongest)
            .build(patterns);
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                for m in pma.find_iter(haystack) {
                    sum += m.start() + m.end() + m.pattern();
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });

    group.bench_function("aho_corasick/dfa", |b| {
        let pma = aho_corasick::AhoCorasickBuilder::new()
            .dfa(true)
            .match_kind(aho_corasick::MatchKind::LeftmostLongest)
            .build(patterns);
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                for m in pma.find_iter(haystack) {
                    sum += m.start() + m.end() + m.pattern();
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });
}

fn add_find_leftmost_first_benches(
    group: &mut BenchmarkGroup<WallTime>,
    patterns: &[String],
    haystacks: &[String],
) {
    group.bench_function("daachorse", |b| {
        let pma: daachorse::DoubleArrayAhoCorasick<usize> =
            daachorse::DoubleArrayAhoCorasickBuilder::new()
                .match_kind(daachorse::MatchKind::LeftmostFirst)
                .build(patterns)
                .unwrap();
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                for m in pma.leftmost_find_iter(haystack) {
                    sum += m.start() + m.end() + m.value();
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });

    group.bench_function("daachorse/charwise", |b| {
        let pma: daachorse::CharwiseDoubleArrayAhoCorasick<usize> =
            daachorse::charwise::CharwiseDoubleArrayAhoCorasickBuilder::new()
                .match_kind(daachorse::MatchKind::LeftmostFirst)
                .build(patterns)
                .unwrap();
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                for m in pma.leftmost_find_iter(haystack) {
                    sum += m.start() + m.end() + m.value();
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });

    group.bench_function("aho_corasick/nfa", |b| {
        let pma = aho_corasick::AhoCorasickBuilder::new()
            .match_kind(aho_corasick::MatchKind::LeftmostFirst)
            .build(patterns);
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                for m in pma.find_iter(haystack) {
                    sum += m.start() + m.end() + m.pattern();
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });

    group.bench_function("aho_corasick/dfa", |b| {
        let pma = aho_corasick::AhoCorasickBuilder::new()
            .dfa(true)
            .match_kind(aho_corasick::MatchKind::LeftmostFirst)
            .build(patterns);
        b.iter(|| {
            let mut sum = 0;
            for haystack in haystacks {
                for m in pma.find_iter(haystack) {
                    sum += m.start() + m.end() + m.pattern();
                }
            }
            if sum == 0 {
                panic!();
            }
        });
    });
}

fn load_file<P>(path: P) -> Vec<String>
where
    P: AsRef<Path>,
{
    let file = File::open(path).unwrap();
    let buf = BufReader::new(file);
    buf.lines().map(|line| line.unwrap()).collect()
}

fn fst_common_prefix_search<'a>(
    fst: &'a fst::raw::Fst<Vec<u8>>,
    s: &'a [u8],
) -> impl Iterator<Item = (u64, u64)> + 'a {
    s.iter()
        .scan(
            (0, fst.root(), fst::raw::Output::zero()),
            move |(pattern_len, node, output), &byte| {
                if let Some(b_index) = node.find_input(byte) {
                    let transition = node.transition(b_index);
                    *pattern_len += 1;
                    *output = output.cat(transition.out);
                    *node = fst.node(transition.addr);
                    return Some((node.is_final(), *pattern_len, output.value()));
                }
                None
            },
        )
        .filter_map(|(is_final, pattern_len, pattern_id)| {
            if is_final {
                Some((pattern_id, pattern_len))
            } else {
                None
            }
        })
}

criterion_group!(
    benches,
    criterion_unidic_find,
    criterion_unidic_find_overlapping,
    criterion_unidic_find_leftmost_longest,
    criterion_unidic_find_leftmost_first,
    criterion_words_100_find,
    criterion_words_100_find_overlapping,
    criterion_words_100_find_leftmost_longest,
    criterion_words_100_find_leftmost_first,
    criterion_words_5000_find,
    criterion_words_5000_find_overlapping,
    criterion_words_5000_find_leftmost_longest,
    criterion_words_5000_find_leftmost_first,
    criterion_words_15000_find,
    criterion_words_15000_find_overlapping,
    criterion_words_15000_find_leftmost_longest,
    criterion_words_15000_find_leftmost_first,
    criterion_words_100000_find,
    criterion_words_100000_find_overlapping,
    criterion_words_100000_find_leftmost_longest,
    criterion_words_100000_find_leftmost_first,
    criterion_unidic_build,
    criterion_words_100_build,
    criterion_words_5000_build,
    criterion_words_15000_build,
    criterion_words_100000_build,
);
criterion_main!(benches);
