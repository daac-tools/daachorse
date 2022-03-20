use std::fs::File;
use std::io::BufRead;
use std::io::BufReader;
use std::path::Path;
use std::time::Duration;

use criterion::{
    criterion_group, criterion_main, measurement::WallTime, BenchmarkGroup, Criterion, SamplingMode,
};

const BUILD_SAMPLE_SIZE: usize = 10;
const BUILD_WARM_UP_TIME: Duration = Duration::from_secs(5);
const BUILD_MEASURE_TIME: Duration = Duration::from_secs(30);

const SEARCH_SAMPLE_SIZE: usize = 30;
const SEARCH_WARM_UP_TIME: Duration = Duration::from_secs(5);
const SEARCH_MEASURE_TIME: Duration = Duration::from_secs(10);

fn criterion_words100000_build(c: &mut Criterion) {
    let mut group = c.benchmark_group("words_100000/build");
    group.sample_size(BUILD_SAMPLE_SIZE);
    group.warm_up_time(BUILD_WARM_UP_TIME);
    group.measurement_time(BUILD_MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);
    let mut patterns = load_file("data/words_100000");
    patterns.sort_unstable();

    add_build_benches(&mut group, &patterns);
}

fn criterion_unidic_build(c: &mut Criterion) {
    let mut group = c.benchmark_group("unidic/build");
    group.sample_size(BUILD_SAMPLE_SIZE);
    group.warm_up_time(BUILD_WARM_UP_TIME);
    group.measurement_time(BUILD_MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);
    let mut patterns = load_file("data/unidic/unidic");
    patterns.sort_unstable();

    add_build_benches(&mut group, &patterns);
}

fn criterion_unidic_find(c: &mut Criterion) {
    let mut group = c.benchmark_group("unidic/find");
    group.sample_size(SEARCH_SAMPLE_SIZE);
    group.warm_up_time(SEARCH_WARM_UP_TIME);
    group.measurement_time(SEARCH_MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);
    let mut patterns = load_file("data/unidic/unidic");
    patterns.sort_unstable();
    let haystacks = load_file("data/wagahaiwa_nekodearu.txt");

    add_find_benches(&mut group, &patterns, &haystacks);
}

fn criterion_words100000_find(c: &mut Criterion) {
    let mut group = c.benchmark_group("words_100000/find");
    group.sample_size(SEARCH_SAMPLE_SIZE);
    group.warm_up_time(SEARCH_WARM_UP_TIME);
    group.measurement_time(SEARCH_MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);
    let mut patterns = load_file("data/words_100000");
    patterns.sort_unstable();
    let haystacks = load_file("data/sherlock.txt");

    add_find_benches(&mut group, &patterns, &haystacks);
}

fn criterion_unidic_find_overlapping(c: &mut Criterion) {
    let mut group = c.benchmark_group("unidic/find_overlapping");
    group.sample_size(SEARCH_SAMPLE_SIZE);
    group.warm_up_time(SEARCH_WARM_UP_TIME);
    group.measurement_time(SEARCH_MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);
    let mut patterns = load_file("data/unidic/unidic");
    patterns.sort_unstable();
    let haystacks = load_file("data/wagahaiwa_nekodearu.txt");

    add_find_overlapping_benches(&mut group, &patterns, &haystacks);
}

fn criterion_words100000_find_overlapping(c: &mut Criterion) {
    let mut group = c.benchmark_group("words_100000/find_overlapping");
    group.sample_size(SEARCH_SAMPLE_SIZE);
    group.warm_up_time(SEARCH_WARM_UP_TIME);
    group.measurement_time(SEARCH_MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);
    let mut patterns = load_file("data/words_100000");
    patterns.sort_unstable();
    let haystacks = load_file("data/sherlock.txt");

    add_find_overlapping_benches(&mut group, &patterns, &haystacks);
}

fn criterion_unidic_leftmost_longest_find(c: &mut Criterion) {
    let mut group = c.benchmark_group("unidic/leftmost_longest_find");
    group.sample_size(SEARCH_SAMPLE_SIZE);
    group.warm_up_time(SEARCH_WARM_UP_TIME);
    group.measurement_time(SEARCH_MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);
    let mut patterns = load_file("data/unidic/unidic");
    patterns.sort_unstable();
    let haystacks = load_file("data/wagahaiwa_nekodearu.txt");

    add_leftmost_longest_find_benches(&mut group, &patterns, &haystacks);
}

fn criterion_words100000_leftmost_longest_find(c: &mut Criterion) {
    let mut group = c.benchmark_group("words_100000/leftmost_longest_find");
    group.sample_size(SEARCH_SAMPLE_SIZE);
    group.warm_up_time(SEARCH_WARM_UP_TIME);
    group.measurement_time(SEARCH_MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);
    let mut patterns = load_file("data/words_100000");
    patterns.sort_unstable();
    let haystacks = load_file("data/sherlock.txt");

    add_leftmost_longest_find_benches(&mut group, &patterns, &haystacks);
}

fn criterion_unidic_leftmost_first_find(c: &mut Criterion) {
    let mut group = c.benchmark_group("unidic/leftmost_first_find");
    group.sample_size(SEARCH_SAMPLE_SIZE);
    group.warm_up_time(SEARCH_WARM_UP_TIME);
    group.measurement_time(SEARCH_MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);
    let mut patterns = load_file("data/unidic/unidic");
    patterns.sort_unstable();
    let haystacks = load_file("data/wagahaiwa_nekodearu.txt");

    add_leftmost_first_find_benches(&mut group, &patterns, &haystacks);
}

fn criterion_words100000_leftmost_first_find(c: &mut Criterion) {
    let mut group = c.benchmark_group("words_100000/leftmost_first_find");
    group.sample_size(SEARCH_SAMPLE_SIZE);
    group.warm_up_time(SEARCH_WARM_UP_TIME);
    group.measurement_time(SEARCH_MEASURE_TIME);
    group.sampling_mode(SamplingMode::Flat);
    let mut patterns = load_file("data/words_100000");
    patterns.sort_unstable();
    let haystacks = load_file("data/sherlock.txt");

    add_leftmost_first_find_benches(&mut group, &patterns, &haystacks);
}

fn add_build_benches(group: &mut BenchmarkGroup<WallTime>, patterns: &[String]) {
    group.bench_function("daachorse", |b| {
        b.iter(|| daachorse::DoubleArrayAhoCorasick::new(patterns).unwrap());
    });

    group.bench_function("daachorse/charwise", |b| {
        b.iter(|| daachorse::charwise::CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap());
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
        let pma = daachorse::DoubleArrayAhoCorasick::new(patterns).unwrap();
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
        let pma = daachorse::charwise::CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
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
        let pma = daachorse::DoubleArrayAhoCorasick::new(patterns).unwrap();
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
        let pma = daachorse::DoubleArrayAhoCorasick::new(patterns).unwrap();
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
        let pma = daachorse::charwise::CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
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
        let pma = daachorse::charwise::CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
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

fn add_leftmost_longest_find_benches(
    group: &mut BenchmarkGroup<WallTime>,
    patterns: &[String],
    haystacks: &[String],
) {
    group.bench_function("daachorse", |b| {
        let pma = daachorse::DoubleArrayAhoCorasickBuilder::new()
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
        let pma = daachorse::charwise::CharwiseDoubleArrayAhoCorasickBuilder::new()
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

fn add_leftmost_first_find_benches(
    group: &mut BenchmarkGroup<WallTime>,
    patterns: &[String],
    haystacks: &[String],
) {
    group.bench_function("daachorse", |b| {
        let pma = daachorse::DoubleArrayAhoCorasickBuilder::new()
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
        let pma = daachorse::charwise::CharwiseDoubleArrayAhoCorasickBuilder::new()
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
    criterion_unidic_leftmost_longest_find,
    criterion_unidic_leftmost_first_find,
    criterion_unidic_build,
    criterion_words100000_find,
    criterion_words100000_find_overlapping,
    criterion_words100000_leftmost_longest_find,
    criterion_words100000_leftmost_first_find,
    criterion_words100000_build,
);
criterion_main!(benches);
