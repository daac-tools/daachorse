use std::collections::HashMap;
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

fn add_build_benches(group: &mut BenchmarkGroup<WallTime>, patterns: &[String]) {
    group.bench_function("daachorse", |b| {
        b.iter(|| daachorse::DoubleArrayAhoCorasick::new(patterns).unwrap());
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
                    sum += m.start() + m.end() + m.pattern();
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
                    sum += m.start() + m.end() + m.pattern();
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
                    sum += m.start() + m.end() + m.pattern();
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
}

fn load_file<P>(path: P) -> Vec<String>
where
    P: AsRef<Path>,
{
    let file = File::open(path).unwrap();
    let buf = BufReader::new(file);
    buf.lines().map(|line| line.unwrap()).collect()
}

criterion_group!(
    benches,
    criterion_unidic_find,
    criterion_unidic_find_overlapping,
    criterion_words100000_find,
    criterion_words100000_find_overlapping,
    criterion_words100000_build,
);
criterion_main!(benches);
