use std::convert::TryFrom;
use std::fs::File;
use std::io::BufRead;
use std::io::BufReader;
use std::path::Path;

fn main() {
    {
        println!("== data/words_100 ==");
        let mut patterns = load_file("data/words_100");
        patterns.sort_unstable();
        show_memory_stats(&patterns);
    }
    {
        println!("== data/words_5000 ==");
        let mut patterns = load_file("data/words_5000");
        patterns.sort_unstable();
        show_memory_stats(&patterns);
    }
    {
        println!("== data/words_15000 ==");
        let mut patterns = load_file("data/words_15000");
        patterns.sort_unstable();
        show_memory_stats(&patterns);
    }
    {
        println!("== data/words_100000 ==");
        let mut patterns = load_file("data/words_100000");
        patterns.sort_unstable();
        show_memory_stats(&patterns);
    }
    {
        println!("== data/unidic/unidic ==");
        let mut patterns = load_file("data/unidic/unidic");
        patterns.sort_unstable();
        show_memory_stats(&patterns);
    }
}

fn show_memory_stats(patterns: &[String]) {
    {
        let pma = daachorse::DoubleArrayAhoCorasick::new(patterns).unwrap();
        format_memory("daachorse (bytewise)", pma.heap_bytes());
    }
    {
        let pma = daachorse::charwise::CharwiseDoubleArrayAhoCorasick::new(patterns).unwrap();
        format_memory("daachorse (charwise)", pma.heap_bytes());
    }
    {
        let pma = aho_corasick::AhoCorasick::new(patterns);
        format_memory("aho_corasick (nfa)", pma.heap_bytes());
    }
    {
        let pma = aho_corasick::AhoCorasickBuilder::new()
            .dfa(true)
            .build(patterns);
        format_memory("aho_corasick (dfa)", pma.heap_bytes());
    }
    {
        let fst = fst::raw::Fst::from_iter_map(
            patterns
                .iter()
                .cloned()
                .enumerate()
                .map(|(i, pattern)| (pattern, i as u64)),
        )
        .unwrap();
        format_memory("fst", fst.as_bytes().len());
    }
    {
        let data = yada::builder::DoubleArrayBuilder::build(
            &patterns
                .iter()
                .cloned()
                .enumerate()
                .map(|(i, pattern)| (pattern, u32::try_from(i).unwrap()))
                .collect::<Vec<_>>(),
        )
        .unwrap();
        format_memory("yada", data.len());
    }
}

fn format_memory(title: &str, bytes: usize) {
    println!(
        "{}: {} bytes, {:.3} MiB",
        title,
        bytes,
        bytes as f64 / (1024.0 * 1024.0)
    );
}

fn load_file<P>(path: P) -> Vec<String>
where
    P: AsRef<Path>,
{
    let file = File::open(path).unwrap();
    let buf = BufReader::new(file);
    buf.lines().map(Result::unwrap).collect()
}
