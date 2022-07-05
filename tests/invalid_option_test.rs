use daachorse::{DoubleArrayAhoCorasick, DoubleArrayAhoCorasickBuilder};

#[test]
fn test_large_num_free_blocks() {
    let pma: Result<DoubleArrayAhoCorasick<usize>, _> = DoubleArrayAhoCorasickBuilder::new()
        .num_free_blocks(u32::MAX)
        .build(["pattern"]);
    assert!(pma.is_err());
}
