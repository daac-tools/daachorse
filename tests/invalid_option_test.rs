use daachorse::DoubleArrayAhoCorasickBuilder;

#[test]
fn test_large_num_free_blocks() {
    assert!(DoubleArrayAhoCorasickBuilder::new()
        .num_free_blocks(u32::MAX)
        .build(["pattern"])
        .is_err());
}
