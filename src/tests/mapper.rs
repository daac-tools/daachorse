use crate::charwise::mapper::CodeMapper;

#[test]
fn test_charwise_code_mapper() {
    let freqs = vec![3, 6, 0, 2, 3, 0, 3];
    let mapper = CodeMapper::new(&freqs);

    assert_eq!(mapper.get(0 as char), Some(1));
    assert_eq!(mapper.get(1 as char), Some(0));
    assert_eq!(mapper.get(2 as char), None);
    assert_eq!(mapper.get(3 as char), Some(4));
    assert_eq!(mapper.get(4 as char), Some(2));
    assert_eq!(mapper.get(5 as char), None);
    assert_eq!(mapper.get(6 as char), Some(3));
    assert_eq!(mapper.get(7 as char), None); // out-of-range
}
