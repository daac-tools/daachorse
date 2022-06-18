use core::num::NonZeroU32;

use crate::*;

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
        NonZeroU32::new(4), // 0  (state=0)
        None,               // 1
        None,               // 2
        None,               // 3  (state=6)
        NonZeroU32::new(8), // 4  (state=1)
        NonZeroU32::new(1), // 5  (state=2)
        None,               // 6  (state=3)
        None,               // 7
        None,               // 8  (state=4)
        None,               // 9
        None,               // 10 (state=5)
    ];
    let check_expected = vec![
        0, // 0  (state=0)
        1, // 1
        2, // 2
        2, // 3  (state=6)
        0, // 4  (state=1)
        1, // 5  (state=2)
        2, // 6  (state=3)
        7, // 7
        0, // 8  (state=4)
        9, // 9
        2, // 10 (state=5)
    ];
    let fail_expected = vec![
        ROOT_STATE_IDX, // 0  (state=0)
        ROOT_STATE_IDX, // 1
        ROOT_STATE_IDX, // 2
        6,              // 3  (state=6)
        ROOT_STATE_IDX, // 4  (state=1)
        ROOT_STATE_IDX, // 5  (state=2)
        ROOT_STATE_IDX, // 6  (state=3)
        ROOT_STATE_IDX, // 7
        4,              // 8  (state=4)
        ROOT_STATE_IDX, // 9
        6,              // 10 (state=5)
    ];

    let pma_base: Vec<_> = pma.states[0..11].iter().map(|state| state.base()).collect();
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
fn test_input_order() {
    let patvals_sorted = vec![("ababa", 0), ("abba", 1), ("baaba", 2)];
    let patvals_unsorted = vec![("abba", 1), ("baaba", 2), ("ababa", 0)];

    let pma_sorted = DoubleArrayAhoCorasick::with_values(patvals_sorted).unwrap();
    let pma_unsorted = DoubleArrayAhoCorasick::with_values(patvals_unsorted).unwrap();

    assert_eq!(pma_sorted.states, pma_unsorted.states);
    assert_eq!(pma_sorted.outputs, pma_unsorted.outputs);
}
