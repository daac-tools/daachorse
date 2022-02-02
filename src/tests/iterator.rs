use crate::charwise::iter::CharWithEndOffsetIterator;

#[test]
fn test_char_with_end_offset_iterator() {
    let test_string = "\u{0000}\u{0001}\u{0002}\u{0004}\u{0008}\u{0010}\u{001f}\u{0020}\u{0040}\
                       \u{007f}\u{0080}\u{0100}\u{01ff}\u{0200}\u{0400}\u{07ff}\u{0800}\u{1000}\
                       \u{1fff}\u{2000}\u{4000}\u{8000}\u{ffff}\u{10000}\u{1ffff}\u{20000}\u{40000}\
                       \u{80000}\u{100000}\u{10ffff}";
    let mut it = unsafe { CharWithEndOffsetIterator::new(test_string.as_bytes().iter().copied()) };

    // 1 byte
    assert_eq!(Some((1, '\u{0000}')), it.next());
    assert_eq!(Some((2, '\u{0001}')), it.next());
    assert_eq!(Some((3, '\u{0002}')), it.next());
    assert_eq!(Some((4, '\u{0004}')), it.next());
    assert_eq!(Some((5, '\u{0008}')), it.next());
    assert_eq!(Some((6, '\u{0010}')), it.next());
    assert_eq!(Some((7, '\u{001f}')), it.next());
    assert_eq!(Some((8, '\u{0020}')), it.next());
    assert_eq!(Some((9, '\u{0040}')), it.next());
    assert_eq!(Some((10, '\u{007f}')), it.next());

    // 2 bytes
    assert_eq!(Some((12, '\u{0080}')), it.next());
    assert_eq!(Some((14, '\u{0100}')), it.next());
    assert_eq!(Some((16, '\u{01ff}')), it.next());
    assert_eq!(Some((18, '\u{0200}')), it.next());
    assert_eq!(Some((20, '\u{0400}')), it.next());
    assert_eq!(Some((22, '\u{07ff}')), it.next());

    // 3 bytes
    assert_eq!(Some((25, '\u{0800}')), it.next());
    assert_eq!(Some((28, '\u{1000}')), it.next());
    assert_eq!(Some((31, '\u{1fff}')), it.next());
    assert_eq!(Some((34, '\u{2000}')), it.next());
    assert_eq!(Some((37, '\u{4000}')), it.next());
    assert_eq!(Some((40, '\u{8000}')), it.next());
    assert_eq!(Some((43, '\u{ffff}')), it.next());

    // 4 bytes
    assert_eq!(Some((47, '\u{10000}')), it.next());
    assert_eq!(Some((51, '\u{1ffff}')), it.next());
    assert_eq!(Some((55, '\u{20000}')), it.next());
    assert_eq!(Some((59, '\u{40000}')), it.next());
    assert_eq!(Some((63, '\u{80000}')), it.next());
    assert_eq!(Some((67, '\u{100000}')), it.next());
    assert_eq!(Some((71, '\u{10ffff}')), it.next());

    // end of iterator
    assert_eq!(None, it.next());
    assert_eq!(None, it.next());
}
