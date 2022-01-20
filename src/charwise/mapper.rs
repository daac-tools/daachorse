/// Trait for mapping characters to identifiers.
pub trait Mapper {
    /// Gets the identifier of a given character (if exists).
    fn get(&self, c: char) -> Option<u32>;

    /// Returns the total amount of heap used by this mapper in bytes.
    fn heap_bytes(&self) -> usize;
}

/// Mapper that directly uses code point values as identifiers.
///
/// # Examples
///
/// ```
/// use daachorse::charwise::{Mapper, NoMapper};
///
/// let mapper = NoMapper::default();
///
/// assert_eq!(mapper.get('a'), Some('a' as u32));
/// assert_eq!(mapper.get('あ'), Some('あ' as u32));
/// assert_eq!(mapper.get('亜'), Some('亜' as u32));
///
/// assert_eq!(mapper.heap_bytes(), 0);
/// ```
#[derive(Clone, Default)]
pub struct NoMapper {}

impl Mapper for NoMapper {
    fn get(&self, c: char) -> Option<u32> {
        Some(c as u32)
    }

    fn heap_bytes(&self) -> usize {
        0
    }
}
