/// Trait for mapping characters to identifiers.
pub trait Mapper {
    /// Builds a new [`Mapper`] from a sequence of pairs
    /// of a character and the friquency.
    fn build(freqs: Vec<(char, u32)>) -> Self;

    /// Gets the identifier of a given character (if exists).
    fn get(&self, c: char) -> Option<u32>;

    /// Returns the total amount of heap used by this mapper in bytes.
    fn heap_bytes(&self) -> usize;
}
