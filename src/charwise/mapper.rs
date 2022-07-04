use alloc::vec::Vec;

use crate::utils::FromU32;

pub const INVALID_CODE: u32 = u32::MAX;

#[derive(Default, Clone, Debug, Eq, Hash, PartialEq)]
pub struct CodeMapper {
    table: Vec<u32>,
    alphabet_size: u32,
}

impl CodeMapper {
    pub fn new(freqs: &[u32]) -> Self {
        let sorted = {
            let mut sorted = vec![];
            for (c, &f) in freqs.iter().enumerate().filter(|(_, &f)| f != 0) {
                sorted.push((c, f));
            }
            // Note: `c1.cmp(c2)` is necessary to uniquely determine the sort result.
            sorted.sort_unstable_by(|(c1, f1), (c2, f2)| f2.cmp(f1).then_with(|| c1.cmp(c2)));
            sorted
        };
        let mut table = vec![INVALID_CODE; freqs.len()];
        for (i, &(c, _)) in sorted.iter().enumerate() {
            table[c] = u32::try_from(i).unwrap();
        }
        Self {
            table,
            alphabet_size: u32::try_from(sorted.len()).unwrap(),
        }
    }

    #[inline(always)]
    pub fn get(&self, c: char) -> Option<u32> {
        self.table
            .get(usize::from_u32(u32::from(c)))
            .copied()
            .filter(|&code| code != INVALID_CODE)
    }

    #[inline(always)]
    pub const fn alphabet_size(&self) -> u32 {
        self.alphabet_size
    }

    #[inline]
    #[allow(dead_code)]
    pub fn heap_bytes(&self) -> usize {
        self.table.len() * core::mem::size_of::<u32>()
    }

    pub fn serialized_bytes(&self) -> usize {
        core::mem::size_of::<u32>()
            + self.table.len() * core::mem::size_of::<u32>()
            + core::mem::size_of::<u32>() // alphabet_size
    }

    pub fn serialize(&self, result: &mut Vec<u8>) {
        result.extend_from_slice(&u32::try_from(self.table.len()).unwrap().to_le_bytes());
        for &x in &self.table {
            result.extend_from_slice(&x.to_le_bytes());
        }
        result.extend_from_slice(&self.alphabet_size.to_le_bytes());
    }

    pub unsafe fn deserialize_unchecked(mut source: &[u8]) -> (Self, &[u8]) {
        let len = usize::from_u32(u32::from_le_bytes(source[0..4].try_into().unwrap()));
        source = &source[4..];
        let mut table = Vec::with_capacity(len);
        for _ in 0..len {
            table.push(u32::from_le_bytes(source[0..4].try_into().unwrap()));
            source = &source[4..];
        }
        let alphabet_size = u32::from_le_bytes(source[0..4].try_into().unwrap());
        source = &source[4..];
        (
            Self {
                table,
                alphabet_size,
            },
            source,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
}
