#[cfg(feature = "std")]
use std::io::{self, Read, Write};

use alloc::vec::Vec;

use core::mem;

const INVALID_CODE: u32 = 0xFFFFFFFF;

#[derive(Clone)]
pub struct CodeMapper {
    table: Vec<u32>,
}

impl CodeMapper {
    pub const fn new() -> Self {
        Self { table: vec![] }
    }

    pub fn build(freqs: &[u32]) -> Self {
        let sorted = {
            let mut sorted = vec![];
            for (c, &f) in freqs.iter().enumerate().filter(|(_, &f)| f != 0) {
                sorted.push((c, f));
            }
            sorted.sort_unstable_by(|(c1, f1), (c2, f2)| f2.cmp(f1).then_with(|| c1.cmp(c2)));
            sorted
        };
        let mut table = vec![INVALID_CODE; freqs.len()];
        for (i, &(c, _)) in sorted.iter().enumerate() {
            table[c] = i as u32;
        }
        Self { table }
    }

    #[inline(always)]
    pub fn get(&self, c: char) -> Option<u32> {
        if let Some(&code) = self.table.get(c as usize) {
            if code != INVALID_CODE {
                return Some(code);
            }
        }
        None
    }

    pub fn heap_bytes(&self) -> usize {
        self.table.len() * mem::size_of::<u32>()
    }

    pub fn serialized_bytes(&self) -> usize {
        self.table.len() * mem::size_of::<u32>() + mem::size_of::<u32>()
    }

    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    pub fn serialize<W>(&self, mut wtr: W) -> io::Result<()>
    where
        W: Write,
    {
        wtr.write_all(&u32::try_from(self.table.len()).unwrap().to_le_bytes())?;
        for x in &self.table {
            wtr.write_all(&x.to_le_bytes())?;
        }
        Ok(())
    }

    pub fn serialize_into_vec(&self, result: &mut Vec<u8>) {
        result.extend_from_slice(&u32::try_from(self.table.len()).unwrap().to_le_bytes());
        for x in &self.table {
            result.extend_from_slice(&x.to_le_bytes());
        }
    }

    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    pub unsafe fn deserialize_unchecked<R>(mut rdr: R) -> io::Result<Self>
    where
        R: Read,
    {
        let mut len_array = [0; 4];
        rdr.read_exact(&mut len_array)?;
        let table_len = u32::from_le_bytes(len_array) as usize;
        let mut table = Vec::with_capacity(table_len);
        for _ in 0..table_len {
            let mut code_array = [0; 4];
            rdr.read_exact(&mut code_array)?;
            table.push(u32::from_le_bytes(code_array));
        }
        Ok(Self { table })
    }

    pub unsafe fn deserialize_from_slice_unchecked(mut source: &[u8]) -> (Self, &[u8]) {
        let table_len = u32::from_le_bytes(source[0..4].try_into().unwrap()) as usize;
        source = &source[4..];
        let mut table = Vec::with_capacity(table_len);
        for _ in 0..table_len {
            table.push(u32::from_le_bytes(source[0..4].try_into().unwrap()));
            source = &source[4..];
        }
        (Self { table }, source)
    }
}
