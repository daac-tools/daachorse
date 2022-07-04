//! Utilities for serializing/deserializing data.

use core::mem;
use core::num::NonZeroU32;

use alloc::vec::Vec;

use crate::utils::FromU32;

pub trait Serializable: Sized {
    fn serialize_to_vec(&self, dst: &mut Vec<u8>);

    fn deserialize_from_slice(src: &[u8]) -> (Self, &[u8]);

    fn serialized_bytes(&self) -> usize {
        mem::size_of::<Self>()
    }
}

impl Serializable for u32 {
    #[inline(always)]
    fn serialize_to_vec(&self, dst: &mut Vec<u8>) {
        dst.extend_from_slice(&self.to_le_bytes());
    }

    #[inline(always)]
    fn deserialize_from_slice(src: &[u8]) -> (Self, &[u8]) {
        // unwrap_unchecked is safe since a 4-byte slice is always converted.
        let x = unsafe { Self::from_le_bytes(src[..4].try_into().unwrap_unchecked()) };
        (x, &src[4..])
    }
}

impl Serializable for Option<NonZeroU32> {
    #[inline(always)]
    fn serialize_to_vec(&self, dst: &mut Vec<u8>) {
        self.map_or(0, NonZeroU32::get).serialize_to_vec(dst);
    }

    #[inline(always)]
    fn deserialize_from_slice(src: &[u8]) -> (Self, &[u8]) {
        let (x, src) = u32::deserialize_from_slice(src);
        (NonZeroU32::new(x), src)
    }
}

impl<S> Serializable for Vec<S>
where
    S: Serializable,
{
    #[inline(always)]
    fn serialize_to_vec(&self, dst: &mut Vec<u8>) {
        u32::try_from(self.len()).unwrap().serialize_to_vec(dst);
        self.iter().for_each(|x| x.serialize_to_vec(dst));
    }

    #[inline(always)]
    fn deserialize_from_slice(src: &[u8]) -> (Self, &[u8]) {
        let (len, mut src) = u32::deserialize_from_slice(src);
        let mut dst = Self::with_capacity(usize::from_u32(len));
        for _ in 0..len {
            let (x, rest) = S::deserialize_from_slice(src);
            dst.push(x);
            src = rest;
        }
        (dst, src)
    }

    fn serialized_bytes(&self) -> usize {
        mem::size_of::<u32>() + mem::size_of::<S>() * self.len()
    }
}
