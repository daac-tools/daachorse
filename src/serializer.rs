//! Utilities for serializing/deserializing data.

use core::mem;
use core::num::NonZeroU32;

use alloc::vec::Vec;

pub trait Serialize {
    fn to_vec(&self, dst: &mut Vec<u8>);
}

pub trait Deserialize: Sized {
    fn from_slice(src: &[u8]) -> (Self, &[u8]);
}

impl Serialize for u32 {
    #[inline(always)]
    fn to_vec(&self, dst: &mut Vec<u8>) {
        dst.extend_from_slice(&self.to_le_bytes());
    }
}

impl Deserialize for u32 {
    #[inline(always)]
    fn from_slice(src: &[u8]) -> (Self, &[u8]) {
        // unwrap_unchecked is safe since a 4-byte slice is always converted.
        let x = unsafe { Self::from_le_bytes(src[..4].try_into().unwrap_unchecked()) };
        (x, &src[4..])
    }
}

impl Serialize for Option<NonZeroU32> {
    #[inline(always)]
    fn to_vec(&self, dst: &mut Vec<u8>) {
        self.map_or(0, NonZeroU32::get).to_vec(dst);
    }
}

impl Deserialize for Option<NonZeroU32> {
    #[inline(always)]
    fn from_slice(src: &[u8]) -> (Self, &[u8]) {
        let (x, src) = u32::from_slice(src);
        (NonZeroU32::new(x), src)
    }
}

pub fn serialize_slice<S>(src: &[S], dst: &mut Vec<u8>)
where
    S: Serialize,
{
    u32::try_from(src.len()).unwrap().to_vec(dst);
    src.iter().for_each(|x| x.to_vec(dst));
}

pub fn deserialize_vec<D>(src: &[u8]) -> (Vec<D>, &[u8])
where
    D: Deserialize,
{
    let (len, mut src) = u32::from_slice(src);
    let mut dst = Vec::with_capacity(usize::try_from(len).unwrap());
    for _ in 0..len {
        let (x, rest) = D::from_slice(src);
        dst.push(x);
        src = rest;
    }
    (dst, src)
}

// Note: Trait bounds other than `Sized` on const fn parameters are unstable
// when a version is smaller than Rust 1.61, nevertheless clippy requires the const marker.
// https://blog.rust-lang.org/2022/05/19/Rust-1.61.0.html#more-capabilities-for-const-fn
#[allow(clippy::missing_const_for_fn)]
pub fn serialized_bytes<S>(src: &[S]) -> usize
where
    S: Serialize,
{
    mem::size_of::<u32>() + mem::size_of::<S>() * src.len()
}
