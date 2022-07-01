//! Utilities for serializing/deserializing data.

use core::num::NonZeroU32;

use alloc::vec::Vec;

#[cfg(feature = "std")]
use std::io::{self, Read, Write};

pub trait Serialize {
    #[cfg(feature = "std")]
    fn to_writer<W>(&self, wtr: W) -> io::Result<()>
    where
        W: Write;

    fn to_vec(&self, dst: &mut Vec<u8>);
}

pub trait Deserialize {
    #[cfg(feature = "std")]
    unsafe fn from_reader<R>(rdr: R) -> io::Result<Self>
    where
        R: Read,
        Self: core::marker::Sized;

    unsafe fn from_slice(src: &[u8]) -> (Self, &[u8])
    where
        Self: core::marker::Sized;
}

impl Serialize for u32 {
    #[cfg(feature = "std")]
    fn to_writer<W>(&self, mut wtr: W) -> io::Result<()>
    where
        W: Write,
    {
        wtr.write_all(&self.to_le_bytes())
    }

    fn to_vec(&self, dst: &mut Vec<u8>) {
        dst.extend_from_slice(&self.to_le_bytes());
    }
}

impl Deserialize for u32 {
    #[cfg(feature = "std")]
    unsafe fn from_reader<R>(mut rdr: R) -> io::Result<Self>
    where
        R: Read,
    {
        let mut buf = [0; 4];
        rdr.read_exact(&mut buf)?;
        Ok(u32::from_le_bytes(buf))
    }

    unsafe fn from_slice(src: &[u8]) -> (Self, &[u8]) {
        (u32::from_le_bytes(src[..4].try_into().unwrap()), &src[4..])
    }
}

impl Serialize for Option<NonZeroU32> {
    #[cfg(feature = "std")]
    fn to_writer<W>(&self, mut wtr: W) -> io::Result<()>
    where
        W: Write,
    {
        self.map_or(0, NonZeroU32::get).to_writer(&mut wtr)
    }
}

impl Deserialize for Option<NonZeroU32> {
    #[cfg(feature = "std")]
    unsafe fn from_reader<R>(mut rdr: R) -> io::Result<Self>
    where
        R: Read,
    {
        Ok(NonZeroU32::new(u32::from_reader(&mut rdr)?))
    }

    unsafe fn from_slice(src: &[u8]) -> (Self, &[u8]) {
        let (x, src) = u32::from_slice(src);
        (NonZeroU32::new(x), src)
    }
}
