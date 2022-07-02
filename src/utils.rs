pub trait FromU32 {
    fn from_u32(src: u32) -> Self;
}

#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
impl FromU32 for usize {
    fn from_u32(src: u32) -> Self {
        unsafe { Self::try_from(src).unwrap_unchecked() }
    }
}
