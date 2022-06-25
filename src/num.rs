#[derive(Clone, Copy, Default, Eq, PartialEq, Debug, Hash)]
pub struct U24([u8; 3]);

impl U24 {
    #[inline(always)]
    pub fn get(self) -> u32 {
        let mut x = [0; 4];
        x[..3].copy_from_slice(&self.0);
        u32::from_le_bytes(x)
    }

    #[inline(always)]
    pub const fn to_le_bytes(self) -> [u8; 3] {
        self.0
    }

    #[inline(always)]
    pub const fn from_le_bytes(bytes: [u8; 3]) -> Self {
        Self(bytes)
    }

    pub const MAX: u32 = 0x00ffffff;
}

impl TryFrom<u32> for U24 {
    type Error = &'static str;

    #[inline(always)]
    fn try_from(value: u32) -> Result<Self, Self::Error> {
        if value <= Self::MAX {
            let mut x = [0; 3];
            x.copy_from_slice(&value.to_le_bytes()[..3]);
            Ok(Self(x))
        } else {
            Err("value must be smaller than 2^24")
        }
    }
}
