#[derive(Clone, Copy, Default, Eq, PartialEq, Debug, Hash)]
pub struct U24(u32);

impl U24 {
    #[inline(always)]
    pub const fn get(self) -> u32 {
        self.0
    }

    pub const MAX: u32 = 0x00ffffff;
}

impl TryFrom<u32> for U24 {
    type Error = &'static str;

    #[inline(always)]
    fn try_from(value: u32) -> Result<Self, Self::Error> {
        if value <= Self::MAX {
            Ok(Self(value))
        } else {
            Err("value must be smaller than 2^24")
        }
    }
}

#[derive(Clone, Copy, Default, Eq, PartialEq, Debug, Hash)]
pub struct U24nU8(u32);

impl U24nU8 {
    #[inline(always)]
    pub const fn a(self) -> U24 {
        U24(self.0 >> 8)
    }

    #[inline(always)]
    pub fn b(self) -> u8 {
        u8::try_from(self.0 & u8::MAX).unwrap()
    }

    #[inline(always)]
    pub fn set_a(&mut self, a: U24) {
        self.0 = a.get() << 8 | u32::from(self.b());
    }

    #[inline(always)]
    pub fn set_b(&mut self, b: u8) {
        self.0 = self.a().get() << 8 | u32::from(b);
    }

    #[inline(always)]
    pub const fn to_le_bytes(self) -> [u8; 4] {
        self.0.to_le_bytes()
    }

    #[inline(always)]
    pub const fn from_le_bytes(bytes: [u8; 4]) -> Self {
        Self(u32::from_le_bytes(bytes))
    }
}
