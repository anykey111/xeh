use crate::prelude::*;

const FMT_BASE_MASK: usize = 0xff;
const FMT_PREFIX_BIT: usize = 0b00001_00000000;
const FMT_TAGS_BIT: usize = 0b00010_00000000;
const FMT_FITSCREEN_BIT: usize   = 0b00100_00000000;
const FMT_UPCASE_BIT: usize = 0b01000_00000000;

pub struct FmtFlags(usize);

impl Default for FmtFlags {
    fn default() -> Self {
        FmtFlags(10 | FMT_PREFIX_BIT)
    }
}

impl FmtFlags {

    pub fn set_base(self, n: usize) -> Self {
        FmtFlags((self.0 & !FMT_BASE_MASK) | (n & FMT_BASE_MASK))
    }

    pub fn base(&self) -> usize {
        self.0 & FMT_BASE_MASK
    }

    pub fn set_show_prefix(self, t: bool) -> Self {
        if t {
            FmtFlags(self.0 | FMT_PREFIX_BIT)
        } else {
            FmtFlags(self.0 & !FMT_PREFIX_BIT)
        }
    }

    pub fn show_prefix(&self) -> bool {
        (self.0 & FMT_PREFIX_BIT) > 0
    }

    pub fn set_show_tags(self, t: bool) -> Self {
        if t {
            FmtFlags(self.0 | FMT_TAGS_BIT)
        } else {
            FmtFlags(self.0 & !FMT_TAGS_BIT)
        }
    }

    pub fn set_upcase(&self, t: bool) -> Self {
        if t {
            FmtFlags(self.0 | FMT_UPCASE_BIT)
        } else {
            FmtFlags(self.0 & !FMT_UPCASE_BIT)
        }
    }

    pub fn upcase(&self) -> bool {
        (self.0 & FMT_UPCASE_BIT) > 0
    }

    pub fn show_tags(&self) -> bool {
        (self.0 & FMT_TAGS_BIT) > 0
    }

    pub fn fitscreen(&self) -> bool {
        (self.0 & FMT_FITSCREEN_BIT) > 0
    }

    pub fn set_fitscreen(self, t: bool) -> Self {
        if t {
            FmtFlags(self.0 | FMT_FITSCREEN_BIT)
        } else {
            FmtFlags(self.0 & !FMT_FITSCREEN_BIT)
        }
    }

    pub fn build(self) -> Cell {
        Cell::from(self.0)
    }

    pub fn into_raw(self) -> usize {
        self.0
    }

    pub fn from_raw(flags: usize) -> Self {
        FmtFlags(flags)
    }
}
