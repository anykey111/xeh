use sha1::{Digest, Sha1};

use crate::cell::XfnType;

#[derive(Debug)]
pub struct Xhash([u8; 20]);

impl Default for Xhash {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl From<XfnType> for Xhash {
    fn from(x: XfnType) -> Self {
        Xhash::from(x as usize)
    }
}

impl From<usize> for Xhash {
    fn from(x: usize) -> Self {
        let mut h = Xhash::default();
        for (i, x) in x.to_ne_bytes().iter().enumerate() {
            h.0[i] = *x;
        }
        h
    }
}

impl From<&str> for Xhash {
    fn from(x: &str) -> Self {
        let mut h = Sha1::new();
        h.input(x.as_bytes());
        Xhash(h.result().into())
    }
}
