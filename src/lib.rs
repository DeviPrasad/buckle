#[allow(unused_variables)]
#[allow(dead_code)]

pub type NatDigit = u64;

pub enum NatStrPadding {
    Minimal,
    Full,
}

pub enum NatStrCase {
    Lower,
    Upper,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Nat {
    pub(crate) bits: u32,
    pub mag: Vec<NatDigit>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct U128 {
    pub(crate) lo: NatDigit,
    pub(crate) hi: NatDigit
}

mod nat;
mod bits;

