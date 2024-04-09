#[allow(unused_variables)]
#[allow(dead_code)]

pub type Digit = (u64);

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum IntStrPadding {
    Minimal,
    Full,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum IntStrCase {
    Lower,
    Upper,
}


#[derive(Clone, Debug, PartialEq)]
pub struct Int {
    // Declared count of bits in the magnitude.
    pub(crate) cb: u32,
    // sign = 1 in the case of positive integers; and -1 for negative integers.
    // sign = 0 when the magnitude is zero.
    // This invariant is maintained by all operations.
    pub(crate) sign: i32,
    // 'lnzd' stands for "leading non-zero digit".
    // 'lnzb' stands for "leading non-zero bit".
    // Zero-based index of the leading/most-significant non-zero digit in 'mag'.
    // The following two are invariants.
    pub(crate) pos_lnzd: i32,
    // If mag has an lnzd, pos_lnzb is the zero-based index of the lnzb within the lnzd.
    pub(crate) pos_lnzb: i32,
    // The magnitude of the integer.
    // A sequence of digits aka 'limbs'. Recall that a digit is a 64-bit quantity.
    // Digits are stored in little-endian format.
    // (0, digits.len()] or (0..digits.len-1)
    pub(crate) mag: Vec<Digit>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct U128 {
    pub(crate) lo: Digit,
    pub(crate) hi: Digit
}

mod nat;
mod bits;

