#[allow(unused_variables)]

#[derive(Debug, Eq, PartialEq)]
pub struct U128 {
    pub(crate) lo: u64,
    pub(crate) hi: u64
}

// sub_with_borrow calculates: diff = x - y - borrow.
// The borrow input must be 0 or 1.
// The borrow_out is guaranteed to be 0 or 1.
#[allow(dead_code)]
pub fn sub_with_borrow(x: u64, y: u64, borrow: u64) -> (/* diff */ u64, /* borrow_out */ u64) {
    debug_assert!(borrow <= 1);
    let (diff, o1) = x.overflowing_sub(y);
    let (diff, o2) = diff.overflowing_sub(borrow);
    assert!(o1 as u64 <= 1 && o2 as u64 <= 1);
    (diff, o1 as u64 | o2 as u64)
}

#[allow(dead_code)]
pub fn add_with_carry(x: u64, y: u64, carry: u64) -> (/* sum */ u64, /* carry_out */ u64) {
    debug_assert!(carry <= 1);
    let (sum, o1) = x.overflowing_add(y);
    let (sum, o2) = sum.overflowing_add(carry);
    assert!(o1 as u64 <= 1 && o2 as u64 <= 1);
    (sum, o1 as u64 | o2 as u64)
}

// This is the simplest version of mul64 using Rust's 128-bit multiplication
pub fn mul64(x: u64, y: u64) -> U128 {
    let r2: u128 = x as u128 * y as u128;
    U128 { lo: r2 as u64, hi: (r2 >> 64) as u64 }
}

