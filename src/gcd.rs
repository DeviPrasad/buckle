use std::cmp::min;
use crate::Int;

// extended binary GCD algorithm
pub fn gcd(a: &Int, b: &Int) -> (/* gcd */Int, /* s */Int, /* t */ Int) {
    let (x, y) = (a.compact(), b.compact());
    let _r = min(x.ctz(), y.ctz()); // find the count of LSBs that can be stripped from x and y
    (Int::zero(0), Int::zero(0), Int::zero(0))
}