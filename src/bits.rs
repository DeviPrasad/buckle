/*
    Copyright 2024 M. Devi Prasad (dp@web3pleb.org)

    Licensed under the Apache License, Version 2.0 (the "License");
    you may not use this file except in compliance with the License.
    You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

    Unless required by applicable law or agreed to in writing, software
    distributed under the License is distributed on an "AS IS" BASIS,
    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
    See the License for the specific language governing permissions and
    limitations under the License.
*/

use crate::Digit;
use crate::U128;

// sub_with_borrow calculates: diff = x - y - borrow.
// The borrow input must be 0 or 1.
// The borrow_out is guaranteed to be 0 or 1.
#[allow(dead_code)]
pub fn sbb(x: Digit, y: Digit, borrow: Digit) -> (/* diff */ Digit, /* borrow_out */ Digit) {
    debug_assert!(borrow <= 1);
    let (diff, o1) = x.overflowing_sub(y);
    let (diff, o2) = diff.overflowing_sub(borrow);
    assert!(o1 as u64 <= 1 && o2 as u64 <= 1);
    (diff, o1 as Digit + o2 as Digit)
}

#[allow(dead_code)]
pub fn adc(x: Digit, y: Digit, carry: Digit) -> (/* sum */ Digit, /* carry_out */ Digit) {
    debug_assert!(carry <= 1);
    let (sum, o1) = x.overflowing_add(y);
    let (sum, o2) = sum.overflowing_add(carry);
    assert!(o1 as Digit <= 1 && o2 as Digit <= 1);
    (sum, o1 as Digit + o2 as Digit)
}

pub fn mul128(x: u128, y: u128) -> u128 {
    x.overflowing_mul(y).0
}

// This is the simplest version of mul64 using Rust's 128-bit multiplication
pub fn mul64(x: Digit, y: Digit) -> U128 {
    let r2: u128 = x as u128 * y as u128;
    U128 { lo: r2 as Digit, hi: (r2 >> 64) as Digit }
}

pub fn mul64_64(x: Digit, y: Digit) -> Digit {
    x.overflowing_mul(y).0
}

pub fn mul128_64(x: u128, y: u64) -> u128 {
    x.overflowing_mul(y as u128).0
}

pub fn add128_64(x: u128, y: u64) -> u128 {
    x.overflowing_add(y as u128).0
}

pub fn add64(x: u64, y: u64) -> u64 {
    x.overflowing_add(y).0
}

pub fn sub128c(x: u128, y: u128) -> (u128, u32) {
    let t = x.overflowing_sub(y);
    (t.0, t.1 as u32)
}

pub fn sub64(x: u64, y: u64) -> u64 {
    x.overflowing_sub(y).0
}

pub fn div64(x: Digit, y: Digit) -> Digit {
    x.overflowing_div(y).0
}

pub fn shl64(x: Digit, n: u32) -> Digit {
    x.overflowing_shl(n).0
}

pub fn shr64(x: Digit, n: u32) -> Digit {
    x.overflowing_shr(n).0
}
//

// Divide a 128 bit number by a 64 bit number,
pub fn div64_rem64(hi: Digit, lo: Digit, divisor: Digit) -> (Digit, Digit) {
    assert!(divisor > 0, "div64 - divide by zero error");
    // assert!(divisor > hi, "div64 - quotient overflow error");

    // when high part is zero, use simple 64-bit division
    if hi == 0 {
        return (lo / divisor, lo % divisor)
    }
    const BASE: u64 = 1 << 32;
    const MASK_32: u64 = BASE - 1;

    let s: u32 = clz(divisor);
    // normalize the divider by stripping away all leading zeroes from it.
    let dn64: Digit = shl64(divisor, s);
    // break the divisor into two 32-bit digits (d1, d0) = y
    let dn32_1: Digit = shr64(dn64, 32);
    let dn32_0: Digit = dn64 & MASK_32;

    // 'hi' normalized 64 bits
    // 's' number of MSB zeroes are shifted out of 'hi' and filled with an equal number of MSB bits from 'lo')
    // When s == 0; 64-s == 64. On x86, shifting by the size of the integer type is undefined.
    // This means, (lo >> 64) is undefined (UB).
    let s_i64: i64 = -(s as i64) & 63;
    let s_i64_right_shifted_63: i64 = -(s as i64) >> 63;
    let lo_normalized: u64 = ((lo as i64 >> s_i64) & s_i64_right_shifted_63) as u64;
    let _lo_normalized_ideal_ = if s == 0 {
        (lo >> 63) >> 1
    } else {
        lo >> (64 - s)
    };
    debug_assert_eq!(_lo_normalized_ideal_, lo_normalized);

    let hn64: Digit = shl64(hi, s) | lo_normalized;
    // 'lo' normalized 64 bits, destructured (ln32_1, ln32_0) = ln64
    let ln64: Digit = shl64(lo, s);
    // higher 32 bits of ln64
    let ln32_1: Digit = shr64(ln64, 32);
    // lower 32 bits of ln64
    let ln32_0: Digit = ln64 & MASK_32;

    // calculate q_hat
    let mut q_hat_1: Digit = div64(hn64, dn32_1);
    let mut r_hat: Digit = sub64(hn64, mul64_64(q_hat_1, dn32_1));
    while q_hat_1 >= BASE || mul64_64(q_hat_1, dn32_0) > (shl64(r_hat, 32) + ln32_1) {
        q_hat_1 -= 1;
        r_hat = add64(r_hat, dn32_1);
        if r_hat >= BASE {
            break
        }
    }

    // multiply and subtract, and decrease j by 1, all at once!
    // update the dividend; ln32_1 is the next 'digit' included in u
    let un21 = sub64(add64(shl64(hn64, 32), ln32_1), mul64_64(q_hat_1, dn64));
    let mut q_hat_0: Digit = div64(un21, dn32_1);
    r_hat = sub64(un21, mul64_64(q_hat_0, dn32_1));

    while q_hat_0 >= BASE || mul64_64(q_hat_0, dn32_0) > add64(shl64(r_hat, 32), ln32_0) {
        q_hat_0 -= 1;
        r_hat = add64(r_hat, dn32_1);
        if r_hat >= BASE {
            break
        }
    }
    (add64(shl64(q_hat_1, 32), q_hat_0),
     (sub64(add64(shl64(un21, 32), ln32_0), mul64_64(q_hat_0, dn64))) >> s)
}

// count of leading zeroes.
pub fn clz(x: Digit) -> u32 {
    x.leading_zeros()
}

#[cfg(test)]
mod bits_test {
    use crate::bits::div64_rem64;

    fn init() {
        crate::init_logger(true)
    }

    #[test]
    fn bits_div64() {
        init();
        {
            let (q, r) = div64_rem64(0, 65537, 1);
            assert_eq!(q, 65537, "quotient");
            assert_eq!(r, 0, "reminder");
        }
        {
            let (q, r) = div64_rem64(0, 65537, 2);
            assert_eq!(q, 65537 >> 1, "quotient");
            assert_eq!(r, 1, "reminder");
        }
        {
            let (q, r) = div64_rem64(0, 100, 35);
            assert_eq!(q, 2, "quotient");
            assert_eq!(r, 30, "reminder");
        }
        {
            let (q, r) = div64_rem64(1, 100, 35);
            assert_eq!(q, 527049830677415763, "quotient");
            assert_eq!(r, 11, "reminder");
        }
        {
            let (q, r) = div64_rem64(32, 100, 35);
            assert_eq!(q, 16865594581677304337, "quotient");
            assert_eq!(r, 17, "reminder");
        }
        {
            let (q, r) = div64_rem64(0xFFFFFFFF, 0, 1 << 32);
            assert_eq!(q, 0xFFFFFFFF00000000, "quotient");
            assert_eq!(r, 0, "reminder");
        }
        {
            let (q, r) = div64_rem64(0xFFFFFFFF, 0, 2 << 32);
            assert_eq!(q, 0x7FFFFFFF80000000, "quotient");
            assert_eq!(r, 0, "reminder");
        }

        {
            let (q, r) = div64_rem64(0x0000000100000000, 0x000000000000FFFF, 0x0000100000000000);
            assert_eq!(q, 0x10000000000000, "quotient");
            assert_eq!(r, 0xFFFF, "reminder");
        }
        {
            let (q, r) = div64_rem64(0x7FFF800000000000, 0x0000000000000000, 0x8000000000000001);
            assert_eq!(q, 0xFFFEFFFFFFFFFFFE, "quotient");
            assert_eq!(r, 0x1000000000002, "reminder");
        }
        {
            let (q, r) = div64_rem64(0x7FFF000000000000, 0x000000000000FFFF, 0x8000000000000000);
            assert_eq!(q, 0xFFFE000000000000, "quotient");
            assert_eq!(r, 0xFFFF, "reminder");
        }
        {
            let (q, r) = div64_rem64(0x7FFFFFFFFFFFFFFF, 0xFFFF00000000FFFF, 0xFF00000000000000);
            assert_eq!(q, 0x8080808080808080, "quotient");
            assert_eq!(r, 0x7FFF00000000FFFF, "reminder");
        }
        {
            let (q, r) = div64_rem64(0x7FFFFFFFFFFFFFFF, 0xFFFF00000000FFFF, 0xFFFFFFFFFFFFFFFF);
            assert_eq!(q, 0x8000000000000000, "quotient");
            assert_eq!(r, 0x7fff00000000ffff, "reminder");
        }
    }

    #[test]
    fn print_64bit_shift() {
        init();

        let v: u64 = 0xFFFF000000000000;
        println!("+--------------------------------------------------------------------------+");
        println!("|  i    j    bin_j     minus_i   mi & 63        sr               w         |");
        println!("+--------------------------------------------------------------------------+");
        for i in 0..=64_u8 {
            let j: u8 = 64 - i;
            let mi_and_63 = (-(i as i8) & 63) as u8;
            let s = (-(i as i8) & 63) as u8;
            let sr = -(i as i64) >> 63;
            println!("|{i:>3}   {j:>3}  {j:>08b}  {minus_i:>08b}  {mi_and_63:>08b} {sr:>016x} {w:>016x} |",
                     minus_i = -(i as i8) as u8,
                     w = (v >> s) & sr as u64
            );
        }
        println!("+--------------------------------------------------------------------------+");
    }
}
