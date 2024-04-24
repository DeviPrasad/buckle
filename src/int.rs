use std::cmp::{max, min, PartialEq};
use std::env;
use std::fmt::Formatter;
use std::ops::{Div, Rem, Shr};

use crate::{bits, Digit, Int, IntStrCase, IntStrPadding, U128};
use crate::bits::{adc, add128_64, add64, bit_width, mul128, mul128_64, mul64, sbb, shl64, sub128c, sub64};

impl std::fmt::Display for Int {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "bits:{:};digits:{:};sign:{:+};mag_hex:{:X?}", self.bit_width(), self.width(), self.sign, self.mag)
    }
}

impl Int {
    pub const BIT_LEN_MIN: u32 = 1 * Digit::BITS;
    // Nat magnitude has at least one limb
    pub const BIT_LEN_MAX: u32 = 16 * 1024;
    pub const DIGITS_MIN: u32 = Int::BIT_LEN_MIN / Digit::BITS;
    pub const DIGITS_MAX: u32 = Int::BIT_LEN_MAX / Digit::BITS;
    pub const DIGIT_VAL_MAX: u32 = (Digit::MAX - 1) as u32;

    pub const KARATSUBA_MUL_THRESHOLD: u32 = 20;
    pub const KARATSUBA_SQR_THRESHOLD: u32 = 40;

    // Burnikel-Ziegler division method is used If the number of digits in the divisor
    // are larger than this value.
    // NOTE: THIS THRESHOLD ONLY FOR DEV_TESTING PURPOSE ONLY!!
    pub const BURNIKEL_ZIEGLER_DIV_THRESHOLD: u32 = 20;

    // Burnikel-Ziegler division method will be used if
    // (a) the number of digits in the divisor is greater than BURNIKEL_ZIEGLER_DIV_THRESHOLD, and
    // (b) the number of digits in the dividend exceeds the sum of the number of digits
    //      in the divisor and the value BURNIKEL_ZIEGLER_DIV_OFFSET.
    pub const BURNIKEL_ZIEGLER_DIV_OFFSET: u32 = 20;

    fn sign_of(s: i32) -> i32 {
        match s {
            0..=i32::MAX => 1,
            _ => -1
        }
    }

    fn check_len(cb: u32) {
        #[cfg(any(debug_assertions, release_test))]
        assert!(cb >= Int::BIT_LEN_MIN && cb <= Int::BIT_LEN_MAX, "Int::check_len - bad bit length");
    }

    fn valid(&self) {
        #[cfg(any(debug_assertions, release_test))]
        {
            let (pos_lnzd, pos_lnzb) = Int::pos_lnzd_lnzb(self.cb, &self.mag);
            assert!(self.cb >= Int::BIT_LEN_MIN && self.cb <= Int::BIT_LEN_MAX,
                    "Int::check_invariant - bad bit length");
            assert_eq!(self.mag.len() as u32, Int::width_of(self.cb), "Int::check_invariant - announced Int size does not match with the magnitude");
            assert!(self.sign == 0 || self.sign == 1 || self.sign == -1, "Int::check_invariant - invalid sign");
            assert!((self.sign == 0 && (self.pos_lnzd == -1 && self.pos_lnzb == -1)) ||
                        (self.sign != 0
                            && (self.pos_lnzb >= 0 && self.pos_lnzb < 64)
                            && (self.pos_lnzd >= 0 && self.pos_lnzd <= self.mag.len() as i32 - 1)),
                    "Int::check_invariant - invalid sign, lnzd, or lnzb values");
            assert_eq!(pos_lnzd, self.pos_lnzd, "Int::check_invariant - bad pos_lnzd value");
            assert_eq!(pos_lnzb, self.pos_lnzb, "Int::check_invariant - bad pos_lnzb value");
        }
    }

    pub fn bit_width(&self) -> u32 {
        self.valid();
        self.cb
    }

    pub fn width(&self) -> u32 {
        self.valid();
        self.mag.len() as u32
    }

    fn width_of(bit_len: u32) -> u32 {
        return
            bit_len / Digit::BITS +
                match bit_len % Digit::BITS {
                    0 => 0,
                    _ => 1
                }
    }

    fn size_plus_1(bit_len: u32) -> u32 {
        bit_len / Digit::BITS + 1
    }

    pub fn new(bit_len: u32) -> Self {
        Int::check_len(bit_len);
        let bit_len = min(max(bit_len, Int::BIT_LEN_MIN), Int::BIT_LEN_MAX);
        let digits = vec![0; Int::width_of(bit_len) as usize];
        let (pos_lnzd, pos_lnzb) = Self::pos_lnzd_lnzb(bit_len, &digits);
        let n = Int {
            cb: bit_len,
            sign: 0,
            mag: digits,
            pos_lnzd,
            pos_lnzb,
        };
        n.valid();
        n
    }

    fn set_invariants(&mut self) {
        let (pos_lnzd, pos_lnzb) = Self::pos_lnzd_lnzb(self.cb, &self.mag);
        self.pos_lnzd = pos_lnzd;
        self.pos_lnzb = pos_lnzb;
        if pos_lnzd == -1 {
            assert_eq!(pos_lnzb, -1);
            self.sign = 0;
        } else {
            self.sign = Self::sign_of(1);
        }
        self.valid();
    }

    // count of leading zeroes in this Int
    pub fn clz(&self) -> u32 {
        if self.pos_lnzd < 0 {
            0
        } else {
            self.width() * Digit::BITS -
                // recall lnzb is zero-based index of the leading set-bit; so we add 1 to it.
                (self.pos_lnzd as u32 * Digit::BITS + self.pos_lnzb as u32 + 1)
        }
    }

    // Find the index of the leading non-zero digit in the magnitude.
    // Determine the index of the leading non-zero bit within this digit.
    fn pos_lnzd_lnzb(bit_len: u32, mag: &Vec<Digit>) -> (i32, i32) {
        // create a mask of N trailing 1's.
        let cb_used_in_leading_digit: u64 = bit_len as u64 & (Digit::BITS - 1) as u64; // mod 64
        let mask = match cb_used_in_leading_digit {
            0 => Digit::MAX,
            _ => (1 << cb_used_in_leading_digit) - 1
        };

        // The most-significant/leading digit may use less than 64-bits (full-width of the Digit).
        // The leading digit should be masked appropriately to ignore the unused leading bits, and
        // to select only the right-sized suffix bits (LSBs).
        let mut rit = mag.iter().rev(); // start at the most-leading digit.
        if let Some((&ld)) = rit.next() { // pick only the leading digit.
            if ld & mask > 0 { // if the used bits contribute a value, return the indices.
                return ((mag.len() - 1) as i32, (bit_width(ld) - 1) as i32)
            }
        }
        // The leading digit is zero. So we walk the others digits (from MSB to LSB).
        for (i, &d) in rit.enumerate() {
            if d > 0 { // check the full width of the digit
                return ((mag.len() - i - 2) as i32, (bit_width(d) - 1) as i32)
            }
        }
        // Every digit is a zero in this Int.
        (-1, -1)
    }

    pub fn from_parts(bit_len: u32, mag: Vec<Digit>) -> Self {
        let bl = min(max(bit_len, Int::BIT_LEN_MIN), Int::BIT_LEN_MAX);
        let mut res = Int::new(bl);
        for (d, s) in res.mag.iter_mut().zip(mag.iter()) {
            *d = *s;
        }
        res.set_invariants();
        res
    }

    pub fn from_le_digits_vec(digits: Vec<Digit>) -> Self {
        #[cfg(any(debug_assertions, release_test))]
        assert!(digits.len() > 0 && digits.len() <= Int::DIGITS_MAX as usize);
        let bit_len: u32 = digits.len() as u32 * Digit::BITS;
        let res = Int::from_parts(bit_len, digits);
        res.valid();
        res
    }

    // number of bits of magnitude may be less than the bit_len
    pub fn from_le_digits_with_capacity(bit_len: u32, digits: Vec<Digit>) -> Self {
        #[cfg(any(debug_assertions, release_test))]
        assert!(digits.len() > 0 && digits.len() <= Int::DIGITS_MAX as usize,
                "from_le_digits_with_capacity - too few or too many digits ({}) in the number", digits.len());
        assert!(Self::width_of(bit_len) as usize >= digits.len(),
                "from_le_digits_with_capacity - bit length capacity {} smaller than digits {}",
                Self::width_of(bit_len), digits.len());
        let res = Int::from_parts(bit_len, digits);
        res.valid();
        res
    }

    pub fn resize(&self, new_len: u32) -> Int {
        self.valid();
        let self_len = Int::width_of(self.cb);
        let new_size = Int::width_of(new_len) as usize;
        if self_len == new_len || new_len == 0 || new_len > Self::BIT_LEN_MAX {
            self.clone()
        } else if self.cb < new_len {
            // need more space to hold digits of a larger magnitude
            let mut lm = vec![0; new_size];
            for (dst, src) in lm.iter_mut().zip(&self.mag[0..]) {
                *dst = *src;
            }
            let larger_nat = Int::from_parts(new_len, lm);
            larger_nat.valid();
            larger_nat
        } else {
            // shrink the size of the magnitude
            let mut sm = vec![0; new_size];
            // 'copy_from_slice' panics if the source and destination lengths are not equal
            sm.copy_from_slice(&self.mag[0..new_size]);
            let smaller_nat = Int::from_parts(new_len, sm);
            // smaller_nat.fix_invariants(smaller_nat.sign);
            smaller_nat.valid();
            smaller_nat
        }
    }

    pub fn new_digit(bit_len: u32, val: Digit) -> Self {
        let mut res = Self::new(bit_len);
        res.mag[0] = val;
        res.set_invariants();
        res.valid();
        res
    }

    pub fn digit_value(&self) -> (bool, Digit) {
        self.valid();
        if self.mag[0] > 0 && // the least-significant digit is non-zero, and
            // either it is a single digit int or the rest of the digits are all zeros
            (self.width() == 1 || self.mag[1..].iter().eq([0].iter())) {
            (true, self.mag[0])
        } else {
            (false, 0)
        }
    }

    pub fn zero(bit_len: u32) -> Int {
        Self::new(bit_len)
    }

    pub fn one(bit_len: u32) -> Int {
        Self::new_digit(bit_len, 1)
    }

    pub fn is_zero(&self) -> bool {
        self.valid();
        self.sign == 0
    }

    pub fn is_one(&self) -> bool {
        self.valid();
        let mut r = self.mag[0] == 1;
        for d in 1..self.width() {
            r = r && d == 0
        }
        r
    }

    pub fn is_compact(&self) -> bool {
        self.pos_lnzd >= 0 && self.pos_lnzd as u32 == self.width() - 1
    }

    pub fn compact(&self) -> Int {
        let mut s = self.clone();
        s.compact_mut();
        s
    }

    pub fn compact_mut(&mut self) {
        self.valid();
        let len = match self.is_zero() {
            true => 1usize, // need at least one digit to store the zero value
            _ => (self.pos_lnzd + 1) as usize
        };
        self.mag.truncate(len);
        self.cb = len as u32 * Digit::BITS;
        self.set_invariants();
        self.valid();
    }

    // returns (count_of_one_bits, most_significant_set_bit)
    pub fn count_ones(&self) -> (u32, u32) {
        let mut c = 0;
        let mut mssb = 0;
        let mut bit = 0;
        for &d in self.mag.iter() {
            c += d.count_ones();
            let mut n = d;
            for _ in 0..64 {
                if (n & 1) == 1 {
                    mssb = bit;
                }
                n = n >> 1;
                bit += 1;
            }
            assert_eq!(bit % 64, 0);
        }
        assert!((c == 0 && mssb == 0) || c > 0);
        (c, mssb)
    }

    pub fn pow2(&self) -> bool {
        self.count_ones().0 == 1 && self.mag[0] != 1
    }

    fn inverse(&self, _n: &Int) -> Int {
        panic!("inverse - not implemented!")
    }

    fn sqrt(&self) -> Int {
        panic!("sqrt - not implemented!")
    }

    fn min(&self, n2: &Self) -> Int {
        if self.lt(&n2) {
            self.clone()
        } else {
            n2.clone()
        }
    }

    fn max(&self, n2: &Int) -> Int {
        if self.gt(&n2) {
            self.clone()
        } else {
            n2.clone()
        }
    }

    pub fn compare<'a>(&'a self, t: &'a Int) -> (/* larger */&Int, /* smaller */&Int, /* sign */i32) {
        if self.pos_lnzd > t.pos_lnzd {
            (self, t, 1)
        } else if self.pos_lnzd < t.pos_lnzd {
            (t, self, -1)
        } else {
            if self.pos_lnzb > t.pos_lnzb {
                (self, t, 1)
            } else if self.pos_lnzb < t.pos_lnzb {
                (t, self, -1)
            } else {
                (self, t, 0)
            }
        }
    }

    fn eq(&self, n2: &Self) -> bool {
        self.valid();
        self.compare(&n2).2 == 0
    }

    fn lt(&self, n2: &Self) -> bool {
        self.valid();
        self.compare(&n2).2 < 0
    }

    fn le(&self, n2: &Self) -> bool {
        self.valid();
        self.compare(&n2).2 <= 0
    }

    fn gt(&self, n2: &Self) -> bool {
        self.valid();
        self.compare(&n2).2 > 0
    }

    fn ge(&self, n2: &Self) -> bool {
        self.valid();
        self.compare(&n2).2 >= 0
    }

    pub fn add(&self, n2: &Int) -> (Int, Digit) {
        let n1 = self;
        #[cfg(any(debug_assertions, release_test))]
        assert_eq!(n1.bit_width(), n2.bit_width(), "add {} >= {}", n1.bit_width(), n2.bit_width());
        n1.valid();
        n2.valid();
        let mut carry: Digit = 0;
        let mut mag = vec![0; Int::width_of(n1.bit_width()) as usize];
        n1.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            (mag[i], carry) = adc(x, y, carry);
        });
        let res = Int::from_parts(n1.bit_width(), mag);
        res.valid();
        (res, carry)
    }

    pub fn sum(&self, n2: &Int) -> Int {
        self.add(&n2).0
    }

    pub fn resize_sum(&self, t: &Int) -> Int {
        let res_bit_len = max(self.bit_width(), t.bit_width());
        let r = if self.bit_width() < res_bit_len {
            Int::sum(&self.resize(res_bit_len), &t)
        } else if t.bit_width() < res_bit_len {
            Int::sum(self, &t.resize(res_bit_len))
        } else {
            Int::sum(self, t)
        };
        r
    }

    pub fn resize_add(&self, t: &Int) -> (Int, Digit) {
        let res_bit_len = max(self.bit_width(), t.bit_width());
        if self.bit_width() < res_bit_len {
            Int::add(&self.resize(res_bit_len), &t)
        } else if t.bit_width() < res_bit_len {
            Int::add(self, &t.resize(res_bit_len))
        } else {
            Int::add(self, t)
        }
    }

    pub fn resize_sub(s: &Int, t: &Int) -> (Int, i64) {
        let res_bit_len = max(s.bit_width(), t.bit_width());
        if s.bit_width() < res_bit_len {
            Int::sub(&s.resize(res_bit_len), t)
        } else if t.bit_width() < res_bit_len {
            Int::sub(s, &t.resize(res_bit_len))
        } else {
            Int::sub(s, t)
        }
    }

    pub fn resize_abs_sub(s: &Int, t: &Int) -> (Int, i32) {
        let res_bit_len = max(s.bit_width(), t.bit_width());
        if s.bit_width() < res_bit_len {
            Int::sub_abs(&s.resize(res_bit_len), t)
        } else if t.bit_width() < res_bit_len {
            Int::sub_abs(s, &t.resize(res_bit_len))
        } else {
            Int::sub_abs(s, t)
        }
    }

    fn _do_sub_(n1: &Int, n2: &Int) -> (Vec<Digit>, Digit, Digit) {
        let mut borrow: Digit = 0;
        let mut mag_diff: Digit = 0; // zero when x.mag == y.mag
        let mut mag = vec![0; Int::width_of(n1.bit_width()) as usize];
        n1.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            let diff: Digit; // diff between each corresponding limbs of x and y
            (diff, borrow) = sbb(x, y, borrow);
            mag_diff |= diff;
            mag[i] = diff;
        });
        (mag, borrow, mag_diff)
    }

    pub fn sub(n1: &Int, n2: &Int) -> (Int, i64) {
        n1.valid();
        n2.valid();

        #[cfg(any(debug_assertions, release_test))]
        assert_eq!(n1.bit_width(), n2.bit_width(), "sub {} != {}", n1.bit_width(), n2.bit_width());

        let (mag, borrow, mag_diff) = Self::_do_sub_(n1, n2);
        let d: i64 = match mag_diff {
            0 => 0,
            _ => 1
        };
        let res = Int::from_parts(n1.bit_width(), mag);
        res.valid();
        (res, (-(borrow as i64)) | d)
    }

    // subtract two magnitudes. Indicate the sign too.
    pub fn sub_abs(&self, n2: &Int) -> (Int, i32) {
        let n1 = self;
        n1.valid();
        n2.valid();

        #[cfg(any(debug_assertions, release_test))]
        assert_eq!(n1.bit_width(), n2.bit_width(), "rut: sub_abs {} != {}", n1.bit_width(), n2.bit_width());

        let (n1, n2, sign) = n1.compare(&n2);
        let (mag, _, _) = Self::_do_sub_(n1, n2);
        let res = Int::from_parts(n1.bit_width(), mag);
        res.valid();
        (res, sign)
    }

    // acc += n * x
    pub fn add_mul_row(&self, x: Digit, acc: &mut [Digit]) -> Digit {
        debug_assert_eq!(self.width(), acc.len() as u32, "add_mul_row - length mismatch.");
        #[cfg(any(debug_assertions, release_test))]
        assert_eq!(self.width(), acc.len() as u32, "add_mul_row - length mismatch.");
        let mut carry: Digit = 0;
        for (i, &a) in self.mag.iter().enumerate() {
            let a_mul_b: U128 = mul64(a, x);
            let column_sum: u128 = a_mul_b.lo as u128 + acc[i] as u128 + carry as u128;
            // use the lower 64 bits as the actual sum.
            acc[i] = column_sum as Digit;
            // a_mul_b and column_sum contribute the new carry
            carry = a_mul_b.hi + (column_sum >> 64) as Digit;
        }
        carry
    }

    // elementary school-book multiplication
    // TODO: optimize when at least one of the arguments is 2^N
    pub fn mul(&self, n2: &Int) -> Int {
        Self::multiply_base_case(&self, n2)
    }

    pub fn mul_karatsuba(&self, n2: &Int) -> Int {
        let mut prod = Self::multiply_karatsuba(&self, n2);
        prod.truncate(self.width() + n2.width());
        prod.valid();
        prod
    }

    pub fn multiply_base_case(n1: &Int, n2: &Int) -> Int {
        n1.valid();
        n2.valid();

        let prod_size = (n1.width() + n2.width()) as usize;
        debug_assert!(prod_size <= Int::DIGITS_MAX as usize,
                      "mul_base_case - product size {prod_size} exceeds Nat limit {}", Int::DIGITS_MAX);
        #[cfg(any(debug_assertions, release_test))]
        if prod_size > Int::DIGITS_MAX as usize {
            assert!(prod_size <= Int::DIGITS_MAX as usize,
                    "mul_base_case - product size {prod_size} exceeds Nat limit {}", Int::DIGITS_MAX);
        }
        // allocate space for the the product accumulator.
        let mut acc: Vec<Digit> = vec![0; prod_size];
        for (i, &a) in n1.mag.iter().enumerate() {
            // clear carry when starting with a new row
            let mut carry: Digit = 0;
            carry = n2.add_mul_row(a, &mut acc[i..i + n2.width() as usize]);
            // the carry must be added to the column 'right' of i + count_digits_in_n2
            acc[i + n2.width() as usize] = carry;
        }
        let mut prod = Int::from_parts(n1.bit_width() + n2.bit_width(), acc);
        prod.set_invariants();
        prod.valid();
        prod
    }

    // Used in Karatsuba multiplication.
    // Split the digits into two blocks, so at best, each of 'blk_len' (or less) size
    // returns (lower_digits, upper_digits)
    fn split_digits(&self, num_digits: u32) -> (Int, Int) {
        let self_len = self.width();
        let cb = num_digits * Digit::BITS; // count of bits required
        if self_len > num_digits {
            // left and right blocks or the lower and upper halves, respectively.
            let (lb, ub) = self.mag.split_at(num_digits as usize);
            let vec_lb = Vec::<Digit>::from(lb);
            let vec_ub = Vec::<Digit>::from(ub);
            (Int::from_parts(cb, vec_lb), Int::from_parts(cb, vec_ub))
        } else {
            (self.clone(), Int::new(cb))
        }
    }

    pub fn multiply_karatsuba(n1: &Int, n2: &Int) -> Int {
        n1.valid();
        n2.valid();

        let n1_len = n1.width();
        let n2_len = n2.width();
        let k = (max(n1_len, n2_len) + 1) / 2;
        let (a0, a1) = n1.split_digits(k);
        let (b0, b1) = n2.split_digits(k);

        let c0 = a0.multiply(&b0);
        let c1 = a1.multiply(&b1);

        let (c2_a, sign_a) = Int::resize_abs_sub(&a0, &a1);
        let (c2_b, sign_b) = Int::resize_abs_sub(&b0, &b1);
        let c2: Int = c2_a.multiply(&c2_b);

        let base_pow_k = Int::new_digit(64 * k + 1, 0).set_bit_mut(64 * k);
        let base_pow_2k = Int::new_digit(64 * 2 * k + 1, 0).set_bit_mut(64 * 2 * k);
        let c1_mul_base_pow_2k = c1.mul(&base_pow_2k);
        let c0_plus_c1 = c0.resize_sum(&c1);
        let mut prod = if sign_a * sign_b >= 0 {
            let (c0_plus_c1_minus_c2, _) = c0_plus_c1.sub_abs(&c2);
            c0.resize_sum(&c0_plus_c1_minus_c2.mul(&base_pow_k)).resize_sum(&c1_mul_base_pow_2k)
        } else {
            let c0_plus_c1_plus_c2 = c0_plus_c1.sum(&c2);
            c0.resize_sum(&c0_plus_c1_plus_c2.multiply(&base_pow_k)).resize_sum(&c1_mul_base_pow_2k)
        };
        prod.valid();
        prod
    }

    fn truncate(&mut self, digits_len: u32) {
        self.cb = digits_len * Digit::BITS;
        self.mag.resize(digits_len as usize, 0);
        self.set_invariants();
        self.valid();
    }

    pub fn multiply(&self, n2: &Int) -> Int {
        let n1 = self;
        n1.valid();
        n2.valid();
        let xl = n1.width();
        let yl = n2.width();
        let mut prod = if xl < Int::KARATSUBA_MUL_THRESHOLD || yl < Int::KARATSUBA_MUL_THRESHOLD {
            Self::multiply_base_case(&n1, &n2)
        } else {
            Self::multiply_karatsuba(&n1, &n2)
        };
        prod.truncate(xl + yl);
        prod.valid();
        prod
    }

    pub fn div(&self, _n: &Int) -> Int {
        panic!("div - not implemented")
    }

    pub fn rem(&self, _n: &Int) -> Int {
        panic!("rem - not implemented")
    }

    pub fn divide(&self, divisor: &Int) -> (Int, Int) {
        self.valid();
        divisor.valid();

        let dividend = &self.compact();
        let divisor = &divisor.compact();

        assert!(!divisor.is_zero(), "Int::divide - division by zero error");

        if dividend.is_zero() {
            (Int::zero(Digit::BITS), Int::zero(Digit::BITS))
        } else if let (1, l) = divisor.count_ones() { // is divisor == 1 or a power of 2?
            // yes! divisor is a power of 2, and therefore, simply shr the dividend by 'l'
            // NOTE: this naturally accommodates division by 1 (when l = 0).
            assert!(l < divisor.bit_width());
            let mut q = dividend.shr(l);
            q.set_invariants();
            q.compact_mut();
            q.valid();
            // l is the zero-based index of the single 1-bit.
            // Clearly, the digit containing this bit is l/64.
            // The bit position within this digit is l%64.
            // Using ((1 << bit) - 1) as the mask clears all bits from bit..64 within the digit.
            let (rem_digit, bit) = (l / Digit::BITS, l % 64);
            eprintln!("divide l = {l}");
            let mut r = dividend.resize(l);
            r.mag[rem_digit as usize] &= (1 << bit) - 1;
            r.set_invariants();
            r.compact_mut();
            r.valid();
            (q, r)
        } else {
            let (_, _, co) = dividend.compare(divisor);
            if co == 0 { // dividend == divisor
                (Int::one(Digit::BITS), Int::zero(Digit::BITS))
            } else if co < 0 { // dividend < divisor
                (Int::zero(Digit::BITS), dividend.compact())
            } else if let (true, digit) = divisor.digit_value() {
                dividend.divide_by_digit(digit)
            } else {
                let m = dividend.width(); // count of digits in the dividend
                let n = divisor.width(); // count of digits in the divisor
                assert!(m > 2 && n >= 2 && m >= n + 1);
                let (mut q, r) =
                    if m < Int::BURNIKEL_ZIEGLER_DIV_THRESHOLD ||
                        (m - n) < Int::BURNIKEL_ZIEGLER_DIV_OFFSET {
                        Self::div_knuth(&dividend, &divisor)
                    } else {
                        panic!("Burnikel-Ziegler division not implemented!")
                    };
                q.set_invariants();
                q.compact_mut();
                q.valid();
                r.valid();
                (q, r)
            }
        }
    }

    pub fn div_by_pow_2(dividend: &Int, l: u32) -> (Int, Int) {
        // divisor is a power of 2, and therefore, simply shr the dividend by 'l'
        // NOTE: this naturally handles division by 1 (when l = 0).
        let mut q = dividend.shr(l);
        q.set_invariants();
        q.compact_mut();
        q.valid();
        // l is the zero-based index of the single 1-bit.
        // Clearly, the digit containing this bit is l/64.
        // The bit position within this digit is l%64.
        // Using ((1 << bit) - 1) as the mask clears all bits from bit..64 within the digit.
        let (rem_digit, bit) = (l / Digit::BITS, l % 64);
        eprintln!("divide l = {l}");
        let mut r = dividend.resize(l);
        r.mag[rem_digit as usize] &= (1 << bit) - 1;
        r.set_invariants();
        r.compact_mut();
        r.valid();
        (q, r)
    }

    fn _normalize_shared_loop_(wn: &mut Vec<Digit>, w: &Vec<Digit>, s: u32, m: u32) -> Int {
        if s > 0 {
            for k in (1..m).rev() {
                let i = k as usize;
                wn[i] = (w[i] << s) | (w[i - 1] >> (Digit::BITS - s));
            }
        } else {
            for k in 0..m {
                let i = k as usize;
                wn[i] = w[i];
            }
        }
        wn[0] = w[0] << s;

        let wn: Vec<Digit> = wn.iter().map(|&x| x).collect();
        let mut num = Int::from_le_digits_vec(wn);
        num.set_invariants();
        num.valid();
        num
    }

    // pushes all leading zeroes out.
    // pre-condition: magnitude > 0
    // post-condition: res.digits_len() = self.digits_len() + (expand as u32)
    fn expand_normalize(&self, s: u32) -> Int {
        self.valid();
        assert!(self.pos_lnzb >= 0 && self.pos_lnzb >= 0);

        let w = &self.mag;
        let m = self.width();
        let mut wn = vec![0; (m + 1) as usize];
        if s > 0 {
            wn[m as usize] = w[m as usize - 1] >> (Digit::BITS - s);
        }
        Self::_normalize_shared_loop_(&mut wn, &w, s, m)
    }

    fn normalize(&self, s: u32) -> Int {
        self.valid();
        assert!(self.pos_lnzb >= 0 && self.pos_lnzb >= 0);

        let w = &self.mag;
        let m = self.width();
        let mut wn = vec![0; m as usize];
        Self::_normalize_shared_loop_(&mut wn, &w, s, m)
    }

    pub fn digit(&self, i: u32) -> Digit {
        assert!(i < self.width(), "Int::digit - invalid index {i} >= {}", self.width());
        self.mag[i as usize]
    }

    pub fn dec(&mut self, i: u32) {
        self.update(i, self.digit(i) - 1);
    }

    pub fn update(&mut self, i: u32, rval: Digit) {
        assert!(i < self.width(), "Int::update - invalid index {i} >= {}", self.width());
        self.mag[i as usize] = rval;
        self.set_invariants();
        self.valid();
    }

    // pre-conditions:
    // divisor is compact. divisor.digits_len() > 1, dividend.digits_len() >= divisor.digits_len()
    //
    pub fn div_knuth(&self, divisor: &Int) -> (/* quotient */Int, /* remainder */Int) {
        let dividend: &Int = self;
        dividend.valid();
        divisor.valid();
        assert!(divisor.is_compact());
        let m = dividend.width();
        let n = divisor.width();
        assert!(n > 1 && m >= n);
        // count of leading zeroes in the divisor.
        // this is the number of bits to be right-shifted to normalize the operands
        let s = divisor.clz();
        let mut vn = divisor.normalize(s);
        // normalize the divider by stripping away leading zeroes.
        assert_eq!(vn.mag[vn.pos_lnzd as usize] & (1 << 63), 1 << 63);
        let mut un = dividend.expand_normalize(s);
        /*
                log::info!("normalized u and v. m = {m}[um_len = ({})], n = {n}[vn_len = ({})]", un.digits_len(), vn.digits_len());
                log::info!("normalized u. um = {un}");
                log::info!("     given u.  m = {dividend}");
                log::info!("normalized v. vn = {vn}");
                log::info!("     given v.  v = {divisor}");
        */
        const BASE: u128 = 1 << 64;
        const BASE_MASK: u128 = BASE - 1;
        let mut q: u128 = 0;
        let mut quotient = Int::from_le_digits_vec(vec![0_u64; (m - n + 1) as usize]);

        for j in (0..=m - n).rev() {
            #[allow(unused_labels)]
            'D3: { // calculate q
                let mut r: u128 = 0;
                let un_s2d: u128 = add128_64(mul128_64(BASE, un.digit(j + n)), un.digit(j + n - 1));
                let vn_ld: u128 = vn.digit(n - 1) as u128;
                q = un_s2d / vn_ld;
                r = un_s2d % vn_ld;
                log::info!("\tD3. Calculate q.");
                while q >= BASE ||
                    r < BASE &&
                        mul128_64(q, vn.digit(n - 2)) > add128_64(mul128(BASE, r), un.digit(j + n - 2)) {
                    q -= 1;
                    r += vn_ld;
                }
            }
            let mut t: i64 = 0;
            //
            #[allow(unused_labels)]
            'D4: {
                // multiply and subtract
                log::info!("\tD4. multiply and subtract");
                let mut k: u128 = 0;
                for i in 0..n {
                    let p: u128 = mul128_64(q, vn.digit(i));
                    let (t, c1) = sub128c(un.digit(i + j) as u128, p & BASE_MASK);
                    let t = t & BASE_MASK;
                    let (t, c2) = sub128c(t, k);
                    let t = t & BASE_MASK;
                    un.update(i + j, t as Digit);
                    let (k3, c3) = sub128c(p >> Digit::BITS, t >> 64);
                    k = k3 + c1 + c2 + c3;
                }
                t = sub64(un.digit(j + n), k as u64) as i64;
                un.update(j + n, t as u64);
            }
            //
            #[allow(unused_labels)]
            'D5: {
                quotient.update(j, q as Digit); // tentative quotient digit
            }
            //
            #[allow(unused_labels)]
            'D6: {
                // add back
                if t < 0 {
                    log::info!("\tD6. add-back");
                    quotient.dec(j);
                    let mut k: Digit = 0;
                    for i in 0..n {
                        let mut t = add128_64(add128_64(un.digit(i + j) as u128, vn.digit(i)), k);
                        un.update(i + j, t as Digit);
                        k = (t >> Digit::BITS) as Digit;
                    }
                    un.update(j + n, add64(un.digit(j + n), k));
                }
            }
        }
        quotient.valid();
        (quotient, vn)
    }

    pub fn divide_by_digit(&self, d: Digit) -> (Int, Int) {
        assert!(d > 0);
        self.valid();
        const BASE: u128 = 1 << 64;

        let len = self.width();
        // note l = n-1 where n is the length of the dividend, and hence, of the result.
        // in the following, i ranges over n-1, n-2,...,0.
        // therefore, l-i ranges over (n-1)-(n-1), (n-1)-(n-2),...,(n-1-0) = 0,1,...n-1
        let mut q = Int::from_le_digits_vec(vec![0; len as usize]);
        let mut r: u128 = 0;
        {
            let l = q.width() as usize - 1;
            for (i, &nd) in self.mag.iter().rev().enumerate() {
                let tq = (r * BASE + nd as u128) / (d as u128);
                assert_eq!((tq >> 64) as u64, 0);
                r = (r * BASE + nd as u128) - (tq * d as u128);
                (q.mag[l - i], r) = (tq as Digit, r);
                assert_eq!(tq as u64, q.mag[l - i]);
            }
        }
        q.set_invariants();
        q.compact_mut();
        q.valid();
        (q, Int::new_digit(Digit::BITS, r as Digit))
    }

    fn clear_bit(&self, pos: u32) -> Int {
        self.valid();
        #[cfg(any(debug_assertions, release_test))]
        assert!(pos < self.bit_width(), "rut: clear_bit {pos} >= {:?}", self.bit_width());
        self.clone().clear_bit_mut(pos)
    }

    fn clear_bit_mut(mut self, pos: u32) -> Int {
        self.valid();
        #[cfg(any(debug_assertions, release_test))]
        assert!(pos < self.bit_width(), "clear_bit_mut {pos} >={:?}", self.bit_width());
        let (l, p) = (pos / Digit::BITS, pos % Digit::BITS);
        self.mag[l as usize] |= self.mag[l as usize] & !(1 << p);
        self.set_invariants();
        self.valid();
        self
    }

    pub fn test_bit(&self, pos: u32) -> bool {
        self.valid();
        #[cfg(any(debug_assertions, release_test))]
        assert!(pos < self.bit_width(), "rut: test_bit {pos} >= {:?}", self.bit_width());
        let (l, p) = (pos / Digit::BITS, pos % Digit::BITS);
        self.mag[l as usize] & (1 << p) != 0
    }

    fn set_bit(&self, pos: u32) -> Int {
        self.valid();
        #[cfg(any(debug_assertions, release_test))]
        debug_assert!(pos < self.bit_width(), "set_bit {pos} >= {:?}", self.bit_width());
        self.clone().set_bit_mut(pos)
    }

    fn shl(&self, count: u32) -> Int {
        self.valid();
        #[cfg(any(debug_assertions, release_test))]
        assert!(count <= self.bit_width(), "shl {count} > {}", self.bit_width());
        let mut r = self.clone();
        r.shl_mut(count);
        r
    }

    fn shl_mut(&mut self, count: u32) {
        let mut t = self;
        let cd = t.width() as usize;
        let mut count = count;
        // iteratively left-shift one digit (or iow, Digit::BITS) at a time.
        while count > 0 {
            // number of bits to be left-shifted, in this iteration, from each digit.
            let c = min(count, Digit::BITS);
            for i in (1..cd).rev() {
                // we need to be careful about the case where c == 64.
                t.mag[i] = ((t.mag[i] << (c - 1)) << 1) | (t.mag[i - 1] >> (Digit::BITS - c));
            }
            t.mag[0] = (t.mag[0] << (c - 1)) << 1;
            count -= c;
        }
        t.set_invariants();
        t.valid();
    }

    fn shl_expand(&self, count: u32) -> Int {
        self.valid();
        let mut r = Int::from_parts(self.bit_width() + count, self.mag.clone());
        r.shl_mut(count);
        r
    }

    // 0 <= count <= self.bit_len()
    fn shr(&self, count: u32) -> Int {
        self.valid();
        #[cfg(any(debug_assertions, release_test))]
        assert!(count <= self.bit_width(), "shr {count} > {}", self.bit_width());
        let mut t = self.clone();
        t.shr_mut(count);
        t
    }

    // nothing much happens when count = 0.
    fn shr_mut(&mut self, count: u32) {
        self.valid();
        let mut t = self;
        let mut count = count;
        // iteratively right-shift one digit (or iow, Digit::BITS) at a time.
        while count > 0 {
            let cd = t.width() as usize;
            // number of bits to be right-shifted, in this iteration, from each digit.
            let c = min(count, Digit::BITS);
            for k in 0..=cd as i32 - 2 { // if cd < 2, loop will not be executed
                let i = k as usize; // keep the compiler happy!
                // we need to be careful about the case where c == 64.
                t.mag[i] = (t.mag[i] >> (c - 1) >> 1) | (t.mag[i + 1] << Digit::BITS - c);
            }
            t.mag[cd - 1] = t.mag[cd - 1] >> (c - 1) >> 1;
            count -= c;
        }
        t.set_invariants();
        t.valid();
    }

    pub fn set_bit_mut(mut self, pos: u32) -> Int {
        self.valid();
        #[cfg(any(debug_assertions, release_test))]
        assert!(pos < self.bit_width(), "set_bit_mut {pos} >= {:?}", self.bit_width());
        let (l, p) = (pos / Digit::BITS, pos % Digit::BITS);
        self.mag[l as usize] |= 1 << p;
        self.set_invariants();
        self.valid();
        self
    }

    pub fn and(&self, n2: &Int) -> Int {
        self.valid();
        n2.valid();
        let mut res = Int::new(self.bit_width());
        self.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            res.mag[i] = x & y;
        });
        res.set_invariants();
        res.valid();
        res
    }

    fn and_mut(mut self, n2: &Int) -> Int {
        self.valid();
        n2.valid();
        for (i, &y) in n2.mag.iter().enumerate() {
            self.mag[i] &= y;
        }
        self.set_invariants();
        self.valid();
        self
    }

    fn or(&self, n2: &Int) -> Int {
        self.valid();
        n2.valid();
        let mut res = Int::new(self.bit_width());
        self.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            res.mag[i] = x | y;
        });
        res.set_invariants();
        res.valid();
        res
    }

    fn or_mut(mut self, n2: &Self) -> Self {
        self.valid();
        n2.valid();
        for (i, &y) in n2.mag.iter().enumerate() {
            self.mag[i] |= n2.mag[i];
        }
        self.set_invariants();
        self.valid();
        self
    }

    fn xor(&self, n2: &Self) -> Self {
        assert_eq!(self.width(), n2.width());
        assert!(self.sign >= 0 && n2.sign >= 0);
        self.valid();
        n2.valid();
        let mut res = Int::new(self.bit_width());
        self.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            res.mag[i] = x ^ y;
        });
        res.set_invariants();
        res.valid();
        res
    }

    fn xor_mut(mut self, n2: &Self) -> Self {
        self.valid();
        n2.valid();
        for (i, &y) in n2.mag.iter().enumerate() {
            self.mag[i] ^= n2.mag[i];
        }
        self.set_invariants();
        self.valid();
        self
    }

    pub fn hex_str(&self, fc: &IntStrCase, pad: &IntStrPadding) -> String {
        self.valid();
        let format = |v: Digit| -> String {
            match (fc, pad) {
                (IntStrCase::Lower, IntStrPadding::Minimal) => format!("{v:0x}"),
                (IntStrCase::Lower, IntStrPadding::Full) => format!("{v:016x}"),
                (IntStrCase::Upper, IntStrPadding::Minimal) => format!("{v:0X}"),
                (IntStrCase::Upper, IntStrPadding::Full) => format!("{v:016X}"),
            }
        };
        let mut s = String::new();
        for (i, &v) in self.mag.iter().rev().enumerate() {
            if !(i == 0 && *pad == IntStrPadding::Minimal && v == 0) {
                s.push_str(&format(v));
            }
        }
        "0x".to_string() + s.as_str()
    }

    pub fn dec_str(&self) -> String {
        "".to_string()
    }

    pub fn bin_str(&self) -> String {
        "".to_string()
    }

    pub fn oct_str(&self) -> String {
        "".to_string()
    }
}

// ensure standard library's debug_assert! macro runs only in non-release builds
// https://doc.rust-lang.org/reference/conditional-compilation.html#debug_assertions
// use the cfg attribute like this: #[cfg(not(debug_assertions))]

#[cfg(test)]
mod int_test {
    use std::cmp::PartialOrd;

    use crate::hex::le_vec_u64;
    use crate::init_logger;
    use crate::int::{Digit, Int, IntStrCase, IntStrPadding};

    fn init() {
        init_logger(true)
    }

    #[test]
    fn int_compact() {
        init();
        {
            let mut zero = Int::zero(16 * 1024);
            assert_eq!(zero.width(), 16 * 1024 / Digit::BITS);
            assert_eq!(zero.bit_width(), 16 * 1024);
            zero.compact_mut();
            assert_eq!(zero, Int::new(64));
            assert_eq!(zero.width(), 1);
            assert_eq!(zero.bit_width(), Digit::BITS);
        }
        {
            let n = Int::new_digit(8 * 1024, 3);
            assert_eq!(n.width(), 8 * 1024 / Digit::BITS);
            let m = n.compact();
            assert_eq!(m.width(), 1);
            assert_eq!(m.mag[0], 3);
            assert_eq!(n.width(), 8 * 1024 / Digit::BITS);
        }
    }

    #[test]
    fn div_knuth() {
        init();
        {
            // n = 1361129467683753854037965870464168361985
            // d = 92233720368547758081
            // n // d = 14757395258967641294 == 0xccccccccccccccce
            // let n = Int::from_le_digits_vec(vec![1, 10, 20], 1);
            let n = Int::from_le_digits_vec(vec![1, 10, 4]);
            let d = Int::from_le_digits_vec(vec![1, 5]);
            let (q, r) = n.div_knuth(&d);
            assert_eq!(q.mag, le_vec_u64("0x0000000000000000ccccccccccccccce"));
        }
    }

    #[test]
    fn int_div_by_digit() {
        init();
        // numerator < denominator
        {
            let n = Int::new_digit(128, 3);
            let d = Int::new_digit(128, 7);
            let (q, r) = n.divide(&d);
            assert_eq!(q.mag, [0]);
            assert_eq!(r.mag, [3]);
        }
        {
            let n = Int::new_digit(128, 0xFFFFFFFFFFFF);
            let d = Int::new_digit(128, 0xFFFFFFFFFFFFFFFF);
            let (q, r) = n.divide(&d);
            assert_eq!(q.mag, [0]);
            assert_eq!(r.mag, [0xFFFFFFFFFFFF]);
        }
        // numerator = denominator
        {
            let n = Int::new_digit(128, 60134725);
            let d = Int::new_digit(128, 60134725);
            let (q, r) = n.divide(&d);
            assert_eq!(q.mag, [1]);
            assert_eq!(r.mag, [0]);
        }
        {
            // 5 digit "random" number
            let n = Int::from_le_digits_vec(vec![100, 0x42, 0xFACEC0DE, 0xCAFEBABE, 0xFF1100001111FFFF]);
            let d = Int::from_le_digits_vec(vec![100, 0x42, 0xFACEC0DE, 0xCAFEBABE, 0xFF1100001111FFFF]);
            let (q, r) = n.divide(&d);
            assert_eq!(q.mag, [1]);
            assert_eq!(r.mag, [0]);
        }
        {
            // 0x10000000000000002000000000000000300000000000000040000000000000005
            // (5 + 4*2**64 + 3*2**128 + 2*2**192 + 1*2**256 + 0*2**320)
            // q = 0x97b425ed097b426 0000000000000000 1c71c71c71c71c71 ed097b425ed097b4
            let n = Int::from_le_digits_vec(vec![5, 4, 3, 2, 1, 0]);
            let d = Int::new_digit(64, 27);
            let (q, r) = n.divide(&d);
            assert_eq!(r.mag, [9]);
            assert_eq!(q.mag, [0xed097b425ed097b4, 0x1c71c71c71c71c71, 0x0000000000000000, 0x97b425ed097b426]);
        }

        // division by powers of 2 converts division into a shr operation
        {
            let n = Int::new_digit(128, 52871);
            let d = Int::new_digit(128, 1);
            let (q, r) = n.divide(&d);
            assert_eq!(q.mag, [52871]);
            assert_eq!(r.mag, [0]);
        }
        {
            let n = Int::new_digit(128, 99885287135);
            let d = Int::new_digit(128, 2);
            let (q, r) = n.divide(&d);
            assert_eq!(q.mag, [99885287135 >> 1]);
            assert_eq!(q.mag, [99885287135 / 2]);
            assert_eq!(r.mag, [99885287135 % 2]);

            let d = Int::new_digit(128, 1 << 63);
            let (q, r) = n.divide(&d);
            assert_eq!(q.mag, [99885287135 >> 63]);
            assert_eq!(q.mag, [99885287135 / (1 << 63)]);
            assert_eq!(r.mag, [99885287135]);

            let d = Int::new_digit(128, 1 << 33);
            let (q, r) = n.divide(&d);
            assert_eq!(q.mag, [99885287135 >> 33]);
            assert_eq!(q.mag, [99885287135 / (1 << 33)]);
            assert_eq!(r.mag, [99885287135 % (1 << 33)]);
        }
        {
            let n = Int::new_digit(128, 99885287135);
            let d = Int::new_digit(128, 4);
            let (q, r) = n.divide(&d);
            assert_eq!(q.mag, [99885287135 >> 2]);
            assert_eq!(q.mag, [99885287135 / 4]);
            assert_eq!(r.mag, [99885287135 % 4]);
        }
        {
            let n = Int::new_digit(128, 99885287135);
            let d = Int::new_digit(128, 1024);
            let (q, r) = n.divide(&d);
            assert_eq!(q.mag, [99885287135 >> 10]);
            assert_eq!(q.mag, [99885287135 / 1024]);
            assert_eq!(r.mag, [99885287135 % 1024]);
        }
        {
            let n = Int::new_digit(128, 52871);
            let d = Int::new_digit(128, 3);
            let (q, r) = n.divide(&d);
            assert_eq!(q.mag, [52871 / 3]);
            assert_eq!(r.mag, [52871 % 3]);
        }
        {
            let n = Int::new_digit(16 * 1024, 99999999999999999);
            let d = Int::new_digit(64, 7);
            let (q, r) = n.divide(&d);
            assert_eq!(q.mag, [99999999999999999 / 7]);
            assert_eq!(r.mag, [99999999999999999 % 7]);
        }
    }

    #[test]
    fn int1k_create() {
        init();
        let n1024 = Int::new(1024);
        assert_eq!(n1024.bit_width(), 1024);
        assert_eq!(n1024.sign, 0);
        assert_eq!(n1024.pos_lnzd, -1);
        assert_eq!(n1024.pos_lnzb, -1);
        let n256 = n1024.resize(256);
        assert_eq!(n256.bit_width(), 256);
        let n4096 = n256.resize(4096);
        assert_eq!(n4096.bit_width(), 4096);
        assert_eq!(n4096.width(), Int::width_of(4096));
        assert_eq!(n1024.bit_width(), 1024);
        assert_eq!(n1024.width(), Int::width_of(1024));
        assert_eq!(n256.bit_width(), 256);
        assert_eq!(n256.width(), Int::width_of(256));
    }

    #[test]
    fn int96_bit_ops() {
        init();
        let n96_x = Int::new_digit(96, 0xFFFF00000000FFFF);
        let n96_y = Int::new_digit(96, 0x00EE000011110000);
        let n96_zero = Int::zero(96);
        {
            assert_eq!(n96_x.bit_width(), 96);
            assert_eq!(n96_x.sign, 1);
            assert_eq!(n96_x.pos_lnzd, 0);
            assert_eq!(n96_x.pos_lnzb, 63);
        }
        {
            assert_eq!(n96_y.bit_width(), 96);
            assert_eq!(n96_y.sign, 1);
            assert_eq!(n96_y.pos_lnzd, 0);
            assert_eq!(n96_y.pos_lnzb, 55);
        }
        {
            assert_eq!(Int::xor(&n96_x, &n96_x), n96_zero);
            assert_eq!(Int::xor(&n96_x, &n96_y), Int::new_digit(96, 0xFF1100001111FFFF));
            assert_eq!(Int::or(&n96_x, &n96_y), Int::new_digit(96, 0xFFFF00001111FFFF));
            assert_eq!(Int::and(&n96_x, &n96_y), Int::new_digit(96, 0x00EE000000000000));
            assert_eq!(Int::and(&n96_x, &n96_x), Int::new_digit(96, 0xFFFF00000000FFFF));
        }
    }

    #[test]
    fn int512_cmp() {
        init();
        let n0 = Int::zero(512);
        let n1 = Int::one(512);
        let n2 = Int::new_digit(512, 2);
        let n65525 = Int::new_digit(512, Int::DIGIT_VAL_MAX as Digit);
        assert_eq!(n0, n0);
        assert_ne!(n1, n2);
        assert!(n1 < n2);
        assert!(n2 > n1);
        assert!(n2 > n0);
        assert!(!(n2 > n2) && !(n2 < n2));
        assert!(!(n2 > n65525));
        assert!(n2 < n65525);
        assert!(n65525 > n2);
    }

    #[test]
    fn comparison() {
        init();
        let n0 = Int::zero(512);
        assert_eq!(n0.bit_width(), 512);
        let n1 = Int::one(512);
        assert_eq!(n1.bit_width(), 512);
        let n2 = Int::new_digit(512, 2);
        assert_eq!(n1.bit_width(), n2.bit_width());
        let n77777 = Int::new_digit(64, 77777);
        let x = Int::new_digit(128, 77777);
        let n65525 = Int::new_digit(512, Int::DIGIT_VAL_MAX as Digit);
        assert!(n0.eq(&n0));
        assert!(n1.lt(&n2) && n1.eq(&n1));
        assert!(n1.le(&n2) && !n1.eq(&n2));
        assert!(n2.le(&n2) && n2.eq(&n2));
        assert!(n77777.ge(&n2) && n77777.eq(&n77777) && n77777.gt(&n2));
        assert!(n2.gt(&n1));
        assert!(n2.gt(&n0));
        assert!(!n2.gt(&n2) && !n2.lt(&n2));
        assert!(!n2.gt(&n65525));
        assert!(n65525.gt(&n2));
        assert!(x.ge(&n77777) && x.eq(&n77777) && x.eq(&x) && x.le(&x));

        assert!(x.eq(&n77777.min(&n65525)));
        assert!(x.lt(&n77777.max(&n65525)));
        assert!(n65525.eq(&n77777.max(&n65525)));
        assert!(n65525.ge(&n77777.max(&n65525)) &&
            n65525.ge(&n77777.min(&n65525)) &&
            n65525.eq(&n77777.max(&n65525)) &&
            x.eq(&n77777.min(&n65525)));
    }

    #[test]
    fn nat4k_set_bit() {
        init();
        let n1 = Int::one(4096);
        assert!(n1.bit_width() >= 4096);
        assert!(n1.test_bit(0));
        assert!(!n1.test_bit(1));
        assert!(!n1.test_bit(4095));

        let n2p4095 = n1.set_bit(4095);
        assert!(n2p4095.bit_width() >= 4096);
        assert!(n2p4095.test_bit(4095));
        assert!(n2p4095.test_bit(0));
        assert!(!n2p4095.test_bit(1));
        assert!(!n2p4095.test_bit(4094));
    }

    #[test]
    fn int_from_parts() {
        let size = 8_usize;
        let val = 1; //Digit::MAX >> Digit::BITS / 4;
        let mag: Vec<Digit> = vec![val; size];

        if Digit::BITS as usize * size == 512usize
        {
            let nat = Int::from_parts(512, mag.clone());
            assert_eq!(nat.mag[0..size], vec![val; size])
        }

        if Digit::BITS as usize * size == 256usize
        {
            let nat = Int::from_parts(256, mag.clone());
            assert_eq!(nat.mag, vec![val; size])
        }

        {
            let nat = Int::from_parts(Digit::BITS * mag.len() as u32, mag.clone());
            assert_eq!(nat.mag, vec![val; size])
        }
        // new number's size > mag.len()
        {
            let n = Int::from_parts(4096, mag.clone());
            assert_eq!(n.bit_width(), 4096);
            assert_eq!(n.width(), Int::width_of(4096));
            assert_eq!(&n.mag[0..mag.len()], vec![val; mag.len()])
        }
    }

    #[test]
    fn hex_64digit() {
        {
            let n96_x = Int::new_digit(96, 0xEEEE000011110000);
            assert_eq!(n96_x.hex_str(&IntStrCase::Upper, &IntStrPadding::Full), "0x0000000000000000EEEE000011110000");
            let n96_x = n96_x.set_bit_mut(95);
            assert_eq!(n96_x.hex_str(&IntStrCase::Upper, &IntStrPadding::Full), "0x0000000080000000EEEE000011110000");
            let n96_x = n96_x.set_bit_mut(94);
            assert_eq!(n96_x.hex_str(&IntStrCase::Lower, &IntStrPadding::Full), "0x00000000c0000000eeee000011110000".to_lowercase());
            assert_eq!(n96_x.hex_str(&IntStrCase::Lower, &IntStrPadding::Minimal), "0xc0000000eeee000011110000");
            assert_eq!(n96_x.hex_str(&IntStrCase::Lower, &IntStrPadding::Minimal), "0xc0000000eeee000011110000");
        }
        {
            let mut n64_x = Int::new_digit(64, 0xEEEE000011110000);
            assert_eq!(n64_x.hex_str(&IntStrCase::Lower, &IntStrPadding::Minimal), "0xeeee000011110000");
            assert_eq!(n64_x.hex_str(&IntStrCase::Upper, &IntStrPadding::Full), "0xEEEE000011110000");
            assert_eq!(n64_x.hex_str(&IntStrCase::Upper, &IntStrPadding::Minimal), "0xEEEE000011110000");
        }
    }

    #[test]
    fn int_mul_largest_128_val() {
        {
            let x256 = Int::from_le_digits_with_capacity(128, vec![0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF]);
            let y128 = Int::new_digit(64, 0);
            let prod_mul = Int::multiply(&x256, &y128);
            assert_eq!(prod_mul.mag, [0, 0, 0]);
            let prod_mul_karatsuba = x256.mul_karatsuba(&y128);
            assert_eq!(prod_mul_karatsuba.mag[0..prod_mul.width() as usize], [0, 0, 0]);
        }
        {
            let x128 = Int::from_le_digits_with_capacity(128, vec![7, 8]);
            let y128 = Int::new_digit(64, 1);
            let prod_mul = Int::multiply(&x128, &y128);
            assert_eq!(prod_mul.mag, [7, 8, 0]);
            let prod_mul_karatsuba = x128.mul_karatsuba(&y128);
            assert_eq!(prod_mul_karatsuba.mag[0..prod_mul.width() as usize], [7, 8, 0]);
        }
        {
            let x128 = Int::from_le_digits_with_capacity(129, vec![0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF]);
            let y128 = Int::new_digit(64, 2);
            let prod_mul = Int::multiply(&x128, &y128);
            assert_eq!(prod_mul.mag[0..3], [0xfffffffffffffffe, 0xffffffffffffffff, 1]);
            let prod_mul_karatsuba = &x128.mul_karatsuba(&y128);
            assert_eq!(prod_mul_karatsuba.mag[0..3], [0xfffffffffffffffe, 0xffffffffffffffff, 1]);
        }
    }

    #[test]
    fn int_karatsuba_mul_128() {
        {
            let x128 = Int::new_digit(128, 7);
            let y128 = Int::new_digit(128, 3);
            let prod = x128.mul_karatsuba(&y128);
            assert_eq!(prod.mag, [21, 0, 0, 0]);
            let prod_book = x128.mul_karatsuba(&y128);
            assert_eq!(prod_book.mag[0..4], [21, 0, 0, 0]);
        }
        {
            let x128 = Int::new_digit(128, 0xFFFF000000050003);
            let y128 = Int::new_digit(128, 1);
            let prod = x128.mul_karatsuba(&y128);
            assert_eq!(prod.mag, [0xFFFF000000050003, 0, 0, 0]);
            let prod_book = x128.mul_karatsuba(&y128);
            assert_eq!(prod_book.mag[0..4], [0xFFFF000000050003, 0, 0, 0]);
        }
        {
            let x128 = Int::new_digit(128, 0xFFFF000000050003);
            let y128 = Int::new_digit(128, 2);
            let prod = x128.mul_karatsuba(&y128);
            assert_eq!(prod.mag, [0xFFFE0000000A0006, 1, 0, 0]);
            let prod_book = x128.mul_karatsuba(&y128);
            assert_eq!(prod_book.mag[0..4], [0xFFFE0000000A0006, 1, 0, 0]);
        }
        {
            let x128 = Int::new_digit(128, 0xFFFF000000050003);
            let y128 = Int::new_digit(128, 0xFFFFFFFF00000000);
            let prod = x128.mul_karatsuba(&y128);
            assert_eq!(prod.mag, [0xFFFAFFFD00000000, 0xFFFEFFFF00060002, 0, 0]);
            let prod_book = x128.mul_karatsuba(&y128);
            assert_eq!(prod_book.mag[0..4], [0xFFFAFFFD00000000, 0xFFFEFFFF00060002, 0, 0]);
        }
    }

    #[test]
    fn int_448_mul_128_out_576() {
        init();
        let x448 = Int::from_le_digits_vec(
            vec![
                0xFFFFFFFFFFFFFFFF,
                0xFFFFFFFFFFFFFFFF,
                0xFFFFFFFFFFFFFFFF,
                0xAAAAAAAAEEEEEEEE,
                0x0000000099999999,
                0xBBBBBBBBEEEEEEEE,
                0xEEEEEEEEFFFFFFFF,
            ]);

        let y128 = Int::from_le_digits_vec(
            vec![
                0xFFFFFFFF9D8E1B2C,
                0xFFFFFFFFFFFFFFFF,
            ]);

        let expected576 = Int::from_le_digits_vec(
            vec![
                0x000000006271e4d4,
                0x0000000000000000,
                0xffffffffffffffff,
                0xe5bf7eb65fd64613,
                0xc4eedd1a5fd64613,
                0x3093e34db13719d6,
                0x5fd64614b3da1ae3,
                0xbbbbbbbb930d2a6c,
                0xeeeeeeeeffffffff,
            ]);

        let prod576_karatsuba = x448.mul_karatsuba(&y128);
        assert_eq!(prod576_karatsuba.width(), expected576.width());
        assert_eq!(prod576_karatsuba.mag, expected576.mag);

        let prod_base_case = Int::multiply(&x448, &y128);
        assert_eq!(prod_base_case.width(), expected576.width());
        assert_eq!(prod_base_case.mag[0..8], expected576.mag[0..8]);
    }

    #[test]
    fn int_mul_256() {
        {
            let n256_x = Int::new_digit(256, 0xFFFF000000050003);
            let n256_y = Int::new_digit(256, 1);
            let prod = n256_x.multiply(&n256_y);
            assert_eq!(prod.mag, [0xFFFF000000050003, 0, 0, 0, 0, 0, 0, 0]);
        }
        {
            let n256_x = Int::new_digit(256, 0xFFFF000000050003);
            let n256_y = Int::new_digit(256, 2);
            let prod = n256_x.multiply(&n256_y);
            assert_eq!(prod.mag, [0xfffe0000000a0006, 1, 0, 0, 0, 0, 0, 0]);
        }
        {
            let n256_x = Int::new_digit(256, 0xFFFF000000050003);
            let n256_y = Int::new_digit(256, 0xFFFF000000000000);
            let prod = n256_x.multiply(&n256_y);
            assert_eq!(prod.mag, [0xfffd000000000000, 0xfffe00010004fffd, 0, 0, 0, 0, 0, 0]);
        }
        {
            let n256_x = Int::new_digit(256, 0xFFFFFFFFFFFFFFFF);
            let n256_y = Int::new_digit(256, 0xFFFFFFFFFFFFFFFF);
            let prod = n256_x.multiply(&n256_y);
            assert_eq!(prod.mag, [1, 0xFFFFFFFFFFFFFFFE, 0, 0, 0, 0, 0, 0]);
        }
        {
            let mut n256_x = Int::from_le_digits_vec(vec![0xFFFFFFFFFFFFFFFF, 0xF, 0, 0]);
            let n256_y = Int::from_le_digits_vec(vec![0xFFFFFFFFFFFFFFFF, 0xF, 0, 0]);
            let prod = n256_x.multiply(&n256_y);
            assert_eq!(prod.mag, [1, 0xffffffffffffffe0, 0xff, 0, 0, 0, 0, 0]);
        }
        {
            let digits = vec![0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF];
            let n256_x = Int::from_le_digits_vec(digits.clone());
            let n256_y = Int::from_le_digits_vec(digits.clone());
            let prod = n256_x.multiply(&n256_y);
            assert_eq!(prod.mag, [
                1, 0, 0, 0,
                0xfffffffffffffffe, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff
            ]);
        }
    }

    #[test]
    fn int_mul_generic() {
        {
            let n256_x = Int::new_digit(256, 0xFFFF000000050003);
            let n512_y = Int::new_digit(2037, 0xFFFFFFFF00000000);
            let prod = n256_x.multiply(&n512_y);
            assert_eq!(prod.mag[0..2], [0xFFFAFFFD00000000, 0xFFFEFFFF00060002]);
            let cd = Int::width_of(2037 + 256);
            assert_eq!(prod.mag[2..], vec![0; cd as usize - 2]);
        }
    }

    #[test]
    fn int_shl() {
        {
            let x128 = Int::new_digit(128, 0xFFFF000000050003);
            assert_eq!(x128.width(), 2);
            assert_eq!(x128.mag, [0xFFFF000000050003, 0]);
            let n2 = x128.shl(64);
            assert_eq!(n2.width(), 2);
            assert_eq!(n2.mag, [0, 0xFFFF000000050003]);
            let n2 = n2.shl(64);
            assert_eq!(n2.mag, [0, 0]);
            let n2 = x128.shl(126);
            assert_eq!(n2.mag, [0, 0xFFFF000000050003 << 62]);
        }
        {
            let x128 = Int::from_le_digits_vec([1, 0, 0, 0].into());
            assert_eq!(x128.width(), 4);
            let n2 = x128.shl(254);
            assert_eq!(n2.mag, [0, 0, 0, 1 << 62]);
            let n2 = x128.shl(64);
            assert_eq!(n2.mag, [0, 1, 0, 0]);
            let n2 = x128.shl(128);
            assert_eq!(n2.mag, [0, 0, 1, 0]);
            let n2 = x128.shl(255);
            assert_eq!(n2.mag, [0, 0, 0, 0x8000000000000000]);
            let n2 = x128.shl(256);
            assert_eq!(n2.mag, [0, 0, 0, 0]);
            let n2 = x128.shl(128);
            assert_eq!(n2.mag, [0, 0, 1, 0]);
        }
    }

    #[test]
    fn int_shr() {
        {
            let x128 = Int::from_le_digits_vec(vec![0xFFFF000000050003, 0]);
            let n2 = x128.shr(8);
            assert_eq!(n2.mag, [0x00FFFF0000000500, 0]);
            let n2 = x128.shr(32);
            assert_eq!(n2.mag, [0x00000000FFFF0000, 0]);
            let n2 = n2.shr(64);
            assert_eq!(n2.mag, [0, 0]);
        }
        {
            let x128 = Int::from_le_digits_vec(vec![0xFFFF000000050003, 0x2222222222222222]);
            assert_eq!(x128.shr(0), x128);
            assert_eq!(x128.shr(1).mag, [0xFFFF000000050003 / 2, 0x2222222222222222 / 2]);
            assert_eq!(x128.shr(3).mag, [0x22 << 61 | 0xFFFF000000050003 >> 3, 0x2222222222222222 >> 3]);
            let mut n2 = x128.shr(8);
            assert_eq!(n2.mag, [0x22FFFF0000000500, 0x0022222222222222]);
            let mut n2 = n2.shr(56);
            assert_eq!(n2.mag, [0x2222222222222222, 0]);
        }
    }

    #[test]
    fn count_ones() {
        init();
        {
            let x = Int::new_digit(256, 0);
            let (c, lx) = x.count_ones();
            assert!(c == 0 && lx == 0);
        }
        {
            let x = Int::new_digit(256, 1);
            let (c, lx) = x.count_ones();
            assert!(c == 1 && lx == 0);
        }
        {
            let x = Int::new_digit(256, 1 << 63);
            let (c, lx) = x.count_ones();
            assert!(c == 1 && lx == 63);
        }
        {
            let x = Int::from_le_digits_vec(vec![0, 2]);
            let (c, lx) = x.count_ones();
            assert!(c == 1 && lx == 65);
        }
        {
            let x = Int::from_le_digits_vec(vec![0, 0xFF00000000000000]);
            let (c, lx) = x.count_ones();
            assert!(c == 8 && lx == 127);
        }
    }

    #[test]
    fn normalize() {
        init_logger(true);
        {
            let x = Int::from_le_digits_vec(vec![1; 1]);
            assert_eq!(x.clz(), 63);
            let xn = x.normalize(x.clz());
            assert_eq!(xn.mag, [1 << 63]);
        }
        {
            let x = Int::from_le_digits_vec(vec![0x8000000000000000; 1]);
            assert_eq!(x.clz(), 0);
            let xn = x.expand_normalize(x.clz());
            assert_eq!(xn.mag, [1 << 63, 0]);
        }
    }

    #[test]
    fn kat() {
        init_logger(true);
        struct Case(Vec<Digit>, Vec<Digit>, Vec<Digit>);
        let cases: Vec<Case> = vec![
            Case(vec![0x7899, 0xbcde], vec![0x789a, 0xbcde], vec![0]),
            Case(vec![0x0001, 0x8000], vec![0x7000, 0x4000], vec![0x0001]),
            Case(vec![0x7899, 0xbcde], vec![0x789a, 0xbcde], vec![0]),
            // one add-back required
            Case(vec![0x0003, 0x0000, 0x8000000000000000], vec!(0x0001, 0x0000, 0x2000000000000000), vec!(0x0003)),

            // one add-back required
            // 9223231299366420480 // 140737488355329 == 65534
            Case(vec![0, 0, 0x8000000000000000, 0x7fffffffffffffff],
                 vec![1, 0, 1 << 63],
                 vec![0xfffffffffffffffe, 0]),
            // add-back not at all required!
            // quotient = 0xa0163aae7699c9a3a530bb5b71b33987cc8f0638e61a1ac3b282203585116a
            Case(le_vec_u64("0x9c25b0d79a4e5ec90a08de24d9010f847409466ed05f54ad98fcc9496d598dca9624924e8e9a3ca1ee6c5ce34fa282f34b0cd55f28657deb3a4ef0e5c551a0"),
                 le_vec_u64("0xf9b336b9cd847da95e5d49f9aace97ff772bf258419b260dd39396bb325dbf5d"),
                 // pad three zeroes in MSB so the quotient gets a redundant zero digit in the MSB
                 le_vec_u64("0x000a0163aae7699c9a3a530bb5b71b33987cc8f0638e61a1ac3b282203585116a")),
            Case(le_vec_u64("0xb72406bf2b361790bfbf125e738ce735cecd1d529c25b0d79a4e5ec95f28657deb3a4ef0e5c551a0"),
                 le_vec_u64("0x6df4c2dfdc781bfc2dae1207156c1a6aea0a572180213c261b13"),
                 le_vec_u64("0x1aa637af3a1f551eb3dfc6f23a601")),
            /* python3
               import secrets
               u = secrets.token_hex(512)
               v = secrets.token_hex(128)
               u // v
             */
            Case(le_vec_u64("0xadc7011f7cb2c70717809dea93d4dfb886e041a33736532d216d1cdb3e1b8003fde8b82bb45c9cf122c72d495a3810912277f40970519d9e634ed426b3b2a867267a3d2b92794ce64238bef94b30fd35ed24cd09b5428f7ba1c92da4fc47850057e45f1a5ac7559d1db39d89bf0e67fcc6a4e407ec2de17863418886ac3b2d041420eb89cf38adf170692c28231d6d3dd63e51bfc7b6b16063ba59f34d82ccf9ac0f73cd7c413468837eea72c9b6d96994edcdd3095ca09929dbe1b322b626493b378519357d1871a1b496be64858d9ece5079f3a842e4ea1760994aed31788d772af9823f410c5dfa8a8ed4320106fc446dcbcd48fdcdc6c44f49944418b180b9b08253b81b922acbaf99baeb8a3ea453c3fe8273c14c6a5d33f2f206e667bb93b7f755c715fb14dcc751939a9801310eed0c80e14ac5900f3794d97a46e73a34f70f9b336b9cd847da95e5d49f9aace97ff772bf258419b260d1c3059ff238abb2370aa3a227d579d28bd04c4de2e749b826ae0ce8279a2df60de27c12ed869c6e7c74089feb4051873a151e6f7d050dcd51157f3d270b02a678274dd357b251a4102368411072c0ce475c46e754092aed0384d67045f54e9d9e1e71f70968a9526b6b21da2998458f3e22925ba104b0656cb786123ec58a11f4f03a4e311c9e73bf66e97067fdfeb5c98ea3e194dd3cd3cdbc893fd7db4501686e1d9fc16a"),
                 le_vec_u64("0xa5197e1da39f842701db6e381f154501702ef1dcb2ae5cdc8122a3782ee00e9a2b13e0468a26afa3921ff6f3e5c09269e46dc373c61d09de3bc76be60578402878bdafbf89cf8f2b579367a9b92fb975d4291fd929eb5a4c6736e6275a879fc7b0a1cb6215e586c0b6d75be72c2e80fde4c9dd974c764428a65273a66fbb8e0e"),
                 le_vec_u64("0x10d74a15716432f223505d3bde3a4c6b53bb2f730b8a959f18983805503f895fae7929756df468f1ed57e3544ffa851fcdd701d4ddf184c471696b99265e180205a454ecc1b24eeb76c4863be48314332f9ee41529187c16bd639937270ff0667048b7a6e197695c3ecbc82a107c2004d4801f79c60eb3b368dd2f72b6b3ed9ae9a8981a7843302cc4f5876a95adf3483c83d4d5ee10ca4a36e757100a08de24d9010f847409466ed05f54ad98fcc9496d598dca9624924e8e9a3ca1ee6c5ce34fa282f34b0cd5482a0038873eeb3c1a5b9b95dddf3cd62a876d5f4679652512113691038cc7173e68ec0751e2d807943aefbdb530786fcd7d387eb790b9db74be724334e7ba7ee1515343c73fbe1e50fb80c4601c67fc8242207a0cbe4d18f125b625c9a00f5b26d0cea96cb3aec5d7cc208f4c37a086b351db780a8b3af9ca15ce3d217f958eac02d4273ef4b9d5067ce6f3a8c2fda216fe09c7122eef94310678319b1575e050ebad4c700816e62ac4643bcaa1d9390340cab33a91f254218")),
        ];

        for case in cases {
            let num = Int::from_le_digits_vec(case.0);
            let d = Int::from_le_digits_vec(case.1);
            let (q, _) = num.div_knuth(&d);
            assert_eq!(q.mag, case.2);
        }
    }
}

#[cfg(not(debug_assertions))]
#[cfg(test)]
mod release {
    use crate::int::Int;

    #[test]
    fn nat4k_set_and_test_bit() {
        let n1 = Int::one(4096);
        assert_eq!(n1.bit_width(), 4096);
        assert!(n1.test_bit(0));
        assert!(!n1.test_bit(1));

        let n2p4095 = n1.set_bit(4095);
        assert_eq!(n2p4095.bit_width(), 4096);
        assert!(n2p4095.test_bit(4095));
        assert!(n2p4095.test_bit(0));
        assert!(!n2p4095.test_bit(1));
        assert!(!n2p4095.test_bit(4094));
        assert!(!n2p4095.test_bit(1600));
        assert!(n2p4095.gt(&n1));

        //assert!(!n2p4095.test_bit(4096));
        //assert!(!n2p4095.test_bit(16000));
    }
}
