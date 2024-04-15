use std::cmp::{max, min, PartialEq};
use std::env;
use std::fmt::Formatter;

use crate::{bits, Digit, Int, IntStrCase, IntStrPadding, U128};

impl std::fmt::Display for Int {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "bits:{:};digits:{:};sign:{:+};mag_hex:{:X?}", self.bits_len(), self.digits_len(), self.sign, self.mag)
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
            assert_eq!(self.mag.len() as u32, Int::exact_size(self.cb), "Int::check_invariant - announced Int size does not match with the magnitude");
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

    pub fn bits_len(&self) -> u32 {
        self.valid();
        self.cb
    }

    pub fn digits_len(&self) -> u32 {
        self.valid();
        self.mag.len() as u32
    }

    fn exact_size(bit_len: u32) -> u32 {
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
        let digits = vec![0; Int::exact_size(bit_len) as usize];
        let (pos_lnzd, pos_lnzb) = Self::pos_lnzd_lnzb(bit_len, &digits);
        assert_eq!(pos_lnzd, -1);
        assert_eq!(pos_lnzb, -1);
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

    fn set_invariants(&mut self, sign: i32) -> &Self {
        self.fix_invariants(sign)
    }

    fn fix_invariants(&mut self, sign: i32) -> &Self {
        let (pos_lnzd, pos_lnzb) = Self::pos_lnzd_lnzb(self.cb, &self.mag);
        self.pos_lnzd = pos_lnzd;
        self.pos_lnzb = pos_lnzb;
        if pos_lnzd == -1 {
            assert_eq!(pos_lnzb, -1);
            self.sign = 0;
        } else {
            self.sign = Self::sign_of(sign);
        }
        self.valid();
        self
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
                return ((mag.len() - 1) as i32, (bits::len_binary_digit(ld) - 1) as i32)
            }
        }
        // The leading digit is zero. So we walk the others digits (from MSB to LSB).
        for (i, &d) in rit.enumerate() {
            if d > 0 { // check the full width of the digit
                return ((mag.len() - i - 2) as i32, (bits::len_binary_digit(d) - 1) as i32)
            }
        }
        // Every digit is a zero in this Int.
        (-1, -1)
    }

    pub fn new_from_parts(bit_len: u32, mag: Vec<Digit>, sign: i32) -> Self {
        let bl = min(max(bit_len, Int::BIT_LEN_MIN), Int::BIT_LEN_MAX);
        let mut res = Int::new(bl);
        for (d, s) in res.mag.iter_mut().zip(mag.iter()) {
            *d = *s;
        }
        res.fix_invariants(sign);
        res
    }

    pub fn new_digit(bit_len: u32, val: Digit) -> Self {
        let mut res = Self::new(bit_len);
        res.mag[0] = val;
        res.fix_invariants(1);
        res.valid();
        res
    }

    pub fn digit_value(&self) -> (bool, Digit) {
        self.valid();
        if self.mag[0] > 0 && // the least-significant digit is non-zero, and
            // either it is a single digit int or the rest of the digits are all zeros
            (self.digits_len() == 1 || self.mag[1..].iter().eq([0].iter())) {
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
        for d in 1..self.digits_len() {
            r = r && d == 0
        }
        r
    }

    pub fn from_le_digits_vec(digits: Vec<Digit>, sign: i32) -> Self {
        #[cfg(any(debug_assertions, release_test))]
        assert!(digits.len() > 0 && digits.len() <= Int::DIGITS_MAX as usize);
        let bit_len: u32 = digits.len() as u32 * Digit::BITS;
        let res = Int::new_from_parts(bit_len, digits, sign);
        res.valid();
        res
    }

    // number of bits of magnitude may be less than the bit_len
    pub fn from_le_digits_with_capacity(bit_len: u32, digits: Vec<Digit>, sign: i32) -> Self {
        #[cfg(any(debug_assertions, release_test))]
        assert!(digits.len() > 0 && digits.len() <= Int::DIGITS_MAX as usize,
                "from_le_digits_with_capacity - too few or too many digits ({}) in the number", digits.len());
        assert!(Self::exact_size(bit_len) as usize >= digits.len(),
                "from_le_digits_with_capacity - bit length capacity {} smaller than digits {}",
                Self::exact_size(bit_len), digits.len());
        let res = Int::new_from_parts(bit_len, digits, sign);
        res.valid();
        res
    }

    pub fn resize(&self, new_len: u32) -> Int {
        self.valid();
        let self_len = Int::exact_size(self.cb);
        let new_size = Int::exact_size(new_len) as usize;
        if self_len == new_len || new_len == 0 || new_len > Self::BIT_LEN_MAX {
            self.clone()
        } else if self.cb < new_len {
            // need more space to hold digits of a larger magnitude
            let mut lm = vec![0; new_size];
            for (dst, src) in lm.iter_mut().zip(&self.mag[0..]) {
                *dst = *src;
            }
            let larger_nat = Int::new_from_parts(new_len, lm, self.sign);
            larger_nat.valid();
            larger_nat
        } else {
            // shrink the size of the magnitude
            let mut sm = vec![0; new_size];
            // 'copy_from_slice' panics if the source and destination lengths are not equal
            sm.copy_from_slice(&self.mag[0..new_size]);
            let smaller_nat = Int::new_from_parts(new_len, sm, self.sign);
            // smaller_nat.fix_invariants(smaller_nat.sign);
            smaller_nat.valid();
            smaller_nat
        }
    }

    pub fn count_ones(&self) -> u32 {
        let mut c = 0;
        for d in self.mag.iter() {
            c += d.count_ones();
        }
        c
    }

    pub fn pow2(&self) -> bool {
        self.count_ones() == 1 && self.mag[0] != 1
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

    fn eq(&self, n2: &Self) -> bool {
        self.valid();
        let mut res = self.bits_len() == n2.bits_len();
        for (x, y) in self.mag.iter().zip(n2.mag.iter()) {
            res &= x == y;
        }
        res
    }

    fn lt(&self, n2: &Self) -> bool {
        self.valid();
        let (_, s) = Int::resize_sub(self, n2);
        s < 0
    }

    fn le(&self, n2: &Self) -> bool {
        self.valid();
        let (_, s) = Int::resize_sub(self, n2);
        s <= 0
    }

    fn gt(&self, n2: &Self) -> bool {
        self.valid();
        let (_, s) = Int::resize_sub(self, n2);
        s > 0
    }

    fn ge(&self, n2: &Self) -> bool {
        self.valid();
        let (_, s) = Int::resize_sub(self, n2);
        s >= 0
    }

    pub fn add(&self, n2: &Int) -> (Int, Digit) {
        let n1 = self;
        #[cfg(any(debug_assertions, release_test))]
        assert_eq!(n1.bits_len(), n2.bits_len(), "add {} >= {}", n1.bits_len(), n2.bits_len());
        n1.valid();
        n2.valid();
        let mut carry: Digit = 0;
        let mut mag = vec![0; Int::exact_size(n1.bits_len()) as usize];
        n1.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            (mag[i], carry) = bits::add_with_carry(x, y, carry);
        });
        let res = Int::new_from_parts(n1.bits_len(), mag, 1);
        res.valid();
        (res, carry)
    }

    pub fn sum(&self, n2: &Int) -> Int {
        self.add(&n2).0
    }

    pub fn resize_sum(&self, t: &Int) -> Int {
        let res_bit_len = max(self.bits_len(), t.bits_len());
        let r = if self.bits_len() < res_bit_len {
            Int::sum(&self.resize(res_bit_len), &t)
        } else if t.bits_len() < res_bit_len {
            Int::sum(self, &t.resize(res_bit_len))
        } else {
            Int::sum(self, t)
        };
        r
    }

    pub fn resize_add(&self, t: &Int) -> (Int, Digit) {
        let res_bit_len = max(self.bits_len(), t.bits_len());
        if self.bits_len() < res_bit_len {
            Int::add(&self.resize(res_bit_len), &t)
        } else if t.bits_len() < res_bit_len {
            Int::add(self, &t.resize(res_bit_len))
        } else {
            Int::add(self, t)
        }
    }

    pub fn resize_sub(s: &Int, t: &Int) -> (Int, i64) {
        let res_bit_len = max(s.bits_len(), t.bits_len());
        if s.bits_len() < res_bit_len {
            Int::sub(&s.resize(res_bit_len), t)
        } else if t.bits_len() < res_bit_len {
            Int::sub(s, &t.resize(res_bit_len))
        } else {
            Int::sub(s, t)
        }
    }

    pub fn resize_abs_sub(s: &Int, t: &Int) -> (Int, i32) {
        let res_bit_len = max(s.bits_len(), t.bits_len());
        if s.bits_len() < res_bit_len {
            Int::sub_abs(&s.resize(res_bit_len), t)
        } else if t.bits_len() < res_bit_len {
            Int::sub_abs(s, &t.resize(res_bit_len))
        } else {
            Int::sub_abs(s, t)
        }
    }

    pub fn sub(n1: &Int, n2: &Int) -> (Int, i64) {
        n1.valid();
        n2.valid();
        debug_assert!(n1.bits_len() == n2.bits_len(), "sub {} != {}", n1.bits_len(), n2.bits_len());
        #[cfg(release_test)]
        assert!(n1.bits_len() == n2.bits_len(), "rut: sub {} >= {}", n1.bits_len(), n2.bits_len());
        let mut borrow: Digit = 0;
        let mut mag_diff: Digit = 0; // will stay zero when x.mag == y.mag
        let mut mag = vec![0; Int::exact_size(n1.bits_len()) as usize];
        n1.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            let diff: Digit; // diff between each corresponding limbs of x and y
            (diff, borrow) = bits::sub_with_borrow(x, y, borrow);
            mag_diff |= diff;
            mag[i] = diff;
        });
        let d: i64 = match mag_diff {
            0 => 0,
            _ => 1
        };
        let res = Int::new_from_parts(n1.bits_len(), mag, 1);
        res.valid();
        (res, (-(borrow as i64)) | d)
    }

    // subtract two magnitudes. Indicate the sign too.
    pub fn sub_abs(&self, n2: &Int) -> (Int, i32) {
        let n1 = self;
        // log::info!("\tn1 = {n1}\n\tn2 = {n2}");
        n1.valid();
        n2.valid();
        debug_assert!(n1.bits_len() == n2.bits_len(), "sub_abs {} != {}", n1.bits_len(), n2.bits_len());
        #[cfg(release_test)]
        assert!(n1.bits_len() == n2.bits_len(), "rut: sub_abs {} >= {}", n1.bits_len(), n2.bits_len());
        let mut borrow: Digit = 0;
        let mut mag_diff: Digit = 0; // will stay zero when x.mag == y.mag
        let (n1, n2, sign) = n1.compare(&n2);
        let mut mag = vec![0; Int::exact_size(n1.bits_len()) as usize];
        n1.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            let diff: Digit; // diff between each corresponding limbs of x and y
            (diff, borrow) = bits::sub_with_borrow(x, y, borrow);
            mag_diff |= diff;
            mag[i] = diff;
        });
        let res = Int::new_from_parts(n1.bits_len(), mag, 1);
        res.valid();
        (res, sign)
    }

    // acc += n * x
    pub fn add_mul_row(&self, x: Digit, acc: &mut [Digit]) -> Digit {
        debug_assert_eq!(self.digits_len(), acc.len() as u32, "add_mul_row - length mismatch.");
        #[cfg(any(debug_assertions, release_test))]
        assert_eq!(self.digits_len(), acc.len() as u32, "add_mul_row - length mismatch.");
        let mut carry: Digit = 0;
        for (i, &a) in self.mag.iter().enumerate() {
            let a_mul_b: U128 = bits::mul64(a, x);
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
        prod.truncate(self.digits_len() + n2.digits_len(), self.sign * n2.sign);
        prod.valid();
        prod
    }

    pub fn multiply_base_case(n1: &Int, n2: &Int) -> Int {
        n1.valid();
        n2.valid();

        let prod_size = (n1.digits_len() + n2.digits_len()) as usize;
        debug_assert!(prod_size <= Int::DIGITS_MAX as usize,
                      "mul_base_case - product size {prod_size} exceeds Nat limit {}", Int::DIGITS_MAX);
        #[cfg(release_test)]
        if prod_size > Int::DIGITS_MAX as usize {
            assert!(prod_size <= Int::DIGITS_MAX as usize,
                    "mul_base_case - product size {prod_size} exceeds Nat limit {}", Int::DIGITS_MAX);
        }
        // allocate space for the the product accumulator.
        let mut acc: Vec<Digit> = vec![0; prod_size];
        for (i, &a) in n1.mag.iter().enumerate() {
            // clear carry when starting with a new row
            let mut carry: Digit = 0;
            carry = n2.add_mul_row(a, &mut acc[i..i + n2.digits_len() as usize]);
            // the carry must be added to the column 'right' of i + count_digits_in_n2
            acc[i + n2.digits_len() as usize] = carry;
        }
        let mut prod = Int::new_from_parts(n1.bits_len() + n2.bits_len(), acc, 1);
        prod.fix_invariants(1);
        prod.valid();
        prod
    }

    // Used in Karatsuba multiplication.
    // Split the digits into two blocks, so at best, each of 'blk_len' (or less) size
    // returns (lower_digits, upper_digits)
    fn split_digits(&self, num_digits: u32) -> (Int, Int) {
        let self_len = self.digits_len();
        let cb = num_digits * Digit::BITS; // count of bits required
        // log::info!("split_digits - len = {self_len}, blk_len = {blk_len}");
        if self_len > num_digits {
            // left and right blocks or the lower and upper halves, respectively.
            let (lb, ub) = self.mag.split_at(num_digits as usize);
            let vec_lb = Vec::<Digit>::from(lb);
            let vec_ub = Vec::<Digit>::from(ub);
            (Int::new_from_parts(cb, vec_lb, self.sign), Int::new_from_parts(cb, vec_ub, self.sign))
        } else {
            (self.clone(), Int::new(cb))
        }
    }

    pub fn multiply_karatsuba(n1: &Int, n2: &Int) -> Int {
        n1.valid();
        n2.valid();

        let n1_len = n1.digits_len();
        let n2_len = n2.digits_len();
        let k = (max(n1_len, n2_len) + 1) / 2;
        let (a0, a1) = n1.split_digits(k);
        let (b0, b1) = n2.split_digits(k);

        let c0 = a0.multiply(&b0);
        let c1 = a1.multiply(&b1);
        // log::info!("mul_karatsuba:\n\ta0 = {},\n\tb0 = {}\n\tc0 = {}", a0, b0, c0);
        // log::info!("mul_karatsuba:\n\ta1 = {},\n\tb1 = {}\n\tc1 = {}", a1, b1, c1);

        let (c2_a, sign_a) = Int::resize_abs_sub(&a0, &a1);
        let (c2_b, sign_b) = Int::resize_abs_sub(&b0, &b1);
        let c2: Int = c2_a.multiply(&c2_b);
        // log::info!("mul_karatsuba:\n\tc2_a = {c2_a},\n\tc2_b = {c2_b}\n\tc2 = {c2}");

        let base_pow_k = Int::new_digit(64 * k + 1, 0).set_bit_mut(64 * k);
        let base_pow_2k = Int::new_digit(64 * 2 * k + 1, 0).set_bit_mut(64 * 2 * k);
        let c1_mul_base_pow_2k = c1.mul(&base_pow_2k);
        let c0_plus_c1 = c0.resize_sum(&c1);
        //let (t1, _) = Int::sub(&c0.resize_sum(c0_plus_c1), &c2);
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

    fn truncate(&mut self, digits_len: u32, sign: i32) {
        self.cb = digits_len * Digit::BITS;
        self.mag.resize(digits_len as usize, 0);
        self.fix_invariants(sign);
        self.valid();
    }

    pub fn multiply(&self, n2: &Int) -> Int {
        let n1 = self;
        n1.valid();
        n2.valid();
        // debug_assert!(n1.bits_len() == n2.bits_len(), "mul {} != {}", n1.bits_len(), n2.bits_len());
        let xl = n1.digits_len();
        let yl = n2.digits_len();
        let mut prod = if xl < Int::KARATSUBA_MUL_THRESHOLD || yl < Int::KARATSUBA_MUL_THRESHOLD {
            // if xl < Nat::KARATSUBA_MUL_THRESHOLD - 18 || yl < Nat::KARATSUBA_MUL_THRESHOLD - 18 {
            Self::multiply_base_case(&n1, &n2)
        } else {
            Self::multiply_karatsuba(&n1, &n2)
        };
        prod.truncate(xl + yl, n1.sign * n2.sign);
        prod.valid();
        prod
    }

    pub fn div(&self, _n: &Int) -> Int {
        panic!("div - not implemented")
    }

    pub fn rem(&self, _n: &Int) -> Int {
        panic!("rem - not implemented")
    }

    pub fn compare<'a>(&'a self, t: &'a Int) -> (&Int, &Int, i32) {
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
        self.set_invariants(self.sign);
        self.valid();
    }

    pub fn divide(&self, divisor: &Int) -> (Int, Int) {
        let dividend = self;
        dividend.valid();
        divisor.valid();

        assert!(!divisor.is_zero(), "Int::divide - division by zero error");

        let (_, _, d) = dividend.compare(divisor);
        if d == 0 { // dividend == divisor
            log::info!("\t{dividend} == {divisor}");
            return (Int::one(Digit::BITS), Int::zero(Digit::BITS))
        }

        if d < 0 { // dividend < divisor
            log::info!("\t{dividend} < {divisor}");
            return (Int::zero(Digit::BITS), dividend.compact())
        }

        if let (true, digit) = divisor.digit_value() {
            return dividend.divide_by_digit(digit)
        }

        let nl = dividend.digits_len(); // count of digits in the dividend
        let dl = divisor.digits_len(); // count of digits in the divisor
        let (q, r): (Int, Int) =
            if nl < Int::BURNIKEL_ZIEGLER_DIV_THRESHOLD ||
                (nl - dl) < Int::BURNIKEL_ZIEGLER_DIV_OFFSET {
                Self::divide_knuth(&dividend, &divisor)
            } else {
                panic!("Burnikel-Ziegler division not implemented!")
            };

        q.valid();
        r.valid();
        (q, r)
    }

    pub fn divide_knuth(&self, divisor: &Int) -> (Int, Int) {
        Int::div_knuth(self, divisor)
    }

    // returns (quotient, remainder)
    pub fn div_knuth(dividend: &Int, divisor: &Int) -> (Int, Int) {
        log::info!("div_knuth - enter");
        dividend.valid();
        divisor.valid();
        let nl = dividend.digits_len();  // count of digits in the dividend
        let dl = divisor.digits_len();   // count of digits in the divisor
        log::info!("div_knuth - leave");
        (Int::zero((nl-dl+1) * Digit::BITS), Int::zero((nl-dl)*Digit::BITS))
    }

    pub fn divide_by_digit(&self, d: Digit) -> (Int, Int) {
        log::info!("divide by digit {d}");
        assert!(d > 0);
        self.valid();
        let num = self;

        let mut r: Digit = 0;
        let mut quotient = Int::new(num.bits_len());
        // notice l = n-1 where n is the length of the dividend, and hence, of the result.
        let l = quotient.digits_len() as usize - 1;
        // in the following, i ranges over n-1, n-2,...,0.
        // therefore, l-i ranges over (n-1)-(n-1), (n-1)-(n-2),...,(n-1-0) = 0,1,...n-1
        for (i, &nd) in num.mag.iter().rev().enumerate() {
            (quotient.mag[l-i], r) = bits::div64(r, nd, d);
        }
        quotient.set_invariants(self.sign);
        quotient.compact_mut();
        quotient.valid();
        (quotient, Int::new_digit(Digit::BITS, r))
    }

    fn clear_bit(&self, pos: u32) -> Int {
        self.valid();
        debug_assert!(pos < self.bits_len(), "clear_bit {pos:} >= {}", self.bits_len());
        #[cfg(release_test)]
        assert!(pos < self.bits_len(), "rut: clear_bit {pos} >= {:?}", self.bits_len());
        self.clone().clear_bit_mut(pos)
    }

    fn clear_bit_mut(mut self, pos: u32) -> Int {
        self.valid();
        debug_assert!(pos < self.bits_len(), "clear_bit_mut {pos} >={:?}", self.bits_len());
        let (l, p) = (pos / Digit::BITS, pos % Digit::BITS);
        #[cfg(release_test)]
        assert!(pos < self.bits_len(), "rut: clear_bit_mut {pos} >= {:?}", self.bits_len());
        self.mag[l as usize] |= self.mag[l as usize] & !(1 << p);
        self.fix_invariants(self.sign);
        self.valid();
        self
    }

    pub fn test_bit(&self, pos: u32) -> bool {
        self.valid();
        debug_assert!(pos < self.bits_len(), "test_bit {pos} >= {:?}", self.bits_len());
        #[cfg(release_test)]
        assert!(pos < self.bits_len(), "rut: test_bit {pos} >= {:?}", self.bits_len());
        let (l, p) = (pos / Digit::BITS, pos % Digit::BITS);
        self.mag[l as usize] & (1 << p) != 0
    }

    fn set_bit(&self, pos: u32) -> Int {
        self.valid();
        #[cfg(any(debug_assertions, release_test))]
        debug_assert!(pos < self.bits_len(), "set_bit {pos} >= {:?}", self.bits_len());
        self.clone().set_bit_mut(pos)
    }

    fn shl(&self, count: u32) -> Int {
        self.valid();
        #[cfg(any(debug_assertions, release_test))]
        assert!(count <= self.bits_len(), "shl {count} > {}", self.bits_len());
        let mut r = self.clone();
        let cd = r.digits_len() as usize;
        let mut count = count;
        // iteratively left-shift bits; each iteration can deal with only Digit::BITS at a time.
        while count > 0 {
            // number of bits to be lef-shifted, in this iteration, from each digit.
            let c = min(count, Digit::BITS);
            for i in (1..cd).rev() {
                // we need to be careful about the corner case where c == 64.
                r.mag[i] = (r.mag[i] << (c - 1) << 1) | (r.mag[i - 1] >> Digit::BITS - c);
            }
            r.mag[0] = r.mag[0] << (c - 1) << 1;
            count -= c;
        }
        r.fix_invariants(r.sign);
        r.valid();
        r
    }

    fn shl_expand(&self, count: u32) -> Int {
        log::info!("shl_expand - enter\n\tself  = {self}\n\tcount = {count}");
        self.valid();

        let mut r = Int::new_from_parts(self.bits_len() + count, self.mag.clone(), self.sign);
        let mut count = count;
        // iteratively left-shift bits; each iteration can deal with only Digit::BITS at a time.
        while count > 0 {
            // number of bits to be lef-shifted, in this iteration, from each digit.
            let c = min(count, Digit::BITS);
            for i in (1_usize..r.digits_len() as usize).rev() {
                // we need to be careful about the corner case where c == 64.
                let d = (r.mag[i] << (c - 1) << 1) | (r.mag[i - 1] >> Digit::BITS - c);
                r.mag[i] = d;
            }
            r.mag[0] = r.mag[0] << (c - 1) << 1;
            count -= c;
        }
        r.fix_invariants(r.sign);
        r.valid();
        log::info!("\tresult = {r}\nshl_expand - leave");
        r
    }

    pub fn set_bit_mut(mut self, pos: u32) -> Int {
        self.valid();
        #[cfg(any(debug_assertions, release_test))]
        assert!(pos < self.bits_len(), "set_bit_mut {pos} >= {:?}", self.bits_len());
        let (l, p) = (pos / Digit::BITS, pos % Digit::BITS);
        self.mag[l as usize] |= 1 << p;
        self.fix_invariants(self.sign);
        self.valid();
        self
    }

    pub fn and(&self, n2: &Int) -> Int {
        self.valid();
        n2.valid();
        let mut res = Int::new(self.bits_len());
        self.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            res.mag[i] = x & y;
        });
        res.fix_invariants(1);
        res.valid();
        res
    }

    fn and_mut(mut self, n2: &Int) -> Int {
        self.valid();
        n2.valid();
        for (i, &y) in n2.mag.iter().enumerate() {
            self.mag[i] &= y;
        }
        self.fix_invariants(1);
        self.valid();
        self
    }

    fn or(&self, n2: &Int) -> Int {
        self.valid();
        n2.valid();
        let mut res = Int::new(self.bits_len());
        self.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            res.mag[i] = x | y;
        });
        res.fix_invariants(1);
        res.valid();
        res
    }

    fn or_mut(mut self, n2: &Self) -> Self {
        self.valid();
        n2.valid();
        for (i, &y) in n2.mag.iter().enumerate() {
            self.mag[i] |= n2.mag[i];
        }
        self.fix_invariants(1);
        self.valid();
        self
    }

    fn xor(&self, n2: &Self) -> Self {
        assert_eq!(self.digits_len(), n2.digits_len());
        assert!(self.sign >= 0 && n2.sign >= 0);
        self.valid();
        n2.valid();
        let mut res = Int::new(self.bits_len());
        self.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            res.mag[i] = x ^ y;
        });
        res.fix_invariants(1);
        res.valid();
        res
    }

    fn xor_mut(mut self, n2: &Self) -> Self {
        self.valid();
        n2.valid();
        for (i, &y) in n2.mag.iter().enumerate() {
            self.mag[i] ^= n2.mag[i];
        }
        self.fix_invariants(1);
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
mod test {
    use std::cmp::PartialOrd;

    use crate::int::{Digit, Int, IntStrCase, IntStrPadding};

    fn init() {
        crate::init_logger(true)
    }

    #[test]
    fn int_compact() {
        init();
        {
            let mut zero = Int::zero(16*1024);
            assert_eq!(zero.digits_len(), 16*1024/Digit::BITS);
            assert_eq!(zero.bits_len(), 16*1024);
            zero.compact_mut();
            assert_eq!(zero, Int::new(64));
            assert_eq!(zero.digits_len(), 1);
            assert_eq!(zero.bits_len(), Digit::BITS);
        }
        {
            let n = Int::new_digit(8*1024, 3);
            assert_eq!(n.digits_len(), 8*1024/Digit::BITS);
            let m = n.compact();
            assert_eq!(m.digits_len(), 1);
            assert_eq!(m.mag[0], 3);
            assert_eq!(n.digits_len(), 8*1024/Digit::BITS);
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
            let n = Int::from_le_digits_vec(vec![100, 0x42, 0xFACEC0DE, 0xCAFEBABE, 0xFF1100001111FFFF], 1);
            let d = Int::from_le_digits_vec(vec![100, 0x42, 0xFACEC0DE, 0xCAFEBABE, 0xFF1100001111FFFF], 1);
            let (q, r) = n.divide(&d);
            assert_eq!(q.mag, [1]);
            assert_eq!(r.mag, [0]);
        }

        {
            let n = Int::new_digit(128, 52871);
            let d = Int::new_digit(128, 1);
            let (q, r) = n.divide(&d);
            assert_eq!(q.mag, [52871]);
            assert_eq!(r.mag, [0]);
        }
        {
            let n = Int::new_digit(128, 52871);
            let d = Int::new_digit(128, 3);
            let (q, r) = n.divide(&d);
            assert_eq!(q.mag, [52871/3]);
            assert_eq!(r.mag, [52871%3]);
        }
        {
            let n = Int::new_digit(16*1024, 99999999999999999);
            let d = Int::new_digit(64, 7);
            let (q, r) = n.divide(&d);
            assert_eq!(q.mag, [99999999999999999/7]);
            assert_eq!(r.mag, [99999999999999999%7]);
        }
    }

    #[test]
    fn int1k_create() {
        init();
        let n1024 = Int::new(1024);
        assert_eq!(n1024.bits_len(), 1024);
        assert_eq!(n1024.sign, 0);
        assert_eq!(n1024.pos_lnzd, -1);
        assert_eq!(n1024.pos_lnzb, -1);
        let n256 = n1024.resize(256);
        assert_eq!(n256.bits_len(), 256);
        let n4096 = n256.resize(4096);
        assert_eq!(n4096.bits_len(), 4096);
        assert_eq!(n4096.digits_len(), Int::exact_size(4096));
        assert_eq!(n1024.bits_len(), 1024);
        assert_eq!(n1024.digits_len(), Int::exact_size(1024));
        assert_eq!(n256.bits_len(), 256);
        assert_eq!(n256.digits_len(), Int::exact_size(256));
    }

    #[test]
    fn int96_bit_ops() {
        init();
        let n96_x = Int::new_digit(96, 0xFFFF00000000FFFF);
        let n96_y = Int::new_digit(96, 0x00EE000011110000);
        let n96_zero = Int::zero(96);
        {
            assert_eq!(n96_x.bits_len(), 96);
            assert_eq!(n96_x.sign, 1);
            assert_eq!(n96_x.pos_lnzd, 0);
            assert_eq!(n96_x.pos_lnzb, 63);
        }
        {
            assert_eq!(n96_y.bits_len(), 96);
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
    fn int512_sub() {
        init();
        let n0 = Int::zero(512);
        assert_eq!(n0.bits_len(), 512);
        let n1 = Int::one(512);
        assert_eq!(n1.bits_len(), 512);
        let n2 = Int::new_digit(512, 2);
        assert_eq!(n1.bits_len(), n2.bits_len());
        let n65525 = Int::new_digit(512, Int::DIGIT_VAL_MAX as Digit);
        assert!(n0.eq(&n0));
        assert!(n1.lt(&n2));
        assert!(n2.gt(&n1));
        assert!(n2.gt(&n0));
        assert!(!n2.gt(&n2) && !n2.lt(&n2));
        assert!(!n2.gt(&n65525));
        assert!(n65525.gt(&n2));
    }

    #[test]
    fn nat4k_set_bit() {
        init();
        let n1 = Int::one(4096);
        assert!(n1.bits_len() >= 4096);
        assert!(n1.test_bit(0));
        assert!(!n1.test_bit(1));
        assert!(!n1.test_bit(4095));

        let n2p4095 = n1.set_bit(4095);
        assert!(n2p4095.bits_len() >= 4096);
        assert!(n2p4095.test_bit(4095));
        assert!(n2p4095.test_bit(0));
        assert!(!n2p4095.test_bit(1));
        assert!(!n2p4095.test_bit(4094));
    }

    const BIT_LEN_128: u32 = 128;
    const BIT_LEN_256: u32 = 256;
    const BIT_LEN_512: u32 = 512;
    const BIT_LEN_1024: u32 = 1024;
    const BIT_LEN_4096: u32 = 4096;
    const BIT_LEN_16K: u32 = 16 * 1024;

    #[test]
    fn int_from_parts() {
        let size = 8_usize;
        let val = 1; //Digit::MAX >> Digit::BITS / 4;
        let mag: Vec<Digit> = vec![val; size];

        if Digit::BITS as usize * size == BIT_LEN_512 as usize
        {
            let nat = Int::new_from_parts(BIT_LEN_512, mag.clone(), 1);
            assert_eq!(nat.mag[0..size], vec![val; size])
        }

        if Digit::BITS as usize * size == BIT_LEN_256 as usize
        {
            let nat = Int::new_from_parts(256, mag.clone(), 1);
            assert_eq!(nat.mag, vec![val; size])
        }

        {
            let nat = Int::new_from_parts(Digit::BITS * mag.len() as u32, mag.clone(), 1);
            //assert_eq!(nat.mag, vec![val; size])
        }
        // new number's size > mag.len()
        {
            let n = Int::new_from_parts(4096, mag.clone(), 1);
            assert_eq!(n.bits_len(), 4096);
            assert_eq!(n.digits_len(), Int::exact_size(4096));
            assert_eq!(&n.mag[0..mag.len() as usize], vec![val; mag.len()])
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
            let x256 = Int::from_le_digits_with_capacity(128, vec![0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF], 1);
            let y128 = Int::new_digit(64, 0);
            let prod_mul = Int::multiply(&x256, &y128);
            assert_eq!(prod_mul.mag, [0, 0, 0]);
            let prod_mul_karatsuba = x256.mul_karatsuba(&y128);
            assert_eq!(prod_mul_karatsuba.mag[0..prod_mul.digits_len() as usize], [0, 0, 0]);
        }
        {
            let x128 = Int::from_le_digits_with_capacity(128, vec![7, 8], 1);
            let y128 = Int::new_digit(64, 1);
            let prod_mul = Int::multiply(&x128, &y128);
            assert_eq!(prod_mul.mag, [7, 8, 0]);
            let prod_mul_karatsuba = x128.mul_karatsuba(&y128);
            assert_eq!(prod_mul_karatsuba.mag[0..prod_mul.digits_len() as usize], [7, 8, 0]);
        }
        {
            let x128 = Int::from_le_digits_with_capacity(129, vec![0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF], 1);
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
            ], 1);

        let y128 = Int::from_le_digits_vec(
            vec![
                0xFFFFFFFF9D8E1B2C,
                0xFFFFFFFFFFFFFFFF,
            ], 1);

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
            ], 1);

        let prod576_karatsuba = x448.mul_karatsuba(&y128);
        assert_eq!(prod576_karatsuba.digits_len(), expected576.digits_len());
        assert_eq!(prod576_karatsuba.mag, expected576.mag);

        let prod_base_case = Int::multiply(&x448, &y128);
        assert_eq!(prod_base_case.digits_len(), expected576.digits_len());
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
            let mut n256_x = Int::from_le_digits_vec(vec![0xFFFFFFFFFFFFFFFF, 0xF, 0, 0], 1);
            let n256_y = Int::from_le_digits_vec(vec![0xFFFFFFFFFFFFFFFF, 0xF, 0, 0], 1);
            let prod = n256_x.multiply(&n256_y);
            assert_eq!(prod.mag, [1, 0xffffffffffffffe0, 0xff, 0, 0, 0, 0, 0]);
        }
        {
            let digits = vec![0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF];
            let n256_x = Int::from_le_digits_vec(digits.clone(), 1);
            let n256_y = Int::from_le_digits_vec(digits.clone(), 1);
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
            let cd = Int::exact_size(2037 + 256);
            assert_eq!(prod.mag[2..], vec![0; cd as usize - 2]);
        }
    }

    #[test]
    fn int_shl() {
        {
            let x128 = Int::new_digit(128, 0xFFFF000000050003);
            assert_eq!(x128.digits_len(), 2);
            assert_eq!(x128.mag, [0xFFFF000000050003, 0]);
            let n2 = x128.shl(64);
            assert_eq!(n2.digits_len(), 2);
            assert_eq!(n2.mag, [0, 0xFFFF000000050003]);
            let n2 = n2.shl(64);
            assert_eq!(n2.mag, [0, 0]);
            let n2 = x128.shl(126);
            assert_eq!(n2.mag, [0, 0xFFFF000000050003 << 62]);
        }
        {
            let x128 = Int::from_le_digits_vec([1, 0, 0, 0].into(), 1);
            assert_eq!(x128.digits_len(), 4);
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
}

#[cfg(not(debug_assertions))]
#[cfg(test)]
mod release {
    use crate::int::Int;

    #[test]
    fn nat4k_set_and_test_bit() {
        let n1 = Int::one(4096);
        assert_eq!(n1.bits_len(), 4096);
        assert!(n1.test_bit(0));
        assert!(!n1.test_bit(1));

        let n2p4095 = n1.set_bit(4095);
        assert_eq!(n2p4095.bits_len(), 4096);
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
