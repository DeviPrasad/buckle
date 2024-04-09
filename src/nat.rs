use std::cmp::{max, min, PartialEq};
use std::ops::Deref;

use crate::{bits, Digit, Int, IntStrCase, IntStrPadding, U128};

impl Int {
    pub const BITS_IN_NAT_LIMB: u32 = Digit::BITS;
    pub const BIT_LEN_MIN: u32 = 1 * Digit::BITS;
    // Nat magnitude has at least one limb
    pub const BIT_LEN_MAX: u32 = 16 * 1024;
    pub const DIGITS_MIN: u32 = Int::BIT_LEN_MIN / Digit::BITS;
    pub const DIGITS_MAX: u32 = Int::BIT_LEN_MAX / Digit::BITS;
    pub const DIGIT_VAL_MAX: u32 = (Digit::MAX - 1) as u32;

    pub const KARATSUBA_MUL_THRESHOLD: u32 = 20;
    pub const KARATSUBA_SQR_THRESHOLD: u32 = 40;

    fn sign_of(s: i32) -> i32 {
        if s > 0 {
            1
        } else if s < 0 {
            -1
        } else {
            0
        }
    }

    fn check_len(cb: u32) {
        debug_assert!(cb >= Int::BIT_LEN_MIN && cb <= Int::BIT_LEN_MAX, "Int::check_len - bad bit length");
        #[cfg(release_test)]
        assert!(cb >= Int::BIT_LEN_MIN && cb <= Int::BIT_LEN_MAX, "Int::check_len - bad bit length");
    }

    fn check_invariant(&self) {
        debug_assert!(self.cb >= Int::BIT_LEN_MIN && self.cb <= Int::BIT_LEN_MAX,
                      "Int::check_invariant - bad bit length");
        debug_assert!(self.mag.len() as u32 == Int::exact_size(self.cb),
                      "Int::check_invariant - announced Int size does not match with the magnitude");
        debug_assert!(self.sign == 0 || self.sign == 1 || self.sign == -1, "Int::check_invariant - invalid sign");
        debug_assert!((self.sign == 0 && (self.pos_lnzd == -1 || self.pos_lnzb == -1)) ||
                          (self.sign != 0
                              && (self.pos_lnzb >= 0 || self.pos_lnzb <= 63)
                              && (self.pos_lnzd >= 0 || self.pos_lnzd <= self.mag.len() as i32 - 1)),
                      "Int::check_invariant - invalid sign, lnzd, or lnzb values");
        let (pos_lnzd, pos_lnzb) = Int::pos_lnzd_lnzb(self.cb, &self.mag);
        debug_assert_eq!(pos_lnzd, self.pos_lnzd, "Int::check_invariant - bad pos_lnzd value");
        debug_assert_eq!(pos_lnzb, self.pos_lnzb, "Int::check_invariant - bad pos_lnzb value");
        #[cfg(release_test)]
        {
            assert!(self.cb >= Int::BIT_LEN_MIN && self.cb <= Int::BIT_LEN_MAX,
                    "Int::check_invariant - bad bit length");
            assert!(self.mag.len() as u32 == Int::exact_size(self.cb),
                    "Int::check_invariant - announced Int size does not match with the magnitude");
            assert!(self.sign == 0 || self.sign == 1 || self.sign == -1, "Int::check_invariant - invalid sign");
            assert!((self.sign == 0 && (self.pos_lnzd == -1 || self.pos_lnzb == -1)) ||
                        (self.sign != 0 && (self.pos_lnzb >= 0 || self.pos_lnzb <= 63)
                            && (self.pos_lnzd >= 0 || self.pos_lnzd <= self.mag.len() as i32 - 1)),
                    "Int::check_invariant - invalid sign, lnzd, or lnzb values");
            assert_eq!(pos_lnzd, self.pos_lnzd, "Int::check_invariant - bad pos_lnzd value");
            assert_eq!(pos_lnzb, self.pos_lnzb, "Int::check_invariant - bad pos_lnzb value");
        }
    }

    pub fn bits_len(&self) -> u32 {
        self.check_invariant();
        self.cb
    }

    pub fn digits_len(&self) -> u32 {
        self.check_invariant();
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
        n.check_invariant();
        n
    }

    fn fix_invariants(&mut self, sign: i32) -> &Self {
        let (pos_lnzd, pos_lnzb) = Self::pos_lnzd_lnzb(self.cb, &self.mag);
        self.pos_lnzd = pos_lnzd;
        self.pos_lnzb = pos_lnzb;
        if pos_lnzd == -1 {
            assert_eq!(pos_lnzb, -1);
            self.sign = Self::sign_of(0);
        } else {
            self.sign = Self::sign_of(sign);
        }
        self.check_invariant();
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
                return ((mag.len() - i - 1) as i32, (bits::len_binary_digit(d) - 1) as i32)
            }
        }
        // Every digit is a zero in this Int.
        (-1, -1)
    }

    pub fn new_from_parts(bit_len: u32, mag: Vec<Digit>, sign: i32) -> Self {
        let bl = min(max(bit_len, Int::BIT_LEN_MIN), Int::BIT_LEN_MAX);
        let mut nat = Int::new(bl);
        for (d, s) in nat.mag.iter_mut().zip(mag.iter()) {
            *d = *s;
        }
        nat.fix_invariants(sign);
        nat
    }

    pub fn new_digit(bit_len: u32, val: Digit) -> Self {
        let mut nat = Self::new(bit_len);
        nat.mag[0] = val;
        nat.fix_invariants(1);
        assert!((val > 0 && nat.pos_lnzd >= 0) || (val == 0 && nat.pos_lnzd == -1));
        nat
    }

    pub fn zero(bit_len: u32) -> Self {
        Self::new(bit_len)
    }

    pub fn one(bit_len: u32) -> Self {
        Self::new_digit(bit_len, 1)
    }

    pub fn from_le_digits(digits: Vec<Digit>, sign: i32) -> Self {
        debug_assert!(digits.len() > 0 && digits.len() <= Int::DIGITS_MAX as usize);
        #[cfg(release_test)]
        assert!(digits.len() > 0 && digits.len() <= Int::DIGITS_MAX as usize);
        let bit_len: u32 = digits.len() as u32 * Digit::BITS;
        let mut int = Int::new_from_parts(bit_len, digits, sign);
        int.fix_invariants(sign);
        int.check_invariant();
        int
    }

    pub fn resize(&self, new_len: u32) -> Int {
        self.check_invariant();
        let self_len = Int::exact_size(self.cb);
        let new_size = Int::exact_size(new_len) as usize;
        if self_len == new_len || new_len == 0 || new_len > Self::BIT_LEN_MAX {
            self.clone()
        } else if self.cb < new_len {
            /* grow */
            let mut larger_nat = Int::new(new_len);
            for (dst, src) in larger_nat.mag.iter_mut().zip(&self.mag[0..self_len as usize]) {
                *dst = *src;
            }
            larger_nat.fix_invariants(larger_nat.sign);
            larger_nat.check_invariant();
            assert_eq!(new_size, larger_nat.mag.len());
            larger_nat
        } else /* self.bits > new_len */ {
            /* shrink */
            let mut smaller_nat = Int::new(new_len);
            // 'copy_from_slice' panics if the source and destination lengths are not equal
            smaller_nat.mag.copy_from_slice(&self.mag[0..new_size]);
            smaller_nat.fix_invariants(smaller_nat.sign);
            smaller_nat.check_invariant();
            assert_eq!(new_size, smaller_nat.mag.len());
            smaller_nat
        }
    }

    pub fn expand_mut(mut self, new_bit_len: u32) -> Self {
        self.check_invariant();
        if self.cb < new_bit_len {
            self.cb = new_bit_len;
            self.mag.resize(Self::exact_size(new_bit_len) as usize, 0);
        }
        self.fix_invariants(self.sign);
        self.check_invariant();
        self
    }

    fn inverse(&self, _n: &Int) -> Int {
        panic!("inverse - no implementation")
    }

    fn sqrt(&self) -> Int {
        panic!("sqrt - no implementation")
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
        self.check_invariant();
        let mut res = self.bits_len() == n2.bits_len();
        for (x, y) in self.mag.iter().zip(n2.mag.iter()) {
            res &= x == y;
        }
        res
    }

    fn lt(&self, n2: &Self) -> bool {
        self.check_invariant();
        let (_, s) = Int::resize_and_sub(self, n2);
        s < 0
    }

    fn le(&self, n2: &Self) -> bool {
        self.check_invariant();
        let (_, s) = Int::resize_and_sub(self, n2);
        s <= 0
    }

    fn gt(&self, n2: &Self) -> bool {
        self.check_invariant();
        let (_, s) = Int::resize_and_sub(self, n2);
        s > 0
    }

    fn ge(&self, n2: &Self) -> bool {
        self.check_invariant();
        let (_, s) = Int::resize_and_sub(self, n2);
        s >= 0
    }

    pub fn add(&self, n2: &Int) -> (Int, Digit) {
        let n1 = self;
        n1.check_invariant();
        n2.check_invariant();
        // debug_assert!(n1.bits_len() == n2.bits_len(), "add {} != {}", n1.bits_len(), n2.bits_len());
        // #[cfg(release_test)]
        // assert!(n1.bits_len() == n2.bits_len(), "rut: add {} >= {}", n1.bits_len(), n2.bits_len());
        let mut carry: Digit = 0;
        let mut res = Int::new(n1.bits_len());
        n1.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            let limb_sum: Digit;
            (limb_sum, carry) = bits::add_with_carry(x, y, carry);
            res.mag[i] = limb_sum;
        });
        res.fix_invariants(1);
        res.check_invariant();
        (res, carry)
    }

    pub fn sum(&self, n2: &Int) -> Int {
        let n1 = self;
        n1.check_invariant();
        n2.check_invariant();
        debug_assert!(n1.bits_len() == n2.bits_len(), "sum {} != {}", n1.bits_len(), n2.bits_len());
        let res_msb_pos: usize = max(n1.bits_len(), n2.bits_len()) as usize;
        #[cfg(release_test)]
        assert!(n1.bits_len() == n2.bits_len(), "rut: sum {} >= {}", n1.bits_len(), n2.bits_len());
        let mut carry: Digit = 0;
        let mut res = Int::new(n1.bits_len()); // has provision for the potential carry
        n1.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            let limb_sum: Digit;
            (limb_sum, carry) = bits::add_with_carry(x, y, carry);
            res.mag[i] = limb_sum;
        });
        // TODO: what to do with the carry? Ignore overflow?
        // res.mag[res_msb_pos] = carry;
        res.fix_invariants(1);
        res.check_invariant();
        res
    }

    pub fn resize_and_add(&self, t: &Self) -> (Self, Digit) {
        let res_bit_len = max(self.bits_len(), t.bits_len());
        if self.bits_len() < res_bit_len {
            Self::add(&self.resize(res_bit_len), &t)
        } else if t.bits_len() < res_bit_len {
            Self::add(self, &t.resize(res_bit_len))
        } else {
            Self::add(self, t)
        }
    }

    pub fn resize_and_sub(s: &Int, t: &Int) -> (Self, i64) {
        let res_bit_len = max(s.bits_len(), t.bits_len());
        if s.bits_len() < res_bit_len {
            Self::sub(&s.resize(res_bit_len), t)
        } else if t.bits_len() < res_bit_len {
            Self::sub(s, &t.resize(res_bit_len))
        } else {
            Self::sub(s, t)
        }
    }

    pub fn sub(n1: &Int, n2: &Int) -> (Int, i64) {
        n1.check_invariant();
        n2.check_invariant();
        debug_assert!(n1.bits_len() == n2.bits_len(), "sub {} != {}", n1.bits_len(), n2.bits_len());
        #[cfg(release_test)]
        assert!(n1.bits_len() == n2.bits_len(), "rut: sub {} >= {}", n1.bits_len(), n2.bits_len());
        let mut borrow: Digit = 0;
        let mut mag_diff: Digit = 0; // will stay zero when x.mag == y.mag
        let mut res = Int::new(n1.bits_len());
        n1.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            let limb_diff: Digit; // diff between each corresponding limbs of x and y
            (limb_diff, borrow) = bits::sub_with_borrow(x, y, borrow);
            mag_diff |= limb_diff;
            res.mag[i] = limb_diff;
        });
        let d: i64 = match mag_diff {
            0 => 0,
            _ => 1
        };
        res.fix_invariants(1);
        res.check_invariant();
        (res, (-(borrow as i64)) | d)
    }

    pub fn minus(n1: &Int, n2: &Int) -> Int {
        n1.check_invariant();
        n2.check_invariant();
        debug_assert!(n1.bits_len() == n2.bits_len(), "sub {} != {}", n1.bits_len(), n2.bits_len());
        #[cfg(release_test)]
        assert!(n1.bits_len() == n2.bits_len(), "rut: sub {} >= {}", n1.bits_len(), n2.bits_len());
        let mut borrow: Digit = 0;
        let mut mag_diff: Digit = 0; // will stay zero when x.mag == y.mag
        let mut res = Int::new(n1.bits_len());
        n1.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            let limb_diff: Digit; // diff between each corresponding limbs of x and y
            (limb_diff, borrow) = bits::sub_with_borrow(x, y, borrow);
            mag_diff |= limb_diff;
            res.mag[i] = limb_diff;
        });
        res.fix_invariants(1);
        res.check_invariant();
        res
    }

    // acc += n * x
    pub fn add_mul_row(&self, x: Digit, acc: &mut [Digit]) -> Digit {
        debug_assert_eq!(self.mag.len(), acc.len(), "add_mul_row - length mismatch.");
        #[cfg(release_test)]
        assert_eq!(self.mag.len(), acc.len(), "add_mul_row - length mismatch.");
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
    //
    pub fn mul_base_case(n1: &Int, n2: &Int) -> Int {
        n1.check_invariant();
        n2.check_invariant();

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
        prod.check_invariant();
        prod
    }

    fn split_digits(&self, blk_len: u32) -> (Int, Int) {
        let self_len = self.digits_len();
        let nat_part_len = blk_len * Digit::BITS;
        if self_len > blk_len {
            let mag: &Vec<Digit> = &self.mag;
            let (uh, lh) = mag.split_at(blk_len as usize);
            let vec_uh = Vec::<Digit>::from(uh);
            let vec_lh = Vec::<Digit>::from(lh);
            (Int::new_from_parts(nat_part_len, vec_uh, 1), Int::new_from_parts(nat_part_len, vec_lh, 1))
        } else {
            (self.clone(), Int::new(nat_part_len))
        }
    }

    pub fn mul_karatsuba(n1: &Int, n2: &Int) -> Int {
        n1.check_invariant();
        n2.check_invariant();

        let n1_len = n1.digits_len();
        let n2_len = n2.digits_len();
        let mid = (max(n1_len, n2_len) + 1) / 2;
        let (xh, xl) = n1.split_digits(mid);
        let (yh, yl) = n2.split_digits(mid);

        let p1 = xh.mul(&yh);
        let p2 = xl.mul(&yl);

        // p3=(xh+xl)*(yh+yl)
        let p3: Int = xh.sum(&xl).mul(&yh.sum(&yl));

        // result = p1 * 2^(64*2*half) + (p3 - p1 - p2) * 2^(64*half) + p2
        /*let res: Int = p1.shl(64 * mid)
                         .sum(p3.minus(p1)
                                .minus(&p2))
                         .shl(64 * mid)
                         .sum(&p2);*/

        let prod_size = (n1.digits_len() + n2.digits_len()) as usize;
        debug_assert!(prod_size <= Int::DIGITS_MAX as usize,
                      "mul_karatsuba - product size {prod_size} exceeds Nat limit {}", Int::DIGITS_MAX);
        #[cfg(release_test)]
        if prod_size > Int::DIGITS_MAX as usize {
            assert!(prod_size <= Int::DIGITS_MAX as usize,
                    "mul_karatsuba - product size {prod_size} exceeds Nat limit {}", Int::DIGITS_MAX);
        }
        let mut prod = Int::new(0);
        prod.fix_invariants(1);
        prod.check_invariant();
        prod
    }

    pub fn mul(&self, n2: &Int) -> Int {
        let n1 = self;
        n1.check_invariant();
        n2.check_invariant();
        // debug_assert!(n1.bits_len() == n2.bits_len(), "mul {} != {}", n1.bits_len(), n2.bits_len());
        let xl = n1.digits_len();
        let yl = n2.digits_len();
        if xl < Int::KARATSUBA_MUL_THRESHOLD || yl < Int::KARATSUBA_MUL_THRESHOLD {
            // if xl < Nat::KARATSUBA_MUL_THRESHOLD - 18 || yl < Nat::KARATSUBA_MUL_THRESHOLD - 18 {
            Self::mul_base_case(&n1, &n2)
        } else {
            Self::mul_karatsuba(&n1, &n2)
        }
    }

    pub fn div(&self, _n: &Int) -> Int {
        panic!("div - no implementation")
    }

    pub fn rem(&self, _n: &Int) -> Int {
        panic!("rem - no implementation")
    }

    pub fn divide(&self, _n: &Int) -> (Int, Int) {
        panic!("divide - no implementation")
    }

    fn clear_bit(&self, pos: u32) -> Int {
        self.check_invariant();
        debug_assert!(pos < self.bits_len(), "clear_bit {pos:} >= {}", self.bits_len());
        #[cfg(release_test)]
        assert!(pos < self.bits_len(), "rut: clear_bit {pos} >= {:?}", self.bits_len());
        self.clone().clear_bit_mut(pos)
    }

    fn clear_bit_mut(mut self, pos: u32) -> Int {
        self.check_invariant();
        debug_assert!(pos < self.bits_len(), "clear_bit_mut {pos} >={:?}", self.bits_len());
        let (l, p) = (pos / Digit::BITS, pos % Digit::BITS);
        #[cfg(release_test)]
        assert!(pos < self.bits_len(), "rut: clear_bit_mut {pos} >= {:?}", self.bits_len());
        self.mag[l as usize] |= self.mag[l as usize] & !(1 << p);
        self.fix_invariants(self.sign);
        self.check_invariant();
        self
    }

    pub fn test_bit(&self, pos: u32) -> bool {
        self.check_invariant();
        debug_assert!(pos < self.bits_len(), "test_bit {pos} >= {:?}", self.bits_len());
        #[cfg(release_test)]
        assert!(pos < self.bits_len(), "rut: test_bit {pos} >= {:?}", self.bits_len());
        let (l, p) = (pos / Int::BITS_IN_NAT_LIMB, pos % Int::BITS_IN_NAT_LIMB);
        self.mag[l as usize] & (1 << p) != 0
    }

    fn set_bit(&self, pos: u32) -> Int {
        self.check_invariant();
        debug_assert!(pos < self.bits_len(), "set_bit {pos} >= {:?}", self.bits_len());
        #[cfg(release_test)]
        assert!(pos < self.bits_len(), "rut: set_bit {pos} >= {:?}", self.bits_len());
        self.clone().set_bit_mut(pos)
    }

    fn shl(&self, count: u32) -> Int {
        self.check_invariant();
        debug_assert!(count <= self.bits_len(), "shl {count} > {}", self.bits_len());
        #[cfg(release_test)]
        assert!(count < self.bits_len(), "rut: shl {count} >= {}", self.bits_len());
        let bits_count = self.bits_len() + count;
        let digits_count = Int::exact_size(bits_count);

        let mut mag = vec![0; digits_count as usize];
        for (d, s) in mag.iter_mut().rev().zip(self.mag.iter().rev()) {
            *d = *s;
        }
        let mut nat = Int::new_from_parts(bits_count, mag, 1);
        nat.fix_invariants(self.sign);
        nat.check_invariant();
        nat
    }

    pub fn set_bit_mut(mut self, pos: u32) -> Int {
        self.check_invariant();
        debug_assert!(pos < self.bits_len(), "set_bit_mut {pos} >= {:?}", self.bits_len());
        let (l, p) = (pos / Int::BITS_IN_NAT_LIMB, pos % Int::BITS_IN_NAT_LIMB);
        #[cfg(release_test)]
        assert!(pos < self.bits_len(), "rut: set_bit_mut {pos} >= {:?}", self.bits_len());
        self.mag[l as usize] |= 1 << p;
        self.fix_invariants(self.sign);
        self.check_invariant();
        self
    }

    pub fn and(&self, n2: &Int) -> Int {
        self.check_invariant();
        n2.check_invariant();
        let mut res = Int::new(self.bits_len());
        self.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            res.mag[i] = x & y;
        });
        res.fix_invariants(1);
        res.check_invariant();
        res
    }

    fn and_mut(mut self, n2: &Int) -> Int {
        self.check_invariant();
        n2.check_invariant();
        for (i, &y) in n2.mag.iter().enumerate() {
            self.mag[i] &= y;
        }
        self.fix_invariants(1);
        self.check_invariant();
        self
    }

    fn or(&self, n2: &Int) -> Int {
        self.check_invariant();
        n2.check_invariant();
        let mut res = Int::new(self.bits_len());
        self.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            res.mag[i] = x | y;
        });
        res.fix_invariants(1);
        res.check_invariant();
        res
    }

    fn or_mut(mut self, n2: &Self) -> Self {
        self.check_invariant();
        n2.check_invariant();
        for (i, &y) in n2.mag.iter().enumerate() {
            self.mag[i] |= n2.mag[i];
        }
        self.fix_invariants(1);
        self.check_invariant();
        self
    }

    fn xor(&self, n2: &Self) -> Self {
        assert_eq!(self.digits_len(), n2.digits_len());
        assert!(self.sign >= 0 && n2.sign >= 0);
        self.check_invariant();
        n2.check_invariant();
        let mut res = Int::new(self.bits_len());
        self.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            res.mag[i] = x ^ y;
        });
        res.fix_invariants(1);
        res.check_invariant();
        res
    }

    fn xor_mut(mut self, n2: &Self) -> Self {
        self.check_invariant();
        n2.check_invariant();
        for (i, &y) in n2.mag.iter().enumerate() {
            self.mag[i] ^= n2.mag[i];
        }
        self.fix_invariants(1);
        self.check_invariant();
        self
    }

    pub fn hex_str(&self, fc: &IntStrCase, pad: &IntStrPadding) -> String {
        self.check_invariant();
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
    use crate::nat::{Digit, Int, IntStrCase, IntStrPadding};

    #[test]
    fn nat1k_create() {
        let n1024 = Int::new(1024);
        assert_eq!(n1024.bits_len(), 1024);
        assert_eq!(n1024.sign, 0);
        assert_eq!(n1024.pos_lnzd, -1);
        assert_eq!(n1024.pos_lnzb, -1);
        let n256 = n1024.resize(256);
        assert_eq!(n256.bits_len(), 256);
        let n4096 = n256.resize(4096);
        assert_eq!(n4096.bits_len(), 4096);
        assert_eq!(n4096.mag.len(), Int::exact_size(4096) as usize);
        assert_eq!(n1024.bits_len(), 1024);
        assert_eq!(n1024.mag.len(), Int::exact_size(1024) as usize);
        assert_eq!(n256.bits_len(), 256);
        assert_eq!(n256.mag.len(), Int::exact_size(256) as usize);
    }

    #[test]
    fn nat96_bit_ops() {
        let n96_zero = Int::zero(96);
        let n96_x = Int::new_digit(96, 0xFFFF00000000FFFF);
        assert_eq!(n96_x.bits_len(), 96);
        assert_eq!(n96_x.sign, 1);
        assert_eq!(n96_x.pos_lnzd, 1);
        assert_eq!(n96_x.pos_lnzb, 63);

        let n96_y = Int::new_digit(96, 0x00EE000011110000);
        assert_eq!(n96_y.bits_len(), 96);
        assert_eq!(n96_y.sign, 1);
        assert_eq!(n96_y.pos_lnzd, 1);
        assert_eq!(n96_y.pos_lnzb, 55);

        assert_eq!(Int::xor(&n96_x, &n96_x), n96_zero);
        assert_eq!(Int::xor(&n96_x, &n96_y), Int::new_digit(96, 0xFF1100001111FFFF));
        assert_eq!(Int::or(&n96_x, &n96_y), Int::new_digit(96, 0xFFFF00001111FFFF));
        assert_eq!(Int::and(&n96_x, &n96_y), Int::new_digit(96, 0x00EE000000000000));
        assert_eq!(Int::and(&n96_x, &n96_x), Int::new_digit(96, 0xFFFF00000000FFFF));
    }

    #[test]
    fn nat512_cmp() {
        let n0 = Int::zero(512);
        assert_eq!(n0.bits_len(), 512);
        let n1 = Int::one(512);
        assert_eq!(n1.bits_len(), 512);
        /*
        let n2 = Int::new_single_digit(512, 2);
        assert_eq!(n1.bits_len(), n2.bits_len());
        let n65525 = Int::new_single_digit(512, Int::DIGIT_VAL_MAX as Digit);
        assert!(n0.eq(&n0));
        assert!(n1.lt(&n2));
        assert!(n2.gt(&n1));
        assert!(n2.gt(&n0));
        assert!(!n2.gt(&n2) && !n2.lt(&n2));
        assert!(!n2.gt(&n65525));
        assert!(n65525.gt(&n2));
         */
    }

    #[test]
    fn nat512_sub() {
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
    fn nat_from_parts() {
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
        // this would fail because requested size > magnitude's current size
        /*
        {
            let nat = Nat::new_from_parts(4096, mag.clone());
            assert_eq!(nat.bits_len(), 4096);
            assert_eq!(nat.nat_len(), 4096/64);
            assert_eq!(nat.mag, vec![0xFFFFFFFF_u64; 512])
        }
        */
    }

    #[test]
    fn hex_64digit() {
        {
            let n96_x = Int::new_digit(96, 0xEEEE000011110000);
            assert_eq!(n96_x.hex_str(&IntStrCase::Upper, &IntStrPadding::Full), "0x0000000000000000EEEE000011110000");
            ///*
            let n96_x = n96_x.set_bit_mut(95);
            assert_eq!(n96_x.hex_str(&IntStrCase::Upper, &IntStrPadding::Full), "0x0000000080000000EEEE000011110000");
            let n96_x = n96_x.set_bit_mut(94);
            assert_eq!(n96_x.hex_str(&IntStrCase::Lower, &IntStrPadding::Full), "0x00000000c0000000eeee000011110000".to_lowercase());
            assert_eq!(n96_x.hex_str(&IntStrCase::Lower, &IntStrPadding::Minimal), "0xc0000000eeee000011110000");
            assert_eq!(n96_x.hex_str(&IntStrCase::Lower, &IntStrPadding::Minimal), "0xc0000000eeee000011110000");
            //*/
        }
        {
            let mut n64_x = Int::new_digit(64, 0xEEEE000011110000);
            assert_eq!(n64_x.hex_str(&IntStrCase::Lower, &IntStrPadding::Minimal), "0xeeee000011110000");
            assert_eq!(n64_x.hex_str(&IntStrCase::Upper, &IntStrPadding::Full), "0xEEEE000011110000");
            assert_eq!(n64_x.hex_str(&IntStrCase::Upper, &IntStrPadding::Minimal), "0xEEEE000011110000");
        }
    }

    #[test]
    fn nat_mul_256() {
        {
            let n256_x = Int::new_digit(256, 0xFFFF000000050003);
            let n256_y = Int::new_digit(256, 1);
            let prod = n256_x.mul(&n256_y);
            assert_eq!(prod.mag, [0xFFFF000000050003, 0, 0, 0, 0, 0, 0, 0]);
        }
        {
            let n256_x = Int::new_digit(256, 0xFFFF000000050003);
            let n256_y = Int::new_digit(256, 2);
            let prod = n256_x.mul(&n256_y);
            assert_eq!(prod.mag, [0xfffe0000000a0006, 1, 0, 0, 0, 0, 0, 0]);
        }
        {
            let n256_x = Int::new_digit(256, 0xFFFF000000050003);
            let n256_y = Int::new_digit(256, 0xFFFF000000000000);
            let prod = n256_x.mul(&n256_y);
            assert_eq!(prod.mag, [0xfffd000000000000, 0xfffe00010004fffd, 0, 0, 0, 0, 0, 0]);
        }
        {
            let n256_x = Int::new_digit(256, 0xFFFFFFFFFFFFFFFF);
            let n256_y = Int::new_digit(256, 0xFFFFFFFFFFFFFFFF);
            let prod = n256_x.mul(&n256_y);
            assert_eq!(prod.mag, [1, 0xFFFFFFFFFFFFFFFE, 0, 0, 0, 0, 0, 0]);
        }
        {
            let mut n256_x = Int::from_le_digits(vec![0xFFFFFFFFFFFFFFFF, 0xF, 0, 0], 1);
            let n256_y = Int::from_le_digits(vec![0xFFFFFFFFFFFFFFFF, 0xF, 0, 0], 1);
            let prod = n256_x.mul(&n256_y);
            assert_eq!(prod.mag, [1, 0xffffffffffffffe0, 0xff, 0, 0, 0, 0, 0]);
        }
        {
            let digits = vec![0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF];
            let n256_x = Int::from_le_digits(digits.clone(), 1);
            let n256_y = Int::from_le_digits(digits.clone(), 1);
            let prod = n256_x.mul(&n256_y);
            assert_eq!(prod.mag, [
                1, 0, 0, 0,
                0xfffffffffffffffe, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff
            ]);
        }
    }

    #[test]
    fn nat_mul_generic() {
        {
            let n256_x = Int::new_digit(256, 0xFFFF000000050003);
            let n512_y = Int::new_digit(2037, 0xFFFFFFFF00000000);
            let prod = n256_x.mul(&n512_y);
            assert_eq!(prod.mag[0..2], [0xFFFAFFFD00000000, 0xFFFEFFFF00060002]);
            let cd = Int::exact_size(2037+256);
            assert_eq!(prod.mag[2..], vec![0; cd as usize - 2]);
        }
    }

    #[cfg(nat_32bit_digit)]
    #[test]
    fn hex_32digit() {
        {
            let n96_x = Int::new_digit(96, 0xEE001100);
            assert_eq!(n96_x.hex_str(&IntStrCase::Upper, &IntStrPadding::Full), "0x0000000000000000EE001100");
            let n96_x = n96_x.set_bit_mut(95);
            assert_eq!(n96_x.hex_str(&IntStrCase::Upper, &IntStrPadding::Full), "0x8000000000000000EE001100");
            let n96_x = n96_x.set_bit_mut(94);
            assert_eq!(n96_x.hex_str(&IntStrCase::Lower, &IntStrPadding::Full), "0xc000000000000000ee001100".to_lowercase());
            assert_eq!(n96_x.hex_str(&IntStrCase::Lower, &IntStrPadding::Minimal), "0xc00000000ee001100");
            assert_eq!(n96_x.hex_str(&IntStrCase::Lower, &IntStrPadding::Minimal), "0xc00000000ee001100");
        }
        {
            let mut n64_x = Int::new_digit(64, 0xEE001100);
            assert_eq!(n64_x.hex_str(&IntStrCase::Lower, &IntStrPadding::Minimal), "0x0ee001100");
            assert_eq!(n64_x.hex_str(&IntStrCase::Upper, &IntStrPadding::Minimal), "0x0EE001100");
            assert_eq!(n64_x.hex_str(&IntStrCase::Upper, &IntStrPadding::Full), "0x00000000EE001100");
        }
    }
}

#[cfg(not(debug_assertions))]
#[cfg(test)]
mod release {
    use crate::nat::Int;

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
