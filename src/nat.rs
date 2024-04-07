use std::cmp::{max, min};
use crate::{bits, Nat, NatDigit, NatStrCase, NatStrPadding, U128};

impl Nat {
    pub const BITS_IN_NAT_LIMB: u32 = NatDigit::BITS;
    pub const BIT_LEN_MIN: u32 = 1 * NatDigit::BITS;
    // Nat magnitude has at least one limb
    pub const BIT_LEN_MAX: u32 = 16 * 1024;
    pub const NAT_DIGITS_MIN: u32 = Nat::BIT_LEN_MIN / NatDigit::BITS;
    pub const NAT_DIGITS_MAX: u32 = Nat::BIT_LEN_MAX / NatDigit::BITS;
    pub const NAT_DIGIT_VAL_MAX: u32 = (NatDigit::MAX - 1) as u32;

    fn check_invariant(&self) {
        debug_assert!(self.bits >= Nat::BIT_LEN_MIN && self.bits <= Nat::BIT_LEN_MAX,
                      "check_invariant - bad bit length");
        debug_assert!(self.mag.len() as u32 == Nat::size(self.bits),
                      "check_invariant - announced nat len does not match the magnitude size");
        #[cfg(release_test)]
        {
            assert!(self.bits >= Nat::BIT_LEN_MIN && self.bits <= Nat::BIT_LEN_MAX,
                    "rut: check_invariant - bad bit length");
            assert!(self.mag.len() as u32 == Nat::size(self.bits),
                    "rut: check_invariant - announced nat len does not match the magnitude size");
        }
    }

    pub fn bits_len(&self) -> u32 {
        self.check_invariant();
        self.bits
    }

    pub fn digits_len(&self) -> u32 {
        self.check_invariant();
        self.mag.len() as u32
    }

    fn size(bit_len: u32) -> u32 {
        return
            (bit_len / Nat::BITS_IN_NAT_LIMB) +
                match bit_len % Nat::BITS_IN_NAT_LIMB {
                    0 => 0,
                    _ => 1
                }
    }

    pub fn new(bit_len: u32) -> Self {
        let bit_len = min(max(bit_len, Nat::BIT_LEN_MIN), Nat::BIT_LEN_MAX);
        let n = Nat {
            bits: bit_len,
            mag: vec![0; Nat::size(bit_len) as usize],
        };
        n.check_invariant();
        n
    }

    pub fn new_from_parts(bit_len: u32, mag: Vec<NatDigit>) -> Self {
        let bl = min(max(bit_len, Nat::BIT_LEN_MIN), Nat::BIT_LEN_MAX);
        let new_size = Nat::size(bl) as usize;
        let mag_size = mag.len();
        debug_assert!(mag_size >= new_size, "new_from_parts - bad request");
        #[cfg(release_test)]
        assert!(mag_size >= new_size, "rut - new_from_parts called with bad arguments");
        let nat =
            if new_size == mag_size {
                Nat {
                    bits: bit_len,
                    mag,
                }
            } else {
                let mut n = Nat::new(bl);
                n.mag.copy_from_slice(&mag[0..new_size]);
                n
            };
        nat.check_invariant();
        nat
    }

    pub fn zero(bit_len: u32) -> Self {
        Self::new(bit_len)
    }

    pub fn one(bit_len: u32) -> Self {
        Self::new_single_digit(bit_len, 1)
    }

    /*
    pub fn from_le(data: &[u64]) -> Self {
        debug_assert!(data.len() <= SIZE);
        Nat { bits: 0, mag: data.clone() }
    }
    */

    pub fn new_single_digit(bit_len: u32, val: NatDigit) -> Self {
        let mut n = Self::new(bit_len);
        n.mag[0] = val;
        n.check_invariant();
        n
    }

    pub fn resize(&self, new_len: u32) -> Nat {
        self.check_invariant();
        let self_len = Nat::size(self.bits);
        let new_size = Nat::size(new_len) as usize;
        if self_len == new_len || new_len == 0 || new_len > Self::BIT_LEN_MAX {
            self.clone()
        } else if self.bits < new_len {
            /* grow */
            let mut larger_nat = Nat::new(new_len);
            for (dst, src) in larger_nat.mag.iter_mut().zip(&self.mag[0..self_len as usize]) {
                *dst = *src;
            }
            larger_nat.check_invariant();
            assert_eq!(new_size, larger_nat.mag.len());
            larger_nat
        } else /* self.bits > new_len */ {
            /* shrink */
            let mut smaller_nat = Nat::new(new_len);
            // 'copy_from_slice' panics if the source and destination lengths are not equal
            smaller_nat.mag.copy_from_slice(&self.mag[0..new_size]);
            smaller_nat.check_invariant();
            assert_eq!(new_size, smaller_nat.mag.len());
            smaller_nat
        }
    }

    pub fn expand_mut(mut self, new_bit_len: u32) -> Self {
        self.check_invariant();
        if self.bits < new_bit_len {
            self.bits = new_bit_len;
            self.mag.resize(Self::size(new_bit_len) as usize, 0);
        }
        self.check_invariant();
        self
    }

    fn inverse(&self, _n: &Nat) -> Nat {
        panic!("inverse - no implementation")
    }

    fn sqrt(&self) -> Nat {
        panic!("sqrt - no implementation")
    }

    fn min(&self, n2: &Self) -> Nat {
        if self.lt(&n2) {
            self.clone()
        } else {
            n2.clone()
        }
    }

    fn max(&self, n2: &Nat) -> Nat {
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
        let (_, s) = Nat::resize_and_sub(self, n2);
        s < 0
    }

    fn le(&self, n2: &Self) -> bool {
        self.check_invariant();
        let (_, s) = Nat::resize_and_sub(self, n2);
        s <= 0
    }

    fn gt(&self, n2: &Self) -> bool {
        self.check_invariant();
        let (_, s) = Nat::resize_and_sub(self, n2);
        s > 0
    }

    fn ge(&self, n2: &Self) -> bool {
        self.check_invariant();
        let (_, s) = Nat::resize_and_sub(self, n2);
        s >= 0
    }

    pub fn add(n1: &Nat, n2: &Nat) -> (Nat, NatDigit) {
        n1.check_invariant();
        n2.check_invariant();
        debug_assert!(n1.bits_len() == n2.bits_len(), "add {} != {}", n1.bits_len(), n2.bits_len());
        #[cfg(release_test)]
        assert!(n1.bits_len() == n2.bits_len(), "rut: add {} >= {}", n1.bits_len(), n2.bits_len());
        let mut carry: NatDigit = 0;
        let mut res = Nat::new(n1.bits_len());
        n1.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            let limb_sum: NatDigit;
            (limb_sum, carry) = bits::add_with_carry(x, y, carry);
            res.mag[i] = limb_sum;
        });
        res.check_invariant();
        (res, carry)
    }

    pub fn resize_and_add(&self, t: &Self) -> (Self, NatDigit) {
        let res_bit_len = max(self.bits_len(), t.bits_len());
        if self.bits_len() < res_bit_len {
            Self::add(&self.resize(res_bit_len), &t)
        } else if t.bits_len() < res_bit_len {
            Self::add(self, &t.resize(res_bit_len))
        } else {
            Self::add(self, t)
        }
    }

    pub fn resize_and_sub(s: &Nat, t: &Nat) -> (Self, i64) {
        let res_bit_len = max(s.bits_len(), t.bits_len());
        if s.bits_len() < res_bit_len {
            Self::sub(&s.resize(res_bit_len), t)
        } else if t.bits_len() < res_bit_len {
            Self::sub(s, &t.resize(res_bit_len))
        } else {
            Self::sub(s, t)
        }
    }

    pub fn sub(n1: &Nat, n2: &Nat) -> (Nat, i64) {
        n1.check_invariant();
        n2.check_invariant();
        debug_assert!(n1.bits_len() == n2.bits_len(), "sub {} != {}", n1.bits_len(), n2.bits_len());
        #[cfg(release_test)]
        assert!(n1.bits_len() == n2.bits_len(), "rut: sub {} >= {}", n1.bits_len(), n2.bits_len());
        let mut borrow: NatDigit = 0;
        let mut mag_diff: NatDigit = 0; // will stay zero when x.mag == y.mag
        let mut res = Nat::new(n1.bits_len());
        n1.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            let limb_diff: NatDigit; // diff between each corresponding limbs of x and y
            (limb_diff, borrow) = bits::sub_with_borrow(x, y, borrow);
            mag_diff |= limb_diff;
            res.mag[i] = limb_diff;
        });
        let d: i64 = match mag_diff {
            0 => 0,
            _ => 1
        };
        res.check_invariant();
        (res, (-(borrow as i64)) | d)
    }

    // acc += n * x
    pub fn add_mul_row(&self, x: NatDigit, acc: &mut [NatDigit]) -> NatDigit {
        debug_assert_eq!(self.mag.len(), acc.len(), "add_mul_row - length mismatch.");
        #[cfg(release_test)]
        assert_eq!(self.mag.len(), acc.len(), "add_mul_row - length mismatch.");
        let mut carry: NatDigit = 0;
        for (i, &a) in self.mag.iter().enumerate() {
            let a_mul_b: U128 = bits::mul64(a, x);
            let column_sum: u128 = a_mul_b.lo as u128 + acc[i] as u128 + carry as u128;
            // use the lower 64 bits as the actual sum.
            acc[i] = column_sum as NatDigit;
            // a_mul_b and column_sum contribute the new carry
            carry = a_mul_b.hi + (column_sum >> 64) as NatDigit;
        }
        carry
    }

    // elementary school-book multiplication
    //
    pub fn mul(n1: &Nat, n2: &Nat) -> Nat {
        n1.check_invariant();
        n2.check_invariant();
        debug_assert!(n1.bits_len() == n2.bits_len(), "mul {} != {}", n1.bits_len(), n2.bits_len());

        let prod_size = (n1.digits_len() + n2.digits_len()) as usize;
        debug_assert!(prod_size <= Nat::NAT_DIGITS_MAX as usize,
                      "mul - product size {prod_size} exceeds Nat limit {}", Nat::NAT_DIGITS_MAX);
        #[cfg(release_test)]
        if prod_size > Nat::NAT_DIGITS_MAX as usize {
            assert!(prod_size <= Nat::NAT_DIGITS_MAX as usize,
                    "mul - product size {prod_size} exceeds Nat limit {}", Nat::NAT_DIGITS_MAX);
        }
        // allocate space for the the product accumulator.
        let mut acc: Vec<NatDigit> = vec![0; prod_size];
        for (i, &a) in n1.mag.iter().enumerate() {
            // clear carry when starting with a new row
            let mut carry: NatDigit = 0;
            carry = n2.add_mul_row(a, &mut acc[i..i + n2.digits_len() as usize]);
            // the carry must be added to the column 'right' of i + count_digits_in_n2
            acc[i + n2.digits_len() as usize] = carry;
        }
        let prod = Nat::new_from_parts(n1.bits_len() + n2.bits_len(), acc);
        prod.check_invariant();
        prod
    }

    pub fn div(&self, _n: &Nat) -> Nat {
        panic!("div - no implementation")
    }

    pub fn rem(&self, _n: &Nat) -> Nat {
        panic!("rem - no implementation")
    }

    pub fn divide(&self, _n: &Nat) -> (Nat, Nat) {
        panic!("divide - no implementation")
    }

    fn clear_bit(&self, pos: u32) -> Nat {
        self.check_invariant();
        debug_assert!(pos < self.bits_len(), "clear_bit {pos:} >= {}", self.bits_len());
        #[cfg(release_test)]
        assert!(pos < self.bits_len(), "rut: clear_bit {pos} >= {:?}", self.bits_len());
        self.clone().clear_bit_mut(pos)
    }

    fn clear_bit_mut(mut self, pos: u32) -> Nat {
        self.check_invariant();
        debug_assert!(pos < self.bits_len(), "clear_bit_mut {pos} >={:?}", self.bits_len());
        let (l, p) = (pos / Nat::BITS_IN_NAT_LIMB, pos % Nat::BITS_IN_NAT_LIMB);
        #[cfg(release_test)]
        assert!(pos < self.bits_len(), "rut: clear_bit_mut {pos} >= {:?}", self.bits_len());
        self.mag[l as usize] |= self.mag[l as usize] & !(1 << p);
        self.check_invariant();
        self
    }

    pub fn test_bit(&self, pos: u32) -> bool {
        self.check_invariant();
        debug_assert!(pos < self.bits_len(), "test_bit {pos} >= {:?}", self.bits_len());
        #[cfg(release_test)]
        assert!(pos < self.bits_len(), "rut: test_bit {pos} >= {:?}", self.bits_len());
        let (l, p) = (pos / Nat::BITS_IN_NAT_LIMB, pos % Nat::BITS_IN_NAT_LIMB);
        self.mag[l as usize] & (1 << p) != 0
    }

    fn set_bit(&self, pos: u32) -> Nat {
        self.check_invariant();
        debug_assert!(pos < self.bits_len(), "set_bit {pos} >= {:?}", self.bits_len());
        #[cfg(release_test)]
        assert!(pos < self.bits_len(), "rut: set_bit {pos} >= {:?}", self.bits_len());
        self.clone().set_bit_mut(pos)
    }

    pub fn set_bit_mut(mut self, pos: u32) -> Nat {
        self.check_invariant();
        debug_assert!(pos < self.bits_len(), "set_bit_mut {pos} >= {:?}", self.bits_len());
        let (l, p) = (pos / Nat::BITS_IN_NAT_LIMB, pos % Nat::BITS_IN_NAT_LIMB);
        #[cfg(release_test)]
        assert!(pos < self.bits_len(), "rut: set_bit_mut {pos} >= {:?}", self.bits_len());
        self.mag[l as usize] |= 1 << p;
        self.check_invariant();
        self
    }

    pub fn and(&self, n2: &Nat) -> Nat {
        self.check_invariant();
        n2.check_invariant();
        let mut res = Nat::new(self.bits_len());
        self.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            res.mag[i] = x & y;
        });
        res.check_invariant();
        res
    }

    fn and_mut(mut self, n2: &Nat) -> Nat {
        self.check_invariant();
        n2.check_invariant();
        for (i, &y) in n2.mag.iter().enumerate() {
            self.mag[i] &= y;
        }
        self.check_invariant();
        self
    }

    fn or(&self, n2: &Nat) -> Nat {
        self.check_invariant();
        n2.check_invariant();
        let mut res = Nat::new(self.bits_len());
        self.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            res.mag[i] = x | y;
        });
        res.check_invariant();
        res
    }

    fn or_mut(mut self, n2: &Self) -> Self {
        self.check_invariant();
        n2.check_invariant();
        for (i, &y) in n2.mag.iter().enumerate() {
            self.mag[i] |= n2.mag[i];
        }
        self.check_invariant();
        self
    }

    fn xor(&self, n2: &Self) -> Self {
        self.check_invariant();
        n2.check_invariant();
        let mut res = Nat::new(self.bits_len());
        self.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            res.mag[i] = x ^ y;
        });
        res.check_invariant();
        res
    }

    fn xor_mut(mut self, n2: &Self) -> Self {
        self.check_invariant();
        n2.check_invariant();
        for (i, &y) in n2.mag.iter().enumerate() {
            self.mag[i] ^= n2.mag[i];
        }
        self.check_invariant();
        self
    }

    pub fn hex_str(&self, fc: &NatStrCase, pad: &NatStrPadding) -> String {
        self.check_invariant();
        let format = |v: NatDigit| -> String {
            match (fc, pad) {
                (NatStrCase::Lower, NatStrPadding::Minimal) => format!("{v:0x}"),
                (NatStrCase::Lower, NatStrPadding::Full) => format!("{v:016x}"),
                (NatStrCase::Upper, NatStrPadding::Minimal) => format!("{v:0X}"),
                (NatStrCase::Upper, NatStrPadding::Full) => format!("{v:016X}"),
            }
        };
        let mut s = String::new();
        for &v in self.mag.iter().rev() {
            s.push_str(&format(v));
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
    use crate::nat::{Nat, NatDigit, NatStrCase, NatStrPadding};

    #[test]
    fn nat1k_create() {
        let n1024 = Nat::new(1024);
        assert_eq!(n1024.bits_len(), 1024);
        let n256 = n1024.resize(256);
        assert_eq!(n256.bits_len(), 256);
        let n4096 = n256.resize(4096);
        assert_eq!(n4096.bits_len(), 4096);
        assert_eq!(n4096.mag.len(), (4096 / Nat::BITS_IN_NAT_LIMB) as usize);
        assert_eq!(n1024.bits_len(), 1024);
        assert_eq!(n1024.mag.len(), (1024 / Nat::BITS_IN_NAT_LIMB) as usize);
        assert_eq!(n256.bits_len(), 256);
        assert_eq!(n256.mag.len(), (256 / Nat::BITS_IN_NAT_LIMB) as usize);
    }

    #[test]
    fn nat96_bit_ops() {
        let n96_zero = Nat::zero(96);
        let n96_x = Nat::new_single_digit(96, 0xFFFF00000000FFFF);
        assert!(n96_x.bits_len() >= 96);
        let n96_y = Nat::new_single_digit(96, 0xEEEE000011110000);
        assert_eq!(n96_y.bits_len(), 96);

        assert_eq!(Nat::xor(&n96_x, &n96_x), n96_zero);
        assert_eq!(Nat::xor(&n96_x, &n96_y), Nat::new_single_digit(96, 0x111100001111FFFF));
        assert_eq!(Nat::or(&n96_x, &n96_y), Nat::new_single_digit(96, 0xFFFF00001111FFFF));
        assert_eq!(Nat::and(&n96_x, &n96_y), Nat::new_single_digit(96, 0xEEEE000000000000));
        assert_eq!(Nat::and(&n96_x, &n96_x), Nat::new_single_digit(96, 0xFFFF00000000FFFF));
    }

    #[test]
    fn nat512_cmp() {
        let n0 = Nat::zero(512);
        assert_eq!(n0.bits_len(), 512);
        let n1 = Nat::one(512);
        assert_eq!(n1.bits_len(), 512);
        let n2 = Nat::new_single_digit(512, 2);
        assert_eq!(n1.bits_len(), n2.bits_len());
        let n65525 = Nat::new_single_digit(512, Nat::NAT_DIGIT_VAL_MAX as NatDigit);
        assert!(n0.eq(&n0));
        assert!(n1.lt(&n2));
        assert!(n2.gt(&n1));
        assert!(n2.gt(&n0));
        assert!(!n2.gt(&n2) && !n2.lt(&n2));
        assert!(!n2.gt(&n65525));
        assert!(n65525.gt(&n2));
    }

    #[test]
    fn nat512_sub() {
        let n0 = Nat::zero(512);
        assert_eq!(n0.bits_len(), 512);
        let n1 = Nat::one(512);
        assert_eq!(n1.bits_len(), 512);
        let n2 = Nat::new_single_digit(512, 2);
        assert_eq!(n1.bits_len(), n2.bits_len());
        let n65525 = Nat::new_single_digit(512, Nat::NAT_DIGIT_VAL_MAX as NatDigit);
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
        let n1 = Nat::one(4096);
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
        let val = NatDigit::MAX >> NatDigit::BITS / 4;
        let mag: Vec<NatDigit> = vec![val; size];

        if NatDigit::BITS as usize * size == BIT_LEN_512 as usize
        {
            let nat = Nat::new_from_parts(BIT_LEN_512, mag.clone());
            assert_eq!(nat.mag, vec![val; size])
        }

        if NatDigit::BITS as usize * size == BIT_LEN_256 as usize
        {
            let nat = Nat::new_from_parts(256, mag.clone());
            assert_eq!(nat.mag, vec![val; size])
        }

        {
            let nat = Nat::new_from_parts(NatDigit::BITS * mag.len() as u32, mag.clone());
            assert_eq!(nat.mag, vec![val; size])
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

    // #[cfg(nat_64bit_digit)]
    #[test]
    fn hex_64digit() {
        {
            let n96_x = Nat::new_single_digit(96, 0xEEEE000011110000);
            assert_eq!(n96_x.hex_str(&NatStrCase::Upper, &NatStrPadding::Full), "0x0000000000000000EEEE000011110000");
            ///*
            let n96_x = n96_x.set_bit_mut(95);
            assert_eq!(n96_x.hex_str(&NatStrCase::Upper, &NatStrPadding::Full), "0x0000000080000000EEEE000011110000");
            let n96_x = n96_x.set_bit_mut(94);
            assert_eq!(n96_x.hex_str(&NatStrCase::Lower, &NatStrPadding::Full), "0x00000000c0000000eeee000011110000".to_lowercase());
            assert_eq!(n96_x.hex_str(&NatStrCase::Lower, &NatStrPadding::Minimal), "0xc0000000eeee000011110000");
            assert_eq!(n96_x.hex_str(&NatStrCase::Lower, &NatStrPadding::Minimal), "0xc0000000eeee000011110000");
            //*/
        }
        {
            let mut n64_x = Nat::new_single_digit(64, 0xEEEE000011110000);
            assert_eq!(n64_x.hex_str(&NatStrCase::Lower, &NatStrPadding::Minimal), "0xeeee000011110000");
            assert_eq!(n64_x.hex_str(&NatStrCase::Upper, &NatStrPadding::Full), "0xEEEE000011110000");
            assert_eq!(n64_x.hex_str(&NatStrCase::Upper, &NatStrPadding::Minimal), "0xEEEE000011110000");
        }
    }

    #[test]
    fn nat_mul_256() {
        {
            let n256_x = Nat::new_single_digit(256, 0xFFFF000000050003);
            let n256_y = Nat::new_single_digit(256, 1);
            let prod = Nat::mul(&n256_x, &n256_y);
            assert_eq!(prod.mag[0], 0xFFFF000000050003);
            assert_eq!(prod.mag[1], 0);
            assert_eq!(prod.mag[2], 0);
            assert_eq!(prod.mag[3], 0);
        }
        {
            let n256_x = Nat::new_single_digit(256, 0xFFFF000000050003);
            let n256_y = Nat::new_single_digit(256, 2);
            let prod = Nat::mul(&n256_x, &n256_y);
            assert_eq!(prod.mag[0], 0xfffe0000000a0006);
            assert_eq!(prod.mag[1], 1);
            assert_eq!(prod.mag[2], 0);
            assert_eq!(prod.mag[3], 0);
        }
        {
            let n256_x = Nat::new_single_digit(256, 0xFFFF000000050003);
            let n256_y = Nat::new_single_digit(256, 0xFFFF000000000000);
            let prod = Nat::mul(&n256_x, &n256_y);
            assert_eq!(prod.mag[0], 0xfffd000000000000);
            assert_eq!(prod.mag[1], 0xfffe00010004fffd);
            assert_eq!(prod.mag[2], 0);
            assert_eq!(prod.mag[3], 0);
        }
        {
            let n256_x = Nat::new_single_digit(256, 0xFFFFFFFFFFFFFFFF);
            let n256_y = Nat::new_single_digit(256, 0xFFFFFFFFFFFFFFFF);
            let prod = Nat::mul(&n256_x, &n256_y);
            assert_eq!(prod.mag[0], 0x0000000000000001);
            assert_eq!(prod.mag[1], 0xfffffffffffffffe);
            assert_eq!(prod.mag[2], 0);
            assert_eq!(prod.mag[3], 0);
        }
        {
            let mut n256_x = Nat::new_single_digit(256, 0xFFFFFFFFFFFFFFFF);
            n256_x.mag[1] = 0xF;
            let mut n256_y = Nat::new_single_digit(256, 0xFFFFFFFFFFFFFFFF);
            n256_y.mag[1] = 0xF;
            let prod = Nat::mul(&n256_x, &n256_y);
            assert_eq!(prod.mag[0], 1);
            assert_eq!(prod.mag[1], 0xffffffffffffffe0);
            assert_eq!(prod.mag[2], 0xff);
            assert_eq!(prod.mag[3], 0);
        }
        {
            let mut n256_x = Nat::new(256);
            n256_x.mag[0] = 0xFFFFFFFFFFFFFFFF;
            n256_x.mag[1] = 0xFFFFFFFFFFFFFFFF;
            n256_x.mag[2] = 0xFFFFFFFFFFFFFFFF;
            n256_x.mag[3] = 0xFFFFFFFFFFFFFFFF;
            let mut n256_y = Nat::new(256);
            n256_y.mag[0] = 0xFFFFFFFFFFFFFFFF;
            n256_y.mag[1] = 0xFFFFFFFFFFFFFFFF;
            n256_y.mag[2] = 0xFFFFFFFFFFFFFFFF;
            n256_y.mag[3] = 0xFFFFFFFFFFFFFFFF;
            let prod = Nat::mul(&n256_x, &n256_y);

            assert_eq!(prod.mag[0], 1);
            assert_eq!(prod.mag[1], 0);
            assert_eq!(prod.mag[2], 0);
            assert_eq!(prod.mag[3], 0);
            assert_eq!(prod.mag[4], 0xfffffffffffffffe);
            assert_eq!(prod.mag[5], 0xffffffffffffffff);
            assert_eq!(prod.mag[6], 0xffffffffffffffff);
            assert_eq!(prod.mag[7], 0xffffffffffffffff);
        }
    }

    #[cfg(nat_32bit_digit)]
    #[test]
    fn hex_32digit() {
        {
            let n96_x = Nat::new_single_digit(96, 0xEE001100);
            assert_eq!(n96_x.hex_str(&NatStrCase::Upper, &NatStrPadding::Full), "0x0000000000000000EE001100");
            let n96_x = n96_x.set_bit_mut(95);
            assert_eq!(n96_x.hex_str(&NatStrCase::Upper, &NatStrPadding::Full), "0x8000000000000000EE001100");
            let n96_x = n96_x.set_bit_mut(94);
            assert_eq!(n96_x.hex_str(&NatStrCase::Lower, &NatStrPadding::Full), "0xc000000000000000ee001100".to_lowercase());
            assert_eq!(n96_x.hex_str(&NatStrCase::Lower, &NatStrPadding::Minimal), "0xc00000000ee001100");
            assert_eq!(n96_x.hex_str(&NatStrCase::Lower, &NatStrPadding::Minimal), "0xc00000000ee001100");
        }
        {
            let mut n64_x = Nat::new_single_digit(64, 0xEE001100);
            assert_eq!(n64_x.hex_str(&NatStrCase::Lower, &NatStrPadding::Minimal), "0x0ee001100");
            assert_eq!(n64_x.hex_str(&NatStrCase::Upper, &NatStrPadding::Minimal), "0x0EE001100");
            assert_eq!(n64_x.hex_str(&NatStrCase::Upper, &NatStrPadding::Full), "0x00000000EE001100");
        }
    }
}

#[cfg(not(debug_assertions))]
#[cfg(test)]
mod release {
    use crate::nat::Nat;

    #[test]
    fn nat4k_set_and_test_bit() {
        let n1 = Nat::one(4096);
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
