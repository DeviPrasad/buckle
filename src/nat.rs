use std::cmp::{max, min};

use crate::bits;

pub const BITS_PER_NAT_LIMB: u32 = u64::BITS;

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
    pub mag: Vec<u64>,
}

impl Nat {
    pub const BIT_LEN_MIN: u32 = 64;
    pub const BIT_LEN_MAX: u32 = 16 * 1024;

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

    pub fn bit_len(&self) -> u32 {
        self.check_invariant();
        self.bits
    }

    pub fn nat_len(&self) -> u32 {
        self.check_invariant();
        self.mag.len() as u32
    }

    fn size(bit_len: u32) -> u32 {
        return
            (bit_len / BITS_PER_NAT_LIMB) +
                match bit_len % BITS_PER_NAT_LIMB {
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

    pub fn new_from_parts(bit_len: u32, mag: Vec<u64>) -> Self {
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
        Self::new_u64(bit_len, 1)
    }

    /*
    pub fn from_le(data: &[u64]) -> Self {
        debug_assert!(data.len() <= SIZE);
        Nat { bits: 0, mag: data.clone() }
    }
    */

    pub fn new_u64(bit_len: u32, val: u64) -> Self {
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
        let mut res = self.bit_len() == n2.bit_len();
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

    pub fn add(n1: &Nat, n2: &Nat) -> (Nat, u64) {
        n1.check_invariant();
        n2.check_invariant();
        debug_assert!(n1.bit_len() == n2.bit_len(), "add {} != {}", n1.bit_len(), n2.bit_len());
        #[cfg(release_test)]
        assert!(n1.bit_len() == n2.bit_len(), "rut: add {} >= {}", n1.bit_len(), n2.bit_len());
        let mut carry: u64 = 0;
        let mut res = Nat::new(n1.bit_len());
        n1.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            let limb_sum: u64;
            (limb_sum, carry) = bits::add_with_carry(x, y, carry);
            res.mag[i] = limb_sum;
        });
        res.check_invariant();
        (res, carry)
    }

    pub fn resize_and_add(&self, t: &Self) -> (Self, u64) {
        let res_bit_len = max(self.bit_len(), t.bit_len());
        if self.bit_len() < res_bit_len {
            Self::add(&self.resize(res_bit_len), &t)
        } else if t.bit_len() < res_bit_len {
            Self::add(self, &t.resize(res_bit_len))
        } else {
            Self::add(self, t)
        }
    }

    pub fn resize_and_sub(s: &Nat, t: &Nat) -> (Self, i64) {
        let res_bit_len = max(s.bit_len(), t.bit_len());
        if s.bit_len() < res_bit_len {
            Self::sub(&s.resize(res_bit_len), t)
        } else if t.bit_len() < res_bit_len {
            Self::sub(s, &t.resize(res_bit_len))
        } else {
            Self::sub(s, t)
        }
    }

    pub fn sub(n1: &Nat, n2: &Nat) -> (Nat, i64) {
        n1.check_invariant();
        n2.check_invariant();
        debug_assert!(n1.bit_len() == n2.bit_len(), "sub {} != {}", n1.bit_len(), n2.bit_len());
        #[cfg(release_test)]
        assert!(n1.bit_len() == n2.bit_len(), "rut: sub {} >= {}", n1.bit_len(), n2.bit_len());
        let mut borrow: u64 = 0;
        let mut mag_diff: u64 = 0; // will stay zero when x.mag == y.mag
        let mut res = Nat::new(n1.bit_len());
        n1.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            let limb_diff: u64; // diff between each corresponding limbs of x and y
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

    // school-book multiplication
    //
    pub fn mul(n1: &Nat, n2: &Nat) -> Nat {
        n1.check_invariant();
        n2.check_invariant();
        debug_assert!(n1.bit_len() == n2.bit_len(), "mul {} != {}", n1.bit_len(), n2.bit_len());
        let mut product: Vec<u64> = vec![0; (n1.nat_len() as u64 * 2) as usize];
        let n2_len = n2.nat_len() as usize;
        for (i, &x) in n1.mag.iter().enumerate() {
            let mut carry: u64 = 0;
            for (j, &y) in n2.mag.iter().enumerate() {
                let r: bits::U128 = bits::mul64(x, y);
                let sum = r.lo as u128 + product[i + j] as u128 + carry as u128;
                product[i + j] = sum as u64;
                carry = r.hi + ((sum >> 64) as u64);
            }
            product[i + n2_len] = carry;
        }
        let prod = Nat::new_from_parts(n1.bit_len() * 2, product);
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
        debug_assert!(pos < self.bit_len(), "clear_bit {pos:} >= {}", self.bit_len());
        #[cfg(release_test)]
        assert!(pos < self.bit_len(), "rut: clear_bit {pos} >= {:?}", self.bit_len());
        self.clone().clear_bit_mut(pos)
    }

    fn clear_bit_mut(mut self, pos: u32) -> Nat {
        self.check_invariant();
        debug_assert!(pos < self.bit_len(), "clear_bit_mut {pos} >={:?}", self.bit_len());
        let (l, p) = (pos / BITS_PER_NAT_LIMB, pos % BITS_PER_NAT_LIMB);
        #[cfg(release_test)]
        assert!(pos < self.bit_len(), "rut: clear_bit_mut {pos} >= {:?}", self.bit_len());
        self.mag[l as usize] |= self.mag[l as usize] & !(1 << p);
        self.check_invariant();
        self
    }

    pub fn test_bit(&self, pos: u32) -> bool {
        self.check_invariant();
        debug_assert!(pos < self.bit_len(), "test_bit {pos} >= {:?}", self.bit_len());
        #[cfg(release_test)]
        assert!(pos < self.bit_len(), "rut: test_bit {pos} >= {:?}", self.bit_len());
        let (l, p) = (pos / BITS_PER_NAT_LIMB, pos % BITS_PER_NAT_LIMB);
        self.mag[l as usize] & (1 << p) != 0
    }

    fn set_bit(&self, pos: u32) -> Nat {
        self.check_invariant();
        debug_assert!(pos < self.bit_len(), "set_bit {pos} >= {:?}", self.bit_len());
        #[cfg(release_test)]
        assert!(pos < self.bit_len(), "rut: set_bit {pos} >= {:?}", self.bit_len());
        self.clone().set_bit_mut(pos)
    }

    pub fn set_bit_mut(mut self, pos: u32) -> Nat {
        self.check_invariant();
        debug_assert!(pos < self.bit_len(), "set_bit_mut {pos} >= {:?}", self.bit_len());
        let (l, p) = (pos / BITS_PER_NAT_LIMB, pos % BITS_PER_NAT_LIMB);
        #[cfg(release_test)]
        assert!(pos < self.bit_len(), "rut: set_bit_mut {pos} >= {:?}", self.bit_len());
        self.mag[l as usize] |= 1 << p;
        self.check_invariant();
        self
    }

    pub fn and(&self, n2: &Nat) -> Nat {
        self.check_invariant();
        n2.check_invariant();
        let mut res = Nat::new(self.bit_len());
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
        let mut res = Nat::new(self.bit_len());
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
        let mut res = Nat::new(self.bit_len());
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
        let format = |v: u64| -> String {
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
    use crate::nat::{Nat, NatStrCase, NatStrPadding};

    #[test]
    fn nat1k_create() {
        let n1024 = Nat::new(1024);
        assert_eq!(n1024.bit_len(), 1024);
        let n256 = n1024.resize(256);
        assert_eq!(n256.bit_len(), 256);
        let n4096 = n256.resize(4096);
        assert_eq!(n4096.bit_len(), 4096);
        assert_eq!(n4096.mag.len(), 4096 / 64);
        assert_eq!(n1024.bit_len(), 1024);
        assert_eq!(n1024.mag.len(), 1024 / 64);
        assert_eq!(n256.bit_len(), 256);
        assert_eq!(n256.mag.len(), 256 / 64);
    }

    #[test]
    fn nat512_cmp() {
        let n0 = Nat::zero(512);
        assert_eq!(n0.bit_len(), 512);
        let n1 = Nat::one(512);
        assert_eq!(n1.bit_len(), 512);
        let n2 = Nat::new_u64(512, 2);
        assert_eq!(n1.bit_len(), n2.bit_len());
        let n65525 = Nat::new_u64(512, 65535);
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
        assert_eq!(n0.bit_len(), 512);
        let n1 = Nat::one(512);
        assert_eq!(n1.bit_len(), 512);
        let n2 = Nat::new_u64(512, 2);
        assert_eq!(n1.bit_len(), n2.bit_len());
        let n65525 = Nat::new_u64(512, 65535);
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
        assert!(n1.bit_len() >= 4096);
        assert!(n1.test_bit(0));
        assert!(!n1.test_bit(1));
        assert!(!n1.test_bit(4095));

        let n2p4095 = n1.set_bit(4095);
        assert!(n2p4095.bit_len() >= 4096);
        assert!(n2p4095.test_bit(4095));
        assert!(n2p4095.test_bit(0));
        assert!(!n2p4095.test_bit(1));
        assert!(!n2p4095.test_bit(4094));
    }

    #[test]
    fn nat96_bit_ops() {
        let n96_zero = Nat::zero(96);
        let n96_x = Nat::new_u64(96, 0xFFFF00000000FFFF);
        assert!(n96_x.bit_len() >= 96);
        let n96_y = Nat::new_u64(96, 0xEEEE000011110000);
        assert_eq!(n96_y.bit_len(), 96);

        assert_eq!(Nat::xor(&n96_x, &n96_x), n96_zero);
        assert_eq!(Nat::xor(&n96_x, &n96_y), Nat::new_u64(96, 0x111100001111FFFF));
        assert_eq!(Nat::or(&n96_x, &n96_y), Nat::new_u64(96, 0xFFFF00001111FFFF));
        assert_eq!(Nat::and(&n96_x, &n96_y), Nat::new_u64(96, 0xEEEE000000000000));
        assert_eq!(Nat::and(&n96_x, &n96_x), Nat::new_u64(96, 0xFFFF00000000FFFF));
    }

    #[test]
    fn hex() {
        {
            let n96_x = Nat::new_u64(96, 0xEEEE000011110000);
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
            let mut n64_x = Nat::new_u64(64, 0xEEEE000011110000);
            assert_eq!(n64_x.hex_str(&NatStrCase::Lower, &NatStrPadding::Minimal), "0xeeee000011110000");
            assert_eq!(n64_x.hex_str(&NatStrCase::Upper, &NatStrPadding::Full), "0xEEEE000011110000");
            assert_eq!(n64_x.hex_str(&NatStrCase::Upper, &NatStrPadding::Minimal), "0xEEEE000011110000");
        }
    }

    #[test]
    fn nat_mul_256() {
        {
            let n256_x = Nat::new_u64(256, 0xFFFF000000050003);
            let n256_y = Nat::new_u64(256, 1);
            let prod = Nat::mul(&n256_x, &n256_y);
            assert_eq!(prod.mag[0], 0xFFFF000000050003);
            assert_eq!(prod.mag[1], 0);
            assert_eq!(prod.mag[2], 0);
            assert_eq!(prod.mag[3], 0);
        }
        {
            let n256_x = Nat::new_u64(256, 0xFFFF000000050003);
            let n256_y = Nat::new_u64(256, 2);
            let prod = Nat::mul(&n256_x, &n256_y);
            assert_eq!(prod.mag[0], 0xfffe0000000a0006);
            assert_eq!(prod.mag[1], 1);
            assert_eq!(prod.mag[2], 0);
            assert_eq!(prod.mag[3], 0);
        }
        {
            let n256_x = Nat::new_u64(256, 0xFFFF000000050003);
            let n256_y = Nat::new_u64(256, 0xFFFF000000000000);
            let prod = Nat::mul(&n256_x, &n256_y);
            assert_eq!(prod.mag[0], 0xfffd000000000000);
            assert_eq!(prod.mag[1], 0xfffe00010004fffd);
            assert_eq!(prod.mag[2], 0);
            assert_eq!(prod.mag[3], 0);
        }
        {
            let n256_x = Nat::new_u64(256, 0xFFFFFFFFFFFFFFFF);
            let n256_y = Nat::new_u64(256, 0xFFFFFFFFFFFFFFFF);
            let prod = Nat::mul(&n256_x, &n256_y);
            assert_eq!(prod.mag[0], 0x0000000000000001);
            assert_eq!(prod.mag[1], 0xfffffffffffffffe);
            assert_eq!(prod.mag[2], 0);
            assert_eq!(prod.mag[3], 0);
        }
        {
            let mut n256_x = Nat::new_u64(256, 0xFFFFFFFFFFFFFFFF);
            n256_x.mag[1] = 0xF;
            let mut n256_y = Nat::new_u64(256, 0xFFFFFFFFFFFFFFFF);
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
            /*eprintln!("{:0X} {:0X} {:0X} {:0X} {:0X} {:0X} {:0X} {:0X}",
                      prod.mag[7],
                      prod.mag[6],
                      prod.mag[5],
                      prod.mag[4],
                      prod.mag[3],
                      prod.mag[2],
                      prod.mag[1],
                      prod.mag[0]);*/
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

    #[test]
    fn nat_from_parts() {
        let mag = vec![0xFFFFFFFF_u64; 8];
        {
            let nat = Nat::new_from_parts(512, mag.clone());
            assert_eq!(nat.mag, vec![0xFFFFFFFF_u64; 8])
        }
        {
            let nat = Nat::new_from_parts(256, mag.clone());
            assert_eq!(nat.mag, vec![0xFFFFFFFF_u64; 4])
        }
        {
            let nat = Nat::new_from_parts(128, mag.clone());
            assert_eq!(nat.mag, vec![0xFFFFFFFF_u64; 2])
        }
        // this would fail because requested size > magnitude's current size
        /*
        {
            let nat = Nat::new_from_parts(4096, mag.clone());
            assert_eq!(nat.bit_len(), 4096);
            assert_eq!(nat.nat_len(), 4096/64);
            assert_eq!(nat.mag, vec![0xFFFFFFFF_u64; 512])
        }
        */
    }
}

#[cfg(not(debug_assertions))]
#[cfg(test)]
mod release {
    use crate::nat::Nat;

    #[test]
    fn nat4k_set_and_test_bit() {
        let n1 = Nat::one(4096);
        assert_eq!(n1.bit_len(), 4096);
        assert!(n1.test_bit(0));
        assert!(!n1.test_bit(1));

        let n2p4095 = n1.set_bit(4095);
        assert_eq!(n2p4095.bit_len(), 4096);
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
