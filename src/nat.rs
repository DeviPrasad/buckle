use std::cmp::{max, min};

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
    pub(crate) mag: Vec<u64>,
}

impl Nat {
    pub const BIT_LEN_MIN: u32 = 64;
    pub const BIT_LEN_MAX: u32 = 16 * 1024;

    pub fn size(bit_len: u32) -> u32 {
        return
            (bit_len / BITS_PER_NAT_LIMB) +
                match bit_len % BITS_PER_NAT_LIMB {
                    0 => 0,
                    _ => 1
                }
    }

    pub fn new(bit_len: u32) -> Self {
        Nat {
            bits: min(max(bit_len, Nat::BIT_LEN_MIN), Nat::BIT_LEN_MAX),
            mag: vec![0; Self::size(bit_len) as usize],
        }
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
        n
    }

    pub fn resize(&self, new_len: u32) -> Nat {
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
            assert_eq!(new_size, larger_nat.mag.len());
            larger_nat
        } else /* self.bits > new_len */ {
            /* shrink */
            let mut smaller_nat = Nat::new(new_len);
            // 'copy_from_slice' panics if the source and destination lengths are not equal
            smaller_nat.mag.copy_from_slice(&self.mag[0..new_size]);
            assert_eq!(new_size, smaller_nat.mag.len());
            smaller_nat
        }
    }

    pub fn expand_mut(mut self, new_bit_len: u32) -> Self {
        if self.bits < new_bit_len {
            self.bits = new_bit_len;
            self.mag.resize(Self::size(new_bit_len) as usize, 0);
        }
        self
    }

    fn bit_len(&self) -> u32 {
        self.bits
    }

    fn eq(&self, n2: &Self) -> bool {
        let mut res = self.bit_len() == n2.bit_len();
        for (x, y) in self.mag.iter().zip(n2.mag.iter()) {
            res &= x == y;
        }
        res
    }

    fn lt(&self, n2: &Self) -> bool {
        let (_, s) = Nat::resize_and_sub(self, n2);
        s < 0
    }

    fn le(&self, n2: &Self) -> bool {
        let (_, s) = Nat::resize_and_sub(self, n2);
        s <= 0
    }

    fn gt(&self, n2: &Self) -> bool {
        let (_, s) = Nat::resize_and_sub(self, n2);
        s > 0
    }

    fn ge(&self, n2: &Self) -> bool {
        let (_, s) = Nat::resize_and_sub(self, n2);
        s >= 0
    }

    pub fn add(n1: &Nat, n2: &Nat) -> (Nat, u64) {
        let mut carry: u64 = 0;
        let mut res = Nat::new(n1.bit_len());
        n1.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            let limb_sum: u64;
            (limb_sum, carry) = crate::bits::add_with_carry(x, y, carry);
            res.mag[i] = limb_sum;
        });
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
        let mut borrow: u64 = 0;
        let mut mag_diff: u64 = 0; // will stay zero when x.mag == y.mag
        let mut res = Nat::new(n1.bit_len());
        n1.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            let limb_diff: u64; // diff between each corresponding limbs of x and y
            (limb_diff, borrow) = crate::bits::sub_with_borrow(x, y, borrow);
            mag_diff |= limb_diff;
            res.mag[i] = limb_diff;
        });
        let d: i64 = match mag_diff {
            0 => 0,
            _ => 1
        };
        (res, (-(borrow as i64)) | d)
    }

    fn clear_bit(&self, pos: u32) -> Nat {
        debug_assert!(pos < self.bit_len(), "clear_bit_mut {pos} >= {:?}", self.bit_len());
        self.clone().clear_bit_mut(pos)
    }

    fn clear_bit_mut(mut self, pos: u32) -> Nat {
        debug_assert!(pos < self.bit_len(), "clear_bit_mut {pos} >={:?}", self.bit_len());
        let (l, p) = (pos / BITS_PER_NAT_LIMB, pos % BITS_PER_NAT_LIMB);
        self.mag[l as usize] |= self.mag[l as usize] & !(1 << p);
        self
    }

    pub fn test_bit(&self, pos: u32) -> bool {
        debug_assert!(pos < self.bit_len(), "test_bit {pos} >= {:?}", self.bit_len());
        let (l, p) = (pos / BITS_PER_NAT_LIMB, pos % BITS_PER_NAT_LIMB);
        self.mag[l as usize] & (1 << p) != 0
    }

    fn set_bit(&self, pos: u32) -> Nat {
        debug_assert!(pos < self.bit_len(), "set_bit {pos} >= {:?}", self.bit_len());
        self.clone().set_bit_mut(pos)
    }

    pub fn set_bit_mut(mut self, pos: u32) -> Nat {
        debug_assert!(pos < self.bit_len(), "set_bit_mut {pos} >= {:?}", self.bit_len());
        let (l, p) = (pos / BITS_PER_NAT_LIMB, pos % BITS_PER_NAT_LIMB);
        self.mag[l as usize] |= 1 << p;
        self
    }

    fn and(n1: &Nat, n2: &Nat) -> Nat {
        let mut res = Nat::new(n1.bit_len());
        n1.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            res.mag[i] = x & y;
        });
        res
    }

    fn and_mut(mut self, n2: &Nat) -> Nat {
        for (i, &y) in n2.mag.iter().enumerate() {
            self.mag[i] &= y;
        }
        self
    }

    fn or(n1: &Nat, n2: &Nat) -> Nat {
        let mut res = Nat::new(n1.bit_len());
        n1.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            res.mag[i] = x | y;
        });
        res
    }

    fn or_mut(mut self, n2: &Self) -> Self {
        for (i, &y) in n2.mag.iter().enumerate() {
            self.mag[i] |= n2.mag[i];
        }
        self
    }

    fn xor(n1: &Nat, n2: &Self) -> Self {
        let mut res = Nat::new(n1.bit_len());
        n1.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            res.mag[i] = x ^ y;
        });
        res
    }

    fn xor_mut(&mut self, n2: &Self) -> Self {
        for (i, &y) in n2.mag.iter().enumerate() {
            self.mag[i] ^= n2.mag[i];
        }
        self.clone()
    }

    pub fn hex_str(&self, fc: &NatStrCase, pad: &NatStrPadding) -> String {
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
mod tests {
    use crate::nat::Nat;

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
    #[cfg(not(debug_assertions))]
    #[test]
    fn release_nat4k_set_and_test_bit() {
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

        // assert!(!n2p4095.test_bit(4096));
        // assert!(!n2p4095.test_bit(16000));
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

}
