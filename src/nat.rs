use crate::nat::NatStrCase::Lower;

pub const BITS_PER_NAT_LIMB: usize = u64::BITS as usize;

pub enum NatStrPadding {
    Minimal,
    Full,
}

pub enum NatStrCase {
    Lower,
    Upper,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Nat<const BITS: u32> {
    pub(crate) bits: u32,
    pub(crate) mag: Vec<u64>,
}

impl<const BITS: u32> Default for Nat<BITS> {
    fn default() -> Self {
        let size: usize =
            BITS as usize / BITS_PER_NAT_LIMB +
                match BITS as usize % BITS_PER_NAT_LIMB {
                    0 => 0,
                    _ => 1
                };
        Nat {
            bits: BITS,
            mag: vec![0; size],
        }
    }
}

impl<const BITS: u32> Nat<BITS> {
    pub const MSB_POS: usize = BITS as usize - 1;
    pub fn nat_size() -> u32 {
        (BITS as usize / BITS_PER_NAT_LIMB + 1) as u32
    }

    pub fn zero() -> Self {
        Self::default()
    }
    pub fn one() -> Self {
        Self::new_u64(1)
    }

    /*
    pub fn from_le(data: &[u64]) -> Self {
        debug_assert!(data.len() <= SIZE);
        Nat { bits: 0, mag: data.clone() }
    }
    */

    pub fn new_u64(val: u64) -> Self {
        let mut n = Self::default();
        n.mag[0] = val;
        n
    }

    pub fn add(&self, n2: &Self) -> (Self, u64) {
        let mut carry: u64 = 0;
        let mut res = Nat::<BITS>::default();
        self.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            let limb_sum: u64;
            (limb_sum, carry) = crate::bits::add_with_carry(x, y, carry);
            res.mag[i] = limb_sum;
        });
        (res, carry)
    }

    pub fn sub(&self, n2: &Self) -> (Self, i64) {
        let mut borrow: u64 = 0;
        let mut mag_diff: u64 = 0; // will stay zero when x.mag == y.mag
        let mut res = Nat::<BITS>::default();
        self.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
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

    pub fn mul(&self, _n: &Self) -> Self {
        self.clone()
    }

    pub fn div(&self, _n: &Self) -> Self {
        self.clone()
    }

    pub fn rem(&self, _n: &Self) -> Self {
        self.clone()
    }

    pub fn divide(&self, _n: &Self) -> (Self, Self) {
        panic!("divide - no implementation")
    }

    fn inverse(&self, _n: &Self) -> Self {
        panic!("inverse - no implementation")
    }

    fn sqrt(&self) -> Self {
        panic!("sqrt - no implementation")
    }

    fn min(&self, n2: &Self) -> Self {
        if self.lt(&n2) {
            self.clone()
        } else {
            n2.clone()
        }
    }

    fn max(&self, n2: &Self) -> Self {
        if self.gt(&n2) {
            self.clone()
        } else {
            n2.clone()
        }
    }

    fn eq(&self, n2: &Self) -> bool {
        let mut res = true;
        for (x, y) in self.mag.iter().zip(n2.mag.iter()) {
            res &= x == y;
        }
        res
    }

    fn lt(&self, n2: &Self) -> bool {
        let (_, s) = self.sub(n2);
        s < 0
    }

    fn le(&self, n2: &Self) -> bool {
        let (_, s) = self.sub(n2);
        s <= 0
    }

    fn gt(&self, n2: &Self) -> bool {
        let (_, s) = self.sub(n2);
        s > 0
    }

    fn ge(&self, n2: &Self) -> bool {
        let (_, s) = self.sub(n2);
        s >= 0
    }

    fn bit_count(&self) -> u32 {
        BITS
    }

    fn clear_bit(&self, pos: usize) -> Self {
        debug_assert!(pos <= Self::MSB_POS, "clear_bit_mut {pos} >= {BITS}");
        self.clone().clear_bit_mut(pos)
    }

    fn clear_bit_mut(mut self, pos: usize) -> Self {
        debug_assert!(pos <= Self::MSB_POS, "clear_bit_mut {pos} >= {BITS}");
        let (l, p) = (pos / BITS_PER_NAT_LIMB, pos % BITS_PER_NAT_LIMB);
        self.mag[l] |= self.mag[l] & !(1 << p);
        self
    }

    pub fn test_bit(&self, pos: usize) -> bool {
        debug_assert!(pos <= Self::MSB_POS, "test_bit {pos} >= {BITS}");
        let (l, p) = (pos / BITS_PER_NAT_LIMB, pos % BITS_PER_NAT_LIMB);
        self.mag[l] & (1 << p) != 0
    }

    fn set_bit(&self, pos: usize) -> Self {
        debug_assert!(pos <= Self::MSB_POS, "set_bit {pos} >= {BITS}");
        self.clone().set_bit_mut(pos)
    }

    pub fn set_bit_mut(mut self, pos: usize) -> Self {
        debug_assert!(pos <= Self::MSB_POS, "set_bit_mut {pos} >= {BITS}");
        let (l, p) = (pos / BITS_PER_NAT_LIMB, pos % BITS_PER_NAT_LIMB);
        self.mag[l] |= 1 << p;
        self
    }

    fn shl(&self, _n: u64) -> Self {
        self.clone()
    }

    fn shl_mut(&mut self, _n: u64) -> Self {
        self.clone()
    }

    fn shr(&self, _n: u64) -> Self {
        self.clone()
    }

    fn shr_mut(&mut self, _n: u64) -> Self {
        self.clone()
    }

    fn and(&self, n2: &Self) -> Self {
        let mut res = Nat::<BITS>::default();
        self.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            res.mag[i] = x & y;
        });
        res
    }

    fn and_mut(mut self, n2: &Self) -> Self {
        for (i, &y) in n2.mag.iter().enumerate() {
            self.mag[i] &= y;
        }
        self
    }

    fn or(&self, n2: &Self) -> Self {
        let mut res = Nat::<BITS>::default();
        self.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
            res.mag[i] = x | y;
        });
        res
    }

    fn or_mut(&mut self, n2: &Self) -> Self {
        for (i, &y) in n2.mag.iter().enumerate() {
            self.mag[i] |= n2.mag[i];
        }
        self.clone()
    }

    fn xor(&self, n2: &Self) -> Self {
        let mut res = Nat::<BITS>::default();
        self.mag.iter().zip(n2.mag.iter()).enumerate().for_each(|(i, (&x, &y))| {
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

    pub fn leading_non_zero_limb(&self) -> Option<u32> {
        for (i, &v) in self.mag.iter().rev().enumerate() {
            if v > 0 {
                return Some(i as u32);
            }
        }
        None
    }

    pub fn hex_str(&self, fc: &NatStrCase, pad: &NatStrPadding) -> String {
        let format = |v: u64| -> String {
            match (fc, pad) {
                (Lower, NatStrPadding::Minimal) => format!("{v:0x}"),
                (Lower, NatStrPadding::Full) => format!("{v:016x}"),
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
    use super::{BITS_PER_NAT_LIMB, Nat, NatStrCase, NatStrPadding};

    #[test]
    fn nat1k_create() {
        const NAT_1K_BITS: usize = 1024 / BITS_PER_NAT_LIMB + 1;
        let n = Nat::<1024>::default();
        assert!(n.bit_count() >= 1024);
    }

    #[test]
    fn nat512_cmp() {
        let n0 = Nat::<512>::zero();
        assert_eq!(n0.bit_count(), 512);
        let n1 = Nat::<512>::one();
        assert_eq!(n1.bit_count(), 512);
        let n2 = Nat::<512>::new_u64(2);
        assert_eq!(n1.bit_count(), n2.bit_count());
        let n65525 = Nat::<512>::new_u64(65535);
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
        let n1 = Nat::<4096>::one();
        assert!(n1.bit_count() >= 4096);
        assert!(n1.test_bit(0));
        assert!(!n1.test_bit(1));
        assert!(!n1.test_bit(4095));

        let n2p4095 = n1.set_bit(4095);
        assert!(n2p4095.bit_count() >= 4096);
        assert!(n2p4095.test_bit(4095));
        assert!(n2p4095.test_bit(0));
        assert!(!n2p4095.test_bit(1));
        assert!(!n2p4095.test_bit(4094));
    }

    #[cfg(not(debug_assertions))]
    #[test]
    fn release_nat4k_set_and_test_bit() {
        let n1 = Nat::<4096>::one();
        assert_eq!(n1.bit_count(), 4096);
        assert!(n1.test_bit(0));
        assert!(!n1.test_bit(1));

        let n2p4095 = n1.set_bit(4095);
        assert_eq!(n2p4095.bit_count(), 4096);
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
        let n96_zero = Nat::<96>::zero();
        let n96_x = Nat::<96>::new_u64(0xFFFF00000000FFFF);
        assert!(n96_x.bit_count() >= 96);
        let n96_y = Nat::<96>::new_u64(0xEEEE000011110000);
        assert_eq!(n96_y.bit_count(), 96);

        assert_eq!(n96_x.xor(&n96_x), n96_zero);
        assert_eq!(n96_x.xor(&n96_y), Nat::<96>::new_u64(0x111100001111FFFF));
        assert_eq!(n96_x.or(&n96_y), Nat::<96>::new_u64(0xFFFF00001111FFFF));
        assert_eq!(n96_x.and(&n96_y), Nat::<96>::new_u64(0xEEEE000000000000));
        assert_eq!(n96_x.and(&n96_x), Nat::<96>::new_u64(0xFFFF00000000FFFF));
    }

    #[test]
    fn hex() {
        {
            let n96_x = Nat::<96>::new_u64(0xEEEE000011110000);
            assert_eq!(n96_x.hex_str(&NatStrCase::Upper, &NatStrPadding::Full), "0x0000000000000000EEEE000011110000");
            assert_eq!(n96_x.hex_str(&NatStrCase::Lower, &NatStrPadding::Minimal), "0x0EEEE000011110000".to_lowercase());
            let n96_x = n96_x.set_bit_mut(95);
            assert_eq!(n96_x.hex_str(&NatStrCase::Upper, &NatStrPadding::Full), "0x0000000080000000EEEE000011110000");
            let n96_x = n96_x.set_bit_mut(94);
            assert_eq!(n96_x.hex_str(&NatStrCase::Lower, &NatStrPadding::Full), "0x00000000C0000000EEEE000011110000".to_lowercase());
            assert_eq!(n96_x.hex_str(&NatStrCase::Lower, &NatStrPadding::Minimal), "0xC0000000EEEE000011110000".to_lowercase());
            assert_eq!(n96_x.hex_str(&NatStrCase::Lower, &NatStrPadding::Minimal), "0xC0000000EEEE000011110000".to_lowercase());
        }
        {
            let n64_x = Nat::<64>::new_u64(0xEEEE000011110000);
            assert_eq!(n64_x.hex_str(&NatStrCase::Upper, &NatStrPadding::Full), "0xEEEE000011110000");
            assert_eq!(n64_x.hex_str(&NatStrCase::Upper, &NatStrPadding::Minimal), "0xEEEE000011110000");
        }
    }
}
