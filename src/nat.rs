pub const BITS_PER_NAT_LIMB: usize = u64::BITS as usize;

#[derive(Clone, Debug)]
pub struct Nat<const SIZE: usize> {
    pub(crate) mag: [u64; SIZE],
}

impl<const SIZE: usize> Default for Nat<SIZE> {
    fn default() -> Self {
        Nat {
            mag: [0; SIZE],
        }
    }
}

impl<const SIZE: usize> Nat<SIZE> {
    pub const MSB_POS: usize = SIZE * BITS_PER_NAT_LIMB - 1;
    pub fn bits_to_nat_size(bit_count: usize) -> usize {
        bit_count / BITS_PER_NAT_LIMB + 1
    }

    pub fn zero() -> Self {
        Self::default()
    }
    pub fn one() -> Self {
        Self::new_u64(1)
    }

    pub fn new_u64(val: u64) -> Self {
        // let n = Self::default();
        Nat {
            mag: core::array::from_fn::<_, SIZE, _>(
                |i| if i == 0 {
                    val
                } else {
                    0
                })
        }
    }

    pub fn add(&self, n2: &Self) -> (Self, u64) {
        let mut carry: u64 = 0;
        let mut res = Nat::<SIZE>::default();
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
        let mut res = Nat::<SIZE>::default();
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
        SIZE as u32 * u64::BITS
    }

    fn clear_bit(&self, pos: usize) -> Self {
        debug_assert!(pos <= Self::MSB_POS);
        self.clone().clear_bit_mut(pos)
    }

    fn clear_bit_mut(mut self, pos: usize) -> Self {
        debug_assert!(pos <= Self::MSB_POS);
        if pos <= Self::MSB_POS {
            let (l, p) = (pos / BITS_PER_NAT_LIMB, pos % BITS_PER_NAT_LIMB);
            self.mag[l] |= self.mag[l] & !(1 << p);
        }
        self
    }

    pub fn test_bit(&self, pos: usize) -> bool {
        debug_assert!(pos <= Self::MSB_POS);
        if pos <= Self::MSB_POS {
            let (l, p) = (pos / BITS_PER_NAT_LIMB, pos % BITS_PER_NAT_LIMB);
            self.mag[l] & (1 << p) != 0
        } else {
            false
        }
    }

    fn set_bit(&self, pos: usize) -> Self {
        debug_assert!(pos <= Self::MSB_POS);
        self.clone().set_bit_mut(pos)
    }

    pub fn set_bit_mut(mut self, pos: usize) -> Self {
        debug_assert!(pos <= Self::MSB_POS);
        if pos <= Self::MSB_POS {
            let (l, p) = (pos / BITS_PER_NAT_LIMB, pos % BITS_PER_NAT_LIMB);
            self.mag[l] |= 1 << p;
        }
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
        let mut res = Nat::<SIZE>::default();
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
        let mut res = Nat::<SIZE>::default();
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
        let mut res = Nat::<SIZE>::default();
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

    pub fn hex_str(&self) -> String {
        "".to_string()
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
    use super::{BITS_PER_NAT_LIMB, Nat};

    #[test]
    fn test_nat1k_create() {
        const NAT_1K_BITS: usize = 1024 / BITS_PER_NAT_LIMB + 1;
        let n = Nat::<NAT_1K_BITS>::default();
        assert!(n.bit_count() >= 1024);
    }

    #[test]
    fn test_nat512_cmp() {
        const NAT_512_BITS: usize = 512 / BITS_PER_NAT_LIMB + 1;
        let n0 = Nat::<NAT_512_BITS>::zero();
        assert!(n0.bit_count() >= 512);
        let n1 = Nat::<NAT_512_BITS>::one();
        assert!(n1.bit_count() >= 512);
        let n2 = Nat::<NAT_512_BITS>::new_u64(2);
        assert!(n1.bit_count() >= n2.bit_count());
        let n65525 = Nat::<NAT_512_BITS>::new_u64(65535);
        assert!(n0.eq(&n0));
        assert!(n1.lt(&n2));
        assert!(n2.gt(&n1));
        assert!(n2.gt(&n0));
        assert!(!n2.gt(&n2) && !n2.lt(&n2));
        assert!(!n2.gt(&n65525));
        assert!(n65525.gt(&n2));
    }

    #[test]
    fn test_nat4k_set_bit() {
        let n1 = Nat::<{ 4096_usize / BITS_PER_NAT_LIMB + 1}>::one();
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
    fn test_release_nat4k_set_and_test_bit() {
        let n1 = Nat::<{ 4096 / BITS_PER_NAT_LIMB }>::one();
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

        assert!(!n2p4095.test_bit(4096));
        assert!(!n2p4095.test_bit(16000));
        assert!(!n1.test_bit(4096));
        assert!(!n1.test_bit(16000));
        assert!(!n1.test_bit(1600));
    }

    #[test]
    fn test_nat96_bit_ops() {
        let n96_01 = Nat::<{ 96_usize / BITS_PER_NAT_LIMB + 1 }>::new_u64(0xFFFF00000000FFFF);
        assert!(n96_01.bit_count() >= 96);
        let n96_02 = Nat::<{ 96_usize / BITS_PER_NAT_LIMB + 1}>::new_u64(0x1111000011110000);
        assert!(n96_02.bit_count() >= 96);

        let n96_zero = n96_01.xor(&n96_01);
        assert_eq!(n96_zero.mag[0], 0);
        assert_eq!(n96_zero.mag[1], 0);
    }
}
