use crate::{Digit, Int};

impl Int {
    // extended binary GCD algorithm
    pub fn gcd(a: &Int, b: &Int) -> (/* gcd */Int, /* s */Int, /* t */ Int) {
        let (mut x, mut y) = (a.compact(), b.compact());
        let mut sr = 0;
        while x.even() && y.even() {
            x.shr_mut(1);
            y.shr_mut(1);
            sr += 1;
        }
        let alpha = x.clone();
        let beta = y.clone();
        let (mut u, mut v, mut s, mut t) = (Int::one(Digit::BITS),
                                            Int::zero(Digit::BITS),
                                            Int::zero(Digit::BITS),
                                            Int::one(Digit::BITS));

        // from here on we maintain the following invariant:
        // x = u * alpha + v * beta, and
        // y = s * alpha + t * beta #
        while x.even() {
            x.shrs_mut(1);
            if u.even() && v.even() {
                u.shr_mut(1);
                v.shr_mut(1);
            } else {
                u = u.add(&beta).0;
                u.shr_mut(1);
                v = v.sub(&alpha).0;
                v.shr_mut(1);
            }
        }
        x.valid();
        y.valid();
        u.valid();
        v.valid();
        while x.ne(&y) {
            if y.even() {
                y.shr_mut(1);
                // Note: since y is even, the following holds:
                // (i) if s, t are both odd then so are alpha, beta
                // (ii) if s is odd and t even then alpha must be even, so beta is odd.
                // (iii) if t is odd and s even then beta must be even, so alpha is odd.
                // so for each of (i), (ii) and (iii) (s + beta) and (t - alpha) are even.
                if s.even() && t.even() {
                    s.shr_mut(1);
                    t.shr_mut(1);
                } else {
                    s = s.add(&beta).0;
                    s.shr_mut(1);
                    t = t.sub(&alpha).0;
                    t.shr_mut(1);
                }
            } else if y.less(&x) {
                (x, y, u, v, s, t) = (y, x, s, t, u, v)
            } else {
                (y, s, t) = (y.sub(&x).0, s.sub(&u).0, t.sub(&v).0)
            }
        }
        let mf = Int::new_digit(x.bit_width(), 1);
        let gcd = mf.shl(sr).mul(&x).compact();

        (gcd, s, t)
    }
}

#[cfg(test)]
mod gcd_tests {
    use crate::{Digit, hex, init_logger, Int};

    #[test]
    fn basic() {
        init_logger(true);
        let x = Int::new_digit(Digit::BITS, 23);
        let y = Int::new_digit(Digit::BITS, 71);
        let (gcd, _s, _t) = Int::gcd(&x, &y);
        assert_eq!(gcd.mag, vec![1]);

        let x = Int::new_digit(Digit::BITS, 383);
        let y = Int::new_digit(Digit::BITS, 271);
        let (gcd, _s, _t) = Int::gcd(&x, &y);
        assert_eq!(gcd.mag, vec![1]);

        let x = Int::new_digit(Digit::BITS, 21);
        let y = Int::new_digit(Digit::BITS, 1203);
        let (gcd, _, _) = Int::gcd(&x, &y);
        assert_eq!(gcd.mag, vec![3]);

        let x = Int::new_digit(Digit::BITS, 19932);
        let y = Int::new_digit(Digit::BITS, 468);
        let (gcd, s, t) = Int::gcd(&x, &y);
        assert_eq!(gcd.mag, vec![12]);
        // assert_eq!(gcd.mag, x.mul(&s).sub(&y.mul(&t)).0.mag);

        let x = Int::from_le_digits_vec(hex::le_vec_u64("0x1bddff867272a9296ac493c251d7f46f09a5591fe"));
        let y = Int::from_le_digits_vec(hex::le_vec_u64("0xb55930a2a68a916450a7de006031068c5ddb0e5c"));
        let (gcd, s, t) = Int::gcd(&x, &y);
        assert_eq!(gcd.mag, vec![2]);

        let x = Int::from_le_digits_vec(hex::le_vec_u64("0x2f0ece5b1ee9c15e132a01d55768dc13"));
        let y = Int::from_le_digits_vec(hex::le_vec_u64("0x1c6f4fd9873cdb24466e6d03e1cc66e7"));
        let (gcd, s, t) = Int::gcd(&x, &y);
        assert_eq!(gcd.mag, vec![1]);
    }
}
