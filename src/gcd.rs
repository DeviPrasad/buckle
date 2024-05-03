use crate::{Digit, Int};

impl Int {
    // extended binary GCD algorithm
    pub fn gcd(a: &Int, b: &Int) -> (/* gcd */Int, /* s */Int, /* t */ Int) {
        let (mut x, mut y) = (a.compact(), b.compact());
        let mut sr: u64 = 1;
        while x.even() && y.even() {
            x.shrs_mut(1);
            y.shrs_mut(1);
            sr *= 2;
        }
        let alpha = x.clone();
        let beta = y.clone();
        let (mut u, mut v, mut s, mut t) = (Int::one(Digit::BITS),  // Sx
                                            Int::zero(Digit::BITS), // Tx
                                            Int::zero(Digit::BITS), // Sy
                                            Int::one(Digit::BITS)); // Ty

        // from here on we maintain the following invariant:
        // x = u * alpha + v * beta, and
        // y = s * alpha + t * beta #
        assert_eq!(x, u.mul(&alpha).add(&v.mul(&beta)).0);
        assert_eq!(y, s.mul(&alpha).add(&t.mul(&beta)).0);
        while x.even() {
            x.shrs_mut(1);
            if u.even() && v.even() {
                u.shrs_mut(1);
                v.shrs_mut(1);
            } else {
                u = u.add(&beta).0;
                u.shrs_mut(1);
                v = v.sub(&alpha).0;
                v.shrs_mut(1);
            }
            assert_eq!(x, u.mul(&alpha).add(&v.mul(&beta)).0);
            assert_eq!(y, s.mul(&alpha).add(&t.mul(&beta)).0);
        }
        let mut step: u64 = 0;
        while x.ne(&y) {
            x.valid();
            y.valid();
            u.valid();
            v.valid();
            step += 1;
            if y.even() {
                y.shrs_mut(1);
                // Note: since y is even, the following holds:
                // (i) if s, t are both odd then so are alpha, beta
                // (ii) if s is odd and t even then alpha must be even, so beta is odd.
                // (iii) if t is odd and s even then beta must be even, so alpha is odd.
                // so for each of (i), (ii) and (iii) (s + beta) and (t - alpha) are even.
                if s.even() && t.even() {
                    s.shrs_mut(1);
                    t.shrs_mut(1);
                    let sxa = s.mul(&alpha).compact();
                    let txb = t.mul(&beta).compact();
                    let sxa_plus_txb = sxa.sub(&txb).0.compact();
                    log::info!("step {step}");
                    // assert_eq!(y, sxa_plus_txb);
                } else {
                    s = s.sum(&beta);
                    s.shrs_mut(1);
                    t = t.sub(&alpha).0;
                    t.shrs_mut(1);
                    //log::info!("\t size_of_s = {}, size_of_t = {}, size_of_beta = {}", s.width(), t.width(), beta.width());
                    let sxa = s.mul(&alpha).compact();
                    let txb = t.mul(&beta).compact();
                    let sxa_plus_txb = sxa.add(&txb).0.compact();
                    //log::info!("\t size_of_sxa = {}, size_of_txb = {}, sxa_plus_txb = {}", sxa.width(), txb.width(), sxa_plus_txb.width());
                    //log::info!("\t sxa = {sxa:?}, txb = {txb:?}, sxa_plus_txb = {sxa_plus_txb:?}");
                    //assert_eq!(y, sxa_plus_txb);
                }
                //assert_eq!(x, u.mul(&alpha).add(&v.mul(&beta)).0.compact());
            } else if y.lt(&x) {
                std::mem::swap(&mut x, &mut y);
                std::mem::swap(&mut u, &mut s);
                std::mem::swap(&mut v, &mut t);
                // assert_eq!(x, u.mul(&alpha).add(&v.mul(&beta)).0.compact());

                let sxa = s.mul(&alpha).compact();
                let txb = t.mul(&beta).compact();
                let sxa_plus_txb = sxa.add(&txb).0.compact();
                //assert_eq!(y, sxa_plus_txb);
            } else {
                (y, s, t) = (y.sub(&x).0, s.sub(&u).0, t.sub(&v).0);
                // assert_eq!(x, u.mul(&alpha).add(&v.mul(&beta)).0.compact());
                let sxa = s.mul(&alpha).compact();
                let txb = t.mul(&beta).compact();
                let sxa_plus_txb = sxa.add(&txb).0.compact();
                //log::info!("\t sxa = {sxa:?}, txb = {txb:?}, sxa_plus_txb = {sxa_plus_txb:?}");
                //assert_eq!(y, sxa_plus_txb);
            }
        }
        let gcd = x.mul_digit(sr).compact();
        // assert_eq!(gcd, (a.mul(&s).add(&b.mul(&t)).0));
        (gcd, s, t)
    }
}

#[cfg(test)]
mod gcd_tests {
    use crate::{Digit, hex, init_logger, Int};

    #[test]
    fn gcd_10_4() {
        init_logger(true);
        let x = Int::new_digit(Digit::BITS, 10);
        let y = Int::new_digit(Digit::BITS, 4);
        let (gcd, _s, _t) = Int::gcd(&x, &y);
        assert_eq!(gcd.mag, vec![2]);
        //assert_eq!(_t, Int::one(64));
        //assert_eq!(_s, Int::one(64));
        //assert_eq!(gcd, x.mul(&_s).sub(&y.mul(&_t)).0);
    }

    #[test]
    fn gcd_23_71() {
        init_logger(true);
        let x = Int::new_digit(Digit::BITS, 23);
        let y = Int::new_digit(Digit::BITS, 71);
        let (gcd, _s, _t) = Int::gcd(&x, &y);
        assert_eq!(gcd.mag, vec![1]);
    }

    #[test]
    fn second() {
        init_logger(true);
        let x = Int::new_digit(Digit::BITS, 383);
        let y = Int::new_digit(Digit::BITS, 271);
        let (gcd, _, _) = Int::gcd(&x, &y);
        assert_eq!(gcd.mag, vec![1]);

        let x = Int::new_digit(Digit::BITS, 21);
        let y = Int::new_digit(Digit::BITS, 1203);
        let (gcd, _, _) = Int::gcd(&x, &y);
        assert_eq!(gcd.mag, vec![3]);

        let x = Int::new_digit(Digit::BITS, 19932);
        let y = Int::new_digit(Digit::BITS, 468);
        let (gcd, _s, _t) = Int::gcd(&x, &y);
        assert_eq!(gcd.mag, vec![12]);
        //assert_eq!(gcd, x.mul(&_s).add(&y.mul(&_t)).0);

        let x = Int::from_le_digits_vec(hex::le_vec_u64("0x2f0ece5b1ee9c15e132a01d55768dc13"));
        let y = Int::from_le_digits_vec(hex::le_vec_u64("0x1c6f4fd9873cdb24466e6d03e1cc66e7"));
        let (gcd, _s, _t) = Int::gcd(&x, &y);
        assert_eq!(gcd.mag, vec![1]);
    }

    #[test]
    fn large_01() {
        init_logger(true);
        let x = Int::from_le_digits_vec(hex::le_vec_u64("0x1bddff867272a9296ac493c251d7f46f09a5591fe"));
        let y = Int::from_le_digits_vec(hex::le_vec_u64("0xb55930a2a68a916450a7de006031068c5ddb0e5c"));
        let (gcd, _s, _t) = Int::gcd(&x, &y);
        assert_eq!(gcd.mag, vec![2]);
    }
}
