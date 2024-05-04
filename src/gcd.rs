use crate::{Digit, Int};

impl Int {
    fn check_invariant(_tag: &str, x: &Int, y: &Int, s: &Int, t: &Int, u: &Int, v: &Int, alpha: &Int, beta: &Int) {
        {
            let sxa = s.mul(&alpha).compact();
            let txb = t.mul(&beta).compact();
            let sxa_plus_txb = Int::isum_cx(&sxa, &txb);
            assert_eq!(*y, sxa_plus_txb, "[{_tag}] [y value] ");
        }
        {
            let uxa = u.mul(&alpha).compact();
            let vxb = v.mul(&beta).compact();
            let uxa_plus_vxb = Int::isum_cx(&uxa, &vxb);
            assert_eq!(*x, uxa_plus_vxb, "[{_tag}] [x value] ");
        }
    }

    // extended binary GCD algorithm
    pub fn xb_gcd(a: &Int, b: &Int) -> (/* gcd */Int, /* s */Int, /* t */ Int) {
        let (a, b, _) = a.compare_abs(&b);
        let (mut x, mut y) = (a.compact(), b.compact());
        if x.is_zero() && y.is_zero() {
            return (Int::zero(Digit::BITS), Int::zero(Digit::BITS), Int::zero(Digit::BITS))
        }
        if x.is_zero() {
            return (y, Int::zero(Digit::BITS), Int::one(Digit::BITS))
        }
        if y.is_zero() {
            return (x, Int::one(Digit::BITS), Int::zero(Digit::BITS))
        }

        let mut sr: u64 = 1;
        while x.even() && y.even() {
            x.shrs_mut(1);
            y.shrs_mut(1);
            sr *= 2;
        }

        let alpha = x.clone();
        let beta = y.clone();

        let (mut u, mut v, mut s, mut t) = (Int::one(Digit::BITS),
                                            Int::zero(Digit::BITS),
                                            Int::zero(Digit::BITS),
                                            Int::one(Digit::BITS));

        let mut dbg_step: u64 = 0;
        // from here on the following invariant will be maintained
        // x = u * alpha + v * beta, and
        // y = s * alpha + t * beta
        Self::check_invariant(&"Init_1", &x, &y, &s, &t, &u, &v, &alpha, &beta);
        while x.even() {
            dbg_step += 1;
            x.shrs_mut(1);
            if u.even() && v.even() {
                u.shrs_mut(1);
                v.shrs_mut(1);
            } else {
                u = Self::isum_cx(&u, &beta);
                u.shrs_mut(1);
                v = Self::isub(&v, &alpha);
                v.shrs_mut(1);
            }
        }
        Self::check_invariant(&"Init_2", &x, &y, &s, &t, &u, &v, &alpha, &beta);

        dbg_step = 0;
        while x.ne(&y) {
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
                } else {
                    s = Self::isum_cx(&s, &beta);
                    s.shrs_mut(1);
                    t = Self::isub(&t, &alpha);
                    t.shrs_mut(1);
                }
            } else if y.lt(&x) {
                std::mem::swap(&mut x, &mut y);
                std::mem::swap(&mut u, &mut s);
                std::mem::swap(&mut v, &mut t);
            } else {
                y = Self::isub(&y, &x);
                s = Self::isub(&s, &u);
                t = Self::isub(&t, &v);
            }
            dbg_step += 1;
            Self::check_invariant(&format!("Step {}", dbg_step), &x, &y, &s, &t, &u, &v, &alpha, &beta);
        }
        eprintln!();
        x = x.compact();
        log::info!("[{dbg_step} steps]. answer = {sr} * {x:?}");
        let gcd = x.mul_digit(sr).compact();
        assert_eq!(gcd, Int::isum_cx(&a.mul(&s), &b.mul(&t)));
        (gcd, s, t)
    }
}

#[cfg(test)]
mod xb_gcd_tests {
    use crate::{Digit, hex, init_logger, Int};

    #[test]
    fn xb_gcd_10_4() {
        init_logger(true);
        let x = Int::new_digit(Digit::BITS, 10);
        let y = Int::new_digit(Digit::BITS, 4);
        let (gcd, s, t) = Int::xb_gcd(&x, &y);
        assert_eq!(gcd.mag, vec![2]);
        assert_eq!(gcd, Int::isum_cx(&x.mul(&s), &y.mul(&t)));
    }

    #[test]
    fn xb_gcd_23_71() {
        init_logger(true);
        let y = Int::new_digit(Digit::BITS, 71);
        let x = Int::new_digit(Digit::BITS, 23);
        let (gcd, t, s) = Int::xb_gcd(&x, &y);
        assert_eq!(gcd.mag, vec![1]);
        assert_eq!(gcd.mag, Int::isum_cx(&x.mul(&s), &y.mul(&t)).compact().mag);
    }

    #[test]
    fn gcd_0_0() {
        init_logger(true);
        let (gcd, _, _) = Int::xb_gcd(&Int::zero(8 * 1024), &Int::zero(30 * 1024));
        assert_eq!(gcd.mag, vec![0]);

        let (one, two) = (Int::one(8 * 1024), Int::new_digit(30 * 1024, 2));
        let (gcd, s, t) = Int::xb_gcd(&two, &one);
        assert_eq!(gcd.mag, vec![1]);
        assert_eq!(s.mag, vec![0]);
        assert_eq!(t.mag, vec![1]);
        assert_eq!(gcd.mag, Int::isum_cx(&two.mul(&s), &one.mul(&t)).compact().mag);
    }

    #[test]
    fn gcd_generic() {
        init_logger(true);

        let (gcd, _, _) = Int::xb_gcd(&Int::zero(8 * 1024), &Int::zero(16 * 1024));
        assert_eq!(gcd.mag, vec![0]);

        let x = Int::new_digit(Digit::BITS, 383);
        let y = Int::new_digit(Digit::BITS, 271);
        let (gcd, s, t) = Int::xb_gcd(&x, &y);
        assert_eq!(gcd.mag, vec![1]);
        assert_eq!(gcd.mag, Int::isum_cx(&x.mul(&s), &y.mul(&t)).compact().mag);

        let x = Int::new_digit(Digit::BITS, 21);
        let y = Int::new_digit(Digit::BITS, 1203);
        let (gcd, t, s) = Int::xb_gcd(&y, &x);
        assert_eq!(gcd.mag, vec![3]);
        assert_eq!(gcd.mag, Int::isum_cx(&x.mul(&s), &y.mul(&t)).compact().mag);

        let x = Int::new_digit(Digit::BITS, 19932);
        let y = Int::new_digit(Digit::BITS, 468);
        let (gcd, s, t) = Int::xb_gcd(&x, &y);
        assert_eq!(gcd.mag, vec![12]);
        assert_eq!(gcd.mag, Int::isum_cx(&x.mul(&s), &y.mul(&t)).compact().mag);

        let x = Int::from_le_digits_vec(hex::le_vec_u64("0x2f0ece5b1ee9c15e132a01d55768dc13"));
        let y = Int::from_le_digits_vec(hex::le_vec_u64("0x1c6f4fd9873cdb24466e6d03e1cc66e7"));
        let (gcd, s, t) = Int::xb_gcd(&x, &y);
        assert_eq!(gcd.mag, vec![1]);
        assert_eq!(gcd.mag, Int::isum_cx(&x.mul(&s), &y.mul(&t)).compact().mag);
    }

    #[test]
    fn large_01() {
        init_logger(true);
        let x = Int::from_le_digits_vec(hex::le_vec_u64("0x1bddff8672798818702628404586660124231666590441350907779881665195127924124302499409069557482037680503618674958345165348598546621611058181932992384466619862a9296ac493c251d7f46f09a5591fe"));
        let y = Int::from_le_digits_vec(hex::le_vec_u64("0x155930538409855781710263070340545529285331804072344415991929979941742087976920492592737cd12832002646692252892099898498983185530082598031944449317211a2a68a916450a7de006031068c5ddb0e5c0"));
        let (gcd, s, t) = Int::xb_gcd(&y, &x);
        assert_eq!(gcd.mag, vec![2]);
        assert_eq!(gcd.mag, Int::isum_cx(&x.mul(&s), &y.mul(&t)).compact().mag);
    }

    #[test]
    fn gcd_prime_512bits() {
        init_logger(true);
        let x = Int::from_le_digits_vec(hex::le_vec_u64("0xfaf6c5bb3ceb44b53ba8e5c2bfca16f8ec39abcd20d563a3d1164cecbe17d28b94400baed8aa90c6a79edff01e694814846178bf92341441ceca6a81efb5e157"));
        let y = Int::from_le_digits_vec(hex::le_vec_u64("0xd1207993b73101bc62ca7a4ae2ffc3c15709094afb5537f9b21a0a882ab5be1e2532194518acde235ddd9368eb3b153a8b2604575730b0065474b9e40e72e78d"));
        let (gcd, s, t) = Int::xb_gcd(&y, &x);
        assert_eq!(gcd.mag, vec![1]);
        assert_eq!(gcd.mag, Int::isum_cx(&x.mul(&s), &y.mul(&t)).compact().mag);
    }

    #[test]
    fn gcd_prime_128bits() {
        init_logger(true);
        let x = Int::from_le_digits_vec(hex::le_vec_u64("0xfaf6c5bb3ceb44b53ba8e5c2bfca16f8"));
        let y = Int::from_le_digits_vec(hex::le_vec_u64("0xd1207993b73101bc62ca7a4ae2ffc3c1"));
        let (gcd, s, t) = Int::xb_gcd(&x, &y);
        assert_eq!(gcd.mag, vec![17]);
        assert_eq!(gcd.mag, Int::isum_cx(&x.mul(&s), &y.mul(&t)).compact().mag);
    }
}
