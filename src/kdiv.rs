use std::ops::Div;

use crate::{bits, Digit};

type D16 = u16;

// obtains the u64 value of the hex str 's'
// pre-conditions:
// 's' must be a str of at most 16 hex chars; it cannot be empty.
// panics on bad input.
pub fn to_u16(s: &[u8]) -> D16 {
    assert!(s.len() > 0 && s.len() <= 4);
    let mut n: u16 = 0;
    let mut k: u16 = 0;
    for &hd in s.iter().rev() {
        match crate::hex::val(hd) {
            Ok(v) => {
                log::info!("to_u16 s = {s:?} n = {n} v = {v}, k = {k}, p = {}", (1u32 << k*4));
                n += v as u16 * (1u16 << k * 4);
                k += 1;
            }
            Err(c) => panic!("bad hex char {}", c)
        }
    }
    n
}

// creates a 'big-endian' vector of u64 values.
// may prefix the given hex str with adequate number of zeroes so the length is a multiple of 16.
pub fn vec_u16(s: &str) -> Vec<D16> {
    if !(&s[0..2] == "0x") {
        panic!("hex string must start with '0x'; found {:#?}", s[0..2].to_ascii_lowercase());
    }

    let maybe_prefix_zeros = |s: &str| -> Vec<u8> {
        let n = s.len() % 4;
        let mut lzs: Vec<u8> = if n > 0 {
            [b'0'].repeat(4 - n)
        } else {
            [].into()
        };
        lzs.extend_from_slice(s.as_bytes());
        lzs
    };

    let vu16: Vec<D16> =
        maybe_prefix_zeros(&s[2..])
            .chunks(4)
            .map(|hc| to_u16(hc))
            .collect();

    // #[cfg(noob)]
    if cfg!(noob)
    {
        // c-like iteration for storing numbers
        let mut be_vec = vec![0u16; 0];
        let be_hs = maybe_prefix_zeros(&s[2..]);
        for hc in be_hs.chunks(4) {
            be_vec.push(to_u16(hc))
        }
        let len = be_hs.len() / 4 +
            match be_hs.len() % 4 {
                0 => 0,
                _ => 1
            };
        log::info!("noob - vec_u16: {s}");
        assert_eq!(be_vec.len(), len);
        assert_eq!(vu16, be_vec);
    }
    vu16
}

pub fn le_vec_u16(s: &str) -> Vec<D16> {
    let mut v = vec_u16(s);
    v.reverse();
    v
}

fn d16_len(a: D16) -> u32 {
    let mut len = 0;
    let mut x = a as usize;
    if x >= 1 << 8 {
        x >>= 8;
        len += 8;
    }
    return len + bits::LEN_8[x] as u32
}

fn d16_nlz(x: D16) -> u32 {
    D16::BITS - d16_len(x)
}

fn _shr16_(x: D16, s: u16) -> u16 {
    (x >> (-(s as i16) & 15)) & ((-(s as i16) >> 15) as D16)
}

fn d16_normalize(w: &Vec<D16>, s: u32, expand: bool) -> Vec<D16> {
    let mut wn = vec![0; w.len() + expand as usize];
    let m = w.len();
    if expand {
        if s > 0 {
            wn[m] = w[m - 1] >> (D16::BITS - s);
        }
    }
    for i in (1..m).rev() {
        // we are careful about the case where c == 64.
        if s > 0 {
            wn[i] = (w[i] << s) | (w[i - 1] >> (D16::BITS - s));
        } else {
            wn[i] = w[i];
        }
        // wn[i] = (w[i] << s) | _shr16_(w[i - 1], (D16::BITS - s) as u16);
    }
    wn[0] = w[0] << s;
    wn
}

pub fn _add32_(x: u32, y: u32) -> u32 {
    if cfg!(debug_assertions) {
        x.overflowing_add(y).0
    } else {
        x + y
    }
}

fn _mul32_(x: u32, y: u32) -> u32 {
    if cfg!(debug_assertions) {
        x.overflowing_mul(y).0
    } else {
        x * y
    }
}

fn magnitude(digits: &Vec<u16>) -> u128 {
    let mut v = 0_u128;
    let mut k = 0_u128;
    for &d in digits {
        v += (d as u128) * (1 << (k * 16));
        k += 1;
    }
    v
}

fn div(u: &Vec<D16>, v: &Vec<D16>) -> Vec<D16> {
    log::info!("{}", "-".repeat(70));
    let m = u.len();
    let n = v.len();
    assert!(n >= 1 && v[n - 1] > 0 && m >= n);
    let s = d16_nlz(v[n - 1] as D16); // 0 <= s <= 15
    let vn = d16_normalize(&v, s, false);
    let mut un = d16_normalize(&u, s, true);
    log::info!("Normalized Divisor: {v:?} << {s} ==> {vn:?}");
    log::info!("Normalized Dividend: {u:?} << {s} ==> {un:?}");
    const BASE: u32 = 1 << 16;
    const BASE_MASK: u32 = BASE - 1;
    let mut q: u32 = 0;
    let mut quotient = vec![0u16; m - n + 1];

    for j in (0..=m - n).rev() {
        log::info!("Iteration {j}: m = {m}, n = {n}, m-n = {}", m-n);
        #[allow(unused_labels)]
        'D3: { // calculate q
            let mut r: u32 = 0;
            let un_s2d: u32 = (un[j + n] as u32 * BASE) + un[j + n - 1] as u32;
            let vn_ld: u32 = vn[n - 1] as u32;
            q = un_s2d / vn_ld;
            r = un_s2d % vn_ld;
            log::info!("\tD3. Calculate q.");
            log::info!("\t\tj = {j}, {un_s2d}/{vn_ld}, r = {}, q = {}", r, q);
            while q >= BASE ||
                _mul32_(q, vn[n - 2] as u32) > (_mul32_(BASE, r) + un[j + n - 2] as u32) {
                log::info!("\t\t q_correction: q = {q}, v[n-1] = {vn_ld}, vn[n-2] = {}, r = {r}, un[j+n-2] = {}", (vn[n - 2] as u32), (un[j + n - 2] as u32));
                q -= 1;
                r += vn_ld;
                // log::info!("\t\t q and r ");
            }
        }
        let mut t: i32 = 0;
        //
        #[allow(unused_labels)]
        'D4: { // multiply and subtract
            let mut k: i32 = 0;
            log::info!("\tD4. multiply and subtract");
            for i in 0..n {
                // assert_eq!(k & 0xFFFF0000u32 as i32, 0);
                let p: u32 = _mul32_(q, vn[i] as u32);
                let (t1, o1) = (un[i + j] as u16).overflowing_sub((p & BASE_MASK) as u16);
                let (t2, o2) = t1.overflowing_sub(k as u16);
                un[i + j] = t2 as u16;
                assert!(o1 as u32 + o2 as u32 <= 2);
                let mut _o3_ = true;
                let (k3, _o3_) = ((p >> D16::BITS) as i32).overflowing_sub((t >> D16::BITS) as i32 + o1 as i32 + o2 as i32);
                assert_eq!(_o3_, false);
                k = k3 as i32
            }
            t = (un[j + n] as i32 - k as i32) as i32;
            un[j + n] = t as D16;
        }
        #[allow(unused_labels)]
        'D5: {
            quotient[j] = q as u16; // tentative quotient digit
        }
        #[allow(unused_labels)]
        'D6: { // add back
            if t < 0 {
                log::warn!("\tD6. add-back");
                quotient[j] = quotient[j] - 1; //
                let mut k: u32 = 0;
                for i in 0..n {
                    let mut t: u32 = (un[i + j] as u32 + vn[i] as u32) + k as u32;
                    un[i + j] = t as u16;
                    k = (t >> D16::BITS) as u32;
                }
                un[j + n] = un[j + n] + k as D16;
            }
        }
        log::info!("Step Result: j = {j}, quotient = {quotient:?}");
    }
    log::info!("");
    log::info!("Result: quotient = {quotient:?}");
    log::info!("{}", "-".repeat(70));
    quotient
}

#[cfg(test)]
mod d16_k_tests {
    use crate::init_logger;
    use crate::kdiv::{D16, d16_nlz, d16_normalize, div, le_vec_u16, magnitude};

    #[test]
    fn vec16_normalize() {
        init_logger(true);
        {
            let x = vec![1; 1];
            assert_eq!(d16_nlz(x[0]), 15);
            let xn = d16_normalize(&x, 15, false);
            assert_eq!(xn, [1 << 15]);
        }
        {
            let x = vec![0x8000u16; 1];
            assert_eq!(d16_nlz(x[0]), 0);
            let xn = d16_normalize(&x, d16_nlz(x[0]), true);
            assert_eq!(xn, [1 << 15, 0]);
        }
    }

    #[test]
    fn kat() {
        init_logger(true);
        struct Case(Vec<D16>, Vec<D16>, Vec<u16>);
        let cases: Vec<Case> = vec![
            Case(vec![0xffff, 0xffff], vec![0x0000, 0x0001], vec![0xffff]),
            Case(vec![0x7899, 0xbcde], vec![0x789a, 0xbcde], vec![0]),
            Case(vec![0x89ab, 0x4567, 0x0123], vec![0x0000, 0x0001], vec![0x4567, 0x0123]), // 1250999896491 / 65536

            // (0xfffe * 2**16 + 0x8000 * 2**32) == 140741783191552
            // (0xffff +  2**16 * 0x8000) == 2147549183
            // (140741783191552, 2147549183, 65535)
            // Case(vec![0, 0xfffe, 0x8000], vec!(0xffff, 0x8000), vec!(0xffff, 0x0000))

            // add-back required
            // 0x0003 + 2**16 * 0x0000 + 2**32 * 0x8000 == 140737488355331
            // 140737488355331 // 35184372088833 == 3
            //Case(vec![0x0003, 0x0000, 0x8000], vec!(0x0001, 0x0000, 0x2000), vec!(0x0003)),

            // add-back required
            // 9223231299366420480 // 140737488355329 == 65534
            // Case(vec![0, 0, 0x8000, 0x7fff], vec![1, 0, 0x8000], vec![0xfffe]),

            // Shows that multiply-and-subtract quantity cannot be treated as signed.
            // 0xfffe + 2**32 * 0x8000 + 2**48 * 0xffff
            // 9223372041149612032 // 140737488420863
            //Case(vec![0, 0xfffe, 0, 0x8000], vec![0xffff, 0, 0x8000], vec![0xffff]),

        ];

        for case in cases {
            let q = div(&case.0, &case.1);
            assert_eq!(q, case.2);
        }
    }

    #[test]
    fn div_01() {
        init_logger(true);
        {
            let u: Vec<D16> = vec![0, 0, 1];
            let v: Vec<D16> = vec![0, 2];
            assert_eq!(magnitude(&u), 1 << 32);
            assert_eq!(magnitude(&v), 1 << 17);
            let q = div(&u, &v);
            assert_eq!(q, [32768, 0]);
        }
        {
            let u: Vec<D16> = vec![1, 1, 0];
            let v: Vec<D16> = vec![1, 1];
            assert_eq!(magnitude(&u), 65537);
            assert_eq!(magnitude(&v), 65537);
            let q = div(&u, &v);
            assert_eq!(q, [1, 0]);

            let u: Vec<D16> = vec![1, 1];
            let v: Vec<D16> = vec![1, 1];
            assert_eq!(magnitude(&u), 65537);
            assert_eq!(magnitude(&v), 65537);
            let q = div(&u, &v);
            assert_eq!(q, [1]);
        }
        {
            let u: Vec<D16> = vec![1, 10, 4];
            let v: Vec<D16> = vec![1, 5];
            assert_eq!(magnitude(&u), 17180524545);
            assert_eq!(magnitude(&v), 327681);
            let q = div(&u, &v);
            assert_eq!(q, [52430, 0]);
        }
        {
            // vec![1, 10, 10] == le_vec_u16("0xa000a0001") == 42950328321
            // vec![1, 10, 5] == le_vec_u16("0x5000a0001") ==  21475491841
            let u: Vec<D16> = le_vec_u16("0x5000a0001");
            let v: Vec<D16> = le_vec_u16("0x50001"); // == 327681
            assert_eq!(u, vec![1, 10, 5]);
            assert_eq!(v, vec![1, 5]);
            assert_eq!(magnitude(&u), 21475491841);
            assert_eq!(magnitude(&v), 327681);
            let q = div(&u, &v); // == 65537
            assert_eq!(q, [1, 1]);

            let u: Vec<D16> = le_vec_u16("0xa000a0001"); // == 42950328321
            let v: Vec<D16> = le_vec_u16("0x50001"); // == 327681
            assert_eq!(u, vec![1, 10, 10]);
            assert_eq!(v, vec![1, 5]);
            assert_eq!(magnitude(&u), 42950328321);
            assert_eq!(magnitude(&v), 327681);
            let q = div(&u, &v); // == 131073
            assert_eq!(q, [1, 2]);

            let u: Vec<D16> = le_vec_u16("0x64000a000a0001"); // == 28147540621393921
            let v: Vec<D16> = le_vec_u16("0x1400050001"); // == 85899673601
            assert_eq!(u, vec![1, 10, 10, 100]); // 1 + 10 * 2**16 + 10 * 2**32 + 100 * 2**48
            assert_eq!(v, vec![1, 5, 20]); // 1 + (5 * 2**16) + (20 * 2**32)
            assert_eq!(magnitude(&u), 28147540621393921);
            assert_eq!(magnitude(&v), 85899673601);
            let q = div(&u, &v); // == 327679
            assert_eq!(q, [65535, 4]);
        }
    }
}