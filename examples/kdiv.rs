use std::ops::Div;
use buckle::bits;

//
// https://news.ycombinator.com/item?id=26562819
// https://skanthak.hier-im-netz.de/division.html
// https://github.com/hcs0/Hackers-Delight/blob/master/divmnu.c.txt
//

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
        match buckle::hex::val(hd) {
            Ok(v) => {
                // log::info!("to_u16 s = {s:?} n = {n} v = {v}, k = {k}, p = {}", 1u32 << k*4);
                n += v as u16 * (1_u16 << k * 4);
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
        if s > 0 {
            wn[i] = (w[i] << s) | (w[i - 1] >> (D16::BITS - s));
        } else {
            wn[i] = w[i];
        }
    }
    wn[0] = w[0] << s;
    wn
}

pub fn _add32_(x: u32, y: u32) -> u32 {
    x.overflowing_add(y).0
}

pub fn _add32_16(x: u32, y: u16) -> u32 {
    x.overflowing_add(y as u32).0
}

pub fn _add16_(x: u16, y: u16) -> u16 {
    x.overflowing_add(y).0
}

fn _mul32_16(x: u32, y: u16) -> u32 {
    x.overflowing_mul(y as u32).0
}

fn _mul_32_(x: u32, y: u32) -> u32 {
    x.overflowing_mul(y).0
}

pub fn _sub16_(x: u16, y: u16) -> u16 {
    x.overflowing_sub(y).0
}

pub fn _sub32_(x: u32, y: u32) -> (u32, u32) {
    //(x.saturating_sub(y), false)
    let t = x.overflowing_sub(y);
    (t.0, t.1 as u32)
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

const BASE: u32 = 1 << 16;

fn div(u: &Vec<D16>, v: &Vec<D16>) -> Vec<D16> {
    let m = u.len();
    let n = v.len();
    assert!(n > 1 && v[n - 1] > 0 && m >= n);
    let s = d16_nlz(v[n - 1]);
    assert!(s <= 15);
    let vn = d16_normalize(&v, s, false);
    let mut un = d16_normalize(&u, s, true);
    let mut q: u32 = 0;
    let mut quotient = vec![0u16; m - n + 1];

    for j in (0..=m - n).rev() {
        #[allow(unused_labels)]
        'D3: { // calculate q
            let mut r: u32 = 0;
            let un_s2d: u32 = _add32_16(_mul32_16(BASE, un[j + n]), un[j + n - 1]);
            let vn_ld: u32 = vn[n - 1] as u32;
            q = un_s2d / vn_ld;
            r = un_s2d % vn_ld;
            log::info!("\tD3. Calculate q.");
            // log::info!("\t\tj = {j}, {un_s2d}/{vn_ld}, r = {}, q = {}", r, q);
            // log::info!("\t\tq_correction: q = {q}, v[n-2] = {}, _mul32_(q, vn[n - 2] as u32) = {},  vn[n-1] = {vn_ld}, r = {r}, un[j+n-2] = {}, (_mul32_(BASE, r) + un[j + n - 2] as u32) = {}", (vn[n - 2] as u32), _mul32_(q, vn[n - 2] as u32), (un[j + n - 2] as u32), (_mul32_(BASE, r) + un[j + n - 2] as u32));
            while q >= BASE ||
                r < BASE &&
                    _mul32_16(q, vn[n - 2]) > _add32_16(_mul_32_(BASE, r), un[j + n - 2]) {
                q -= 1;
                r += vn_ld;
            }
        }
        let mut t: i16 = 0;
        //
        #[allow(unused_labels)]
        'D4: {
            // multiply and subtract
            log::info!("\tD4. multiply and subtract");
            let mut k: u32 = 0;
            for i in 0..n {
                let p: u32 = _mul32_16(q, vn[i]);
                let (t, c1) = _sub32_(un[i + j] as u32, p & 0xFFFF);
                let t = t & 0xFFFF;
                let (t, c2) = _sub32_(t, k);
                let t = t & 0xFFFF;
                un[i + j] = t as u16;
                let (k3, c3) = _sub32_(p >> D16::BITS, t >> 16);
                k = k3 + c1 + c2 + c3;
            }
            t = _sub16_(un[j + n], k as u16) as i16;
            un[j + n] = t as u16;
        }
        //
        #[allow(unused_labels)]
        'D5: {
            quotient[j] = q as u16; // tentative quotient digit
        }
        //
        #[allow(unused_labels)]
        'D6: {
            // add back
            if t < 0 {
                log::info!("\tD6. add-back");
                quotient[j] = quotient[j] - 1;
                let mut k: u16 = 0;
                for i in 0..n {
                    // let mut t: u32 = (un[i + j] as u32 + vn[i] as u32) + k as u32;
                    let mut t = _add32_16(_add32_16(un[i + j] as u32, vn[i]), k);
                    un[i + j] = t as u16;
                    k = (t >> D16::BITS) as u16;
                }
                un[j + n] = _add16_(un[j + n], k);
            }
        }
    }

    quotient
}
/*
 * Simple test mode:
    RUSTFLAGS="--cfg=release_test --cfg=noob -Adead_code -Aunused"
        RUSTDOCFLAGS="--cfg=release_test  -Adead_code -Aunused" cargo test -- --show-output
 * and, for 'release' mode testing:
    RUSTFLAGS="--cfg=release_test --cfg=noob -Adead_code -Aunused"
        RUSTDOCFLAGS="--cfg=release_test  -Adead_code -Aunused" cargo test --release -- --show-output
*/
#[cfg(test)]
mod d16_k_tests {
    use buckle::init_logger;
    use crate::{D16, d16_nlz, d16_normalize, le_vec_u16};
    use super::{D16, d16_nlz, d16_normalize, div, le_vec_u16, magnitude};

    #[test]
    fn u16_arith() {
        assert_eq!(2_u16.overflowing_sub(3_u16), (0xFFFF, true));
        let (t1, o1) = 2_u16.overflowing_sub(3_u16); //  0xFF
        let (t2, o2) = t1.overflowing_sub(1_u16);
        assert_eq!(t2, 0xFFFE);
        assert_eq!(o1, true);
        assert_eq!(o2, false);
        let (t2, o3) = t1.overflowing_sub(0xFFFF);
        assert_eq!((t2, o3), (0, false));
        let (t2, o3) = t2.overflowing_sub(0xFFFF);
        assert_eq!(o3, true);

        let (t1, o1) = 2_u16.overflowing_sub(4_u16); //  0xFFFE
        let (t2, o2) = t1.overflowing_sub(0xFFFF); // 0xFFFE - 0xFFFF
        assert_eq!(t1, 0xFFFE);
        assert_eq!(t2, 0xFFFF);
        assert_eq!(o1, true);
        assert_eq!(o2, true);

        let (t3, o3) = t1.overflowing_sub(0xFFFD); // 0xFFFE - 0xFFFD
        assert_eq!(t3, 1);
        assert_eq!(o3, false);
    }

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
            //Case(vec![0xffff, 0xffff], vec![0x0000, 0x0001], vec![0xffff]), // pass
            Case(vec![0x7899, 0xbcde], vec![0x789a, 0xbcde], vec![0]),  // pass

            // 0x89ab + 2**16*0x4567 + 2**32 * 0x0123 == 1250999896491
            // 2**16*0x0001 == 65536
            // 1250999896491 / 65536
            Case(vec![0x89ab, 0x4567, 0x0123], vec![0x0000, 0x0001], vec![0x4567, 0x0123]),  // pass

            // Shows that first q_hat can = b + 1.
            // (0xfffe * 2**16 + 0x8000 * 2**32) == 140741783191552
            // (0xffff +  2**16 * 0x8000) == 2147549183
            // 140741783191552 / 2147549183 == 65535
            Case(vec![0, 0xfffe, 0x8000], vec!(0xffff, 0x8000), vec!(0xffff, 0x0000)),  // pass

            // add-back required
            // 0x0003 + 2**16 * 0x0000 + 2**32 * 0x8000 == 140737488355331
            // 140737488355331 // 35184372088833 == 3
            Case(vec![0x0003, 0x0000, 0x8000], vec!(0x0001, 0x0000, 0x2000), vec!(0x0003)),

            // add-back required
            // 9223231299366420480 // 140737488355329 == 65534
            Case(vec![0, 0, 0x8000, 0x7fff], vec![1, 0, 0x8000], vec![0xfffe, 0]),

            // Shows that multiply-and-subtract quantity cannot be treated as signed.
            // 2**16 * 0xfffe + 2**48 * 0x8000 == 9223372041149612032
            // 0xffff + 2**32 * 0x8000 == 140737488420863
            // 9223372041149612032 // 140737488420863 == 65535
            Case(vec![0, 0xfffe, 0, 0x8000], vec![0xffff, 0, 0x8000], vec![0xffff, 0]),
            Case(vec![0x0001, 0x8000], vec![0x7000, 0x4000], vec![0x0001]),
            Case(vec![0x7899, 0xbcde], vec![0x789a, 0xbcde], vec![0]),
            Case(le_vec_u16("0x9c25b0d79a4e5ec95f28657deb3a4ef0e5c551a0"),
                 le_vec_u16("0xd39396bb325dbf5d"),
                 le_vec_u16("0x0000bceebb7803a068b8c8eef5b9")),
            Case(le_vec_u16("0xb72406bf2b361790bfbf125e738ce735cecd1d529c25b0d79a4e5ec95f28657deb3a4ef0e5c551a0"),
                 le_vec_u16("0x6df4c2dfdc781bfc2dae1207156c1a6aea0a572180213c261b13"),
                 le_vec_u16("0x1aa637af3a1f551eb3dfc6f23a601")),

            /* python3
               import secrets
               u = secrets.token_hex(512)
               v = secrets.token_hex(128)
               u // v
             */
            Case(le_vec_u16("0xadc7011f7cb2c70717809dea93d4dfb886e041a33736532d216d1cdb3e1b8003fde8b82bb45c9cf122c72d495a3810912277f40970519d9e634ed426b3b2a867267a3d2b92794ce64238bef94b30fd35ed24cd09b5428f7ba1c92da4fc47850057e45f1a5ac7559d1db39d89bf0e67fcc6a4e407ec2de17863418886ac3b2d041420eb89cf38adf170692c28231d6d3dd63e51bfc7b6b16063ba59f34d82ccf9ac0f73cd7c413468837eea72c9b6d96994edcdd3095ca09929dbe1b322b626493b378519357d1871a1b496be64858d9ece5079f3a842e4ea1760994aed31788d772af9823f410c5dfa8a8ed4320106fc446dcbcd48fdcdc6c44f49944418b180b9b08253b81b922acbaf99baeb8a3ea453c3fe8273c14c6a5d33f2f206e667bb93b7f755c715fb14dcc751939a9801310eed0c80e14ac5900f3794d97a46e73a34f70f9b336b9cd847da95e5d49f9aace97ff772bf258419b260d1c3059ff238abb2370aa3a227d579d28bd04c4de2e749b826ae0ce8279a2df60de27c12ed869c6e7c74089feb4051873a151e6f7d050dcd51157f3d270b02a678274dd357b251a4102368411072c0ce475c46e754092aed0384d67045f54e9d9e1e71f70968a9526b6b21da2998458f3e22925ba104b0656cb786123ec58a11f4f03a4e311c9e73bf66e97067fdfeb5c98ea3e194dd3cd3cdbc893fd7db4501686e1d9fc16a"),
                 le_vec_u16("0xa5197e1da39f842701db6e381f154501702ef1dcb2ae5cdc8122a3782ee00e9a2b13e0468a26afa3921ff6f3e5c09269e46dc373c61d09de3bc76be60578402878bdafbf89cf8f2b579367a9b92fb975d4291fd929eb5a4c6736e6275a879fc7b0a1cb6215e586c0b6d75be72c2e80fde4c9dd974c764428a65273a66fbb8e0e"),
                 le_vec_u16("0x10d74a15716432f223505d3bde3a4c6b53bb2f730b8a959f18983805503f895fae7929756df468f1ed57e3544ffa851fcdd701d4ddf184c471696b99265e180205a454ecc1b24eeb76c4863be48314332f9ee41529187c16bd639937270ff0667048b7a6e197695c3ecbc82a107c2004d4801f79c60eb3b368dd2f72b6b3ed9ae9a8981a7843302cc4f5876a95adf3483c83d4d5ee10ca4a36e757100a08de24d9010f847409466ed05f54ad98fcc9496d598dca9624924e8e9a3ca1ee6c5ce34fa282f34b0cd5482a0038873eeb3c1a5b9b95dddf3cd62a876d5f4679652512113691038cc7173e68ec0751e2d807943aefbdb530786fcd7d387eb790b9db74be724334e7ba7ee1515343c73fbe1e50fb80c4601c67fc8242207a0cbe4d18f125b625c9a00f5b26d0cea96cb3aec5d7cc208f4c37a086b351db780a8b3af9ca15ce3d217f958eac02d4273ef4b9d5067ce6f3a8c2fda216fe09c7122eef94310678319b1575e050ebad4c700816e62ac4643bcaa1d9390340cab33a91f254218")),
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

fn main() {}