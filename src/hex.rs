/*
    Copyright 2024 M. Devi Prasad (dp@web3pleb.org)

    Licensed under the Apache License, Version 2.0 (the "License");
    you may not use this file except in compliance with the License.
    You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

    Unless required by applicable law or agreed to in writing, software
    distributed under the License is distributed on an "AS IS" BASIS,
    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
    See the License for the specific language governing permissions and
    limitations under the License.
*/

pub fn val(c: u8) -> Result<u8, char> {
    match c {
        b'0'..=b'9' => Ok(c - b'0'),
        b'a'..=b'f' => Ok(10 + c - b'a'),
        b'A'..=b'F' => Ok(10 + c - b'A'),
        _ => {
            log::error!("hex - reject '{}'", c as char);
            Err(c as char)
        },
    }
}

// obtains the u64 value of the hex str 's'
// pre-conditions:
// 's' must be a str of at most 16 hex chars; it cannot be empty.
// panics on bad input.
pub fn to_u64(s: &[u8]) -> u64 {
    assert!(s.len() > 0 && s.len() <= 16);
    let mut n: u64 = 0;
    let mut k: u64 = 0;
    for &hd in s.iter().rev() {
        match val(hd) {
            Ok(v) => {
                n += v as u64 * (1 << k*4);
                k += 1;
            }
            Err(c) => panic!("bad hex char '{c}'")
        }
    }
    n
}

// creates a 'big-endian' vector of u64 values.
// may prefix the given hex str with adequate number of zeroes so the length is a multiple of 16.
pub fn vec_u64(s: &str) -> Vec<u64> {
    if !(&s[0..2] == "0x") {
        panic!("hex string must start with '0x'; found {:#?}", s[0..2].to_ascii_lowercase());
    }

    let maybe_prefix_zeros = |s: &str| -> Vec<u8> {
        let n = s.len() % 16;
        let mut lzs: Vec<u8> = if n > 0 {
            [b'0'].repeat(16 - n)
        } else {
            [].into()
        };
        lzs.extend_from_slice(s.as_bytes());
        lzs
    };

    let vu64: Vec<u64> =
        maybe_prefix_zeros(&s[2..])
            .chunks(16)
            .map(|hc| to_u64(hc))
            .collect();

        // #[cfg(noob)]
        if cfg!(noob)
        {
            // c-like iteration for storing numbers
            let mut be_vec = vec![0u64; 0];
            let be_hs = maybe_prefix_zeros(&s[2..]);
            for hc in be_hs.chunks(16) {
                be_vec.push(to_u64(hc))
            }
            let len = be_hs.len() / 16 +
                match be_hs.len() % 16 {
                    0 => 0,
                    _ => 1
                };
            log::info!("noob - vec_u64: {s}");
            assert_eq!(be_vec.len(), len);
            assert_eq!(vu64, be_vec);
        }
    vu64
}

pub fn le_vec_u64(s: &str) -> Vec<u64> {
    let mut v = vec_u64(s);
    v.reverse();
    v
}

// RUSTLOG="info" RUSTFLAGS="--cfg=release_test --cfg=noob -Adead_code -Aunused"  RUSTDOCFLAGS="--cfg=release_test --cfg=noob -Adead_code -Aunused" cargo test hex_tests::test_short_chunk  -- --show-output
#[cfg(test)]
mod hex_tests {
    use crate::hex::{le_vec_u64, vec_u64};

    #[test]
    fn test_short_chunk() {
        crate::init_logger(true);
        {
            let v = le_vec_u64("0x0");
            assert_eq!(v, [0]);
        }
        {
            let s = "0x000000000000000100000000000000020000000000000003000000000000000400000000000000050000000000000006";
            let v = le_vec_u64(s);
            assert_eq!(v, [6, 5, 4, 3, 2, 1]);
            let v = vec_u64(s);
            assert_eq!(v, [1, 2, 3, 4, 5, 6]);
        }
        {
            let v = le_vec_u64("0x00000000000000000000000000000000000000000000000000000000000000000000000000");
            assert_eq!(v, [0, 0, 0, 0, 0]);
        }
        {
            let v = le_vec_u64("0xffff");
            assert_eq!(v, [0xffff]);
        }
        {
            let v = le_vec_u64("0x10000");
            assert_eq!(v, [65536]);
        }
        {
            let v = le_vec_u64("0xffff");
            assert_eq!(v, [0xffff]);
        }
        {
            let v = le_vec_u64("0xffffffffffffffffffffffffffffffff");
            assert_eq!(v, [0xffffffffffffffff, 0xffffffffffffffff]);
        }
        {
            let v = vec_u64("0x2f684bda12f684bdc71c71c71c71c71c8e38e38e38e38e38f684bda12f684bda");
            assert_eq!(v, [0x2f684bda12f684bd, 0xc71c71c71c71c71c, 0x8e38e38e38e38e38, 0xf684bda12f684bda]);
        }
        {
            let v = le_vec_u64("0x100000000000000010000000000000002");
            assert_eq!(v, [2, 1, 1]);

            let v = le_vec_u64("0x40000000000000001");
            assert_eq!(v, [1, 4]);
        }
    }
}
