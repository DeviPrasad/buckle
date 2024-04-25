#[allow(unused_variables)]
#[allow(unused_labels)]
#[allow(dead_code)]

use std::io::Write;
use chrono::Local;
use env_logger::Builder;
use log::LevelFilter;

pub fn init_logger(is_test: bool) {
    let _ = Builder::new()
        .format(|buf, record| {
            writeln!(buf,
                     "{} [{}] - {}",
                     Local::now().format("%Y-%m-%dT%H:%M:%S"),
                     record.level(),
                     record.args()
            )
        })
        .filter(None, LevelFilter::Info)
        .is_test(is_test)
        .format_timestamp_secs()
        .try_init();
}

pub type Digit = u64;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum IntStrPadding {
    Minimal,
    Full,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum IntStrCase {
    Lower,
    Upper,
}


#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct Int {
    // Declared count of bits in the magnitude.
    cb: u32,
    // sign = 1 in the case of positive integers; and -1 for negative integers.
    // sign = 0 when the magnitude is zero.
    // This invariant is maintained by all operations.
    sign: i32,
    // 'lnzd' stands for "leading non-zero digit".
    // 'lnzb' stands for "leading non-zero bit".
    // 'pos_lnzb' is the zero-based index of the lnzb within lnzd.
    // These two fields are invariants.
    // Zero-based index of the leading (or most-significant) non-zero digit in 'mag'.
    // When Int magnitude is zero, 'pos_lnzd' == -1 and 'pos_lnzb' == -1.
    pos_lnzd: i32,
    pos_lnzb: i32,
    // The magnitude of the integer.
    // A sequence of digits aka 'limbs'. Recall that a digit is a 64-bit quantity.
    // Digits are stored in little-endian format.
    // (0, digits.len()] or (0..digits.len-1)
    mag: Vec<Digit>,
}

#[derive(Debug, Eq, PartialEq)]
pub struct U128 {
    lo: Digit,
    hi: Digit
}

pub mod int;
pub mod bits;
pub mod hex;
