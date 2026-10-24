//! Differential test: the Aeneas-friendly patched crate must behave exactly like
//! upstream. Exhaustive on all inputs up to 3 bytes, random beyond that.
use std::borrow::Cow;
use std::env;
extern crate patched;

fn sets_up() -> Vec<&'static upstream::AsciiSet> {
    vec![upstream::CONTROLS, upstream::NON_ALPHANUMERIC, &upstream::AsciiSet::EMPTY]
}
fn sets_pa() -> Vec<&'static patched::AsciiSet> {
    vec![patched::CONTROLS, patched::NON_ALPHANUMERIC, &patched::AsciiSet::EMPTY]
}

fn check(input: &[u8], su: &'static upstream::AsciiSet, sp: &'static patched::AsciiSet) {
    let a: Vec<&str> = upstream::percent_encode(input, su).collect();
    let b: Vec<&str> = patched::percent_encode(input, sp).collect();
    assert_eq!(a, b, "encode chunks differ on {:?}", input);
    let a: Vec<u8> = upstream::percent_decode(input).collect();
    let b: Vec<u8> = patched::percent_decode(input).collect();
    assert_eq!(a, b, "decode differs on {:?}", input);
    // Display, Debug and the alloc conversions (patch 2).
    let (eu, ep) = (upstream::percent_encode(input, su), patched::percent_encode(input, sp));
    assert_eq!(format!("{}", eu), format!("{}", ep), "Display differs on {:?}", input);
    assert_eq!(format!("{:?}", eu), format!("{:?}", ep), "Debug differs on {:?}", input);
    assert_eq!(format!("{:#?}", eu), format!("{:#?}", ep), "Debug# differs on {:?}", input);
    let (cu, cp): (Cow<str>, Cow<str>) = (eu.into(), ep.into());
    assert_eq!(cu, cp, "Cow<str> differs on {:?}", input);
    assert_eq!(matches!(cu, Cow::Owned(_)), matches!(cp, Cow::Owned(_)), "Cow<str> variant differs on {:?}", input);
    let (du, dp) = (upstream::percent_decode(input), patched::percent_decode(input));
    assert_eq!(format!("{:?}", du), format!("{:?}", dp), "decode Debug differs on {:?}", input);
    let (cu, cp): (Cow<[u8]>, Cow<[u8]>) = (du.clone().into(), dp.clone().into());
    assert_eq!(cu, cp, "Cow<[u8]> differs on {:?}", input);
    assert_eq!(matches!(cu, Cow::Owned(_)), matches!(cp, Cow::Owned(_)), "Cow<[u8]> variant differs on {:?}", input);
    let (ru, rp) = (du.clone().decode_utf8(), dp.clone().decode_utf8());
    match (&ru, &rp) {
        (Ok(x), Ok(y)) => {
            assert_eq!(x, y, "decode_utf8 differs on {:?}", input);
            assert_eq!(matches!(x, Cow::Owned(_)), matches!(y, Cow::Owned(_)), "decode_utf8 variant differs on {:?}", input);
        }
        (Err(x), Err(y)) => assert_eq!(x, y, "decode_utf8 error differs on {:?}", input),
        _ => panic!("decode_utf8 Ok/Err differs on {:?}", input),
    }
    let (lu, lp) = (du.decode_utf8_lossy(), dp.decode_utf8_lossy());
    assert_eq!(lu, lp, "decode_utf8_lossy differs on {:?}", input);
    assert_eq!(matches!(lu, Cow::Owned(_)), matches!(lp, Cow::Owned(_)), "decode_utf8_lossy variant differs on {:?}", input);
}

fn main() {
    let random_cases: u64 = env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(2_000_000);
    let (su, sp) = (sets_up(), sets_pa());
    // Interesting alphabet for length-3 exhaustive: all 256 values.
    let mut n = 0u64;
    for k in 0..su.len() {
        check(&[], su[k], sp[k]);
        for a in 0..=255u8 {
            check(&[a], su[k], sp[k]);
            for b in 0..=255u8 {
                check(&[a, b], su[k], sp[k]);
                if k == 0 { for c in 0..=255u8 { check(&[a, b, c], su[k], sp[k]); n += 1; } }
            }
        }
    }
    // Random longer inputs biased toward '%', hex digits and boundary bytes.
    let alphabet: Vec<u8> = b"%%%%0123456789abcdefABCDEFgG z\x00\x1f\x7f\x80\xff".to_vec();
    let mut x: u64 = 0x9E3779B97F4A7C15;
    let mut next = || { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x };
    for _ in 0..random_cases {
        let len = (next() % 24) as usize;
        let biased = next() % 2 == 0;
        let v: Vec<u8> = (0..len).map(|_| {
            let r = next();
            if biased { alphabet[(r % alphabet.len() as u64) as usize] } else { r as u8 }
        }).collect();
        let k = (next() % 3) as usize;
        check(&v, su[k], sp[k]);
        n += 1;
    }
    println!("difftest OK: {} cases (exhaustive up to length 2 for 3 sets, length 3 for CONTROLS, plus random)", n);
}
