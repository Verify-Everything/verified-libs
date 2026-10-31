//! Test vectors for the hand-written std models in external/FunsExternal.lean.
//! Each line: `kind|input|expected`, computed by real Rust std. tests/ModelTest.lean
//! evaluates the Lean model on every input and compares. Hex is lowercase, no separators.
use std::borrow::Cow;
use std::io::{BufWriter, Write};

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{:02x}", x)).collect()
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

// Bytes at the edges of the UTF-8 lead/continuation ranges (Unicode Table 3-7).
const EDGE: [u8; 25] = [
    0x00, 0x41, 0x7F, 0x80, 0x8F, 0x90, 0x9F, 0xA0, 0xBF, 0xC0, 0xC1, 0xC2, 0xDF, 0xE0, 0xE1,
    0xEC, 0xED, 0xEE, 0xEF, 0xF0, 0xF1, 0xF3, 0xF4, 0xF5, 0xFF,
];

fn utf8_line(out: &mut impl Write, b: &[u8]) {
    // from_utf8 (core and String): validity. from_utf8_lossy: variant + bytes.
    let valid = std::str::from_utf8(b).is_ok();
    assert_eq!(valid, String::from_utf8(b.to_vec()).is_ok());
    let lossy = String::from_utf8_lossy(b);
    let (var, bytes) = match &lossy {
        Cow::Borrowed(s) => ("B", s.as_bytes()),
        Cow::Owned(s) => ("O", s.as_bytes()),
    };
    writeln!(out, "utf8|{}|{}{}{}", hex(b), if valid { "V" } else { "I" }, var, hex(bytes)).unwrap();
    lossy_borrow_check(b, valid);
}

// Named assumption A-lossy-ptr (creusot/README.md): for NON-EMPTY valid UTF-8 `v`,
// String::from_utf8_lossy(v) is Cow::Borrowed at v's own address and length. Checked on a slice
// and on a Vec's buffer (the case in decode_utf8_lossy). Empty input is excluded on purpose: std
// returns a static "" there, which can sit at a different address (README.md).
fn lossy_borrow_check(b: &[u8], valid: bool) {
    if b.is_empty() || !valid {
        return;
    }
    let owned = b.to_vec();
    for v in [b, &owned[..]] {
        let ok = match String::from_utf8_lossy(v) {
            Cow::Borrowed(s) => std::ptr::eq(s.as_bytes() as *const [u8], v as *const [u8]),
            Cow::Owned(_) => false,
        };
        if !ok {
            eprintln!("A-lossy-ptr fails for input {}", hex(v));
            std::process::exit(1);
        }
    }
}

fn main() {
    let n_random: usize = std::env::args().nth(1).map(|s| s.parse().unwrap()).unwrap_or(200_000);
    let stdout = std::io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut rng = Rng(0x9E3779B97F4A7C15);
    std::panic::set_hook(Box::new(|_| {}));

    // char::from(u8), u8::is_ascii: every byte.
    for b in 0..=255u8 {
        writeln!(out, "char_from_u8|{:02x}|{:x}", b, char::from(b) as u32).unwrap();
        writeln!(out, "is_ascii|{:02x}|{}", b, b.is_ascii() as u8).unwrap();
    }
    // char::to_digit: every radix 0..=40 on chars U+0000..U+02FF plus some far ones.
    // Rust panics for radix outside 2..=36: expected "P".
    let mut chars: Vec<u32> = (0..0x300).collect();
    chars.extend([0xFF10, 0xFF21, 0xFF41, 0x10FFFF, 0x1D7CE]);
    for radix in 0..=40u32 {
        for &c in &chars {
            let ch = char::from_u32(c).unwrap();
            let r = std::panic::catch_unwind(|| ch.to_digit(radix));
            let e = match r {
                Err(_) => "P".to_string(),
                Ok(None) => "N".to_string(),
                Ok(Some(d)) => format!("{:x}", d),
            };
            writeln!(out, "to_digit|{:x},{:x}|{}", c, radix, e).unwrap();
        }
    }
    // UTF-8: all inputs of length <= 2, all length 3 and 4 over EDGE, random ones.
    utf8_line(&mut out, &[]);
    for a in 0..=255u8 {
        utf8_line(&mut out, &[a]);
        for b in 0..=255u8 {
            utf8_line(&mut out, &[a, b]);
        }
    }
    for &a in &EDGE {
        for &b in &EDGE {
            for &c in &EDGE {
                utf8_line(&mut out, &[a, b, c]);
                for &d in &EDGE {
                    utf8_line(&mut out, &[a, b, c, d]);
                }
            }
        }
    }
    for _ in 0..n_random {
        let len = rng.below(17) as usize;
        let v: Vec<u8> = (0..len)
            .map(|_| match rng.below(4) {
                0 => EDGE[rng.below(EDGE.len() as u64) as usize],
                1 => 0x80 + rng.below(0x40) as u8,
                _ => rng.below(256) as u8,
            })
            .collect();
        utf8_line(&mut out, &v);
    }
    // Valid strings (random scalar values) through String ops.
    for _ in 0..20_000 {
        let mk = |rng: &mut Rng| -> String {
            let len = rng.below(6) as usize;
            (0..len)
                .map(|_| loop {
                    let c = match rng.below(4) {
                        0 => rng.below(0x80) as u32,
                        1 => rng.below(0x800) as u32,
                        2 => rng.below(0x10000) as u32,
                        _ => rng.below(0x110000) as u32,
                    };
                    if let Some(ch) = char::from_u32(c) {
                        break ch;
                    }
                })
                .collect()
        };
        let a = mk(&mut rng);
        let b = mk(&mut rng);
        let c = mk(&mut rng);
        // to_owned, push_str, extend(iter of &str), String::from_utf8_unchecked round trip.
        let mut s = a.as_str().to_owned();
        s.push_str(&b);
        s.extend([c.as_str(), b.as_str()]);
        writeln!(out, "strops|{},{},{}|{}", hex(a.as_bytes()), hex(b.as_bytes()), hex(c.as_bytes()), hex(s.as_bytes())).unwrap();
    }
    // Slices: split_first, Iter::len / as_slice after k steps, to_owned, Vec::extend.
    for _ in 0..20_000 {
        let len = rng.below(10) as usize;
        let v: Vec<u8> = (0..len).map(|_| rng.below(256) as u8).collect();
        let k = if len == 0 { 0 } else { rng.below(len as u64 + 1) as usize };
        let mut it = v.iter();
        for _ in 0..k {
            it.next();
        }
        let sf = match v.split_first() {
            None => "N".to_string(),
            Some((x, r)) => format!("{:02x},{}", x, hex(r)),
        };
        let mut w = v[..k].to_owned();
        w.extend(it.clone().copied());
        writeln!(out, "slice|{},{}|{};{};{};{}", hex(&v), k, sf, it.len(), hex(it.as_slice()), hex(&w)).unwrap();
    }
}
