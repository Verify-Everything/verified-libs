//! Cross-check of the Aeneas translation (tests/CrossCheck.lean evaluates the extracted Lean
//! code) against the compiled, unpatched upstream crate. Each line: `kind|input|expected`.
use percent_encoding::*;
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

/// The sets used for encoding, built through the public API. Ids must match CrossCheck.lean.
fn sets() -> Vec<&'static AsciiSet> {
    let v = vec![
        CONTROLS.add(0),
        NON_ALPHANUMERIC.add(0),
        CONTROLS.add(b' ').add(b'"').add(b'#').add(b'<').add(b'>'),
        NON_ALPHANUMERIC.remove(b'-').remove(b'.').remove(b'_').remove(b'~'),
        CONTROLS.complement(),
        CONTROLS.union(NON_ALPHANUMERIC.remove(b'%')),
        (!CONTROLS.add(0)) + CONTROLS.add(0),
    ];
    v.into_iter().map(|s| &*Box::leak(Box::new(s))).collect()
}

fn mask(s: &'static AsciiSet) -> String {
    let mut m = [0u8; 16];
    for b in 0..128u8 {
        // contains() is private upstream; should_percent_encode = contains || non-ASCII.
        if percent_encode(&[b], s).next() != Some(std::str::from_utf8(&[b]).unwrap()) {
            m[(b / 8) as usize] |= 1 << (b % 8);
        }
    }
    hex(&m)
}

fn rand_bytes(rng: &mut Rng, max: u64) -> Vec<u8> {
    let len = rng.below(max + 1) as usize;
    (0..len)
        .map(|_| match rng.below(6) {
            0 => b'%',
            1 => b"0123456789abcdefABCDEFgG"[rng.below(24) as usize],
            2 => 0x80 + rng.below(0x80) as u8,
            _ => rng.below(256) as u8,
        })
        .collect()
}

fn main() {
    let n: usize = std::env::args().nth(1).map(|s| s.parse().unwrap()).unwrap_or(50_000);
    let stdout = std::io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    let mut rng = Rng(0xD1B54A32D192ED03);
    let sets = sets();
    for (i, s) in sets.iter().enumerate() {
        writeln!(out, "set|{}|{}", i, mask(s)).unwrap();
    }
    // AsciiSet::add / remove on a non-ASCII byte panic (index out of bounds).
    for b in [0x80u8, 0xC3, 0xFF] {
        let a = std::panic::catch_unwind(|| CONTROLS.add(b)).is_err();
        let r = std::panic::catch_unwind(|| CONTROLS.remove(b)).is_err();
        writeln!(out, "addrm|{:02x}|{}{}", b, if a { "P" } else { "-" }, if r { "P" } else { "-" }).unwrap();
    }
    for k in 0..n {
        let input = if k < 256 { vec![k as u8] } else { rand_bytes(&mut rng, 24) };
        let si = rng.below(sets.len() as u64) as usize;
        let it = percent_encode(&input, sets[si]);
        let (lo, hi) = it.size_hint();
        let chunks: Vec<&str> = it.clone().collect();
        let joined: String = chunks.concat();
        let disp = it.to_string();
        assert_eq!(disp, joined);
        let cow: Cow<str> = it.into();
        let var = if matches!(cow, Cow::Borrowed(_)) { "B" } else { "O" };
        writeln!(
            out,
            "enc|{},{}|{};{};{};{},{}",
            si,
            hex(&input),
            chunks.len(),
            hex(joined.as_bytes()),
            var,
            lo,
            hi.unwrap()
        )
        .unwrap();

        let d = percent_decode(&input);
        let (lo, hi) = d.size_hint();
        let dec: Vec<u8> = d.clone().collect();
        let cow: Cow<[u8]> = d.clone().into();
        let cv = if matches!(cow, Cow::Borrowed(_)) { "B" } else { "O" };
        let u = match d.clone().decode_utf8() {
            Ok(Cow::Borrowed(s)) => format!("VB{}", hex(s.as_bytes())),
            Ok(Cow::Owned(s)) => format!("VO{}", hex(s.as_bytes())),
            Err(_) => "I".to_string(),
        };
        let l = match d.decode_utf8_lossy() {
            Cow::Borrowed(s) => format!("B{}", hex(s.as_bytes())),
            Cow::Owned(s) => format!("O{}", hex(s.as_bytes())),
        };
        writeln!(out, "dec|{}|{};{};{};{};{},{}", hex(&input), hex(&dec), cv, u, l, lo, hi.unwrap()).unwrap();
    }
}
