// Differential test: crc32fast vs a bitwise reference CRC-32, random data, random splits.
fn reference(mut crc: u32, data: &[u8]) -> u32 {
    crc = !crc;
    for &b in data {
        crc ^= b as u32;
        for _ in 0..8 { crc = if crc & 1 != 0 { (crc >> 1) ^ 0xEDB8_8320 } else { crc >> 1 }; }
    }
    !crc
}
struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 } }
fn main() {
    let cases: u64 = std::env::args().nth(1).map(|s| s.parse().unwrap()).unwrap_or(20000);
    let mut r = Rng(0x9E37_79B9_7F4A_7C15);
    let mut buf = vec![0u8; 1 << 16];
    for b in buf.iter_mut() { *b = r.next() as u8; }
    let mut n = 0u64;
    for i in 0..cases {
        let len = match i % 4 { 0 => (r.next() % 64) as usize, 1 => (r.next() % 1024) as usize, 2 => (r.next() % 8192) as usize, _ => (r.next() % 65536) as usize };
        let off = (r.next() % 64) as usize; let len = len.min(buf.len() - off);
        let data = &buf[off..off + len];
        let init = if i % 3 == 0 { 0 } else { r.next() as u32 };
        let want = reference(init, data);
        // one pass
        let mut h = crc32fast::Hasher::new_with_initial(init); h.update(data);
        assert_eq!(h.clone().finalize(), want, "one pass len={len} off={off}");
        // random split
        let k = if len == 0 { 0 } else { (r.next() as usize) % (len + 1) };
        let mut a = crc32fast::Hasher::new_with_initial(init); a.update(&data[..k]); a.update(&data[k..]);
        assert_eq!(a.finalize(), want, "split len={len} k={k}");
        // combine
        let mut x = crc32fast::Hasher::new_with_initial(init); x.update(&data[..k]);
        let mut y = crc32fast::Hasher::new(); y.update(&data[k..]);
        x.combine(&y);
        assert_eq!(x.finalize(), want, "combine len={len} k={k}");
        if init == 0 { assert_eq!(crc32fast::hash(data), want); }
        n += 1;
    }
    println!("ok {n} cases");
    // byte counter at the top of u64 (fork: wraps; upstream: panics with overflow checks)
    let mut h = crc32fast::Hasher::new_with_initial_len(0, u64::MAX); h.update(b"x");
    let mut g = crc32fast::Hasher::new(); g.update(b"x");
    let mut z = crc32fast::Hasher::new_with_initial_len(0, u64::MAX); z.combine(&g);
    println!("overflow case finalize={:08x} {:08x}", h.finalize(), z.finalize());
}
