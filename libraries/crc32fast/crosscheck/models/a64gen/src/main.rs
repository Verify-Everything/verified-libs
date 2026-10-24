// Runs the aarch64 CRC32B / CRC32X instructions on random inputs (real CPU or qemu) and prints
// `name 0 crc data result` in hex for ModelCheckA64.lean.
use core::arch::aarch64::{__crc32b, __crc32d};
struct Rng(u64);
impl Rng { fn u64(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 } }
#[target_feature(enable = "crc")]
unsafe fn run(r: &mut Rng, k: usize) {
    for i in 0..k {
        let c = if i % 7 == 0 { 0 } else if i % 11 == 0 { u32::MAX } else { r.u64() as u32 };
        let b = r.u64() as u8; let d = if i % 13 == 0 { 0 } else { r.u64() };
        println!("crc32b 0 {c:x} {b:x} {:x}", __crc32b(c, b));
        println!("crc32d 0 {c:x} {d:x} {:x}", __crc32d(c, d));
    }
}
fn main() {
    let k: usize = std::env::args().nth(1).map(|s| s.parse().unwrap()).unwrap_or(1000);
    if !std::arch::is_aarch64_feature_detected!("crc") { eprintln!("CPU lacks crc"); std::process::exit(2); }
    let mut r = Rng(0x9E37_79B9_7F4A_7C15);
    unsafe { run(&mut r, k) }
}
