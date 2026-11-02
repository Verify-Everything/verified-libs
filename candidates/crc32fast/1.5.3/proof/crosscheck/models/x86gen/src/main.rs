// Runs every x86 intrinsic that crc32fast uses on random inputs on the real CPU and prints
// `name imm arg.. result` (hex; a register is printed as the integer whose bit 8k.. is byte k).
// ModelCheck.lean evaluates the Lean models on the same lines and compares.
use std::arch::x86_64::*;
use std::mem::transmute;
struct Rng(u64);
impl Rng {
    fn u64(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 }
    fn u128(&mut self) -> u128 { ((self.u64() as u128) << 64) | self.u64() as u128 }
    fn bytes<const N: usize>(&mut self) -> [u8; N] { let mut b = [0u8; N]; for x in b.iter_mut() { *x = self.u64() as u8; } b }
}
fn h128(x: __m128i) -> String { format!("{:x}", unsafe { transmute::<__m128i, u128>(x) }) }
fn h256(x: __m256i) -> String { let l: [u128; 2] = unsafe { transmute(x) }; format!("{:x}{:032x}", l[1], l[0]) }
fn h512(x: __m512i) -> String { let l: [u128; 4] = unsafe { transmute(x) }; format!("{:x}{:032x}{:032x}{:032x}", l[3], l[2], l[1], l[0]) }
fn m128(x: u128) -> __m128i { unsafe { transmute(x) } }
fn m256(l: [u128; 2]) -> __m256i { unsafe { transmute(l) } }
fn m512(l: [u128; 4]) -> __m512i { unsafe { transmute(l) } }
fn n(s: String) -> String { let t = s.trim_start_matches('0'); if t.is_empty() { "0".into() } else { t.into() } }
macro_rules! imm_each { ($imm:ident in [$($v:literal),*] => $body:expr) => { $( { const $imm: i32 = $v; $body; } )* } }

#[target_feature(enable = "sse2,ssse3,sse4.1,pclmulqdq,avx,avx2,avx512f,vpclmulqdq")]
unsafe fn run(r: &mut Rng, k: usize) {
    for _ in 0..k {
        let (a, b) = (r.u128(), r.u128());
        let (ma, mb) = (m128(a), m128(b));
        println!("xor128 0 {a:x} {b:x} {}", n(h128(_mm_xor_si128(ma, mb))));
        println!("and128 0 {a:x} {b:x} {}", n(h128(_mm_and_si128(ma, mb))));
        println!("add_epi8 0 {a:x} {b:x} {}", n(h128(_mm_add_epi8(ma, mb))));
        println!("shuffle_epi8 0 {a:x} {b:x} {}", n(h128(_mm_shuffle_epi8(ma, mb))));
        let c = r.u64() as u32;
        println!("cvtsi32 0 {c:x} {}", n(h128(_mm_cvtsi32_si128(c as i32))));
        let (e1, e0) = (r.u64(), r.u64());
        println!("set_epi64x 0 {e1:x} {e0:x} {}", n(h128(_mm_set_epi64x(e1 as i64, e0 as i64))));
        let d: [u32; 4] = transmute(r.u128());
        println!("set_epi32 0 {:x} {:x} {:x} {:x} {}", d[3], d[2], d[1], d[0], n(h128(_mm_set_epi32(d[3] as i32, d[2] as i32, d[1] as i32, d[0] as i32))));
        let e = r.u64() as u8;
        println!("set1_epi8 0 {e:x} {}", n(h128(_mm_set1_epi8(e as i8))));
        let s: [u8; 16] = r.bytes();
        let si: [i8; 16] = transmute(s);
        let v = _mm_setr_epi8(si[0], si[1], si[2], si[3], si[4], si[5], si[6], si[7], si[8], si[9], si[10], si[11], si[12], si[13], si[14], si[15]);
        println!("setr_epi8 0 {} {}", s.iter().map(|x| format!("{x:x}")).collect::<Vec<_>>().join(" "), n(h128(v)));
        imm_each!(I in [0, 1, 2, 3, 4, 7, 8, 12, 15, 16, 17, 255] => println!("srli_si128 {} {a:x} {}", I, n(h128(_mm_srli_si128::<I>(ma)))));
        imm_each!(I in [0, 1, 2, 3] => println!("extract_epi32 {} {a:x} {:x}", I, _mm_extract_epi32::<I>(ma) as u32));
        imm_each!(I in [0x00, 0x01, 0x10, 0x11] => println!("clmul128 {} {a:x} {b:x} {}", I, n(h128(_mm_clmulepi64_si128::<I>(ma, mb)))));
        // 256
        let (a2, b2) = ([r.u128(), r.u128()], [r.u128(), r.u128()]);
        let (wa, wb) = (m256(a2), m256(b2));
        let qs: [u64; 4] = [r.u64(), r.u64(), r.u64(), r.u64()];
        println!("set256_epi64x 0 {:x} {:x} {:x} {:x} {}", qs[3], qs[2], qs[1], qs[0], n(h256(_mm256_set_epi64x(qs[3] as i64, qs[2] as i64, qs[1] as i64, qs[0] as i64))));
        println!("cast256_128 0 {} {}", n(h256(wa)), n(h128(_mm256_castsi256_si128(wa))));
        println!("cast128_256 0 {a:x} {}", n(h256(_mm256_castsi128_si256(ma))));
        imm_each!(I in [0, 1] => println!("extracti128 {} {} {}", I, n(h256(wa)), n(h128(_mm256_extracti128_si256::<I>(wa)))));
        println!("xor256 0 {} {} {}", n(h256(wa)), n(h256(wb)), n(h256(_mm256_xor_si256(wa, wb))));
        imm_each!(I in [0x00, 0x01, 0x10, 0x11] => println!("clmul256 {} {} {} {}", I, n(h256(wa)), n(h256(wb)), n(h256(_mm256_clmulepi64_epi128::<I>(wa, wb)))));
        // 512
        let (a4, b4) = ([r.u128(), r.u128(), r.u128(), r.u128()], [r.u128(), r.u128(), r.u128(), r.u128()]);
        let (za, zb) = (m512(a4), m512(b4));
        let o: Vec<u64> = (0..8).map(|_| r.u64()).collect();
        println!("set512_epi64 0 {} {}", o.iter().rev().map(|x| format!("{x:x}")).collect::<Vec<_>>().join(" "),
            n(h512(_mm512_set_epi64(o[7] as i64, o[6] as i64, o[5] as i64, o[4] as i64, o[3] as i64, o[2] as i64, o[1] as i64, o[0] as i64))));
        imm_each!(I in [0, 1, 2, 3] => println!("extracti32x4 {} {} {}", I, n(h512(za)), n(h128(_mm512_extracti32x4_epi32::<I>(za)))));
        println!("cast128_512 0 {a:x} {}", n(h512(_mm512_castsi128_si512(ma))));
        println!("cast512_128 0 {} {}", n(h512(za)), n(h128(_mm512_castsi512_si128(za))));
        println!("xor512 0 {} {} {}", n(h512(za)), n(h512(zb)), n(h512(_mm512_xor_si512(za, zb))));
        imm_each!(I in [0x00, 0x01, 0x10, 0x11] => println!("clmul512 {} {} {} {}", I, n(h512(za)), n(h512(zb)), n(h512(_mm512_clmulepi64_epi128::<I>(za, zb)))));
        // unaligned loads (the patch's load128/256/512 helpers)
        let buf: [u8; 80] = r.bytes(); let off = (r.u64() % 16) as usize;
        let hb = buf[off..off + 64].iter().map(|x| format!("{x:x}")).collect::<Vec<_>>().join(" ");
        println!("load128 0 {hb} {}", n(h128(_mm_loadu_si128(buf[off..].as_ptr() as *const __m128i))));
        println!("load256 0 {hb} {}", n(h256(_mm256_loadu_si256(buf[off..].as_ptr() as *const __m256i))));
        println!("load512 0 {hb} {}", n(h512(_mm512_loadu_si512(buf[off..].as_ptr() as *const __m512i))));
    }
}
fn main() {
    let k: usize = std::env::args().nth(1).map(|s| s.parse().unwrap()).unwrap_or(200);
    for f in ["sse2", "ssse3", "sse4.1", "pclmulqdq", "avx2", "avx512f", "vpclmulqdq"] {
        let ok = match f { "sse2" => is_x86_feature_detected!("sse2"), "ssse3" => is_x86_feature_detected!("ssse3"), "sse4.1" => is_x86_feature_detected!("sse4.1"),
            "pclmulqdq" => is_x86_feature_detected!("pclmulqdq"), "avx2" => is_x86_feature_detected!("avx2"), "avx512f" => is_x86_feature_detected!("avx512f"), _ => is_x86_feature_detected!("vpclmulqdq") };
        if !ok { eprintln!("CPU lacks {f}; cannot check all models"); std::process::exit(2); }
    }
    let mut r = Rng(0x2545_F491_4F6C_DD1D);
    unsafe { run(&mut r, k) }
}
