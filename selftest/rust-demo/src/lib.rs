/// Saturating add: the Lean fixture proves it never overflows and equals min(a+b, MAX).
pub fn add_sat(a: u32, b: u32) -> u32 {
    if a > u32::MAX - b { u32::MAX } else { a + b }
}
