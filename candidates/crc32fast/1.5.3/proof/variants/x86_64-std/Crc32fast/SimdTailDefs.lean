import Crc32fast.SimdSpec

/-!
# The end of `reduce_128_to_crc`: the partial last block and the Barrett reduction

Both are written here as pure functions that follow the Rust code step by step, so the
code proofs only have to unfold the monadic version.
-/

open x86

namespace Crc32Spec

def mask32 : BitVec 128 := 0#32 ++ 0#32 ++ 0#32 ++ (~~~0#32)
def k5 : BitVec 128 := 0#64 ++ 0x163cd6124#64
def pu : BitVec 128 := 0x1F7011641#64 ++ 0x1DB710641#64

/-- The three folding steps after the last full block, ending in the 32-bit CRC register. -/
def barrett (x : BitVec 128) : BitVec 32 :=
  let x3 := clmulSel 16#32 x k3k4 ^^^ srliBytes 8#32 x
  let x4 := clmulSel 0#32 (x3 &&& mask32) k5 ^^^ srliBytes 4#32 x3
  let t1 := clmulSel 16#32 (x4 &&& mask32) pu
  let t2 := clmulSel 0#32 (t1 &&& mask32) pu
  extract32 1#32 (x4 ^^^ t2)

def seqBytes : BitVec 128 :=
  fromBytes 128 ((List.range 16).map fun i => BitVec.ofNat 8 i)

def set1 (b : BitVec 8) : BitVec 128 := fromBytes 128 (List.replicate 16 b)

/-- Shuffle controls for a tail of `n` bytes (`n - 16` as a byte, then XOR 0x80). -/
def shlCtl (n : Nat) : BitVec 128 := addBytes seqBytes (set1 (BitVec.ofNat 8 (n + 240)))
def shrCtl (n : Nat) : BitVec 128 := shlCtl n ^^^ set1 0x80#8

/-- Merge the last `n < 16` bytes `p` (zero-padded block) into the register `x`. -/
def tailStep (n : Nat) (x p : BitVec 128) : BitVec 128 :=
  (shuffle x (shrCtl n) ^^^ shuffle p (shlCtl n)) ^^^ F k3k4 (shuffle x (shlCtl n))

end Crc32Spec
