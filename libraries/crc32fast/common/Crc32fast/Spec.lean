/-!
# Reference specification of CRC-32 (IEEE 802.3 / zlib / PNG)

This is the textbook bit-at-a-time definition of the reflected CRC-32 with
polynomial `0x04C11DB7` (reflected form `0xEDB88320`), initial value
`0xFFFFFFFF` and final XOR `0xFFFFFFFF`. It has no tables and no unrolling, so
it can be checked against the standard by reading it.

`update prev data` matches crc32fast's convention: `prev` is a finished CRC
value (0 for "nothing hashed yet"), and the result is the finished CRC of the
previous data followed by `data`.
-/

namespace Crc32Spec

/-- The CRC-32 polynomial, bit-reflected. -/
def POLY : BitVec 32 := 0xEDB88320#32

/-- Shift the register right by one bit, XOR-ing in the polynomial when a 1
falls off the end. -/
def bitStep (c : BitVec 32) : BitVec 32 :=
  if c.getLsbD 0 then (c >>> 1) ^^^ POLY else c >>> 1

/-- Feed one byte: XOR it into the low byte of the register, then do 8 bit steps. -/
def byteStep (c : BitVec 32) (b : BitVec 8) : BitVec 32 :=
  let c := c ^^^ b.zeroExtend 32
  bitStep (bitStep (bitStep (bitStep (bitStep (bitStep (bitStep (bitStep c)))))))

/-- The raw register after feeding `data` (no initial or final inversion). -/
def crcRaw (c : BitVec 32) (data : List (BitVec 8)) : BitVec 32 :=
  data.foldl byteStep c

/-- Continue a finished CRC `prev` with more `data`. -/
def update (prev : BitVec 32) (data : List (BitVec 8)) : BitVec 32 :=
  ~~~ (crcRaw (~~~ prev) data)

/-- The CRC-32 of a byte string. -/
def crc32 (data : List (BitVec 8)) : BitVec 32 :=
  update 0#32 data

/-! ## Sanity checks against published check values -/

private def bytes (s : String) : List (BitVec 8) :=
  s.toUTF8.toList.map (fun b => b.toBitVec)

-- The standard CRC-32 check value (e.g. Greg Cook's CRC catalogue, "CRC-32/ISO-HDLC").
example : crc32 (bytes "123456789") = 0xCBF43926#32 := by decide +kernel
example : crc32 [] = 0#32 := by decide +kernel
-- Test vectors used in crc32fast's own test suite.
example : crc32 (bytes "hello world") = 0x0d4a1185#32 := by decide +kernel

/-! ## Basic algebra of the spec -/

theorem crcRaw_nil (c : BitVec 32) : crcRaw c [] = c := rfl

theorem crcRaw_cons (c : BitVec 32) (b : BitVec 8) (l : List (BitVec 8)) :
    crcRaw c (b :: l) = crcRaw (byteStep c b) l := rfl

theorem crcRaw_append (c : BitVec 32) (l₁ l₂ : List (BitVec 8)) :
    crcRaw c (l₁ ++ l₂) = crcRaw (crcRaw c l₁) l₂ := by
  simp [crcRaw, List.foldl_append]

/-- Incremental updates agree with a single pass. -/
theorem update_append (prev : BitVec 32) (l₁ l₂ : List (BitVec 8)) :
    update (update prev l₁) l₂ = update prev (l₁ ++ l₂) := by
  simp [update, crcRaw_append]

theorem update_nil (prev : BitVec 32) : update prev [] = prev := by
  simp [update, crcRaw_nil]

end Crc32Spec
