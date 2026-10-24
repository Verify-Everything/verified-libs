import Crc32fast.Baseline

/-!
# Public API: `hash` and `Hasher`

`Hasher::update` with the baseline kernel (`spec = none`). The API-level theorems for every
kernel are in `HasherFull.lean`.
-/

open Aeneas Aeneas.Std Result crc32fast Crc32Spec

namespace Crc32fastVerif

theorem U64.add_ok (x y : U64) (h : x.val + y.val ≤ U64.max) :
    ∃ z : U64, z.val = x.val + y.val ∧ (x + y : Result U64) = ok z := by
  simp only [HAdd.hAdd, UScalar.add, UScalar.tryMk, UScalar.tryMkOpt]
  have hc : UScalar.check_bounds UScalarTy.U64 (Add.add x.val y.val) = true := by
    simp only [UScalar.check_bounds, decide_eq_true_eq]
    show x.val + y.val < _
    scalar_tac
  rw [dif_pos hc]
  exact ⟨_, by simp, rfl⟩

/-- `Hasher::update` with the baseline kernel advances the state by the spec's `update`; the byte
count wraps modulo 2^64 (the verified fix). -/
theorem update_eq (h : Hasher) (buf : Slice U8) (hs : h.spec = none) :
    h.update buf = ok {
      amount := core.num.U64.wrapping_add h.amount (UScalar.cast .U64 (Slice.len buf)),
      state := ⟨update h.state.bv (bytes buf.val)⟩, spec := none } := by
  unfold Hasher.update
  simp only [lift]
  rw_bind; rw_bind
  rw [hs]
  simp only []
  rw [update_fast_16_eq]
  rw_bind

theorem slice_len_le_u64 (s : Slice U8) : s.length ≤ U64.max := by
  have h1 : s.length ≤ Usize.max := by scalar_tac
  have h2 : Usize.max ≤ U64.max := by
    simp only [Usize.max, U64.max]
    have : Usize.numBits ≤ U64.numBits := by
      cases System.Platform.numBits_eq <;> simp [Usize.numBits, U64.numBits, *]
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) this
    omega
  exact le_trans h1 h2

end Crc32fastVerif
