import Crc32fast.Baseline

/-!
# Public API: `hash` and `Hasher`

On the portable build `Hasher::new` always picks the baseline implementation
(`specialized::State` is an empty type there), so `Hasher::update` runs
`update_fast_16`. These theorems tie the public API to the spec.
-/

open Aeneas Aeneas.Std Result crc32fast Crc32Spec

namespace Crc32fastVerif

theorem new_with_initial_len_eq (init : U32) (amount : U64) :
    Hasher.new_with_initial_len init amount = ok { amount, state := init, spec := none } := by
  simp only [Hasher.new_with_initial_len, Hasher.internal_new_specialized, specialized.State.new,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual,
    core.option.Option.unwrap_or_else,
    Hasher.new_with_initial_len.closure.Insts.CoreOpsFunctionFnOnceTupleHasher,
    Hasher.new_with_initial_len.closure.Insts.CoreOpsFunctionFnOnceTupleHasher.call_once,
    Hasher.internal_new_baseline, bind_ok, bind_tc_ok]
  rfl

theorem new_eq : Hasher.new = ok { amount := 0#u64, state := 0#u32, spec := none } := by
  unfold Hasher.new Hasher.new_with_initial DEFAULT_INIT_STATE
  exact new_with_initial_len_eq _ _

theorem U64.add_ok (x y : U64) (h : x.val + y.val ≤ U64.max) :
    ∃ z : U64, z.val = x.val + y.val ∧ (x + y : Result U64) = ok z := by
  simp only [HAdd.hAdd, UScalar.add, UScalar.tryMk, UScalar.tryMkOpt]
  have hc : UScalar.check_bounds UScalarTy.U64 (Add.add x.val y.val) = true := by
    simp only [UScalar.check_bounds, decide_eq_true_eq]
    show x.val + y.val < _
    scalar_tac
  rw [dif_pos hc]
  exact ⟨_, by simp, rfl⟩

/-- `Hasher::update` advances the state by the spec's `update`, provided the
running byte count does not overflow `u64` (Rust would panic in debug builds;
Aeneas models overflow as failure). -/
theorem update_eq (h : Hasher) (buf : Slice U8) (hs : h.spec = none)
    (hlen : h.amount.val + buf.length ≤ U64.max) :
    ∃ amt : U64, amt.val = h.amount.val + buf.length ∧
      h.update buf = ok { amount := amt, state := ⟨update h.state.bv (bytes buf.val)⟩, spec := none } := by
  have hc : (UScalar.cast .U64 (Slice.len buf)).val = buf.length := by
    rw [UScalar.cast_val_eq]; simp only [Slice.len_val]
    apply Nat.mod_eq_of_lt; scalar_tac
  obtain ⟨z, hz, hadd⟩ := U64.add_ok h.amount (UScalar.cast .U64 (Slice.len buf)) (by rw [hc]; exact hlen)
  refine ⟨z, by rw [hz, hc], ?_⟩
  unfold Hasher.update
  simp only [lift]
  rw_bind
  rw [hadd]
  rw_bind
  rw [hs]
  simp only []
  rw [update_fast_16_eq]
  rw_bind

/-- `crc32fast::hash` computes the CRC-32 of its input. -/
theorem hash_eq (buf : Slice U8) : crc32fast.hash buf = ok ⟨crc32 (bytes buf.val)⟩ := by
  have hlen : (0#u64).val + buf.length ≤ U64.max := by
    have h1 : buf.length ≤ Usize.max := by scalar_tac
    have h2 : Usize.max ≤ U64.max := by
      simp only [Usize.max, U64.max, UScalar.max]
      have : Usize.numBits ≤ U64.numBits := by
        cases System.Platform.numBits_eq <;> simp [Usize.numBits, U64.numBits, *]
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) this
      omega
    have := le_trans h1 h2
    simpa using this
  obtain ⟨amt, _, hu⟩ := update_eq { amount := 0#u64, state := 0#u32, spec := none } buf rfl hlen
  unfold crc32fast.hash
  rw [new_eq]
  rw_bind
  rw [hu]
  rw_bind
  rfl

theorem slice_len_le_u64 (s : Slice U8) : s.length ≤ U64.max := by
  have h1 : s.length ≤ Usize.max := by scalar_tac
  have h2 : Usize.max ≤ U64.max := by
    simp only [Usize.max, U64.max]
    have : Usize.numBits ≤ U64.numBits := by
      cases System.Platform.numBits_eq <;> simp [Usize.numBits, U64.numBits, *]
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) this
    omega
  exact le_trans h1 h2

/-- Incremental hashing: feeding `a` then `b` to a `Hasher` gives the same
checksum as `hash` on the concatenation `a ++ b`. -/
theorem update_update_eq_hash (a b c : Slice U8) (hc : c.val = a.val ++ b.val) :
    (do
      let h ← Hasher.new
      let h ← h.update a
      let h ← h.update b
      h.finalize) = crc32fast.hash c := by
  have hlc := slice_len_le_u64 c
  have hl : c.val.length = a.val.length + b.val.length := by simp [hc]
  have hab : a.val.length + b.val.length ≤ U64.max := by
    simp only [Slice.length] at hlc; omega
  obtain ⟨amt1, hamt1, hu1⟩ := update_eq { amount := 0#u64, state := 0#u32, spec := none } a rfl
    (by simp only [Slice.length]; simp; omega)
  obtain ⟨amt2, _, hu2⟩ := update_eq
    { amount := amt1, state := (⟨update (0#u32).bv (bytes a.val)⟩ : U32), spec := none } b rfl
    (by simp only [Slice.length] at hamt1 ⊢; simp at hamt1 ⊢; omega)
  rw [hash_eq, new_eq]
  rw_bind
  rw [hu1]
  rw_bind
  rw [hu2]
  rw_bind
  simp only [Hasher.finalize, hc, bytes, List.map_append]
  congr 2
  simp only [crc32, ← update_append]
  rfl

end Crc32fastVerif
