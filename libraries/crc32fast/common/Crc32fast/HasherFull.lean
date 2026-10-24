import Crc32fast.Variant
import Crc32fast.Hasher
import Crc32fast.Combine

/-!
# The whole public API, whichever kernel `State` picked

Every `update` theorem holds for any `spec : Option State`, so it does not matter what CPU feature
detection returned. `newState` (what `State::new` returns) comes from `Detect.lean`, the one file
that differs between the `std` and `no_std` builds.
-/

open Aeneas Aeneas.Std Result crc32fast Crc32Spec

namespace Crc32fastVerif

theorem cast_len_u64 (buf : Slice U8) : (UScalar.cast .U64 (Slice.len buf)).val = buf.length := by
  rw [UScalar.cast_val_eq]; simp only [Slice.len_val]
  apply Nat.mod_eq_of_lt
  have h1 := slice_len_le_u64 buf
  scalar_tac

/-- `Hasher::update`, any kernel, any input: the state advances by the spec's `update` and the
    byte count by `buf.len()` modulo 2^64. It never fails. -/
theorem update_eq_any (h : Hasher) (buf : Slice U8) :
    h.update buf = ok {
      amount := core.num.U64.wrapping_add h.amount (UScalar.cast .U64 (Slice.len buf)),
      state := ⟨update h.state.bv (bytes buf.val)⟩, spec := h.spec } := by
  unfold Hasher.update
  simp only [lift]
  rw_bind; rw_bind
  rcases hs : h.spec with _ | s
  · simp only []
    rw [update_fast_16_eq]
    rw_bind
  · simp only []
    rw [state_update_eq]
    rw_bind

/-- The byte count after `update` is `amount + buf.len()` modulo 2^64. -/
theorem amount_after (a : U64) (buf : Slice U8) :
    (core.num.U64.wrapping_add a (UScalar.cast .U64 (Slice.len buf))).val = (a.val + buf.length) % 2 ^ 64 := by
  simp only [core.num.U64.wrapping_add, UScalar.wrapping_add_val_eq, cast_len_u64]
  simp [U64.size, U64.numBits]

theorem update_ok (h : Hasher) (buf : Slice U8) : ∃ h', h.update buf = ok h' := ⟨_, update_eq_any h buf⟩

/-- Incremental hashing with any kernel: feeding `a` then `b` gives the CRC of `a ++ b`. -/
theorem update_update_any (h : Hasher) (a b : Slice U8) :
    ∃ h2, (do let h1 ← h.update a; h1.update b) = ok h2 ∧
      h2.state.bv = update h.state.bv (bytes a.val ++ bytes b.val) ∧
      h2.amount.val = (h.amount.val + a.length + b.length) % 2 ^ 64 ∧ h2.spec = h.spec := by
  refine ⟨Hasher.mk
      (core.num.U64.wrapping_add (core.num.U64.wrapping_add h.amount (UScalar.cast .U64 (Slice.len a)))
        (UScalar.cast .U64 (Slice.len b)))
      ⟨update (update h.state.bv (bytes a.val)) (bytes b.val)⟩ h.spec,
    by rw [update_eq_any, bind_ok, update_eq_any], ?_, ?_, rfl⟩
  · show update (update h.state.bv (bytes a.val)) (bytes b.val) = _
    exact (update_append _ _ _)
  · show (core.num.U64.wrapping_add _ _).val = _
    rw [amount_after, amount_after, Nat.mod_add_mod]

/-! ## The rest of the `Hasher` API -/

/-- `Clone` gives back an identical hasher. -/
theorem clone_eq (h : Hasher) : Hasher.Insts.CoreCloneClone.clone h = ok h := by
  rcases h with ⟨amt, st, sp⟩
  unfold Hasher.Insts.CoreCloneClone.clone
  rcases sp with _ | s <;>
    simp only [lift, core.clone.impls.CloneU64.clone, core.clone.impls.CloneU32.clone, bind_ok,
      core.option.Option.Insts.CoreCloneClone.clone, state_clone_eq]

theorem total_len_eq (h : Hasher) : h.total_len = ok h.amount := rfl

theorem finalize_eq (h : Hasher) : h.finalize = ok h.state := rfl

theorem reset_eq (h : Hasher) : h.reset = ok { h with amount := 0#u64, state := 0#u32 } := rfl

theorem default_eq : Hasher.Insts.CoreDefaultDefault.default = Hasher.new := rfl

theorem internal_new_specialized_eq (init : U32) (amount : U64) :
    Hasher.internal_new_specialized init amount =
      ok (newState.map fun s => { amount, state := init, spec := some s }) := by
  unfold Hasher.internal_new_specialized
  rw [state_new_eq, bind_ok]
  generalize newState = o
  rcases o with _ | s <;>
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual, Option.map]

theorem internal_new_baseline_eq (init : U32) (amount : U64) :
    Hasher.internal_new_baseline init amount = ok { amount, state := init, spec := none } := rfl

/-- `new_with_initial_len` keeps `init` and `amount` and takes the kernel `State::new` picked. -/
theorem new_with_initial_len_eq (init : U32) (amount : U64) :
    Hasher.new_with_initial_len init amount = ok { amount, state := init, spec := newState } := by
  unfold Hasher.new_with_initial_len
  rw [internal_new_specialized_eq, bind_ok]
  generalize newState = o
  rcases o with _ | s <;>
    simp only [Option.map, core.option.Option.unwrap_or_else,
      Hasher.new_with_initial_len.closure.Insts.CoreOpsFunctionFnOnceTupleHasher,
      Hasher.new_with_initial_len.closure.Insts.CoreOpsFunctionFnOnceTupleHasher.call_once,
      Hasher.internal_new_baseline, bind_ok, bind_tc_ok]
  rfl

theorem new_with_initial_eq (init : U32) :
    Hasher.new_with_initial init = ok { amount := 0#u64, state := init, spec := newState } := by
  unfold Hasher.new_with_initial
  exact new_with_initial_len_eq _ _

theorem new_eq : Hasher.new = ok { amount := 0#u64, state := 0#u32, spec := newState } := by
  unfold Hasher.new DEFAULT_INIT_STATE
  exact new_with_initial_eq _

/-- `crc32fast::hash` computes the CRC-32 of its input, with whichever kernel was picked. -/
theorem hash_eq (buf : Slice U8) : crc32fast.hash buf = ok ⟨crc32 (bytes buf.val)⟩ := by
  unfold crc32fast.hash
  rw [new_eq, bind_ok, update_eq_any, bind_ok]
  rfl

/-- Incremental hashing: feeding `a` then `b` to a new `Hasher` gives `hash (a ++ b)`. -/
theorem update_update_eq_hash (a b c : Slice U8) (hc : c.val = a.val ++ b.val) :
    (do
      let h ← Hasher.new
      let h ← h.update a
      let h ← h.update b
      h.finalize) = crc32fast.hash c := by
  rw [hash_eq, new_eq, bind_ok, update_eq_any, bind_ok, update_eq_any, bind_ok, finalize_eq]
  simp only [hc, bytes, List.map_append]
  congr 2
  simp only [crc32, ← update_append]
  rfl

/-- `core::hash::Hasher::write` is `update`. -/
theorem write_eq (h : Hasher) (buf : Slice U8) : Hasher.Insts.CoreHashHasher.write h buf = h.update buf := rfl

/-- `core::hash::Hasher::finish` is the CRC widened to `u64`. -/
theorem finish_eq (h : Hasher) :
    Hasher.Insts.CoreHashHasher.finish h = ok ⟨h.state.bv.setWidth 64⟩ := by
  unfold Hasher.Insts.CoreHashHasher.finish
  rw [clone_eq, bind_ok, finalize_eq, bind_ok]
  rfl

/-- `Debug` writes exactly `crc32fast::Hasher` (no fields, no braces) and returns the writer's
    result, whatever the hasher's state. -/
theorem fmt_eq (h : Hasher) (f : core.fmt.Formatter) :
    Hasher.Insts.CoreFmtDebug.fmt h f = ok (core.fmt.Formatter.sink f (toStr "crc32fast::Hasher")) := by
  unfold Hasher.Insts.CoreFmtDebug.fmt
  simp only [core.fmt.Formatter.debug_struct]
  generalize core.fmt.Formatter.sink f (toStr "crc32fast::Hasher") = p
  rcases p with ⟨r, f'⟩
  simp only [bind_ok, uncurry_apply_pair, core.fmt.builders.DebugStruct.finish, Bool.false_eq_true, if_false, id]

/-- Hashing `a` and `b` separately and combining gives `hash(a ++ b)`. -/
theorem combine_eq_hash (a b c : Slice U8) (hc : c.val = a.val ++ b.val) :
    (do
      let ha ← Hasher.new
      let ha ← ha.update a
      let hb ← Hasher.new
      let hb ← hb.update b
      let ha ← ha.combine hb
      ha.finalize) = crc32fast.hash c := by
  have hB : (core.num.U64.wrapping_add 0#u64 (UScalar.cast .U64 (Slice.len b))).val = (bytes b.val).length := by
    have hb : b.val.length < 2 ^ 64 := by
      have := slice_len_le_u64 b; simp [Slice.length, U64.max, U64.numBits] at this; omega
    rw [amount_after]
    simp only [bytes, List.length_map, Slice.length]
    rw [Nat.mod_eq_of_lt (by simp; omega)]; simp
  rw [hash_eq, new_eq, bind_ok, update_eq_any, bind_ok, bind_ok, update_eq_any, bind_ok,
    hasher_combine_eq _ _ (bytes b.val) rfl hB, bind_ok, finalize_eq]
  simp only [hc, bytes, List.map_append]
  congr 2
  simp only [crc32, ← update_append]
  rfl

end Crc32fastVerif
