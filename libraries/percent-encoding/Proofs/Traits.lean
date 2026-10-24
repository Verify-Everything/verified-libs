/-
  Derived and small trait impls: PartialEq, Clone, and thin wrappers.
  Plain (non-`module`) file, like Proofs/Sets.lean.
-/
import Proofs.Sets

open Aeneas Aeneas.Std Result WP
open percent_encoding percent_encoding.Spec

namespace percent_encoding.Proofs

theorem allM_zip_eq {α : Type} [DecidableEq α] (l1 l2 : List α) (h : l1.length = l2.length) :
    List.allM (fun (p : α × α) => (ok (decide (p.1 = p.2)) : Result Bool))
      (List.zip l1 l2) = ok (decide (l1 = l2)) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all <;> rfl
  | cons x xs ih =>
    cases l2 with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.zip_cons_cons, List.allM, bind_ok]
      by_cases hxy : x = y
      · subst hxy; simpa using ih ys h
      · simp [hxy]; rfl

/-- The element-wise loop used by the derived `PartialEq` for arrays and slices
    decides list equality when the lengths agree. -/
theorem allM_zip_ne_eq {α : Type} [DecidableEq α] (f : α × α → Result Bool)
    (hf : ∀ p, f p = ok (decide (p.1 = p.2))) (l1 l2 : List α) (h : l1.length = l2.length) :
    List.allM f (List.zip l1 l2) = ok (decide (l1 = l2)) := by
  rw [show f = (fun p => ok (decide (p.1 = p.2))) from funext hf]
  exact allM_zip_eq l1 l2 h

/-! ### Derived `PartialEq` / `Eq` -/

theorem asciiSet_eq_iff (s o : ascii_set.AsciiSet) : s = o ↔ s.mask.val = o.mask.val := by
  cases s; cases o
  simp only [ascii_set.AsciiSet.mk.injEq]
  exact Std.Array.eq_iff _ _

/-- Derived `AsciiSet == AsciiSet` is structural equality and never panics. -/
@[step]
theorem asciiSet_eq_spec (s o : ascii_set.AsciiSet) :
    ascii_set.AsciiSet.Insts.CoreCmpPartialEqAsciiSet.eq s o ⦃ b => (b = true ↔ s = o) ⦄ := by
  unfold ascii_set.AsciiSet.Insts.CoreCmpPartialEqAsciiSet.eq core.array.equality.PartialEqArray.eq
  have h : s.mask.val.length = o.mask.val.length := by simp
  simp only [Array.length, h, ite_true, liftFun2, core.cmp.impls.PartialEqU32.ne]
  rw [allM_zip_ne_eq _ (by intro p; simp; exact ⟨UScalar.eq_of_val_eq, UScalar.val_eq_of_eq⟩) _ _ h]
  apply (WP.spec_ok _).2
  simp [asciiSet_eq_iff]

/-- The four 32-bit mask words cover exactly the 128 ASCII bytes, so two sets
    are equal exactly when they contain the same ASCII bytes. Together with
    `asciiSet_eq_spec`, `==` on `AsciiSet` is set equality. -/
theorem asciiSet_eq_iff_inSet (s o : ascii_set.AsciiSet) :
    s = o ↔ ∀ c, c < 128 → inSet s c = inSet o c := by
  constructor
  · rintro rfl _ _; rfl
  · intro h
    rw [asciiSet_eq_iff]
    apply List.ext_getElem (by simp)
    intro k hk1 hk2
    have hk : k < 4 := by simpa using hk1
    apply UScalar.eq_of_val_eq
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 32
    · have := h (32 * k + j) (by omega)
      rw [inSet_eq_chunk, inSet_eq_chunk] at this
      have e1 : (32 * k + j) / 32 = k := by omega
      have e2 : (32 * k + j) % 32 = j := by omega
      simp only [e1, e2, show 32 * k + j < 128 by omega, decide_true, Bool.true_and] at this
      simpa [mask_getElem! s k hk, mask_getElem! o k hk] using this
    · have b1 := (s.mask.val[k]).hBounds
      have b2 := (o.mask.val[k]).hBounds
      simp only [UScalarTy.numBits] at b1 b2
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le b1 (Nat.pow_le_pow_right (by omega) (by omega))),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le b2 (Nat.pow_le_pow_right (by omega) (by omega)))]

theorem slice_u8_eq_spec (a b : Slice Std.U8) :
    core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 a b ⦃ r => (r = true ↔ a = b) ⦄ := by
  unfold core.slice.cmp.PartialEqSlice.eq
  by_cases h : a.length = b.length
  · simp only [h, ite_true, liftFun2, core.cmp.impls.PartialEqU8.ne]
    rw [allM_zip_ne_eq _ (by intro p; simp; exact ⟨UScalar.eq_of_val_eq, UScalar.val_eq_of_eq⟩) _ _ h]
    apply (WP.spec_ok _).2
    simp [Slice.eq_iff]
  · simp only [h, ite_false]
    apply (WP.spec_ok _).2
    simp only [Bool.false_eq_true, false_iff]
    rintro rfl; exact h rfl

/-- Derived `PercentEncode == PercentEncode` compares the remaining input and
    the set (by value, through the `&AsciiSet` reference), and never panics. -/
@[step]
theorem percentEncode_eq_spec (a b : PercentEncode) :
    PercentEncode.Insts.CoreCmpPartialEqPercentEncode.eq a b ⦃ r => (r = true ↔ a = b) ⦄ := by
  unfold PercentEncode.Insts.CoreCmpPartialEqPercentEncode.eq
  apply WP.spec_bind (slice_u8_eq_spec a.bytes b.bytes)
  intro r1 h1
  cases a; cases b
  split
  · apply WP.spec_mono (asciiSet_eq_spec _ _)
    intro r hr
    simp_all
  · apply (WP.spec_ok _).2
    simp_all

/-- `Eq::assert_fields_are_eq` is a no-op for both types. -/
theorem asciiSet_assert_fields_are_eq (s : ascii_set.AsciiSet) :
    ascii_set.AsciiSet.Insts.CoreCmpEq.assert_fields_are_eq s = ok () := rfl
theorem percentEncode_assert_fields_are_eq (s : PercentEncode) :
    PercentEncode.Insts.CoreCmpEq.assert_fields_are_eq s = ok () := rfl

/-! ### Derived `Clone` and thin wrappers -/

/-- Derived `Clone` returns an identical iterator. -/
theorem percentEncode_clone_spec (it : PercentEncode) :
    PercentEncode.Insts.CoreCloneClone.clone it = ok it := by
  simp [PercentEncode.Insts.CoreCloneClone.clone, core.clone.impls.CloneShared.clone]

theorem percentDecode_clone_spec (d : PercentDecode) :
    PercentDecode.Insts.CoreCloneClone.clone d = ok d := by
  simp [PercentDecode.Insts.CoreCloneClone.clone, core.slice.iter.Iter.Insts.CoreCloneClone.clone]

/-- `utf8_percent_encode` is `percent_encode` on the string's bytes. -/
theorem utf8_percent_encode_spec (input : Str) (set : ascii_set.AsciiSet) :
    utf8_percent_encode input set = percent_encode input set := by
  unfold utf8_percent_encode core.str.Str.as_bytes; exact bind_ok _ _

/-- `percent_decode_str` is `percent_decode` on the string's bytes. -/
theorem percent_decode_str_spec (input : Str) :
    percent_decode_str input = percent_decode input := by
  unfold percent_decode_str core.str.Str.as_bytes; exact bind_ok _ _

/-- `utf8_percent_encode` is correct: it yields the reference encoding of the UTF-8 bytes. -/
theorem utf8_percent_encode_correct (input : Str) (set : ascii_set.AsciiSet) :
    (do let it ← utf8_percent_encode input set
        encodeCollect (input.length + 1) it)
      ⦃ out => out = encode set (strBytes input) ⦄ := by
  rw [utf8_percent_encode_spec]; exact percent_encode_correct input set

theorem percent_decode_str_correct (input : Str) :
    (do let d ← percent_decode_str input
        decodeCollect (input.length + 1) d)
      ⦃ out => out = decode (strBytes input) ⦄ := by
  rw [percent_decode_str_spec]; exact percent_decode_correct input

/-- `AsciiSet::EMPTY` contains no byte. -/
theorem EMPTY_spec (c : Nat) : inSet ascii_set.AsciiSet.EMPTY c = false := by
  unfold inSet ascii_set.AsciiSet.EMPTY
  by_cases h : c < 128
  · rcases chunk_cases c h with e | e | e | e <;> simp [e, Array.repeat]
  · simp [h]

/-! ### `size_hint` -/

/-- Each decoded byte consumes one or three input bytes. -/
theorem decode_length_bounds (l : List Nat) :
    (decode l).length ≤ l.length ∧ l.length ≤ 3 * (decode l).length := by
  induction l using decode.induct with
  | case1 => simp [decode]
  | case2 h l rest hv lv hh hl ih =>
    rw [decode]; simp only [hh, hl, List.length_cons]; omega
  | case3 h l rest hnot ih =>
    rw [decode]
    split
    · rename_i hv lv hh hl; exact absurd hl (hnot hv lv hh)
    · simp only [List.length_cons] at *; omega
  | case4 b rest hb ih =>
    rw [decode]
    · simp only [List.length_cons]; omega
    · exact hb

theorem remBytes_length (it : core.slice.iter.Iter Std.U8) :
    (remBytes it).length = it.slice.length - it.i := by
  simp [remBytes, Slice.length]

/-- `PercentDecode::size_hint` is sound: the number of bytes the iterator
    still yields (the reference decoding of what is left) lies between the two
    bounds. Assumes the Rust guarantee that a slice is at most `isize::MAX`
    bytes long, which keeps `bytes + 2` from overflowing; the Aeneas slice model
    only bounds lengths by `usize::MAX`. -/
theorem decode_size_hint_spec (d : PercentDecode) (hlen : d.bytes.slice.length ≤ Isize.max) :
    PercentDecode.Insts.CoreIterTraitsIteratorIteratorU8.size_hint d ⦃ p =>
      p.1.val ≤ (decode (remBytes d.bytes)).length ∧
      p.2.map (·.val) = some (remBytes d.bytes).length ∧
      (decode (remBytes d.bytes)).length ≤ (remBytes d.bytes).length ⦄ := by
  unfold PercentDecode.Insts.CoreIterTraitsIteratorIteratorU8.size_hint
    core.slice.iter.Iter.Insts.CoreIterTraitsExact_sizeExactSizeIteratorSharedT.len
  have hb := decode_length_bounds (remBytes d.bytes)
  rw [remBytes_length] at hb ⊢
  have hmax : Isize.max + 2 ≤ (Usize.max : Int) := by
    rw [Isize.max_def, Usize.max_def]
    simp only [Isize.numBits, Usize.numBits]
    cases System.Platform.numBits_eq <;> simp_all
  have hv : (Usize.ofNatCore (d.bytes.slice.length - d.bytes.i)
      (by have := d.bytes.slice.property; scalar_tac)).val = d.bytes.slice.length - d.bytes.i :=
    Usize.ofNatCore_val_eq _
  step*
  · simp only [hv] at *; scalar_tac
  · refine ⟨?_, by simp [hv], hb.1⟩
    rw [i1_post, i_post, hv]
    omega

/-- Number of chunks the Rust iterator `PercentEncode` yields before `None`
    (like `iter.count()`); `fuel` bounds the steps as in `encodeCollect`. -/
noncomputable def encodeCount : Nat → PercentEncode → Result Nat
  | 0, _ => fail .panic
  | fuel + 1, it => do
    let (r, it') ← PercentEncode.Insts.CoreIterTraitsIteratorIteratorSharedAStr.next it
    match r with
    | none => ok 0
    | some _ => do
      let n ← encodeCount fuel it'
      ok (n + 1)

theorem encodeCount_spec (fuel : Nat) (it : PercentEncode) (h : it.bytes.length < fuel) :
    encodeCount fuel it ⦃ n => n ≤ it.bytes.length ∧ (it.bytes.length = 0 ↔ n = 0) ⦄ := by
  induction fuel generalizing it with
  | zero => omega
  | succ k ih =>
    unfold encodeCount
    apply WP.spec_bind (encode_next_spec it)
    rintro ⟨r, it'⟩ ⟨_, hr⟩
    cases r with
    | none =>
      apply (WP.spec_ok _).2
      simp [Slice.length, hr.1]
    | some chunk =>
      apply WP.spec_bind (ih it' (by omega))
      intro n hn
      apply (WP.spec_ok _).2
      omega

theorem encode_size_hint_val (it : PercentEncode) :
    PercentEncode.Insts.CoreIterTraitsIteratorIteratorSharedAStr.size_hint it ⦃ p =>
      p.1.val = (if it.bytes.length = 0 then 0 else 1) ∧ p.2.map (·.val) = some it.bytes.length ⦄ := by
  unfold PercentEncode.Insts.CoreIterTraitsIteratorIteratorSharedAStr.size_hint
    core.slice.Slice.is_empty
  rw [bind_ok]
  by_cases h0 : it.bytes.length = 0
  · simp only [h0, decide_true, ite_true]
    apply (WP.spec_ok _).2
    simp
  · simp only [h0, decide_false, Bool.false_eq_true, ite_false]
    apply (WP.spec_ok _).2
    simp [Slice.len]

/-- `PercentEncode::size_hint` is sound and exact about emptiness: an empty
    input yields `(0, Some 0)` and no chunks; otherwise `(1, Some len)` and
    between 1 and `len` chunks. -/
theorem encode_size_hint_spec (it : PercentEncode) :
    (do let p ← PercentEncode.Insts.CoreIterTraitsIteratorIteratorSharedAStr.size_hint it
        let n ← encodeCount (it.bytes.length + 1) it
        ok (p, n))
      ⦃ q => q.1.1.val ≤ q.2 ∧ q.1.2.map (·.val) = some it.bytes.length ∧ q.2 ≤ it.bytes.length ⦄ := by
  apply WP.spec_bind (encode_size_hint_val it)
  rintro p ⟨h1, h2⟩
  apply WP.spec_bind (encodeCount_spec (it.bytes.length + 1) it (by omega))
  rintro n ⟨h3, h4⟩
  apply (WP.spec_ok _).2
  refine ⟨?_, h2, h3⟩
  rw [h1]
  split <;> omega

/-! ### `add` / `remove` on non-ASCII bytes -/

/-- A WP spec pins the result down to `ok v` for some `v` satisfying it. -/
theorem spec_eq_ok {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ x => P x ⦄) :
    ∃ v, m = ok v ∧ P v := by
  cases m using Result.cases with
  | ret r => exact ⟨r, rfl, (WP.spec_ok _).1 h⟩
  | vis i k => exact ((WP.spec_vis i k).1 h).elim
  | div => exact (WP.spec_div.1 h).elim

theorem bind_eq_fail_of_spec {α β : Type} {m : Result α} {P : α → Prop} {k : α → Result β} {e : Error}
    (h : m ⦃ x => P x ⦄) (hk : ∀ v, P v → k v = fail e) : Std.bind m k = fail e := by
  obtain ⟨v, hv, hp⟩ := spec_eq_ok h
  rw [hv, bind_ok, hk v hp]

/-- **Finding.** `AsciiSet::add` panics (array index out of bounds) for every
    non-ASCII byte. The function is public and its docs do not say so. -/
theorem add_nonascii_panics (s : ascii_set.AsciiSet) (b : Std.U8) (hb : 128 ≤ b.val) :
    ascii_set.AsciiSet.add s b = fail .arrayOutOfBounds := by
  have hb' : b.val < 256 := by have := b.hBounds; simpa [UScalarTy.numBits] using this
  unfold ascii_set.AsciiSet.add
  simp only [lift, bind_ok]
  refine bind_eq_fail_of_spec BITS_PER_CHUNK_spec (fun c hc => ?_)
  have hc0 : c.val ≠ 0 := by omega
  refine bind_eq_fail_of_spec (UScalar.rem_spec _ hc0) (fun r hr => ?_)
  refine bind_eq_fail_of_spec (P := fun _ => True)
    (WP.spec_mono (UScalar.ShiftLeft_spec 1#u32 r _ (by simp [hr, hc]; omega) rfl) (by simp)) (fun m _ => ?_)
  obtain ⟨q, hq, hqv⟩ := UScalar.div_spec (UScalar.cast .Usize b) hc0
  rw [hq, bind_ok]
  have hpow : b.val < 2 ^ System.Platform.numBits := by
    cases System.Platform.numBits_eq <;> simp_all <;> omega
  have hq4 : 4 ≤ q.val := by
    simp [UScalar.cast_val_eq, Nat.mod_eq_of_lt hpow, hc] at hqv; omega
  have : Array.index_usize s.mask q = fail .arrayOutOfBounds := by
    unfold Array.index_usize
    rw [show s.mask[q]? = none by simp; omega]
  rw [this, bind_fail]

/-- **Finding.** `AsciiSet::remove` panics the same way for non-ASCII bytes. -/
theorem remove_nonascii_panics (s : ascii_set.AsciiSet) (b : Std.U8) (hb : 128 ≤ b.val) :
    ascii_set.AsciiSet.remove s b = fail .arrayOutOfBounds := by
  have hb' : b.val < 256 := by have := b.hBounds; simpa [UScalarTy.numBits] using this
  unfold ascii_set.AsciiSet.remove
  simp only [lift, bind_ok]
  refine bind_eq_fail_of_spec BITS_PER_CHUNK_spec (fun c hc => ?_)
  have hc0 : c.val ≠ 0 := by omega
  refine bind_eq_fail_of_spec (UScalar.rem_spec _ hc0) (fun r hr => ?_)
  refine bind_eq_fail_of_spec (P := fun _ => True)
    (WP.spec_mono (UScalar.ShiftLeft_spec 1#u32 r _ (by simp [hr, hc]; omega) rfl) (by simp)) (fun m _ => ?_)
  obtain ⟨q, hq, hqv⟩ := UScalar.div_spec (UScalar.cast .Usize b) hc0
  rw [hq, bind_ok]
  have hpow : b.val < 2 ^ System.Platform.numBits := by
    cases System.Platform.numBits_eq <;> simp_all <;> omega
  have hq4 : 4 ≤ q.val := by
    simp [UScalar.cast_val_eq, Nat.mod_eq_of_lt hpow, hc] at hqv; omega
  have : Array.index_usize s.mask q = fail .arrayOutOfBounds := by
    unfold Array.index_usize
    rw [show s.mask[q]? = none by simp; omega]
  rw [this, bind_fail]
