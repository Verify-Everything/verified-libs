import Crc32fast.Table

/-!
# The portable Rust code computes the spec

Equational proofs: each generated function is shown to return `ok` of the spec
value, so they also prove the code never panics on these inputs.
-/

open Aeneas Aeneas.Std Result crc32fast Crc32Spec

namespace Crc32fastVerif

theorem fromLE4 (b0 b1 b2 b3 : BitVec 8) (h) :
    (BitVec.fromLEBytes [b0, b1, b2, b3]).cast h = le32 b0 b1 b2 b3 := by
  simp [BitVec.fromLEBytes]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_le32]
  iterate 32 (rcases i with _ | i; · simp)
  omega

theorem Slice.index_usize_ok {α} [Inhabited α] (v : Slice α) (i : Usize) (h : i.val < v.val.length) :
    Slice.index_usize v i = ok v.val[i.val]! := by
  simp [Slice.index_usize, List.getElem?_eq_getElem h]

theorem Slice.index_usize_ofNat {α} [Inhabited α] (v : Slice α) (n : Nat) (hn) (h : n < v.length) :
    Slice.index_usize v (Usize.ofNat n hn) = ok v.val[n]! := by
  rw [Slice.index_usize_ok _ _ (by simpa using h)]
  simp


theorem Array.index_usize_ok {α} [Inhabited α] {n : Usize} (v : Std.Array α n) (i : Usize) (h : i.val < v.val.length) :
    Array.index_usize v i = ok v.val[i.val]! := by
  simp [Array.index_usize, List.getElem?_eq_getElem h]

theorem tbl_entry (k n : Nat) (hk : k < 16) (hn : n < 256) :
    ((table.CRC32_TABLE.val[k]!).val[n]!).bv = tbl k (BitVec.ofNat 8 n) := by
  have h := congrArg (fun l => (l[k]!)[n]!) table_eq
  simp only [tblRows] at h
  simp [hk, hn, getElem!_pos] at h ⊢
  exact h

def bytes (l : List U8) : List (BitVec 8) := l.map (·.bv)

theorem update_slow_loop_unfold (it : core.slice.iter.Iter U8) (c : U32) :
    baseline.update_slow_loop it c = (do
      let r ← baseline.update_slow_loop.body it c
      match r with
      | .cont (it', c') => baseline.update_slow_loop it' c'
      | .done x => ok x) := by
  conv => lhs; unfold baseline.update_slow_loop; rw [loop]
  simp only []
  congr 1; funext r
  rcases r with ⟨⟨it', c'⟩⟩ | x <;> rfl

theorem U32.shr_ok (c : U32) (k : I32) (h0 : 0 ≤ k.val) (h : k.toNat < 32) :
    (c >>> k : Result U32) = ok ⟨c.bv >>> k.toNat⟩ := by
  simp only [HShiftRight.hShiftRight, UScalar.shiftRight_IScalar, UScalar.shiftRight]
  simp only [ge_iff_le, h0, ite_true]
  rw [if_pos (by simpa using h)]

theorem cast_usize_val_lt (x : U8) : (UScalar.cast .Usize x).val < 256 := by
  have := x.hBounds
  rw [UScalar.cast_val_eq]
  have h2 : 256 ≤ 2 ^ UScalarTy.Usize.numBits := by
    cases System.Platform.numBits_eq <;> simp [UScalarTy.numBits, *]
  have : x.val < 256 := by scalar_tac
  rw [Nat.mod_eq_of_lt (by omega)]; exact this

theorem table_index (k : Usize) (hk : k.val < 16) :
    table.CRC32_TABLE.index_usize k = ok table.CRC32_TABLE.val[k.val]! :=
  Array.index_usize_ok _ _ (by simpa using hk)

theorem table_lookup (k : Nat) (hk : k < 16) (x : U8) :
    (table.CRC32_TABLE.val[k]!).index_usize (UScalar.cast .Usize x) = ok ⟨tbl k x.bv⟩ := by
  have hx := cast_usize_val_lt x
  rw [Array.index_usize_ok _ _ (by simpa using hx)]
  congr 1
  rw [UScalar.eq_equiv_bv_eq]
  refine (tbl_entry k _ hk hx).trans ?_
  show _ = tbl k x.bv
  congr 1
  rw [UScalar.cast_val_eq]
  have h2 : 256 ≤ 2 ^ UScalarTy.Usize.numBits := by
    cases System.Platform.numBits_eq <;> simp [UScalarTy.numBits, *]
  have : x.val < 256 := by scalar_tac
  rw [Nat.mod_eq_of_lt (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  simp only [UScalar.val]
  exact Nat.mod_eq_of_lt (x.bv.isLt)

theorem update_slow_body_some (s : Slice U8) (i : Nat) (c : U32) (h : i < s.length) :
    baseline.update_slow_loop.body ⟨s, i⟩ c = ok (.cont (⟨s, i + 1⟩, ⟨byteStep c.bv s.val[i]!.bv⟩)) := by
  simp only [baseline.update_slow_loop.body, core.slice.iter.IteratorSliceIter.next, Slice.len_val, h,
    _root_.dite_true, bind_ok, lift, table_index 0#usize (by decide)]
  simp only [show (0#usize).val = 0 from rfl, table_lookup 0 (by decide), bind_ok,
    U32.shr_ok c 8#i32 (by decide) (by decide)]
  have hs : s.val[i]! = s[i] := by simp [getElem!_pos, h]
  rw [byteStep_table, hs]
  rfl

theorem update_slow_body_none (s : Slice U8) (i : Nat) (c : U32) (h : ¬ i < s.length) :
    baseline.update_slow_loop.body ⟨s, i⟩ c = ok (.done c) := by
  simp only [baseline.update_slow_loop.body, core.slice.iter.IteratorSliceIter.next, Slice.len_val, h,
    _root_.dite_false, bind_ok]
  rfl

theorem update_slow_loop_eq (s : Slice U8) (i : Nat) (c : U32) :
    baseline.update_slow_loop ⟨s, i⟩ c = ok ⟨crcRaw c.bv (bytes (s.val.drop i))⟩ := by
  induction h : s.length - i generalizing i c with
  | zero =>
    have hi : ¬ i < s.length := by omega
    rw [update_slow_loop_unfold, update_slow_body_none s i c hi, bind_ok]
    simp only [Slice.length] at hi
    simp [List.drop_eq_nil_of_le (by omega : s.val.length ≤ i), bytes, crcRaw]
  | succ n ih =>
    have hi : i < s.length := by omega
    rw [update_slow_loop_unfold, update_slow_body_some s i c hi, bind_ok]
    simp only []
    rw [ih (i + 1) _ (by omega)]
    simp only [Slice.length] at hi
    rw [List.drop_eq_getElem_cons hi]
    simp only [bytes, List.map_cons, crcRaw_cons, getElem!_pos s.val i hi]

/-- `update_slow` computes the spec's `update`. -/
theorem update_slow_eq (prev : U32) (buf : Slice U8) :
    baseline.update_slow prev buf = ok ⟨update prev.bv (bytes buf.val)⟩ := by
  simp only [baseline.update_slow, lift, bind_ok, core.slice.Slice.iter]
  rw [update_slow_loop_eq]
  simp [update]
  rfl

theorem U32.shr_8 (c : U32) : (c >>> 8#i32 : Result U32) = ok ⟨c.bv >>> 8⟩ :=
  U32.shr_ok c 8#i32 (by decide) (by decide)
theorem U32.shr_16 (c : U32) : (c >>> 16#i32 : Result U32) = ok ⟨c.bv >>> 16⟩ :=
  U32.shr_ok c 16#i32 (by decide) (by decide)
theorem U32.shr_24 (c : U32) : (c >>> 24#i32 : Result U32) = ok ⟨c.bv >>> 24⟩ :=
  U32.shr_ok c 24#i32 (by decide) (by decide)

theorem table_index_ofNat (k : Nat) (hk') (h : k < 16) :
    table.CRC32_TABLE.index_usize (Usize.ofNat k hk') = ok table.CRC32_TABLE.val[k]! := by
  rw [table_index _ (by simpa using h)]
  simp

theorem table_lookup32 (k : Nat) (hk : k < 16) (x : U32) (hx : x.bv < 256#32) :
    (table.CRC32_TABLE.val[k]!).index_usize (UScalar.cast .Usize x) = ok ⟨tbl k (x.bv.truncate 8)⟩ := by
  have := table_lookup k hk (UScalar.cast .U8 x)
  have e : UScalar.cast .Usize (UScalar.cast .U8 x) = UScalar.cast .Usize x := by
    rw [UScalar.eq_equiv_bv_eq]
    simp only [UScalar.cast]
    apply BitVec.eq_of_toNat_eq
    have : x.bv.toNat < 256 := by bv_omega
    simp only [BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth]
    have hv : x.bv.toNat % 2 ^ UScalarTy.U8.numBits = x.bv.toNat := Nat.mod_eq_of_lt (by show x.bv.toNat < 256; omega)
    rw [hv]
  rw [e] at this
  rw [this]
  rfl

theorem table_lookup_shr24 (k : Nat) (hk : k < 16) (v : BitVec 32) :
    (table.CRC32_TABLE.val[k]!).index_usize (UScalar.cast .Usize (⟨v >>> 24⟩ : U32)) =
      ok ⟨tbl k ((v >>> 24).truncate 8)⟩ :=
  table_lookup32 k hk _ (by show v >>> 24 < 256#32; bv_omega)

theorem table_lookup_and255 (k : Nat) (hk : k < 16) (y : U32) :
    (table.CRC32_TABLE.val[k]!).index_usize (UScalar.cast .Usize (y &&& 255#u32)) =
      ok ⟨tbl k (y.bv.truncate 8)⟩ := by
  rw [table_lookup32 k hk _ (by
    show y.bv &&& 255#32 < 256#32
    rw [BitVec.lt_def, BitVec.toNat_and]
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide))]
  congr 2
  show tbl k (BitVec.truncate 8 (y.bv &&& 255#32)) = _
  congr 1
  bv_bits 8

theorem from_le_bytes_make4 (b0 b1 b2 b3 : U8) (h) :
    core.num.U32.from_le_bytes (Array.make 4#usize [b0, b1, b2, b3] h) = ⟨le32 b0.bv b1.bv b2.bv b3.bv⟩ := by
  rw [UScalar.eq_equiv_bv_eq]
  apply BitVec.eq_of_toNat_eq
  have hv := Array.make_val 4#usize [b0, b1, b2, b3] h
  generalize Array.make 4#usize [b0, b1, b2, b3] h = A at hv ⊢
  simp only [core.num.U32.from_le_bytes, BitVec.toNat_cast]
  rw [hv]
  show (BitVec.fromLEBytes [b0.bv, b1.bv, b2.bv, b3.bv]).toNat = _
  rw [← BitVec.toNat_cast (by rfl) (BitVec.fromLEBytes [b0.bv, b1.bv, b2.bv, b3.bv]), fromLE4]

theorem bytes_getElem! (l : List U8) (k : Nat) (h : k < l.length) : (bytes l)[k]! = l[k]!.bv := by
  simp [bytes, getElem!_pos, h]

/-- `fold_16` computes the spec's slice-by-16 step, which is feeding 16 bytes. -/
theorem fold_16_eq (crc : U32) (block : Slice U8) (h : 16 ≤ block.length) :
    baseline.fold_16 crc block = ok ⟨crcRaw crc.bv ((bytes block.val).take 16)⟩ := by
  rw [← fold16_eq _ _ (by simp [bytes]; omega)]
  unfold baseline.fold_16
  simp (disch := first | omega | decide) only [Slice.index_usize_ofNat, bind_ok, lift,
    table_index_ofNat, table_lookup, U32.shr_8, U32.shr_16, U32.shr_24, table_lookup_shr24,
    table_lookup_and255, from_le_bytes_make4]
  congr 1
  have hl : 16 ≤ block.val.length := h
  have e : ∀ k, k < 16 → (bytes block.val)[k]! = block.val[k]!.bv :=
    fun k hk => bytes_getElem! _ _ (by omega)
  simp only [fold16, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega),
    e 4 (by omega), e 5 (by omega), e 6 (by omega), e 7 (by omega), e 8 (by omega),
    e 9 (by omega), e 10 (by omega), e 11 (by omega), e 12 (by omega), e 13 (by omega),
    e 14 (by omega), e 15 (by omega)]
  rfl


theorem range_next_usize_lt (s e : Usize) (h : s.val < e.val) :
    ∃ s' : Usize, s'.val = s.val + 1 ∧
      core.iter.range.IteratorRange.next core.iter.range.StepUsize ⟨s, e⟩ = ok (some s, ⟨s', e⟩) := by
  have hb : s.val + 1 ≤ Usize.max := by scalar_tac
  refine ⟨UScalar.ofNatCore (s.val + (1#usize).val) (by scalar_tac), by simp, ?_⟩
  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.PartialOrdUsize, core.clone.CloneUsize, liftFun2, liftFun1, bind_ok,
    core.cmp.impls.PartialOrdUsize.lt, core.clone.impls.CloneUsize.clone, h, decide_true, ite_true,
    core.iter.range.UScalarStep.forward_checked]
  have hb' : s.val + (1#usize).val ≤ UScalar.max UScalarTy.Usize := by scalar_tac
  rw [dif_pos hb', bind_ok]

theorem range_next_usize_ge (s e : Usize) (h : ¬ s.val < e.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize ⟨s, e⟩ = ok (none, ⟨s, e⟩) := by
  simp only [core.iter.range.IteratorRange.next, core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.PartialOrdUsize, liftFun2, bind_ok, core.cmp.impls.PartialOrdUsize.lt, h, decide_false]
  rfl

/-- Rewrite one `bind (ok x) f`, whichever form of bind the generated code uses. -/
macro "rw_bind" : tactic => `(tactic| first | rw [bind_ok] | rw [bind_tc_ok])

def P (b : Slice U8) (c : U32) : BitVec 32 := crcRaw c.bv (bytes b.val)

theorem index_from16 (buf : Slice U8) (h : 16 ≤ buf.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) buf
      { start := 16#usize } = ok (buf.drop 16#usize) := by
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeFromUsizeSlice,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index]
  rw [if_pos (by simpa using h)]

theorem P_fold (buf : Slice U8) (crc : U32) (h : 16 ≤ buf.length) :
    P (buf.drop 16#usize) ⟨crcRaw crc.bv ((bytes buf.val).take 16)⟩ = P buf crc := by
  simp only [P, Slice.drop, Slice.from_val]
  have : (16#usize).val = 16 := by simp
  rw [this, ← crcRaw_append]
  simp only [bytes, Slice.length]
  rw [List.map_drop, List.take_append_drop]

theorem len_drop16 (buf : Slice U8) : (buf.drop 16#usize).length = buf.length - 16 := by
  simp [Slice.drop]

theorem inner_unfold (it : core.ops.range.Range Usize) (b : Slice U8) (c : U32) :
    baseline.update_fast_16_loop0_loop0 it b c = (do
      let r ← baseline.update_fast_16_loop0_loop0.body it b c
      match r with
      | .cont (it', b', c') => baseline.update_fast_16_loop0_loop0 it' b' c'
      | .done x => ok x) := by
  conv => lhs; unfold baseline.update_fast_16_loop0_loop0; rw [loop]
  simp only []
  congr 1; funext r
  rcases r with ⟨⟨it', b', c'⟩⟩ | x <;> rfl

theorem inner_body_none (s e : Usize) (h : ¬ s.val < e.val) (buf : Slice U8) (crc : U32) :
    baseline.update_fast_16_loop0_loop0.body ⟨s, e⟩ buf crc = ok (.done (buf, crc)) := by
  simp only [baseline.update_fast_16_loop0_loop0.body, range_next_usize_ge s e h, bind_ok]
  rfl

theorem inner_body_some (s e s' : Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize ⟨s, e⟩ = ok (some s, ⟨s', e⟩))
    (buf : Slice U8) (crc : U32) (h16 : 16 ≤ buf.length) :
    baseline.update_fast_16_loop0_loop0.body ⟨s, e⟩ buf crc =
      ok (.cont (⟨s', e⟩, buf.drop 16#usize, ⟨crcRaw crc.bv ((bytes buf.val).take 16)⟩)) := by
  simp only [baseline.update_fast_16_loop0_loop0.body, hnext, bind_ok]
  show (do
    let crc1 ← baseline.fold_16 crc buf
    let buf1 ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) buf
      { start := 16#usize }
    ok (ControlFlow.cont ((⟨s', e⟩ : core.ops.range.Range Usize), buf1, crc1))) = _
  rw [fold_16_eq _ _ h16, bind_tc_ok, index_from16 _ h16, bind_tc_ok]

theorem inner_eq (n : Nat) (s e : Usize) (hn : e.val - s.val = n) (buf : Slice U8) (crc : U32)
    (hle : 16 * n ≤ buf.length) :
    ∃ buf' crc', baseline.update_fast_16_loop0_loop0 ⟨s, e⟩ buf crc = ok (buf', crc') ∧
      P buf' crc' = P buf crc ∧ buf'.length = buf.length - 16 * n := by
  induction n generalizing s buf crc with
  | zero =>
    refine ⟨buf, crc, ?_, rfl, by simp⟩
    rw [inner_unfold, inner_body_none s e (by omega), bind_ok]
  | succ n ih =>
    obtain ⟨s', hs', hnext⟩ := range_next_usize_lt s e (by omega)
    have h16 : 16 ≤ buf.length := by omega
    obtain ⟨b2, c2, h2, hP, hl⟩ := ih s' (by omega) (buf.drop 16#usize)
      ⟨crcRaw crc.bv ((bytes buf.val).take 16)⟩ (by rw [len_drop16]; omega)
    refine ⟨b2, c2, ?_, ?_, ?_⟩
    · rw [inner_unfold, inner_body_some s e s' hnext buf crc h16, bind_ok]
      exact h2
    · rw [hP, P_fold _ _ h16]
    · rw [hl, len_drop16]; omega

theorem bytes_at_once : ∃ v : Usize, v.val = 64 ∧ baseline.update_fast_16.BYTES_AT_ONCE = ok v := by
  unfold baseline.update_fast_16.BYTES_AT_ONCE baseline.update_fast_16.UNROLL
  simp only [HMul.hMul, UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt]
  have hc : UScalar.check_bounds UScalarTy.Usize (Mul.mul (16#usize).val (4#usize).val) = true := by
    simp [UScalar.check_bounds]
    cases System.Platform.numBits_eq <;> simp [*] <;> decide
  rw [dif_pos hc]
  exact ⟨_, by simp, rfl⟩

theorem unroll_val : baseline.update_fast_16.UNROLL.val = 4 := by
  unfold baseline.update_fast_16.UNROLL; simp

theorem outer_body_ge (buf : Slice U8) (crc : U32) (h : 64 ≤ buf.length) :
    ∃ b' c', baseline.update_fast_16_loop0.body buf crc = ok (.cont (b', c')) ∧
      P b' c' = P buf crc ∧ b'.length = buf.length - 64 := by
  obtain ⟨v, hv, hB⟩ := bytes_at_once
  obtain ⟨b2, c2, h2, hP, hl⟩ := inner_eq 4 0#usize baseline.update_fast_16.UNROLL
    (by rw [unroll_val]; simp) buf crc (by omega)
  refine ⟨b2, c2, ?_, hP, by rw [hl]⟩
  simp only [baseline.update_fast_16_loop0.body, hB]
  rw_bind
  rw [if_pos (by simp [hv]; omega), h2]
  rw_bind
  rfl

theorem outer_body_lt (buf : Slice U8) (crc : U32) (h : buf.length < 64) :
    baseline.update_fast_16_loop0.body buf crc = ok (.done (buf, crc)) := by
  obtain ⟨v, hv, hB⟩ := bytes_at_once
  simp only [baseline.update_fast_16_loop0.body, hB]
  rw_bind
  rw [if_neg (by simp [hv]; omega)]

theorem outer_unfold (b : Slice U8) (c : U32) :
    baseline.update_fast_16_loop0 b c = (do
      let r ← baseline.update_fast_16_loop0.body b c
      match r with
      | .cont (b', c') => baseline.update_fast_16_loop0 b' c'
      | .done x => ok x) := by
  conv => lhs; unfold baseline.update_fast_16_loop0; rw [loop]
  simp only []
  congr 1; funext r
  rcases r with ⟨⟨b', c'⟩⟩ | x <;> rfl

theorem outer_eq (n : Nat) (buf : Slice U8) (crc : U32) (hn : buf.length = n) :
    ∃ b' c', baseline.update_fast_16_loop0 buf crc = ok (b', c') ∧ P b' c' = P buf crc := by
  induction n using Nat.strong_induction_on generalizing buf crc with
  | _ n ih =>
    by_cases h : 64 ≤ buf.length
    · obtain ⟨b1, c1, h1, hP1, hl1⟩ := outer_body_ge buf crc h
      obtain ⟨b2, c2, h2, hP2⟩ := ih b1.length (by omega) b1 c1 rfl
      refine ⟨b2, c2, ?_, by rw [hP2, hP1]⟩
      rw [outer_unfold, h1, bind_ok]
      exact h2
    · refine ⟨buf, crc, ?_, rfl⟩
      rw [outer_unfold, outer_body_lt buf crc (by omega), bind_ok]

theorem tail_body_ge (buf : Slice U8) (crc : U32) (h : 16 ≤ buf.length) :
    baseline.update_fast_16_loop1.body buf crc =
      ok (.cont (buf.drop 16#usize, ⟨crcRaw crc.bv ((bytes buf.val).take 16)⟩)) := by
  simp only [baseline.update_fast_16_loop1.body]
  rw [if_pos (by simp; omega), fold_16_eq _ _ h]
  rw_bind
  rw [index_from16 _ h]
  rw_bind

theorem tail_body_lt (buf : Slice U8) (crc : U32) (h : buf.length < 16) :
    baseline.update_fast_16_loop1.body buf crc = ok (.done (buf, crc)) := by
  simp only [baseline.update_fast_16_loop1.body]
  rw [if_neg (by simp; omega)]

theorem tail_unfold (b : Slice U8) (c : U32) :
    baseline.update_fast_16_loop1 b c = (do
      let r ← baseline.update_fast_16_loop1.body b c
      match r with
      | .cont (b', c') => baseline.update_fast_16_loop1 b' c'
      | .done x => ok x) := by
  conv => lhs; unfold baseline.update_fast_16_loop1; rw [loop]
  simp only []
  congr 1; funext r
  rcases r with ⟨⟨b', c'⟩⟩ | x <;> rfl

theorem tail_eq (n : Nat) (buf : Slice U8) (crc : U32) (hn : buf.length = n) :
    ∃ b' c', baseline.update_fast_16_loop1 buf crc = ok (b', c') ∧ P b' c' = P buf crc := by
  induction n using Nat.strong_induction_on generalizing buf crc with
  | _ n ih =>
    by_cases h : 16 ≤ buf.length
    · obtain ⟨b2, c2, h2, hP2⟩ := ih (buf.drop 16#usize).length (by rw [len_drop16]; omega)
        (buf.drop 16#usize) ⟨crcRaw crc.bv ((bytes buf.val).take 16)⟩ rfl
      refine ⟨b2, c2, ?_, by rw [hP2, P_fold _ _ h]⟩
      rw [tail_unfold, tail_body_ge buf crc h, bind_ok]
      exact h2
    · refine ⟨buf, crc, ?_, rfl⟩
      rw [tail_unfold, tail_body_lt buf crc (by omega), bind_ok]

/-- The 16-bytes-at-a-time `update_fast_16` computes the spec's `update`. -/
theorem update_fast_16_eq (prev : U32) (buf : Slice U8) :
    baseline.update_fast_16 prev buf = ok ⟨update prev.bv (bytes buf.val)⟩ := by
  obtain ⟨b1, c1, h1, hP1⟩ := outer_eq _ buf (~~~ prev) rfl
  obtain ⟨b2, c2, h2, hP2⟩ := tail_eq _ b1 c1 rfl
  unfold baseline.update_fast_16
  simp only [lift]
  rw_bind
  rw [h1]
  rw_bind
  rw [uncurry_apply_pair, h2]
  rw_bind
  rw [uncurry_apply_pair]
  rw_bind
  rw [update_slow_eq]
  congr 2
  simp only [P] at hP1 hP2
  simp only [update]
  show ~~~(crcRaw (~~~(~~~c2.bv)) (bytes b2.val)) = ~~~(crcRaw (~~~prev.bv) (bytes buf.val))
  rw [BitVec.not_not, hP2, hP1]
  rfl

end Crc32fastVerif
