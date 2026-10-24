import Crc32fast.Aarch64Insn
import Crc32fast.Baseline
import Crc32fast.Combine

/-!
# The aarch64 kernel (`specialized::aarch64`) equals the spec

`crc_bytes` and `crc_quads` feed bytes and `u64`s (8 bytes, little endian) through the
`CRC32B`/`CRC32X` instructions; `calculate` splits the input with `align_to` (any split) and,
for long inputs, runs three streams that `combine` joins.
-/

open Aeneas Aeneas.Std Result crc32fast Crc32Spec

namespace Crc32fastVerif

/-- The bytes of a list of `u64`s, in memory order. -/
def qb (qs : List U64) : List (BitVec 8) := qs.flatMap (fun q => bytes8 q.bv)

theorem qb_nil : qb [] = [] := rfl
theorem qb_cons (q : U64) (qs : List U64) : qb (q :: qs) = bytes8 q.bv ++ qb qs := by
  simp [qb]
theorem qb_append (a b : List U64) : qb (a ++ b) = qb a ++ qb b := by simp [qb]
theorem qb_length (qs : List U64) : (qb qs).length = 8 * qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih => rw [qb_cons, List.length_append, ih]; simp [bytes8]; omega

theorem crc32b_eq (c : U32) (b : U8) :
    core.core_arch.arm_shared.neon.generated.__crc32b c b = ok ⟨crcRaw c.bv [b.bv]⟩ := by
  simp only [core.core_arch.arm_shared.neon.generated.__crc32b, crc32b_spec]; rfl

theorem crc32d_eq (c : U32) (q : U64) :
    core.core_arch.aarch64.neon.generated.__crc32d c q = ok ⟨crcRaw c.bv (bytes8 q.bv)⟩ := by
  simp only [core.core_arch.aarch64.neon.generated.__crc32d, crc32d_spec]

theorem call_b (c : specialized.aarch64.crc_bytes.closure) (acc : U32) (b : U8) :
    specialized.aarch64.crc_bytes.closure.Insts.CoreOpsFunctionFnMutPairU32Shared0U8U32.call_mut
      c (acc, b) = ok (⟨crcRaw acc.bv [b.bv]⟩, c) := by
  simp only [specialized.aarch64.crc_bytes.closure.Insts.CoreOpsFunctionFnMutPairU32Shared0U8U32.call_mut,
    crc32b_eq, bind_ok, uncurry_apply_pair]

theorem call_q (c : specialized.aarch64.crc_quads.closure) (acc : U32) (q : U64) :
    specialized.aarch64.crc_quads.closure.Insts.CoreOpsFunctionFnMutPairU32Shared0U64U32.call_mut
      c (acc, q) = ok (⟨crcRaw acc.bv (bytes8 q.bv)⟩, c) := by
  simp only [specialized.aarch64.crc_quads.closure.Insts.CoreOpsFunctionFnMutPairU32Shared0U64U32.call_mut,
    crc32d_eq, bind_ok, uncurry_apply_pair]

theorem not_bv (c : U32) : (~~~ c).bv = ~~~ c.bv := rfl

theorem not_mk (v : BitVec 32) : (~~~ (UScalar.mk (ty := .U32) v)) = UScalar.mk (ty := .U32) (~~~ v) := rfl

theorem eb32 (v : BitVec 32) : U32.bv (UScalar.mk v) = v := rfl

theorem fold_bytes (l : List U8) (acc : U32) :
    l.foldlM (fun (p : U32 × specialized.aarch64.crc_bytes.closure) x =>
      specialized.aarch64.crc_bytes.closure.Insts.CoreOpsFunctionFnMutPairU32Shared0U8U32.call_mut
        p.2 (p.1, x)) (acc, ()) = ok (⟨crcRaw acc.bv (bytes l)⟩, ()) := by
  induction l generalizing acc with
  | nil => rfl
  | cons b l ih =>
    rw [List.foldlM_cons, call_b, bind_tc_ok, ih]
    simp [bytes, crcRaw]

theorem crc_bytes_eq (c : U32) (s : Slice U8) :
    specialized.aarch64.crc_bytes c s = ok ⟨update c.bv (bytes s.val)⟩ := by
  unfold specialized.aarch64.crc_bytes
  simp only [core.slice.Slice.iter, lift, bind_ok,
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold, List.drop_zero]
  rw [fold_bytes]; simp only [uncurry_apply_pair, bind_ok]
  rfl

theorem fold_quads (l : List U64) (acc : U32) :
    l.foldlM (fun (p : U32 × specialized.aarch64.crc_quads.closure) x =>
      specialized.aarch64.crc_quads.closure.Insts.CoreOpsFunctionFnMutPairU32Shared0U64U32.call_mut
        p.2 (p.1, x)) (acc, ()) = ok (⟨crcRaw acc.bv (qb l)⟩, ()) := by
  induction l generalizing acc with
  | nil => rfl
  | cons b l ih =>
    rw [List.foldlM_cons, call_q, bind_tc_ok, ih, qb_cons, crcRaw_append]

/-! ## `chunks_exact` -/

theorem toChunksExact_spec {α} (n : Nat) (hn : 0 < n) (l : List α) :
    (∀ c ∈ (List.toChunksExact n hn l).1, c.length = n) ∧
      (List.toChunksExact n hn l).1.flatten ++ (List.toChunksExact n hn l).2 = l ∧
      (List.toChunksExact n hn l).2.length < n := by
  unfold List.toChunksExact
  split
  · rename_i h; simp [h]
  · rename_i h
    have ih := toChunksExact_spec n hn (l.drop n)
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨?_, ?_, h3⟩
    · simp only [List.mem_cons]
      rintro c (rfl | hc)
      · simp only [List.length_take]; omega
      · exact h1 c hc
    · simp only [List.flatten_cons, List.append_assoc, h2, List.take_append_drop]
termination_by l.length
decreasing_by simp [List.length_drop]; omega

theorem idx_of {α} (ch : Slice α) (i : Usize) (x : α) (h : ch.val[i.val]? = some x) :
    Slice.index_usize ch i = ok x := by
  simp only [Slice.index_usize, Slice.getElem?_Usize_eq, h]

theorem quads_body_some (cs : List (Slice U64)) (r : Slice U64) (ch : Slice U64)
    (q0 q1 q2 q3 q4 q5 q6 q7 : U64) (h : ch.val = [q0, q1, q2, q3, q4, q5, q6, q7]) (c : U32) :
    specialized.aarch64.crc_quads_loop.body ⟨ch :: cs, r⟩ c =
      ok (.cont (⟨cs, r⟩, ⟨crcRaw c.bv (qb ch.val)⟩)) := by
  unfold specialized.aarch64.crc_quads_loop.body
  simp only [core.slice.iter.IteratorChunksExact.next]
  rw_bind
  simp only [uncurry_apply_pair]
  rw [idx_of ch 0#usize q0 (by rw [h]; rfl), idx_of ch 1#usize q1 (by rw [h]; rfl),
    idx_of ch 2#usize q2 (by rw [h]; rfl), idx_of ch 3#usize q3 (by rw [h]; rfl),
    idx_of ch 4#usize q4 (by rw [h]; rfl), idx_of ch 5#usize q5 (by rw [h]; rfl),
    idx_of ch 6#usize q6 (by rw [h]; rfl), idx_of ch 7#usize q7 (by rw [h]; rfl)]
  simp only [crc32d_eq, bind_tc_ok]
  rw [h]
  simp [qb, crcRaw_append]

theorem quads_body_none (r : Slice U64) (c : U32) :
    specialized.aarch64.crc_quads_loop.body ⟨[], r⟩ c = ok (.done (c, ⟨[], r⟩)) := by
  unfold specialized.aarch64.crc_quads_loop.body
  simp only [core.slice.iter.IteratorChunksExact.next]
  rw_bind
  simp only [uncurry_apply_pair]

theorem quads_unfold (it : core.slice.iter.ChunksExact U64) (c : U32) :
    specialized.aarch64.crc_quads_loop it c = (do
      let r ← specialized.aarch64.crc_quads_loop.body it c
      match r with
      | .cont (it', c') => specialized.aarch64.crc_quads_loop it' c'
      | .done r => ok r) := by
  conv => lhs; unfold specialized.aarch64.crc_quads_loop; rw [loop]
  simp only []
  congr 1; funext r
  rcases r with ⟨⟨it', c'⟩⟩ | r <;> rfl

theorem quads_loop_eq (cs : List (Slice U64)) (hcs : ∀ ch ∈ cs, ch.val.length = 8)
    (r : Slice U64) (c : U32) :
    specialized.aarch64.crc_quads_loop ⟨cs, r⟩ c =
      ok (⟨crcRaw c.bv (qb (cs.flatMap (·.val)))⟩, ⟨[], r⟩) := by
  induction cs generalizing c with
  | nil => rw [quads_unfold, quads_body_none]; rw_bind; rfl
  | cons ch cs ih =>
    have hl := hcs ch (by simp)
    match hv : ch.val, hl with
    | [q0, q1, q2, q3, q4, q5, q6, q7], _ =>
      rw [quads_unfold, quads_body_some cs r ch q0 q1 q2 q3 q4 q5 q6 q7 hv]; rw_bind
      simp only []
      rw [ih (fun c hc => hcs c (by simp [hc]))]
      simp only [List.flatMap_cons, qb_append, crcRaw_append, hv]

theorem flatMap_from {α} (l : List (List α)) (g : {x // x ∈ l} → Slice α)
    (hg : ∀ x, (g x).val = x.1) :
    (l.attach.map g).flatMap (·.val) = l.flatten := by
  rw [List.flatMap_map]
  simp only [hg]
  rw [List.flatMap_def]
  show (l.attach.map Subtype.val).flatten = _
  rw [List.attach_map_subtype_val]

theorem crc_quads_eq (c : U32) (s : Slice U64) :
    specialized.aarch64.crc_quads c s = ok ⟨update c.bv (qb s.val)⟩ := by
  unfold specialized.aarch64.crc_quads
  obtain ⟨h1, h2, _⟩ := toChunksExact_spec (8#usize).val (by decide) s.val
  simp only [lift, core.slice.Slice.chunks_exact]
  rw [dif_pos (by decide)]
  rw_bind; rw_bind
  rw [quads_loop_eq _ (by
    intro ch hch
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hch
    obtain ⟨c', hc', rfl⟩ := hch
    simp only [Slice.from_val]; exact h1 c' hc')]
  rw_bind
  simp only [uncurry_apply_pair, core.slice.iter.ChunksExact.getRemainder,
    core.slice.Slice.iter, core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.fold,
    List.drop_zero, Slice.from_val]
  rw_bind; rw_bind
  simp only [List.drop_zero, Slice.from_val]
  rw [fold_quads]
  rw [flatMap_from _ _ (fun _ => Slice.from_val _ _)]
  simp only [bind_tc_ok, bind_ok, update, not_bv]
  rw [eb32, ← crcRaw_append, ← qb_append, h2]
  erw [bind_ok]
  rfl

/-! ## Machine arithmetic on `usize` -/

theorem Usize.add_ok (x y : Usize) (h : x.val + y.val ≤ Usize.max) :
    ∃ z : Usize, z.val = x.val + y.val ∧ (x + y : Result Usize) = ok z := by
  simp only [HAdd.hAdd, UScalar.add, UScalar.tryMk, UScalar.tryMkOpt]
  have hc : UScalar.check_bounds UScalarTy.Usize (Add.add x.val y.val) = true := by
    simp only [UScalar.check_bounds, decide_eq_true_eq]
    show x.val + y.val < _
    scalar_tac
  rw [dif_pos hc]
  exact ⟨_, by simp, rfl⟩

theorem Usize.mul_ok (x y : Usize) (h : x.val * y.val ≤ Usize.max) :
    ∃ z : Usize, z.val = x.val * y.val ∧ (x * y : Result Usize) = ok z := by
  simp only [HMul.hMul, UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt]
  have hc : UScalar.check_bounds UScalarTy.Usize (Mul.mul x.val y.val) = true := by
    simp only [UScalar.check_bounds, decide_eq_true_eq]
    show x.val * y.val < _
    scalar_tac
  rw [dif_pos hc]
  exact ⟨_, by simp, rfl⟩

/-! ## The three-stream loops -/

/-- `n` words of `x` from index `i`, as bytes. -/
def W (x : List U64) (i n : Nat) : List (BitVec 8) := qb ((x.drop i).take n)

theorem W_zero (x : List U64) (i : Nat) : W x i 0 = [] := by simp [W, qb]

theorem W_succ (x : List U64) (i n : Nat) (h : i < x.length) :
    W x i (n + 1) = bytes8 x[i]!.bv ++ W x (i + 1) n := by
  simp only [W]
  rw [List.drop_eq_getElem_cons h, List.take_succ_cons, qb_cons, getElem!_pos x i h]

theorem tri_inner_unfold (it : core.ops.range.Range Usize) (a b c : Slice U64) (c0 c1 c2 : U32) (i : Usize) :
    specialized.aarch64.calculate_loop0_loop0 it a b c c0 c1 c2 i = (do
      let r ← specialized.aarch64.calculate_loop0_loop0.body a b c i it c0 c1 c2
      match r with
      | .cont (it', c0', c1', c2') => specialized.aarch64.calculate_loop0_loop0 it' a b c c0' c1' c2' i
      | .done r => ok r) := by
  conv => lhs; unfold specialized.aarch64.calculate_loop0_loop0; rw [loop]
  simp only []
  congr 1; funext r
  rcases r with ⟨⟨it', c0', c1', c2'⟩⟩ | r <;> rfl

theorem tri_inner_eq (m : Nat) (k : Usize) (hk : k.val + m = 4) (a b c : Slice U64) (c0 c1 c2 : U32)
    (i : Usize) (ha : i.val + 4 ≤ a.length) (hb : i.val + 4 ≤ b.length) (hc : i.val + 4 ≤ c.length) :
    specialized.aarch64.calculate_loop0_loop0 ⟨k, 4#usize⟩ a b c c0 c1 c2 i =
      ok (⟨crcRaw c0.bv (W a.val (i.val + k.val) m)⟩, ⟨crcRaw c1.bv (W b.val (i.val + k.val) m)⟩,
        ⟨crcRaw c2.bv (W c.val (i.val + k.val) m)⟩) := by
  induction m generalizing k c0 c1 c2 with
  | zero =>
    rw [tri_inner_unfold]
    simp only [specialized.aarch64.calculate_loop0_loop0.body]
    rw [range_next_usize_ge k 4#usize (by simp; omega)]
    rw_bind; simp only [uncurry_apply_pair]
    rw_bind
    simp only [W_zero, crcRaw_nil]
  | succ m ih =>
    obtain ⟨k', hk', hnext⟩ := range_next_usize_lt k 4#usize (by simp; omega)
    obtain ⟨j, hj, hadd⟩ := Usize.add_ok i k (by scalar_tac)
    rw [tri_inner_unfold]
    simp only [specialized.aarch64.calculate_loop0_loop0.body]
    rw [hnext]; rw_bind; simp only [uncurry_apply_pair]
    rw [hadd]; rw_bind
    rw [Slice.index_usize_ok a j (by simp only [Slice.length] at ha; omega)]; rw_bind
    rw [crc32d_eq]; rw_bind
    rw [Slice.index_usize_ok b j (by simp only [Slice.length] at hb; omega)]; rw_bind
    rw [crc32d_eq]; rw_bind
    rw [Slice.index_usize_ok c j (by simp only [Slice.length] at hc; omega)]; rw_bind
    rw [crc32d_eq]; rw_bind
    rw_bind
    simp only []
    rw [ih k' (by omega)]
    have e : i.val + k'.val = j.val + 1 := by omega
    rw [e, ← hj, W_succ a.val j.val m (by simp only [Slice.length] at ha; omega),
      W_succ b.val j.val m (by simp only [Slice.length] at hb; omega),
      W_succ c.val j.val m (by simp only [Slice.length] at hc; omega)]
    simp only [crcRaw_append, eb32]

theorem W_add (x : List U64) (i n m : Nat) : W x i (n + m) = W x i n ++ W x (i + n) m := by
  simp only [W, List.take_add, qb_append, List.drop_drop]

theorem tri_outer_unfold (n3 : Usize) (a b c : Slice U64) (c0 c1 c2 : U32) (i : Usize) :
    specialized.aarch64.calculate_loop0 n3 a b c c0 c1 c2 i = (do
      let r ← specialized.aarch64.calculate_loop0.body n3 a b c c0 c1 c2 i
      match r with
      | .cont (c0', c1', c2', i') => specialized.aarch64.calculate_loop0 n3 a b c c0' c1' c2' i'
      | .done r => ok r) := by
  conv => lhs; unfold specialized.aarch64.calculate_loop0; rw [loop]
  simp only []
  congr 1; funext r
  rcases r with ⟨⟨c0', c1', c2', i'⟩⟩ | r <;> rfl

theorem tri_outer_eq (t : Nat) (n3 : Usize) (hn : n3.val + 4 ≤ Usize.max) (a b c : Slice U64)
    (ha : a.length = n3.val) (hb : b.length = n3.val) (hc : c.length = n3.val)
    (c0 c1 c2 : U32) (i : Usize) (hi : i.val ≤ n3.val) (ht : (n3.val - i.val) / 4 = t) :
    ∃ j : Usize, j.val = i.val + 4 * t ∧
      specialized.aarch64.calculate_loop0 n3 a b c c0 c1 c2 i =
        ok (⟨crcRaw c0.bv (W a.val i.val (4 * t))⟩, ⟨crcRaw c1.bv (W b.val i.val (4 * t))⟩,
          ⟨crcRaw c2.bv (W c.val i.val (4 * t))⟩, j) := by
  induction t generalizing i c0 c1 c2 with
  | zero =>
    refine ⟨i, by simp, ?_⟩
    obtain ⟨i1, hi1, hadd⟩ := Usize.add_ok i 4#usize (by simp; omega)
    rw [tri_outer_unfold]
    simp only [specialized.aarch64.calculate_loop0.body]
    rw [hadd]; rw_bind
    rw [if_neg (by scalar_tac)]
    rw_bind
    simp only [Nat.mul_zero, W_zero, crcRaw_nil]
  | succ t ih =>
    obtain ⟨i1, hi1, hadd⟩ := Usize.add_ok i 4#usize (by simp; omega)
    rw [tri_outer_unfold]
    simp only [specialized.aarch64.calculate_loop0.body]
    rw [hadd]; rw_bind
    rw [if_pos (by scalar_tac)]
    rw [tri_inner_eq 4 0#usize (by simp) a b c c0 c1 c2 i (by omega) (by omega) (by omega)]
    rw_bind; simp only [uncurry_apply_pair]
    rw_bind; rw_bind; simp only []
    obtain ⟨j, hj, h⟩ := ih _ _ _ i1 (by scalar_tac) (by scalar_tac)
    have h4 : (4#usize).val = 4 := by simp
    refine ⟨j, by omega, ?_⟩
    rw [h]
    simp only [eb32, ← crcRaw_append, show 4 * (t + 1) = 4 + 4 * t by ring, W_add, hi1]
    simp

theorem tri_tail_unfold (n3 : Usize) (a b c : Slice U64) (c0 c1 c2 : U32) (i : Usize) :
    specialized.aarch64.calculate_loop1 n3 a b c c0 c1 c2 i = (do
      let r ← specialized.aarch64.calculate_loop1.body n3 a b c c0 c1 c2 i
      match r with
      | .cont (c0', c1', c2', i') => specialized.aarch64.calculate_loop1 n3 a b c c0' c1' c2' i'
      | .done r => ok r) := by
  conv => lhs; unfold specialized.aarch64.calculate_loop1; rw [loop]
  simp only []
  congr 1; funext r
  rcases r with ⟨⟨c0', c1', c2', i'⟩⟩ | r <;> rfl

theorem tri_tail_eq (t : Nat) (n3 : Usize) (a b c : Slice U64)
    (ha : a.length = n3.val) (hb : b.length = n3.val) (hc : c.length = n3.val)
    (c0 c1 c2 : U32) (i : Usize) (hi : i.val ≤ n3.val) (ht : n3.val - i.val = t) :
    specialized.aarch64.calculate_loop1 n3 a b c c0 c1 c2 i =
      ok (⟨crcRaw c0.bv (W a.val i.val t)⟩, ⟨crcRaw c1.bv (W b.val i.val t)⟩,
        ⟨crcRaw c2.bv (W c.val i.val t)⟩) := by
  induction t generalizing i c0 c1 c2 with
  | zero =>
    rw [tri_tail_unfold]
    simp only [specialized.aarch64.calculate_loop1.body]
    rw [if_neg (by scalar_tac)]
    rw_bind
    simp only [W_zero, crcRaw_nil]
  | succ t ih =>
    obtain ⟨i1, hi1, hadd⟩ := Usize.add_ok i 1#usize (by scalar_tac)
    rw [tri_tail_unfold]
    simp only [specialized.aarch64.calculate_loop1.body]
    rw [if_pos (by scalar_tac)]
    simp only [Slice.length] at ha hb hc
    rw [Slice.index_usize_ok a i (by omega)]; rw_bind
    rw [crc32d_eq]; rw_bind
    rw [Slice.index_usize_ok b i (by omega)]; rw_bind
    rw [crc32d_eq]; rw_bind
    rw [Slice.index_usize_ok c i (by omega)]; rw_bind
    rw [crc32d_eq]; rw_bind
    rw [hadd]; rw_bind
    rw_bind; simp only []
    have h1 : (1#usize).val = 1 := by simp
    rw [ih _ _ _ i1 (by omega) (by omega)]
    rw [W_succ a.val i.val t (by omega), W_succ b.val i.val t (by omega), W_succ c.val i.val t (by omega),
      hi1, h1]
    simp only [eb32, crcRaw_append]

/-! ## `align_to`: the `u64`s are the bytes in memory order -/

theorem byte_cons0 (b : BitVec 8) (y : BitVec 64) : a64.byte (b.setWidth 64 ^^^ (y <<< 8)) 0 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [a64.byte]

theorem byte_consS (b : BitVec 8) (y : BitVec 64) (k : Nat) (hk : k < 7) :
    a64.byte (b.setWidth 64 ^^^ (y <<< 8)) (k + 1) = a64.byte y k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [a64.byte, BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  rw [BitVec.getLsbD_of_ge b _ (by omega), show 8 * (k + 1) + i - 8 = 8 * k + i by omega]
  simp [show 8 * (k + 1) + i < 64 by omega, show ¬ 8 * (k + 1) + i < 8 by omega, hi]

theorem byte_ofBytes : ∀ (l : List (BitVec 8)), l.length ≤ 8 → ∀ k (hk : k < l.length),
    a64.byte (a64.ofBytes l) k = l[k]
  | [], _, k, hk => by simp at hk
  | b :: l, hl, 0, _ => by simp only [a64.ofBytes, byte_cons0, List.getElem_cons_zero]
  | b :: l, hl, k + 1, hk => by
    simp only [List.length_cons] at hl hk
    simp only [a64.ofBytes, byte_consS b _ k (by omega), List.getElem_cons_succ]
    exact byte_ofBytes l (by omega) k (by omega)

theorem bytes8_ofBytes (l : List (BitVec 8)) (hl : l.length = 8) : bytes8 (a64.ofBytes l) = l := by
  apply List.ext_getElem
  · simp [bytes8, hl]
  · intro k h1 h2
    simp only [bytes8, List.getElem_map, List.getElem_range]
    exact byte_ofBytes l (by omega) k h2

theorem qb_quadsOf (m : Nat) (l : List U8) (h : 8 * m ≤ l.length) :
    qb (a64.quadsOf m l) = bytes (l.take (8 * m)) := by
  induction m generalizing l with
  | zero => simp [a64.quadsOf, qb, bytes]
  | succ m ih =>
    simp only [a64.quadsOf, qb_cons]
    rw [ih (l.drop 8) (by simp; omega), bytes8_ofBytes _ (by simp; omega),
      show 8 * (m + 1) = 8 + 8 * m by ring, List.take_add]
    simp [bytes]

/-! ## `calculate` -/

theorem split_eq (data : Slice U8) :
    ∃ pre qs post, specialized.aarch64.split_quads data = ok (pre, qs, post) ∧
      bytes pre.val ++ qb qs.val ++ bytes post.val = bytes data.val ∧ 8 * qs.length ≤ data.length := by
  refine ⟨_, _, _, rfl, ?_, ?_⟩
  · simp only [Slice.from_val]
    rw [qb_quadsOf _ _ (by simp only [List.length_drop]; omega)]
    simp only [bytes, ← List.map_append, List.drop_drop]
    congr 1
    rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  · simp only [Slice.length, Slice.from_val, a64.quadsOf_length]
    omega

theorem index_range (s : Slice U64) (x y : Usize) (hxy : x.val ≤ y.val) (hy : y.val ≤ s.length) :
    ∃ s' : Slice U64, s'.val = (s.val.drop x.val).take (y.val - x.val) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U64) s
        { start := x, «end» := y } = ok s' := by
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index]
  rw [if_pos (by scalar_tac)]
  exact ⟨_, by simp [List.slice], rfl⟩

theorem index_from64 (s : Slice U64) (x : Usize) (hx : x.val ≤ s.length) :
    ∃ s' : Slice U64, s'.val = s.val.drop x.val ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U64) s
        { start := x } = ok s' := by
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeFromUsizeSlice,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index]
  rw [if_pos (by simpa using hx)]
  exact ⟨_, by simp [Slice.drop], rfl⟩

theorem usize_le_u64 : Usize.max ≤ U64.max := by
  simp only [Usize.max, U64.max]
  have : Usize.numBits ≤ U64.numBits := by
    cases System.Platform.numBits_eq <;> simp [Usize.numBits, U64.numBits, *]
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) this
  omega

theorem W_all (x : List U64) (n : Nat) (h : x.length = n) : W x 0 n = qb x := by
  simp [W, ← h]

theorem three_blocks {α} (l : List α) (n : Nat) :
    (l.drop 0).take n ++ ((l.drop n).take (2 * n - n) ++ ((l.drop (2 * n)).take (3 * n - 2 * n) ++
      l.drop (3 * n))) = l := by
  rw [show 2 * n - n = n by omega, show 3 * n - 2 * n = n by omega, show 3 * n = 2 * n + n by omega,
    ← List.drop_drop, List.take_append_drop, show 2 * n = n + n by omega, ← List.drop_drop,
    List.take_append_drop, List.drop_zero, List.take_append_drop]

theorem calculate_eq (crc : U32) (data : Slice U8) :
    specialized.aarch64.calculate crc data = ok ⟨update crc.bv (bytes data.val)⟩ := by
  obtain ⟨pre, qs, post, hsplit, hbytes, hlen⟩ := split_eq data
  have hdl : data.length ≤ Usize.max := by scalar_tac
  have hmin : specialized.aarch64.MIN_TRIPLE_QUADS.val = 192 := by
    unfold specialized.aarch64.MIN_TRIPLE_QUADS; simp
  have hql : qs.val.length = qs.length := rfl
  unfold specialized.aarch64.calculate
  rw [hsplit]; rw_bind; simp only [uncurry_apply_pair]
  rw [crc_bytes_eq]; rw_bind
  by_cases hQ : 192 ≤ qs.length
  · rw [if_pos (by scalar_tac)]
    obtain ⟨n3, hdiv, hn3⟩ := UScalar.div_spec (Slice.len qs) (y := 3#usize) (by simp)
    rw [hdiv]; rw_bind
    have hn3' : n3.val = qs.length / 3 := by simpa using hn3
    obtain ⟨i2, hi2, hm8⟩ := Usize.mul_ok n3 8#usize (by simp; omega)
    rw [hm8]; rw_bind
    simp only [lift]; rw_bind
    obtain ⟨a, ha, hia⟩ := index_range qs 0#usize n3 (by simp) (by omega)
    rw [hia]; rw_bind
    obtain ⟨n2, hn2, hm2⟩ := Usize.mul_ok 2#usize n3 (by simp; omega)
    have hn2' : n2.val = 2 * n3.val := by simpa using hn2
    rw [hm2]; rw_bind
    obtain ⟨b, hb, hib⟩ := index_range qs n3 n2 (by omega) (by omega)
    rw [hib]; rw_bind
    obtain ⟨n3x, hn3x, hm3⟩ := Usize.mul_ok 3#usize n3 (by simp; omega)
    have hn3x' : n3x.val = 3 * n3.val := by simpa using hn3x
    rw [hm3]; rw_bind
    obtain ⟨c, hc, hic⟩ := index_range qs n2 n3x (by omega) (by omega)
    rw [hic]; rw_bind
    have hal : a.length = n3.val := by
      simp only [Slice.length, ha, List.length_take, List.length_drop]; simp; omega
    have hbl' : b.length = n3.val := by
      simp only [Slice.length, hb, List.length_take, List.length_drop]; omega
    have hcl : c.length = n3.val := by
      simp only [Slice.length, hc, List.length_take, List.length_drop]; omega
    have hn : n3.val + 4 ≤ Usize.max := by omega
    have hbl : (UScalar.cast .U64 i2).val = 8 * n3.val := by
      rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt]
      · simp at hi2; omega
      · have := usize_le_u64; simp only [U64.max] at this; scalar_tac
    generalize UScalar.cast .U64 i2 = blen at hbl ⊢
    generalize hr : (⟨update crc.bv (bytes pre.val)⟩ : U32) = r
    -- the three streams
    rw_bind; rw_bind; rw_bind
    obtain ⟨j, hj, h0⟩ := tri_outer_eq (n3.val / 4) n3 hn a b c hal hbl' hcl (~~~ r) (~~~ 0#u32)
      (~~~ 0#u32) 0#usize (by simp) (by simp)
    rw [h0]; rw_bind; simp only [uncurry_apply_pair]
    rw [tri_tail_eq (n3.val - j.val) n3 a b c hal hbl' hcl _ _ _ j (by simp at hj; omega) rfl]
    rw_bind; simp only [uncurry_apply_pair]
    rw_bind; rw_bind
    have hj' : j.val = 4 * (n3.val / 4) := by simpa using hj
    have hfull : ∀ x : Slice U64, x.length = n3.val →
        W x.val (0#usize).val (4 * (n3.val / 4)) ++ W x.val j.val (n3.val - j.val) = qb x.val := by
      intro x hx
      have h00 : (0#usize).val = 0 := by simp
      have hA := W_add x.val 0 (4 * (n3.val / 4)) (n3.val - 4 * (n3.val / 4))
      rw [Nat.zero_add] at hA
      rw [h00, hj', ← hA, show 4 * (n3.val / 4) + (n3.val - 4 * (n3.val / 4)) = n3.val by omega]
      exact W_all _ _ hx
    simp only [eb32, ← crcRaw_append, hfull a hal, hfull b hbl', hfull c hcl, not_mk, combine_eq]
    have hbl0 : blen.val ≠ 0 := by omega
    rw [if_neg hbl0]; rw_bind
    simp only [hbl0, ↓reduceIte]
    simp only [eb32, not_bv]
    have hqa : (qb b.val).length = blen.val := by rw [qb_length, hbl]; simp [Slice.length] at hbl'; omega
    have hqc : (qb c.val).length = blen.val := by rw [qb_length, hbl]; simp [Slice.length] at hcl; omega
    have e1 : (~~~ crcRaw (~~~ r.bv) (qb a.val)) = update r.bv (qb a.val) := rfl
    have e2 : ∀ l, (~~~ crcRaw (~~~ (0#u32).bv) l) = crc32 l := fun _ => rfl
    rw [e1, e2, e2, ← hqa, ← update_eq_Zn_xor, hqa, ← hqc]
    rw_bind
    rw [eb32, ← update_eq_Zn_xor, update_append, update_append]
    -- the words after the three blocks, then the trailing bytes
    rw_bind; rw_bind
    obtain ⟨rest, hrest, hif⟩ := index_from64 qs n3x (by omega)
    rw [hif]; rw_bind
    rw [crc_quads_eq]; rw_bind
    have hall : qb a.val ++ (qb b.val ++ qb c.val) ++ qb rest.val = qb qs.val := by
      have h00 : (0#usize).val = 0 := by simp
      rw [← qb_append, ← qb_append, ← qb_append, ha, hb, hc, hrest, hn2', hn3x', h00, Nat.sub_zero]
      simp only [List.append_assoc]
      rw [three_blocks]
    rw [crc_bytes_eq, eb32, eb32, update_append, update_append, ← hr, eb32, update_append,
      ← hbytes, ← hall]
    simp only [List.append_assoc]
  · rw [if_neg (by scalar_tac)]
    rw [crc_quads_eq]; rw_bind
    rw [crc_bytes_eq, eb32, eb32, update_append, update_append, ← hbytes, List.append_assoc]

end Crc32fastVerif
