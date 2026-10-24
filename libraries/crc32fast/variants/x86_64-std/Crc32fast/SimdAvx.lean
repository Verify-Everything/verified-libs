import Crc32fast.SimdWide

/-!
# The AVX2 and AVX-512 (VPCLMULQDQ) paths equal the spec's `update`
-/

open Aeneas Aeneas.Std Result crc32fast Crc32Spec x86

namespace Crc32fastVerif

theorem index_from (buf : Slice U8) (n : Usize) (h : n.val ≤ buf.length) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) buf
      { start := n } = ok (buf.drop n) := by
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeFromUsizeSlice,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index]
  rw [if_pos (by simpa using h)]

theorem drop_val (d : Slice U8) (n : Usize) : (d.drop n).val = d.val.drop n.val := by
  simp [Slice.drop]

theorem drop_length (d : Slice U8) (n : Usize) : (d.drop n).length = d.length - n.val := by
  simp [Slice.drop]

theorem get256_eq (a : Slice U8) (h : 32 ≤ a.length) :
    specialized.pclmulqdq.get256 a = ok (blk (a.val.drop 16) ++ blk a.val, a.drop 32#usize) := by
  unfold specialized.pclmulqdq.get256
  simp only [massert, specialized.pclmulqdq.load256]
  rw [if_pos (by simp; scalar_tac)]
  rw_bind
  rw [if_pos (by simpa using h)]
  rw_bind
  rw [index_from _ _ (by simpa using h)]
  rw_bind
  rw [← fromBytes256]
  rfl

theorem get512_eq (a : Slice U8) (h : 64 ≤ a.length) :
    specialized.pclmulqdq.get512 a =
      ok (blk (a.val.drop 48) ++ blk (a.val.drop 32) ++ blk (a.val.drop 16) ++ blk a.val,
        a.drop 64#usize) := by
  unfold specialized.pclmulqdq.get512
  simp only [massert, specialized.pclmulqdq.load512]
  rw [if_pos (by simp; scalar_tac)]
  rw_bind
  rw [if_pos (by simpa using h)]
  rw_bind
  rw [index_from _ _ (by simpa using h)]
  rw_bind
  rw [← fromBytes512]
  rfl

theorem clmulSel0 (a k : BitVec 128) : clmulSel (0#i32).bv a k = clmul (lo64 a) (lo64 k) := by
  simp only [clmulSel]; rfl

theorem clmulSel17 (a k : BitVec 128) : clmulSel (17#i32).bv a k = clmul (hi64 a) (hi64 k) := by
  simp only [clmulSel]; rfl

theorem reduce256_eq (h1 l1 h2 l2 k : BitVec 128) :
    specialized.pclmulqdq.reduce256 (h1 ++ l1) (h2 ++ l2) (k ++ k) =
      ok ((h2 ^^^ F k h1) ++ (l2 ^^^ F k l1)) := by
  unfold specialized.pclmulqdq.reduce256
  simp only [core.core_arch.x86.vpclmulqdq._mm256_clmulepi64_epi128, core.core_arch.x86.avx2._mm256_xor_si256,
    bind_tc_ok, bind_ok]
  rw [show (h1 ++ l1 : BitVec 256) = (h1 ++ l1 : BitVec (128 * 2)) from rfl, perLane2_2, perLane2_2]
  simp only [clmulSel0, clmulSel17, BitVec.xor_append, F, BitVec.xor_assoc]

theorem reduce512_eq (a b c d a' b' c' d' k : BitVec 128) :
    specialized.pclmulqdq.reduce512 (a ++ b ++ c ++ d) (a' ++ b' ++ c' ++ d') (k ++ k ++ k ++ k) =
      ok ((a' ^^^ F k a) ++ (b' ^^^ F k b) ++ (c' ^^^ F k c) ++ (d' ^^^ F k d)) := by
  unfold specialized.pclmulqdq.reduce512
  simp only [core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128, core.core_arch.x86.avx512f._mm512_xor_si512,
    bind_tc_ok, bind_ok]
  rw [show (a ++ b ++ c ++ d : BitVec 512) = (a ++ b ++ c ++ d : BitVec (128 * 4)) from rfl,
    perLane2_4, perLane2_4]
  simp only [clmulSel0, clmulSel17, BitVec.xor_append, F, BitVec.xor_assoc]

theorem k1024_eq : core.core_arch.x86.avx._mm256_set_epi64x specialized.pclmulqdq.K_1024_HIGH
    specialized.pclmulqdq.K_1024_LOW specialized.pclmulqdq.K_1024_HIGH specialized.pclmulqdq.K_1024_LOW =
    ok (k1024 ++ k1024) := by
  unfold specialized.pclmulqdq.K_1024_HIGH specialized.pclmulqdq.K_1024_LOW
  simp only [core.core_arch.x86.avx._mm256_set_epi64x]
  rfl

theorem k2048_eq : core.core_arch.x86.avx512f._mm512_set_epi64
    specialized.pclmulqdq.K_2048_HIGH specialized.pclmulqdq.K_2048_LOW
    specialized.pclmulqdq.K_2048_HIGH specialized.pclmulqdq.K_2048_LOW
    specialized.pclmulqdq.K_2048_HIGH specialized.pclmulqdq.K_2048_LOW
    specialized.pclmulqdq.K_2048_HIGH specialized.pclmulqdq.K_2048_LOW =
    ok (k2048 ++ k2048 ++ k2048 ++ k2048) := by
  unfold specialized.pclmulqdq.K_2048_HIGH specialized.pclmulqdq.K_2048_LOW
  simp only [core.core_arch.x86.avx512f._mm512_set_epi64]
  rfl

theorem cast256_eq (h l : BitVec 128) : core.core_arch.x86.avx._mm256_castsi256_si128 (h ++ l) = ok l := by
  simp only [core.core_arch.x86.avx._mm256_castsi256_si128]
  congr 1
  have := lane2_0 h l
  simpa [lane] using this

theorem extract256_eq (h l : BitVec 128) :
    core.core_arch.x86.avx2._mm256_extracti128_si256 1#i32 (h ++ l) = ok h := by
  simp only [core.core_arch.x86.avx2._mm256_extracti128_si256]
  rw [show (1#i32).bv.toNat % 2 = 1 from rfl, lane2_1]

theorem cast512_eq (a b c d : BitVec 128) :
    core.core_arch.x86.avx512f._mm512_castsi512_si128 (a ++ b ++ c ++ d) = ok d := by
  simp only [core.core_arch.x86.avx512f._mm512_castsi512_si128]
  congr 1
  have := (lane4 a b c d).1
  simpa [lane] using this

theorem extract512_eq (a b c d : BitVec 128) :
    core.core_arch.x86.avx512f._mm512_extracti32x4_epi32 1#i32 (a ++ b ++ c ++ d) = ok c ∧
    core.core_arch.x86.avx512f._mm512_extracti32x4_epi32 2#i32 (a ++ b ++ c ++ d) = ok b ∧
    core.core_arch.x86.avx512f._mm512_extracti32x4_epi32 3#i32 (a ++ b ++ c ++ d) = ok a := by
  simp only [core.core_arch.x86.avx512f._mm512_extracti32x4_epi32]
  rw [show (1#i32).bv.toNat % 4 = 1 from rfl, show (2#i32).bv.toNat % 4 = 2 from rfl,
    show (3#i32).bv.toNat % 4 = 3 from rfl]
  obtain ⟨_, h1, h2, h3⟩ := lane4 a b c d
  exact ⟨by rw [h1], by rw [h2], by rw [h3]⟩

theorem xor_zext256 (h l : BitVec 128) (z : BitVec 128) :
    (h ++ l) ^^^ z.setWidth 256 = h ++ (l ^^^ z) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_setWidth]
  by_cases h1 : i < 128
  · simp [h1, hi]
  · have := BitVec.getLsbD_of_ge z i (by omega)
    simp [h1, hi, this]

theorem xor_zext512 (a b c d : BitVec 128) (z : BitVec 128) :
    (a ++ b ++ c ++ d) ^^^ z.setWidth 512 = a ++ b ++ c ++ (d ^^^ z) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_setWidth]
  by_cases h1 : i < 128
  · simp [h1, hi]
  · have := BitVec.getLsbD_of_ge z i (by omega)
    simp [h1, hi, this]

/-! ## AVX2: the 8-stream loop -/

def drop128 (d : Slice U8) : Slice U8 := (((d.drop 32#usize).drop 32#usize).drop 32#usize).drop 32#usize

theorem drop128_val (d : Slice U8) : (drop128 d).val = d.val.drop 128 := by
  simp only [drop128, drop_val, List.drop_drop]; simp

theorem drop128_length (d : Slice U8) : (drop128 d).length = d.length - 128 := by
  simp only [Slice.length, drop128_val, List.length_drop]

/-- The 8 streams of four YMM registers, in increasing byte offset. -/
def S8 (h0 l0 h1 l1 h2 l2 h3 l3 : BitVec 128) : BitVec 32 := SL [l0, h0, l1, h1, l2, h2, l3, h3]

theorem avx2_body_ge (k h0 l0 h1 l1 h2 l2 h3 l3 : BitVec 128) (d : Slice U8) (h : 128 ≤ d.length) :
    specialized.pclmulqdq.calculate_avx2_loop.body (k ++ k) d (h0 ++ l0) (h1 ++ l1) (h2 ++ l2) (h3 ++ l3) =
      ok (.cont (drop128 d,
        (blk (d.val.drop 16) ^^^ F k h0) ++ (blk d.val ^^^ F k l0),
        (blk (d.val.drop 48) ^^^ F k h1) ++ (blk (d.val.drop 32) ^^^ F k l1),
        (blk (d.val.drop 80) ^^^ F k h2) ++ (blk (d.val.drop 64) ^^^ F k l2),
        (blk (d.val.drop 112) ^^^ F k h3) ++ (blk (d.val.drop 96) ^^^ F k l3))) := by
  unfold specialized.pclmulqdq.calculate_avx2_loop.body
  have hdl : d.val.length = d.length := rfl
  have h1 : 32 ≤ (d.drop 32#usize).length := by rw [drop_length]; simp; omega
  have h2 : 32 ≤ ((d.drop 32#usize).drop 32#usize).length := by rw [drop_length, drop_length]; simp; omega
  have h3 : 32 ≤ (((d.drop 32#usize).drop 32#usize).drop 32#usize).length := by
    rw [drop_length, drop_length, drop_length]; simp; omega
  rw [if_pos (by simp; scalar_tac), get256_eq d (by omega)]
  rw_bind; rw [uncurry_apply_pair, reduce256_eq]; rw_bind
  rw [get256_eq _ h1]; rw_bind; rw [uncurry_apply_pair, reduce256_eq]; rw_bind
  rw [get256_eq _ h2]; rw_bind; rw [uncurry_apply_pair, reduce256_eq]; rw_bind
  rw [get256_eq _ h3]; rw_bind; rw [uncurry_apply_pair, reduce256_eq]; rw_bind
  simp only [drop128, drop_val, List.drop_drop]
  simp

theorem avx2_body_lt (k : BitVec 256) (v0 v1 v2 v3 : BitVec 256) (d : Slice U8) (h : d.length < 128) :
    specialized.pclmulqdq.calculate_avx2_loop.body k d v0 v1 v2 v3 = ok (.done (d, v0, v1, v2, v3)) := by
  unfold specialized.pclmulqdq.calculate_avx2_loop.body
  rw [if_neg (by simp; scalar_tac)]

theorem avx2_unfold (d : Slice U8) (v0 v1 v2 v3 k : BitVec 256) :
    specialized.pclmulqdq.calculate_avx2_loop d v0 v1 v2 v3 k = (do
      let r ← specialized.pclmulqdq.calculate_avx2_loop.body k d v0 v1 v2 v3
      match r with
      | .cont (d', v0', v1', v2', v3') => specialized.pclmulqdq.calculate_avx2_loop d' v0' v1' v2' v3' k
      | .done r => ok r) := by
  conv => lhs; unfold specialized.pclmulqdq.calculate_avx2_loop; rw [loop]
  simp only []
  congr 1; funext r
  rcases r with ⟨⟨d', v0', v1', v2', v3'⟩⟩ | r <;> rfl

theorem step128 (h0 l0 h1 l1 h2 l2 h3 l3 : BitVec 128) (l : List U8) (h : 128 ≤ l.length) :
    crcRaw (S8 h0 l0 h1 l1 h2 l2 h3 l3) (bytes l) =
      crcRaw (S8 (blk (l.drop 16) ^^^ F k1024 h0) (blk l ^^^ F k1024 l0)
        (blk (l.drop 48) ^^^ F k1024 h1) (blk (l.drop 32) ^^^ F k1024 l1)
        (blk (l.drop 80) ^^^ F k1024 h2) (blk (l.drop 64) ^^^ F k1024 l2)
        (blk (l.drop 112) ^^^ F k1024 h3) (blk (l.drop 96) ^^^ F k1024 l3)) (bytes (l.drop 128)) := by
  unfold S8
  rw [stepFold k1024 [l0, h0, l1, h1, l2, h2, l3, h3] (fun a => foldBy128 a) l (by simp; omega)]
  simp only [blks, List.drop_drop, List.length_cons, List.length_nil, List.zipWith_cons_cons,
    List.zipWith_nil_left]

theorem avx2_loop_eq (n : Nat) (d : Slice U8) (h0 l0 h1 l1 h2 l2 h3 l3 : BitVec 128) (hn : d.length = n) :
    ∃ d' h0' l0' h1' l1' h2' l2' h3' l3',
      specialized.pclmulqdq.calculate_avx2_loop d (h0 ++ l0) (h1 ++ l1) (h2 ++ l2) (h3 ++ l3) (k1024 ++ k1024) =
        ok (d', h0' ++ l0', h1' ++ l1', h2' ++ l2', h3' ++ l3') ∧ d'.length < 128 ∧
      crcRaw (S8 h0 l0 h1 l1 h2 l2 h3 l3) (bytes d.val) =
        crcRaw (S8 h0' l0' h1' l1' h2' l2' h3' l3') (bytes d'.val) := by
  induction n using Nat.strong_induction_on generalizing d h0 l0 h1 l1 h2 l2 h3 l3 with
  | _ n ih =>
    by_cases h : 128 ≤ d.length
    · obtain ⟨d', a0, b0, a1, b1, a2, b2, a3, b3, e, hl, hc⟩ :=
        ih (drop128 d).length (by rw [drop128_length]; omega) (drop128 d) _ _ _ _ _ _ _ _ rfl
      refine ⟨d', a0, b0, a1, b1, a2, b2, a3, b3, ?_, hl, ?_⟩
      · rw [avx2_unfold, avx2_body_ge _ _ _ _ _ _ _ _ _ _ h, bind_ok]; exact e
      · rw [← hc, step128 _ _ _ _ _ _ _ _ _ h, drop128_val]
    · refine ⟨d, h0, l0, h1, l1, h2, l2, h3, l3, ?_, by omega, rfl⟩
      rw [avx2_unfold, avx2_body_lt _ _ _ _ _ _ (by omega), bind_ok]

/-- The CRC state of the 8 streams right after the first 128 bytes. -/
theorem avx2_init (c : BitVec 32) (l : List U8) (h : 128 ≤ l.length) :
    crcRaw (S8 (blk (l.drop 16)) (blk l ^^^ c.setWidth 128) (blk (l.drop 48)) (blk (l.drop 32))
      (blk (l.drop 80)) (blk (l.drop 64)) (blk (l.drop 112)) (blk (l.drop 96))) (bytes (l.drop 128)) =
    crcRaw c (bytes l) := by
  have hx : ∀ a b : BitVec 128, R16 (a ^^^ b) = R16 a ^^^ R16 b := R16_lin
  have key : S8 (blk (l.drop 16)) (blk l ^^^ c.setWidth 128) (blk (l.drop 48)) (blk (l.drop 32))
      (blk (l.drop 80)) (blk (l.drop 64)) (blk (l.drop 112)) (blk (l.drop 96)) =
      Zn (16 * 8) c ^^^ SL (blks l 8) := by
    simp only [S8, blks, SL_cons, SL, List.drop_drop, List.length_cons, List.length_nil, hx, R16_zext,
      Zn_xor, Zn_add, Nat.reduceAdd, Nat.reduceMul]
    ac_rfl
  rw [stepN 8 c l (by omega), key]

theorem calculate_avx2_eq (crc : U32) (data : Slice U8) :
    specialized.pclmulqdq.calculate_avx2 crc data = ok ⟨update crc.bv (bytes data.val)⟩ := by
  unfold specialized.pclmulqdq.calculate_avx2
  by_cases h256 : data.length < 256
  · rw [if_pos (by simp; scalar_tac), calculate_eq]
  rw [if_neg (by simp; scalar_tac)]
  have hdl : data.val.length = data.length := rfl
  have h1 : 32 ≤ (data.drop 32#usize).length := by rw [drop_length]; simp; omega
  have h2 : 32 ≤ ((data.drop 32#usize).drop 32#usize).length := by
    rw [drop_length, drop_length]; simp; omega
  have h3 : 32 ≤ (((data.drop 32#usize).drop 32#usize).drop 32#usize).length := by
    rw [drop_length, drop_length, drop_length]; simp; omega
  rw [get256_eq data (by omega)]; rw_bind; rw [uncurry_apply_pair]
  rw [get256_eq _ h1]; rw_bind; rw [uncurry_apply_pair]
  rw [get256_eq _ h2]; rw_bind; rw [uncurry_apply_pair]
  rw [get256_eq _ h3]; rw_bind; rw [uncurry_apply_pair]
  simp only [lift, bind_ok, cvt_eq, core.core_arch.x86.avx._mm256_castsi128_si256,
    core.core_arch.x86.avx2._mm256_xor_si256, xor_zext256]
  rw [k1024_eq, bind_ok]
  have e32 : (32#usize).val = 32 := rfl
  simp only [drop_val, List.drop_drop, e32, Nat.reduceAdd]
  obtain ⟨d', a0, b0, a1, b1, a2, b2, a3, b3, hl, _, hc⟩ := avx2_loop_eq _ (drop128 data)
    (blk (data.val.drop 16)) (blk data.val ^^^ (~~~crc.bv).setWidth 128)
    (blk (data.val.drop 48)) (blk (data.val.drop 32))
    (blk (data.val.drop 80)) (blk (data.val.drop 64))
    (blk (data.val.drop 112)) (blk (data.val.drop 96)) rfl
  rw [show (((data.drop 32#usize).drop 32#usize).drop 32#usize).drop 32#usize = drop128 data from rfl, hl,
    bind_ok]
  simp only [uncurry_apply_pair]
  rw [k3k4_eq, bind_ok, cast256_eq, bind_ok, extract256_eq, bind_ok, reduce128_eq, bind_ok,
    cast256_eq, bind_ok, reduce128_eq, bind_ok, extract256_eq, bind_ok, reduce128_eq, bind_ok,
    cast256_eq, bind_ok, reduce128_eq, bind_ok, extract256_eq, bind_ok, reduce128_eq, bind_ok,
    cast256_eq, bind_ok, reduce128_eq, bind_ok, extract256_eq, bind_ok, reduce128_eq, bind_ok, r128_eq]
  have hcol : R16 (a3 ^^^ F k3k4 (b3 ^^^ F k3k4 (a2 ^^^ F k3k4 (b2 ^^^ F k3k4 (a1 ^^^ F k3k4
      (b1 ^^^ F k3k4 (a0 ^^^ F k3k4 b0))))))) = S8 a0 b0 a1 b1 a2 b2 a3 b3 :=
    SL_collapse [a0, b1, a1, b2, a2, b3, a3] b0
  rw [hcol, ← hc, drop128_val, avx2_init _ _ (by omega)]
  rfl

/-! ## AVX-512: the 16-stream loop -/

def drop256 (d : Slice U8) : Slice U8 := (((d.drop 64#usize).drop 64#usize).drop 64#usize).drop 64#usize

theorem drop256_val (d : Slice U8) : (drop256 d).val = d.val.drop 256 := by
  simp only [drop256, drop_val, List.drop_drop]; simp

theorem drop256_length (d : Slice U8) : (drop256 d).length = d.length - 256 := by
  simp only [Slice.length, drop256_val, List.length_drop]

/-- The 16 streams of four ZMM registers `a ++ b ++ c ++ d` (lane 0 is `d`), in increasing offset. -/
def S16 (a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3 : BitVec 128) : BitVec 32 :=
  SL [d0, c0, b0, a0, d1, c1, b1, a1, d2, c2, b2, a2, d3, c3, b3, a3]

theorem avx512_body_ge (k a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3 : BitVec 128) (d : Slice U8)
    (h : 256 ≤ d.length) :
    specialized.pclmulqdq.calculate_avx512_loop.body (k ++ k ++ k ++ k) d
      (a0 ++ b0 ++ c0 ++ d0) (a1 ++ b1 ++ c1 ++ d1) (a2 ++ b2 ++ c2 ++ d2) (a3 ++ b3 ++ c3 ++ d3) =
      ok (.cont (drop256 d,
        (blk (d.val.drop 48) ^^^ F k a0) ++ (blk (d.val.drop 32) ^^^ F k b0) ++
          (blk (d.val.drop 16) ^^^ F k c0) ++ (blk d.val ^^^ F k d0),
        (blk (d.val.drop 112) ^^^ F k a1) ++ (blk (d.val.drop 96) ^^^ F k b1) ++
          (blk (d.val.drop 80) ^^^ F k c1) ++ (blk (d.val.drop 64) ^^^ F k d1),
        (blk (d.val.drop 176) ^^^ F k a2) ++ (blk (d.val.drop 160) ^^^ F k b2) ++
          (blk (d.val.drop 144) ^^^ F k c2) ++ (blk (d.val.drop 128) ^^^ F k d2),
        (blk (d.val.drop 240) ^^^ F k a3) ++ (blk (d.val.drop 224) ^^^ F k b3) ++
          (blk (d.val.drop 208) ^^^ F k c3) ++ (blk (d.val.drop 192) ^^^ F k d3))) := by
  unfold specialized.pclmulqdq.calculate_avx512_loop.body
  have hdl : d.val.length = d.length := rfl
  have h1 : 64 ≤ (d.drop 64#usize).length := by rw [drop_length]; simp; omega
  have h2 : 64 ≤ ((d.drop 64#usize).drop 64#usize).length := by rw [drop_length, drop_length]; simp; omega
  have h3 : 64 ≤ (((d.drop 64#usize).drop 64#usize).drop 64#usize).length := by
    rw [drop_length, drop_length, drop_length]; simp; omega
  rw [if_pos (by simp; scalar_tac), get512_eq d (by omega)]
  rw_bind; rw [uncurry_apply_pair, reduce512_eq]; rw_bind
  rw [get512_eq _ h1]; rw_bind; rw [uncurry_apply_pair, reduce512_eq]; rw_bind
  rw [get512_eq _ h2]; rw_bind; rw [uncurry_apply_pair, reduce512_eq]; rw_bind
  rw [get512_eq _ h3]; rw_bind; rw [uncurry_apply_pair, reduce512_eq]; rw_bind
  simp only [drop256, drop_val, List.drop_drop]
  simp

theorem avx512_body_lt (k : BitVec 512) (v0 v1 v2 v3 : BitVec 512) (d : Slice U8) (h : d.length < 256) :
    specialized.pclmulqdq.calculate_avx512_loop.body k d v0 v1 v2 v3 = ok (.done (d, v0, v1, v2, v3)) := by
  unfold specialized.pclmulqdq.calculate_avx512_loop.body
  rw [if_neg (by simp; scalar_tac)]

theorem avx512_unfold (d : Slice U8) (v0 v1 v2 v3 k : BitVec 512) :
    specialized.pclmulqdq.calculate_avx512_loop d v0 v1 v2 v3 k = (do
      let r ← specialized.pclmulqdq.calculate_avx512_loop.body k d v0 v1 v2 v3
      match r with
      | .cont (d', v0', v1', v2', v3') => specialized.pclmulqdq.calculate_avx512_loop d' v0' v1' v2' v3' k
      | .done r => ok r) := by
  conv => lhs; unfold specialized.pclmulqdq.calculate_avx512_loop; rw [loop]
  simp only []
  congr 1; funext r
  rcases r with ⟨⟨d', v0', v1', v2', v3'⟩⟩ | r <;> rfl

theorem step256 (a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3 : BitVec 128) (l : List U8)
    (h : 256 ≤ l.length) :
    crcRaw (S16 a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3) (bytes l) =
      crcRaw (S16 (blk (l.drop 48) ^^^ F k2048 a0) (blk (l.drop 32) ^^^ F k2048 b0)
          (blk (l.drop 16) ^^^ F k2048 c0) (blk l ^^^ F k2048 d0)
        (blk (l.drop 112) ^^^ F k2048 a1) (blk (l.drop 96) ^^^ F k2048 b1)
          (blk (l.drop 80) ^^^ F k2048 c1) (blk (l.drop 64) ^^^ F k2048 d1)
        (blk (l.drop 176) ^^^ F k2048 a2) (blk (l.drop 160) ^^^ F k2048 b2)
          (blk (l.drop 144) ^^^ F k2048 c2) (blk (l.drop 128) ^^^ F k2048 d2)
        (blk (l.drop 240) ^^^ F k2048 a3) (blk (l.drop 224) ^^^ F k2048 b3)
          (blk (l.drop 208) ^^^ F k2048 c3) (blk (l.drop 192) ^^^ F k2048 d3)) (bytes (l.drop 256)) := by
  unfold S16
  rw [stepFold k2048 [d0, c0, b0, a0, d1, c1, b1, a1, d2, c2, b2, a2, d3, c3, b3, a3]
    (fun a => foldBy256 a) l (by simp; omega)]
  simp only [blks, List.drop_drop, List.length_cons, List.length_nil, List.zipWith_cons_cons,
    List.zipWith_nil_left]

theorem avx512_loop_eq (n : Nat) (d : Slice U8)
    (a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3 : BitVec 128) (hn : d.length = n) :
    ∃ (d' : Slice U8) (a0' b0' c0' d0' a1' b1' c1' d1' a2' b2' c2' d2' a3' b3' c3' d3' : BitVec 128),
      specialized.pclmulqdq.calculate_avx512_loop d (a0 ++ b0 ++ c0 ++ d0) (a1 ++ b1 ++ c1 ++ d1)
        (a2 ++ b2 ++ c2 ++ d2) (a3 ++ b3 ++ c3 ++ d3) (k2048 ++ k2048 ++ k2048 ++ k2048) =
        ok (d', a0' ++ b0' ++ c0' ++ d0', a1' ++ b1' ++ c1' ++ d1', a2' ++ b2' ++ c2' ++ d2',
          a3' ++ b3' ++ c3' ++ d3') ∧ d'.length < 256 ∧
      crcRaw (S16 a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3) (bytes d.val) =
        crcRaw (S16 a0' b0' c0' d0' a1' b1' c1' d1' a2' b2' c2' d2' a3' b3' c3' d3') (bytes d'.val) := by
  induction n using Nat.strong_induction_on generalizing d a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 a3 b3 c3 d3 with
  | _ n ih =>
    by_cases h : 256 ≤ d.length
    · obtain ⟨d', x0, y0, z0, w0, x1, y1, z1, w1, x2, y2, z2, w2, x3, y3, z3, w3, e, hl, hc⟩ :=
        ih (drop256 d).length (by rw [drop256_length]; omega) (drop256 d)
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl
      refine ⟨d', x0, y0, z0, w0, x1, y1, z1, w1, x2, y2, z2, w2, x3, y3, z3, w3, ?_, hl, ?_⟩
      · rw [avx512_unfold, avx512_body_ge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h, bind_ok]; exact e
      · rw [← hc, step256 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h, drop256_val]
    · refine ⟨d, a0, b0, c0, d0, a1, b1, c1, d1, a2, b2, c2, d2, a3, b3, c3, d3, ?_, by omega, rfl⟩
      rw [avx512_unfold, avx512_body_lt _ _ _ _ _ _ (by omega), bind_ok]

theorem avx512_init (c : BitVec 32) (l : List U8) (h : 256 ≤ l.length) :
    crcRaw (S16 (blk (l.drop 48)) (blk (l.drop 32)) (blk (l.drop 16)) (blk l ^^^ c.setWidth 128)
      (blk (l.drop 112)) (blk (l.drop 96)) (blk (l.drop 80)) (blk (l.drop 64))
      (blk (l.drop 176)) (blk (l.drop 160)) (blk (l.drop 144)) (blk (l.drop 128))
      (blk (l.drop 240)) (blk (l.drop 224)) (blk (l.drop 208)) (blk (l.drop 192))) (bytes (l.drop 256)) =
    crcRaw c (bytes l) := by
  have hx : ∀ a b : BitVec 128, R16 (a ^^^ b) = R16 a ^^^ R16 b := R16_lin
  have key : S16 (blk (l.drop 48)) (blk (l.drop 32)) (blk (l.drop 16)) (blk l ^^^ c.setWidth 128)
      (blk (l.drop 112)) (blk (l.drop 96)) (blk (l.drop 80)) (blk (l.drop 64))
      (blk (l.drop 176)) (blk (l.drop 160)) (blk (l.drop 144)) (blk (l.drop 128))
      (blk (l.drop 240)) (blk (l.drop 224)) (blk (l.drop 208)) (blk (l.drop 192)) =
      Zn (16 * 16) c ^^^ SL (blks l 16) := by
    simp only [S16, blks, SL_cons, SL, List.drop_drop, List.length_cons, List.length_nil, hx, R16_zext,
      Zn_xor, Zn_add, Nat.reduceAdd, Nat.reduceMul]
    ac_rfl
  rw [stepN 16 c l (by omega), key]

theorem min512 : ∃ m : Usize, m.val = 2048 ∧ specialized.pclmulqdq.MIN_AVX512_BYTES = ok m := by
  unfold specialized.pclmulqdq.MIN_AVX512_BYTES
  simp only [HMul.hMul, UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt]
  have hc : UScalar.check_bounds UScalarTy.Usize (Mul.mul (2#usize).val (1024#usize).val) = true := by
    simp only [UScalar.check_bounds, decide_eq_true_eq]
    show (2#usize).val * (1024#usize).val < 2 ^ UScalarTy.Usize.numBits
    simp only [UScalarTy.Usize_numBits_eq]
    cases System.Platform.numBits_eq <;> simp_all
  rw [dif_pos hc]
  exact ⟨_, by simp, rfl⟩

theorem calculate_avx512_eq (crc : U32) (data : Slice U8) :
    specialized.pclmulqdq.calculate_avx512 crc data = ok ⟨update crc.bv (bytes data.val)⟩ := by
  unfold specialized.pclmulqdq.calculate_avx512
  obtain ⟨m, hm, hmin⟩ := min512
  rw [hmin, bind_ok]
  by_cases hs : data.length < 2048
  · rw [if_pos (by simp; scalar_tac), calculate_avx2_eq]
  rw [if_neg (by simp; scalar_tac)]
  have hdl : data.val.length = data.length := rfl
  have h1 : 64 ≤ (data.drop 64#usize).length := by rw [drop_length]; simp; omega
  have h2 : 64 ≤ ((data.drop 64#usize).drop 64#usize).length := by
    rw [drop_length, drop_length]; simp; omega
  have h3 : 64 ≤ (((data.drop 64#usize).drop 64#usize).drop 64#usize).length := by
    rw [drop_length, drop_length, drop_length]; simp; omega
  rw [get512_eq data (by omega)]; rw_bind; rw [uncurry_apply_pair]
  rw [get512_eq _ h1]; rw_bind; rw [uncurry_apply_pair]
  rw [get512_eq _ h2]; rw_bind; rw [uncurry_apply_pair]
  rw [get512_eq _ h3]; rw_bind; rw [uncurry_apply_pair]
  simp only [lift, bind_ok, cvt_eq, core.core_arch.x86.avx512f._mm512_castsi128_si512,
    core.core_arch.x86.avx512f._mm512_xor_si512, xor_zext512]
  rw [k2048_eq, bind_ok]
  have e64 : (64#usize).val = 64 := rfl
  simp only [drop_val, List.drop_drop, e64, Nat.reduceAdd]
  obtain ⟨d', x0, y0, z0, w0, x1, y1, z1, w1, x2, y2, z2, w2, x3, y3, z3, w3, hl, _, hc⟩ :=
    avx512_loop_eq _ (drop256 data)
      (blk (data.val.drop 48)) (blk (data.val.drop 32)) (blk (data.val.drop 16))
        (blk data.val ^^^ (~~~crc.bv).setWidth 128)
      (blk (data.val.drop 112)) (blk (data.val.drop 96)) (blk (data.val.drop 80)) (blk (data.val.drop 64))
      (blk (data.val.drop 176)) (blk (data.val.drop 160)) (blk (data.val.drop 144)) (blk (data.val.drop 128))
      (blk (data.val.drop 240)) (blk (data.val.drop 224)) (blk (data.val.drop 208)) (blk (data.val.drop 192))
      rfl
  rw [show (((data.drop 64#usize).drop 64#usize).drop 64#usize).drop 64#usize = drop256 data from rfl, hl,
    bind_ok]
  simp only [uncurry_apply_pair]
  obtain ⟨e1, e2, e3⟩ := extract512_eq x0 y0 z0 w0
  obtain ⟨f1, f2, f3⟩ := extract512_eq x1 y1 z1 w1
  obtain ⟨g1, g2, g3⟩ := extract512_eq x2 y2 z2 w2
  obtain ⟨i1, i2, i3⟩ := extract512_eq x3 y3 z3 w3
  rw [k3k4_eq, bind_ok,
    cast512_eq, bind_ok, e1, bind_ok, reduce128_eq, bind_ok, e2, bind_ok, reduce128_eq, bind_ok,
      e3, bind_ok, reduce128_eq, bind_ok,
    cast512_eq, bind_ok, reduce128_eq, bind_ok, f1, bind_ok, reduce128_eq, bind_ok, f2, bind_ok,
      reduce128_eq, bind_ok, f3, bind_ok, reduce128_eq, bind_ok,
    cast512_eq, bind_ok, reduce128_eq, bind_ok, g1, bind_ok, reduce128_eq, bind_ok, g2, bind_ok,
      reduce128_eq, bind_ok, g3, bind_ok, reduce128_eq, bind_ok,
    cast512_eq, bind_ok, reduce128_eq, bind_ok, i1, bind_ok, reduce128_eq, bind_ok, i2, bind_ok,
      reduce128_eq, bind_ok, i3, bind_ok, reduce128_eq, bind_ok]
  have hcol : R16 (x3 ^^^ F k3k4 (y3 ^^^ F k3k4 (z3 ^^^ F k3k4 (w3 ^^^ F k3k4
      (x2 ^^^ F k3k4 (y2 ^^^ F k3k4 (z2 ^^^ F k3k4 (w2 ^^^ F k3k4
      (x1 ^^^ F k3k4 (y1 ^^^ F k3k4 (z1 ^^^ F k3k4 (w1 ^^^ F k3k4
      (x0 ^^^ F k3k4 (y0 ^^^ F k3k4 (z0 ^^^ F k3k4 w0))))))))))))))) =
      S16 x0 y0 z0 w0 x1 y1 z1 w1 x2 y2 z2 w2 x3 y3 z3 w3 :=
    SL_collapse [z0, y0, x0, w1, z1, y1, x1, w2, z2, y2, x2, w3, z3, y3, x3] w0
  have hfin : crcRaw (S16 x0 y0 z0 w0 x1 y1 z1 w1 x2 y2 z2 w2 x3 y3 z3 w3) (bytes d'.val) =
      crcRaw (~~~crc.bv) (bytes data.val) := by
    rw [← hc, drop256_val, avx512_init _ _ (by omega)]
  split
  · rw [r128_eq, bind_ok, calculate_eq, hcol]
    have e0 : ∀ c : BitVec 32, crcRaw c (bytes (Array.to_slice (Std.Array.empty U8)).val) = c := fun _ => rfl
    have eb : ∀ v : BitVec 32, (⟨v⟩ : U32).bv = v := fun _ => rfl
    simp only [e0, update, eb, BitVec.not_not]
    rw [hfin]
  · rw [r128_eq, hcol, hfin]; rfl

end Crc32fastVerif
