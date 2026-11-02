import Crc32fast.SimdTail
import Crc32fast.Hasher

/-!
# The 128-bit PCLMULQDQ path (`calculate`) equals the spec
-/

open Aeneas Aeneas.Std Result crc32fast Crc32Spec x86

namespace Crc32fastVerif

/-- The register a 16-byte load produces. -/
def blk (l : List U8) : BitVec 128 := fromBytes 128 (bytes (l.take 16))

theorem bytesOf_blk (l : List U8) (h : 16 ≤ l.length) : bytesOf (blk l) 16 = bytes (l.take 16) := by
  have hl : (bytes (l.take 16)).length = 16 := by simp [bytes]; omega
  have := bytesOf_fromBytes 128 (bytes (l.take 16)) (by omega)
  rw [hl] at this
  exact this

theorem R16_blk (l : List U8) (h : 16 ≤ l.length) : R16 (blk l) = crcRaw 0#32 (bytes (l.take 16)) := by
  simp only [R16, Rn, bytesOf_blk l h]

theorem get_eq (a : Slice U8) (h : 16 ≤ a.length) :
    specialized.pclmulqdq.get a = ok (blk a.val, a.drop 16#usize) := by
  unfold specialized.pclmulqdq.get
  simp only [massert, specialized.pclmulqdq.load128]
  rw [if_pos (by simp; scalar_tac)]
  rw_bind
  rw [if_pos (by simpa using h)]
  rw_bind
  rw [index_from16 _ h]
  rw_bind
  rfl

theorem reduce128_eq (a b k : BitVec 128) :
    specialized.pclmulqdq.reduce128 a b k = ok (b ^^^ F k a) := by
  unfold specialized.pclmulqdq.reduce128
  simp only [core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128, core.core_arch.x86.sse2._mm_xor_si128,
    bind_tc_ok, bind_ok]
  have h0 : clmulSel (0#i32).bv a k = clmul (lo64 a) (lo64 k) := by
    simp only [clmulSel]; rfl
  have h17 : clmulSel (17#i32).bv a k = clmul (hi64 a) (hi64 k) := by
    simp only [clmulSel]; rfl
  rw [h0, h17, F, BitVec.xor_assoc]

theorem k3k4_eq : core.core_arch.x86.sse2._mm_set_epi64x specialized.pclmulqdq.K4
    specialized.pclmulqdq.K3 = ok k3k4 := by
  unfold specialized.pclmulqdq.K4 specialized.pclmulqdq.K3
  simp only [core.core_arch.x86.sse2._mm_set_epi64x]
  rfl

theorem k1k2_eq : core.core_arch.x86.sse2._mm_set_epi64x specialized.pclmulqdq.K2
    specialized.pclmulqdq.K1 = ok k1k2 := by
  unfold specialized.pclmulqdq.K2 specialized.pclmulqdq.K1
  simp only [core.core_arch.x86.sse2._mm_set_epi64x]
  rfl

/-! ## The 16-byte loop of `reduce_128_to_crc` -/

theorem crcRaw_blk (c : BitVec 32) (x : BitVec 128) (l : List U8) (h : 16 ≤ l.length) :
    crcRaw (R16 x) (bytes l) = crcRaw (R16 (blk l ^^^ F k3k4 x)) (bytes (l.drop 16)) := by
  have hsplit : bytes l = bytes (l.take 16) ++ bytes (l.drop 16) := by
    simp [bytes]
  have hlen : (bytes (l.take 16)).length = 16 := by simp [bytes]; omega
  rw [hsplit, crcRaw_append, crcRaw_split (R16 x) (bytes (l.take 16)), hlen, R16_lin, ← foldBy16, R16_blk l h,
    BitVec.xor_comm (Zn 16 (R16 x))]

theorem r128_body_ge (k : BitVec 128) (x : BitVec 128) (d : Slice U8) (h : 16 ≤ d.length) :
    specialized.pclmulqdq.reduce_128_to_crc_loop.body k x d =
      ok (.cont (blk d.val ^^^ F k x, d.drop 16#usize)) := by
  unfold specialized.pclmulqdq.reduce_128_to_crc_loop.body
  rw [if_pos (by simp; scalar_tac), get_eq d h]
  rw_bind
  rw [uncurry_apply_pair, reduce128_eq]
  rw_bind

theorem r128_body_lt (k : BitVec 128) (x : BitVec 128) (d : Slice U8) (h : d.length < 16) :
    specialized.pclmulqdq.reduce_128_to_crc_loop.body k x d = ok (.done (x, d)) := by
  unfold specialized.pclmulqdq.reduce_128_to_crc_loop.body
  rw [if_neg (by simp; scalar_tac)]

theorem r128_unfold (x : BitVec 128) (d : Slice U8) (k : BitVec 128) :
    specialized.pclmulqdq.reduce_128_to_crc_loop x d k = (do
      let r ← specialized.pclmulqdq.reduce_128_to_crc_loop.body k x d
      match r with
      | .cont (x', d') => specialized.pclmulqdq.reduce_128_to_crc_loop x' d' k
      | .done r => ok r) := by
  conv => lhs; unfold specialized.pclmulqdq.reduce_128_to_crc_loop; rw [loop]
  simp only []
  congr 1; funext r
  rcases r with ⟨⟨x', d'⟩⟩ | r <;> rfl

theorem r128_loop_eq (n : Nat) (x : BitVec 128) (d : Slice U8) (hn : d.length = n) :
    ∃ x' d', specialized.pclmulqdq.reduce_128_to_crc_loop x d k3k4 = ok (x', d') ∧
      d'.length < 16 ∧ crcRaw (R16 x) (bytes d.val) = crcRaw (R16 x') (bytes d'.val) := by
  induction n using Nat.strong_induction_on generalizing x d with
  | _ n ih =>
    by_cases h : 16 ≤ d.length
    · obtain ⟨x2, d2, h2, hl2, hc2⟩ := ih (d.drop 16#usize).length (by rw [len_drop16]; omega)
        (blk d.val ^^^ F k3k4 x) (d.drop 16#usize) rfl
      refine ⟨x2, d2, ?_, hl2, ?_⟩
      · rw [r128_unfold, r128_body_ge _ _ _ h, bind_ok]; exact h2
      · rw [← hc2, crcRaw_blk 0#32 x d.val h]
        simp [Slice.drop]
    · refine ⟨x, d, ?_, by omega, rfl⟩
      rw [r128_unfold, r128_body_lt _ _ _ (by omega), bind_ok]

/-! ## The partial last block -/

theorem I8.sub_ok (x y : I8) (h1 : IScalar.min .I8 ≤ x.val - y.val) (h2 : x.val - y.val ≤ IScalar.max .I8) :
    ∃ z : I8, z.val = x.val - y.val ∧ (x - y : Result I8) = ok z := by
  simp only [HSub.hSub, IScalar.sub, IScalar.tryMk, IScalar.tryMkOpt]
  have hc : IScalar.check_bounds IScalarTy.I8 (Sub.sub x.val y.val) = true := by
    simp only [IScalar.check_bounds, decide_eq_true_eq]
    show -2 ^ (IScalarTy.I8.numBits - 1) ≤ x.val - y.val ∧ x.val - y.val < 2 ^ (IScalarTy.I8.numBits - 1)
    simp only [IScalar.min, IScalar.max, IScalarTy.numBits] at h1 h2 ⊢
    constructor <;> omega

  rw [dif_pos hc]
  exact ⟨_, by simp, rfl⟩

theorem tail_ctl (d : Slice U8) (h : d.length < 16) :
    ∃ i1 : I8, (UScalar.hcast IScalarTy.I8 d.len - 16#i8 : Result I8) = ok i1 ∧
      i1.bv = BitVec.ofNat 8 (d.length + 240) := by
  have hv : (UScalar.hcast IScalarTy.I8 d.len).val = d.length := by
    rw [UScalar.hcast_val_eq]
    have : (d.len.val : Int) = d.length := by simp
    rw [this]
    simp only [IScalarTy.numBits, Int.bmod_def]
    push_cast
    split <;> omega
  obtain ⟨z, hz, hsub⟩ := I8.sub_ok (UScalar.hcast IScalarTy.I8 d.len) 16#i8
    (by rw [hv]; scalar_tac) (by rw [hv]; scalar_tac)
  refine ⟨z, hsub, ?_⟩
  apply BitVec.eq_of_toInt_eq
  have hzv : z.bv.toInt = d.length - 16 := by
    have e : z.bv.toInt = z.val := rfl
    rw [e, hz, hv]; simp
  rw [hzv, BitVec.toInt_ofNat', Int.bmod_def]
  push_cast
  split <;> omega

theorem fromBytes_zeros (w k : Nat) : fromBytes w (List.replicate k 0#8) = 0#w := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, fromBytes_cons, ih]

theorem fromBytes_append_zeros (w : Nat) (l : List (BitVec 8)) (k : Nat) :
    fromBytes w (l ++ List.replicate k 0#8) = fromBytes w l := by
  induction l with
  | nil => rw [List.nil_append, fromBytes_zeros]; rfl
  | cons b l ih => simp [fromBytes_cons, ih]

theorem tail_block_eq (d : Slice U8) (h0 : 0 < d.length) (h : d.length < 16) (x : BitVec 128) :
    (do
      let seq ←
        core.core_arch.x86.sse2._mm_setr_epi8 0#i8 1#i8 2#i8 3#i8 4#i8 5#i8
          6#i8 7#i8 8#i8 9#i8 10#i8 11#i8 12#i8 13#i8 14#i8 15#i8
      let i ← lift (UScalar.hcast .I8 (Slice.len d))
      let i1 ← i - 16#i8
      let mi ← core.core_arch.x86.sse2._mm_set1_epi8 i1
      let shl ← core.core_arch.x86.sse2._mm_add_epi8 seq mi
      let mi1 ← core.core_arch.x86.sse2._mm_set1_epi8 (-128)#i8
      let shr ← core.core_arch.x86.sse2._mm_xor_si128 shl mi1
      let overflow ← core.core_arch.x86.ssse3._mm_shuffle_epi8 x shl
      let x3 ← core.core_arch.x86.ssse3._mm_shuffle_epi8 x shr
      let part := Array.repeat 16#usize 0#u8
      let (s, index_mut_back) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) part
          { «end» := Slice.len d }
      let s1 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s d
      let part1 := index_mut_back s1
      let s2 ← lift (Array.to_slice part1)
      let part2 ← specialized.pclmulqdq.load128 s2
      let mi2 ← core.core_arch.x86.ssse3._mm_shuffle_epi8 part2 shl
      let x4 ← core.core_arch.x86.sse2._mm_xor_si128 x3 mi2
      specialized.pclmulqdq.reduce128 overflow x4 k3k4) =
    ok (tailStep d.length x (fromBytes 128 (bytes d.val))) := by
  obtain ⟨i1, hsub, hbv⟩ := tail_ctl d h
  have hdl : d.val.length = d.length := rfl
  have hlen : d.len.val = d.length := by simp
  simp only [core.core_arch.x86.sse2._mm_setr_epi8, core.core_arch.x86.sse2._mm_set1_epi8, lift, bind_ok]
  rw [hsub, bind_ok]
  simp only [core.core_arch.x86.sse2._mm_add_epi8, core.core_arch.x86.sse2._mm_xor_si128,
    core.core_arch.x86.ssse3._mm_shuffle_epi8, bind_ok]
  generalize hA : Array.repeat 16#usize 0#u8 = A
  have hAv : A.val = List.replicate 16 0#u8 := by rw [← hA, Array.repeat_val]; rfl
  have hAl : A.to_slice.length = 16 := by simp [Slice.length, Array.val_to_slice, hAv]
  simp only [core.array.Array.index_mut, core.ops.index.IndexMutSlice, core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut]
  rw [if_pos (by rw [hAl, hlen]; omega)]
  simp only [bind_ok, bind_tc_ok, uncurry_apply_pair, core.slice.Slice.copy_from_slice]
  rw [if_pos (by
    apply UScalar.eq_of_val_eq
    simp only [Slice.len_val, Slice.length, Slice.from_val, Array.val_to_slice, hAv, List.slice_length]
    simp; omega)]
  simp only [bind_ok, specialized.pclmulqdq.load128]
  generalize hP : A.from_slice (Slice.from (A.to_slice.val.setSlice! 0 d.val) _) = P
  have hPv : P.to_slice.val = d.val ++ List.replicate (16 - d.length) 0#u8 := by
    rw [← hP, Array.val_to_slice, Array.from_slice_val _ _ (by simp [Slice.from_val, hAv])]
    simp only [Slice.from_val, Array.val_to_slice, hAv, List.setSlice!]
    have hm : min d.val.length ((List.replicate 16 0#u8).length - 0) = d.length := by
      simp only [List.length_replicate, hdl]; omega
    simp only [hm, List.take_zero, List.nil_append, Nat.zero_add, List.drop_replicate,
      List.take_of_length_le (show d.val.length ≤ d.length by omega)]
  have hPl : P.to_slice.length = 16 := by
    simp only [Slice.length, hPv, List.length_append, List.length_replicate]; omega
  rw [if_pos (by rw [hPl]), bind_ok, reduce128_eq]
  have hpart : fromBytes 128 (List.map (fun x => x.bv) (List.take 16 P.to_slice.val)) =
      fromBytes 128 (bytes d.val) := by
    rw [hPv, List.take_of_length_le (by simp; omega), List.map_append, List.map_replicate]
    exact fromBytes_append_zeros 128 _ _
  rw [hpart, hbv]
  have hseq : fromBytes 128 [I8.bv 0#i8, I8.bv 1#i8, I8.bv 2#i8, I8.bv 3#i8, I8.bv 4#i8, I8.bv 5#i8,
      I8.bv 6#i8, I8.bv 7#i8, I8.bv 8#i8, I8.bv 9#i8, I8.bv 10#i8, I8.bv 11#i8, I8.bv 12#i8,
      I8.bv 13#i8, I8.bv 14#i8, I8.bv 15#i8] = seqBytes := by rfl
  have h80 : I8.bv (-128)#i8 = 0x80#8 := by rfl
  rw [hseq, h80]
  rfl

theorem barrett_code (x2 : BitVec 128) :
    (do
    let mi ← core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 16#i32 x2 k3k4
    let mi1 ← core.core_arch.x86.sse2._mm_srli_si128 8#i32 x2
    let x3 ← core.core_arch.x86.sse2._mm_xor_si128 mi mi1
    let i ← lift (~~~0#i32)
    let mi2 ← core.core_arch.x86.sse2._mm_set_epi32 0#i32 0#i32 0#i32 i
    let mi3 ← core.core_arch.x86.sse2._mm_and_si128 x3 mi2
    let mi4 ← core.core_arch.x86.sse2._mm_set_epi64x 0#i64 specialized.pclmulqdq.K5
    let mi5 ← core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 0#i32 mi3 mi4
    let mi6 ← core.core_arch.x86.sse2._mm_srli_si128 4#i32 x3
    let x4 ← core.core_arch.x86.sse2._mm_xor_si128 mi5 mi6
    let pu ← core.core_arch.x86.sse2._mm_set_epi64x specialized.pclmulqdq.U_PRIME specialized.pclmulqdq.P_X
    let i1 ← lift (~~~0#i32)
    let mi7 ← core.core_arch.x86.sse2._mm_set_epi32 0#i32 0#i32 0#i32 i1
    let mi8 ← core.core_arch.x86.sse2._mm_and_si128 x4 mi7
    let t1 ← core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 16#i32 mi8 pu
    let i2 ← lift (~~~0#i32)
    let mi9 ← core.core_arch.x86.sse2._mm_set_epi32 0#i32 0#i32 0#i32 i2
    let mi10 ← core.core_arch.x86.sse2._mm_and_si128 t1 mi9
    let t2 ← core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 0#i32 mi10 pu
    let mi11 ← core.core_arch.x86.sse2._mm_xor_si128 x4 t2
    let i3 ← core.core_arch.x86.sse41._mm_extract_epi32 1#i32 mi11
    let i4 ← lift (IScalar.hcast UScalarTy.U32 i3)
    ok (~~~i4)) = ok ⟨~~~ barrett x2⟩ := by
  unfold specialized.pclmulqdq.K5 specialized.pclmulqdq.U_PRIME specialized.pclmulqdq.P_X
  simp only [core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128, core.core_arch.x86.sse2._mm_srli_si128,
    core.core_arch.x86.sse2._mm_xor_si128, core.core_arch.x86.sse2._mm_set_epi32,
    core.core_arch.x86.sse2._mm_and_si128, core.core_arch.x86.sse2._mm_set_epi64x,
    core.core_arch.x86.sse41._mm_extract_epi32, lift, bind_ok]
  have hm : (0#i32).bv ++ (0#i32).bv ++ (0#i32).bv ++ (~~~0#i32).bv = mask32 := by decide
  have hk5 : (0#i64).bv ++ (5969371428#i64).bv = k5 := by decide
  have hpu : (8439010881#i64).bv ++ (7976584769#i64).bv = pu := by decide
  have i0 : I32.bv 0#i32 = 0#32 := rfl
  have i1 : I32.bv 1#i32 = 1#32 := rfl
  have i4 : I32.bv 4#i32 = 4#32 := rfl
  have i8 : I32.bv 8#i32 = 8#32 := rfl
  have i16 : I32.bv 16#i32 = 16#32 := rfl
  rw [hm, hk5, hpu, i0, i1, i4, i8, i16]
  congr 1
  simp only [IScalar.hcast]
  have hn : UScalarTy.U32.numBits = 32 := rfl
  simp only [barrett]
  generalize extract32 _ _ = v
  have e : BitVec.signExtend UScalarTy.U32.numBits v = v := BitVec.signExtend_eq v
  rw [e]
  rfl

/-- `reduce_128_to_crc x data` finishes the CRC of "block `x`, then `data`". -/
theorem r128_eq (x : BitVec 128) (data : Slice U8) :
    specialized.pclmulqdq.reduce_128_to_crc x data = ok ⟨~~~(crcRaw (R16 x) (bytes data.val))⟩ := by
  obtain ⟨x1, d1, hl, hl1, hc⟩ := r128_loop_eq _ x data rfl
  unfold specialized.pclmulqdq.reduce_128_to_crc
  rw [k3k4_eq, bind_ok, hl, bind_ok, uncurry_apply_pair]
  simp only []
  rw [hc]
  split
  · rename_i hpos
    have h0 : 0 < d1.length := by simp at hpos; scalar_tac
    rw [tail_block_eq d1 h0 hl1 x1, bind_ok, barrett_code, barrett_eq, tailStep_eq _ hl1 h0]
    have hb : Rn (fromBytes 128 (bytes d1.val)) d1.length = crcRaw 0#32 (bytes d1.val) := by
      have hl' : (bytes d1.val).length = d1.length := by simp [bytes]
      have := bytesOf_fromBytes 128 (bytes d1.val) (by omega)
      rw [hl'] at this
      simp only [Rn, this]
    have hl' : (bytes d1.val).length = d1.length := by simp [bytes]
    rw [hb, crcRaw_split (R16 x1) (bytes d1.val), hl']
  · rename_i hz
    have h0 : d1.length = 0 := by simp at hz; scalar_tac
    have hnil : d1.val = [] := List.eq_nil_of_length_eq_zero h0
    rw [bind_ok, barrett_code, barrett_eq, hnil, show bytes ([] : List U8) = [] from rfl, crcRaw_nil]

end Crc32fastVerif
