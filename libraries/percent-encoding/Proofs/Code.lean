module
public import Proofs.SpecLemmas
@[expose] public section

open Aeneas Aeneas.Std Result WP
open percent_encoding percent_encoding.Spec

namespace percent_encoding.Proofs

theorem and_two_pow_ne_zero (x k : Nat) : x &&& 2 ^ k ≠ 0 ↔ x.testBit k = true := by
  constructor
  · intro h
    by_contra hc
    apply h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : k = i
    · subst hi; simp_all
    · simp [hi]
  · intro h hz
    have := congrArg (fun n => n.testBit k) hz
    simp [h] at this

@[step]
theorem size_of_u32_spec : core.mem.size_of Std.U32 ⦃ r => r.val = 4 ⦄ := by
  unfold core.mem.size_of; simp

@[step]
theorem BITS_PER_CHUNK_spec : ascii_set.BITS_PER_CHUNK ⦃ r => r.val = 32 ⦄ := by
  unfold ascii_set.BITS_PER_CHUNK
  step*

@[step]
theorem contains_spec (s : ascii_set.AsciiSet) (b : Std.U8) (hb : b.val < 128) :
    ascii_set.AsciiSet.contains s b ⦃ r => r = inSet s b.val ⦄ := by
  unfold ascii_set.AsciiSet.contains
  step*
  have hi : i.val = b.val := by simp [i_post]
  have hi3 : i3.val = b.val := by simp [i3_post]
  have hk : i4.val < 32 := by simp [i4_post, i1_post]; omega
  have hm : mask.val = 2 ^ (b.val % 32) := by
    rw [mask_post, i4_post, hi3, i1_post, Nat.one_shiftLeft]
    apply Nat.mod_eq_of_lt
    have h32 : b.val % 32 < 32 := by omega
    calc 2 ^ (b.val % 32) < 2 ^ 32 := Nat.pow_lt_pow_right (by norm_num) h32
      _ = U32.size := by simp [U32.size, U32.numBits, UScalarTy.numBits]
  have hc : chunk = s.mask.val[b.val / 32]! := by
    have hlen : (s.mask.val).length = 4 := by simp
    have hlt : b.val / 32 < (s.mask.val).length := by rw [hlen]; omega
    simp only [chunk_post, i2_post, hi, i1_post]
    rw [getElem!_pos (s.mask.val) (b.val / 32) hlt]
  have h5 : i5.val = chunk.val &&& 2 ^ (b.val % 32) := by
    rw [i5_post, ← hm]; simp
  have key : (i5 != 0#u32) = true ↔ i5.val ≠ 0 := by
    simp [bne_iff_ne, ne_eq, UScalar.eq_equiv]
  rw [Bool.eq_iff_iff, key, h5, and_two_pow_ne_zero, hc]
  simp [inSet, hb]

@[step]
theorem is_ascii_spec (b : Std.U8) : core.num.U8.is_ascii b ⦃ r => r = decide (b.val < 128) ⦄ := by
  unfold core.num.U8.is_ascii; simp

@[step]
theorem should_percent_encode_spec (s : ascii_set.AsciiSet) (b : Std.U8) :
    ascii_set.AsciiSet.should_percent_encode s b ⦃ r => r = shouldEncode s b.val ⦄ := by
  unfold ascii_set.AsciiSet.should_percent_encode
  step*
  all_goals simp_all [shouldEncode, inSet]

/-- ASCII bytes are valid UTF-8 (each is the encoding of one `char`). -/
theorem utf8Valid_of_ascii (l : List Std.U8) (h : ∀ b ∈ l, b.val < 128) : Utf8Valid l := by
  refine ⟨l.map (fun b => Char.ofNat b.val), ?_⟩
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simp only [u8sToBA, List.utf8Encode, List.toList_data_toByteArray, List.toList_toArray]
  induction l with
  | nil => simp
  | cons b l ih =>
    have hb := h b List.mem_cons_self
    simp only [List.map_cons, List.flatMap_cons]
    rw [← ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have hc : (Char.ofNat b.val).val.toNat = b.val := by
      simp only [Char.ofNat, Char.ofNatAux]
      rw [dif_pos (Or.inl (by omega))]
      simp
    simp only [String.utf8EncodeChar, hc]
    simp [show b.val ≤ 127 by omega]

/-- `str::from_utf8_unchecked` on ASCII bytes: no undefined behaviour, same bytes. -/
@[step]
theorem from_utf8_unchecked_spec (s : Slice Std.U8) (h : ∀ b ∈ s.val, b.val < 128) :
    core.str.converts.from_utf8_unchecked s ⦃ r => (show Slice Std.U8 from r) = s ⦄ := by
  unfold core.str.converts.from_utf8_unchecked
  rw [if_pos (utf8Valid_of_ascii _ h)]
  exact (WP.spec_ok _).2 rfl

set_option maxRecDepth 100000 in
/-- The 768-byte lookup table holds `%XY` for every byte, checked by the kernel. -/
theorem enc_table_slices : ∀ n < 256,
    (percent_encode_byte.ENC_TABLE.to_slice.val.slice (n * 3) (n * 3 + 3)).map (·.val)
      = encByte n := by
  unfold percent_encode_byte.ENC_TABLE
  decide +kernel

theorem encByte_ascii (b : Nat) (hb : b < 256) : ∀ c ∈ encByte b, c < 128 := by
  have h1 : b / 16 < 16 := by omega
  have h2 : b % 16 < 16 := by omega
  intro c hc
  simp only [encByte, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · decide
  · exact hexDigit_lt _ h1
  · exact hexDigit_lt _ h2

@[step]
theorem percent_encode_byte_spec (b : Std.U8) :
    percent_encode_byte b ⦃ r => strBytes r = encByte b.val ⦄ := by
  unfold percent_encode_byte
  have hb := b.hBounds
  simp only [lift]
  have hb' : b.val < 256 := by simpa [UScalarTy.numBits] using hb
  have := enc_table_slices b.val hb'
  step*
  · have hi : index.val = b.val * 3 := by
      rw [index_post, core.convert.num.FromUsizeU8.from_val_eq]
    intro x hx
    simp only [s_post, i1_post, hi] at hx
    exact encByte_ascii _ hb' _ (this ▸ List.mem_map_of_mem hx)
  · have hi : index.val = b.val * 3 := by
      rw [index_post, core.convert.num.FromUsizeU8.from_val_eq]
    simp only [strBytes, bytes, r_post, s_post, i1_post, hi] at *
    exact this

@[step]
theorem split_first_spec (s : Slice Std.U8) :
    core.slice.Slice.split_first s ⦃ r =>
      match r with
      | none => s.val = []
      | some (x, t) => s.val = x :: t.val ⦄ := by
  unfold core.slice.Slice.split_first
  split
  · simp_all
  · rename_i x xs h
    simp [h]

/-- The index search loop stops at the first byte that must be encoded,
    or at the end of the slice. -/
@[step]
theorem encode_next_loop_spec (s : ascii_set.AsciiSet) (rem : Slice Std.U8) :
    next_chunk_loop s rem 0#usize
      ⦃ j => j.val ≤ rem.length ∧
        (∀ k < j.val, shouldEncode s (rem.val[k]!).val = false) ∧
        (j.val < rem.length → shouldEncode s (rem.val[j.val]!).val = true) ⦄ := by
  unfold next_chunk_loop
  apply loop.spec_decr_nat (fun (x : Std.Usize) => rem.length - x.val)
    (fun x => x.val ≤ rem.length ∧ ∀ k < x.val, shouldEncode s (rem.val[k]!).val = false)
  · intro x ⟨hx, hall⟩
    unfold next_chunk_loop.body
    step*
    · have hlt : x.val < rem.length := by scalar_tac
      refine ⟨hx, hall, fun _ => ?_⟩
      rw [getElem!_pos rem.val x.val hlt]; simp_all
    · have hlt : x.val < rem.length := by scalar_tac
      refine ⟨by omega, fun k hk => ?_, by omega⟩
      by_cases hkx : k < x.val
      · exact hall k hkx
      · have : k = x.val := by omega
        subst this; rw [getElem!_pos rem.val x.val hlt]; simp_all
  · simp

theorem lt128_of_not_should (s : ascii_set.AsciiSet) (c : Nat)
    (h : shouldEncode s c = false) : c < 128 := by
  simp only [shouldEncode, Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at h
  exact h.1

theorem take_not_should (s : ascii_set.AsciiSet) (first : Std.U8) (rem : List Std.U8) (i : Nat)
    (hfirst : shouldEncode s first.val = false)
    (hrem : ∀ k < i, shouldEncode s (rem[k]!).val = false) :
    ∀ c ∈ ((first :: rem).take (1 + i)).map (·.val), shouldEncode s c = false := by
  intro c hc
  rw [List.mem_map] at hc
  obtain ⟨x, hx, rfl⟩ := hc
  rw [Nat.add_comm, List.take_succ_cons, List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact hfirst
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have hk' : k < i := by simp at hk; omega
    have := hrem k hk'
    rw [List.getElem_take]
    rwa [getElem!_pos rem k (by simp at hk; omega)] at this

/-- One step of the encoder: returns a chunk whose bytes, followed by the
    encoding of what is left, equal the encoding of the input. Every chunk is
    ASCII, which discharges the `from_utf8_unchecked` safety condition. -/
@[step]
theorem next_chunk_spec (bs : Slice Std.U8) (set : ascii_set.AsciiSet) :
    next_chunk bs set ⦃ r =>
      match r with
      | none => bs.val = []
      | some (chunk, rest) =>
        rest.length < bs.length ∧
        strBytes chunk ++ encode set (bytes rest) = encode set (bytes bs) ∧
        (∀ c ∈ strBytes chunk, c < 128) ⦄ := by
  unfold next_chunk
  step*
  rename_i hp
  obtain ⟨first, rem⟩ := p
  simp only [hp] at o_post
  step*
  · have hfirst : first.val < 256 := by have := first.hBounds; simpa [UScalarTy.numBits] using this
    have hb : bytes bs = first.val :: bytes rem := by simp [bytes, o_post]
    refine ⟨?_, ?_, ?_⟩
    · simp [Slice.length, o_post]
    · rw [hb, s_post]; simp_all [encode]
    · rw [s_post]; exact encByte_ascii _ hfirst
  · have hnot := take_not_should set first rem.val i.val (by simp_all) i_post1
    intro c hc
    have hc' : c.val ∈ ((first :: rem.val).take (1 + i.val)).map (·.val) := by
      rw [unchanged_slice_post2, i1_post, o_post] at hc; exact List.mem_map_of_mem hc
    exact lt128_of_not_should _ _ (hnot _ hc')
  · have hlen : bs.length = rem.length + 1 := by simp [Slice.length, o_post]
    have hnot := take_not_should set first rem.val i.val (by simp_all) i_post1
    have hchunk : strBytes s = (bs.val.take i1.val).map (·.val) := by
      simp [strBytes, bytes, s_post, unchanged_slice_post2]
    have hsplit : bytes bs = (bs.val.take i1.val).map (·.val) ++ bytes remaining1 := by
      simp [bytes, unchanged_slice_post3]
    rw [o_post, i1_post] at hchunk hsplit
    refine ⟨by omega, ?_, ?_⟩
    · rw [hsplit, encode_append, encode_of_not_should _ _ hnot, hchunk]
    · intro c hc
      rw [hchunk] at hc
      exact lt128_of_not_should _ _ (hnot c hc)

/-- One step of the encoder: returns a chunk whose bytes, followed by the
    encoding of what is left, equal the encoding of the input. Every chunk is
    ASCII, which discharges the `from_utf8_unchecked` safety condition. -/
@[step]
theorem encode_next_spec (it : PercentEncode) :
    PercentEncode.Insts.CoreIterTraitsIteratorIteratorSharedAStr.next it ⦃ r it' =>
      it'.ascii_set = it.ascii_set ∧
      match r with
      | none => it.bytes.val = [] ∧ it' = it
      | some chunk =>
        it'.bytes.length < it.bytes.length ∧
        strBytes chunk ++ encode it.ascii_set (bytes it'.bytes) = encode it.ascii_set (bytes it.bytes) ∧
        (∀ c ∈ strBytes chunk, c < 128) ⦄ := by
  unfold PercentEncode.Insts.CoreIterTraitsIteratorIteratorSharedAStr.next
  apply WP.spec_bind (next_chunk_spec it.bytes it.ascii_set)
  intro r hr
  rcases r with _ | ⟨chunk, rest⟩
  · apply (WP.spec_ok _).2; simp_all
  · apply (WP.spec_ok _).2; simp_all

/-- Runs the Rust iterator `PercentEncode` to the end and concatenates the
    chunks, like `iter.collect::<String>()`. `fuel` bounds the number of steps
    (the theorem below shows `input length + 1` is always enough). -/
noncomputable def encodeCollect : Nat → PercentEncode → Result (List Nat)
  | 0, _ => fail .panic
  | fuel + 1, it => do
    let (r, it') ← PercentEncode.Insts.CoreIterTraitsIteratorIteratorSharedAStr.next it
    match r with
    | none => ok []
    | some chunk => do
      let rest ← encodeCollect fuel it'
      ok (strBytes chunk ++ rest)

theorem encodeCollect_spec (fuel : Nat) (it : PercentEncode) (h : it.bytes.length < fuel) :
    encodeCollect fuel it ⦃ out => out = encode it.ascii_set (bytes it.bytes) ⦄ := by
  induction fuel generalizing it with
  | zero => omega
  | succ n ih =>
    unfold encodeCollect
    step*
    subst_vars
    simp_all [bytes, encode]

/-! ### Decoder -/

@[step]
theorem iter_clone_spec (it : core.slice.iter.Iter Std.U8) :
    core.slice.iter.Iter.Insts.CoreCloneClone.clone it ⦃ r => r = it ⦄ := by
  unfold core.slice.iter.Iter.Insts.CoreCloneClone.clone; simp

@[step]
theorem try_branch_spec {T : Type} (o : Option T) :
    core.option.Option.Insts.CoreOpsTry_traitTry.branch o ⦃ r =>
      match o with
      | some x => r = .Continue x
      | none => r = .Break none ⦄ := by
  unfold core.option.Option.Insts.CoreOpsTry_traitTry.branch
  cases o <;> simp

@[step]
theorem from_residual_spec (T : Type) (x : Option Never) :
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual T x
      ⦃ r => r = none ⦄ := by
  unfold core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual; simp

@[step]
theorem char_from_u8_spec (b : Std.U8) :
    Char.Insts.CoreConvertFromU8.from b ⦃ c => c.toNat = b.val ⦄ := by
  have hb : b.val < 256 := by have := b.hBounds; simpa [UScalarTy.numBits] using this
  have : ∀ n < 256, (Char.ofNat n).toNat = n := by decide +kernel
  unfold Char.Insts.CoreConvertFromU8.from
  simp [this _ hb]

/-- `char::to_digit(16)` agrees with `hexVal` on every char coming from a byte. -/
@[step]
theorem to_digit_16_spec (c : Char) (hc : c.toNat < 256) :
    core.char.methods.Char.to_digit c 16#u32 ⦃ r =>
      hexVal c.toNat = r.map (·.val) ∧ ∀ d, r = some d → d.val < 16 ⦄ := by
  unfold core.char.methods.Char.to_digit
  unfold hexVal
  split_ifs <;> simp_all <;> (try split_ifs) <;> (try simp_all) <;> scalar_tac

/-- Remaining bytes of a slice iterator. -/
def remBytes (it : core.slice.iter.Iter Std.U8) : List Nat := (it.slice.val.drop it.i).map (·.val)

@[step]
theorem slice_iter_next_spec (it : core.slice.iter.Iter Std.U8) :
    core.slice.iter.IteratorSliceIter.next it ⦃ o it' =>
      it'.slice = it.slice ∧
      match remBytes it with
      | [] => o = none ∧ it' = it
      | x :: rest => o.map (·.val) = some x ∧ remBytes it' = rest ∧ it'.i = it.i + 1 ⦄ := by
  unfold core.slice.iter.IteratorSliceIter.next
  split
  · rename_i h
    have hd : it.slice.val.drop it.i = it.slice.val[it.i] :: it.slice.val.drop (it.i + 1) :=
      List.drop_eq_getElem_cons (by simpa using h)
    simp [remBytes, hd]
    rfl
  · rename_i h
    have hd : it.slice.val.drop it.i = [] := List.drop_eq_nil_of_le (by simp at h; omega)
    simp [remBytes, hd]

@[step]
theorem after_percent_sign_spec (it : core.slice.iter.Iter Std.U8) :
    after_percent_sign it ⦃ r it' =>
      r.map (·.val) = afterPct (remBytes it) ∧ it'.slice = it.slice ∧
      it'.i = (if r.isSome then it.i + 2 else it.i) ⦄ := by
  unfold after_percent_sign
  step*
  all_goals (subst_vars; (try cases o) <;> (try cases o1) <;> (try cases o2) <;> (try cases o3) <;> simp_all)
  all_goals (try scalar_tac)
  all_goals (split at o_post1 <;> (try split at o2_post1) <;> simp_all [afterPct])
  all_goals (obtain ⟨-, h2, -⟩ := o_post1; subst h2)
  all_goals (try simp_all)
  all_goals (try (rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega))
  all_goals (split <;> simp_all)

theorem remBytes_drop (it it' : core.slice.iter.Iter Std.U8) (n : Nat)
    (hs : it'.slice = it.slice) (hi : it'.i = it.i + n) :
    remBytes it' = (remBytes it).drop n := by
  simp [remBytes, hs, hi, List.drop_drop, Nat.add_comm]

/-- One step of the decoder agrees with the reference decoder. -/
@[step]
theorem decode_next_spec (d : PercentDecode) :
    PercentDecode.Insts.CoreIterTraitsIteratorIteratorU8.next d ⦃ r d' =>
      d'.bytes.slice = d.bytes.slice ∧
      match r with
      | none => remBytes d.bytes = []
      | some b =>
        (remBytes d'.bytes).length < (remBytes d.bytes).length ∧
        b.val :: decode (remBytes d'.bytes) = decode (remBytes d.bytes) ⦄ := by
  unfold PercentDecode.Insts.CoreIterTraitsIteratorIteratorU8.next
  step*
  · split at o_post1 <;> simp_all
  · -- `%`: try to parse two hex digits
    subst_vars
    split at o_post1
    · simp_all
    · rename_i x rest hrem
      obtain ⟨hx, hrest, -⟩ := o_post1
      simp at hx
      rw [hrem]; subst hx; rw [decode_pct, ← hrest]
      cases o1 with
      | none =>
        simp at o1_post o1_post2
        have hi1 : i1 = i := by
          cases i1; cases i; simp_all
        subst hi1
        rw [hrest] at o1_post
        simp [← o1_post, core.option.Option.unwrap_or, o_post, hrest]
      | some v =>
        simp at o1_post o1_post2
        have := remBytes_drop i i1 2 o1_post1 o1_post2
        refine ⟨by rw [o1_post1, o_post], ?_, ?_⟩
        · rw [this]; simp
        · rw [this, hrest] at *
          rw [← o1_post]
          simp [core.option.Option.unwrap_or]
  · rename_i hne
    subst_vars
    split at o_post1
    · simp_all
    · rename_i x rest hrem
      obtain ⟨hx, hrest, -⟩ := o_post1
      simp at hx
      have hne' : byte.val ≠ 37 := by
        intro h; apply hne; scalar_tac
      refine ⟨o_post, by rw [hrem, hrest]; simp, ?_⟩
      rw [hrem, hrest]; subst hx; rw [decode_cons_of_ne _ _ hne']

/-- Runs the Rust iterator `PercentDecode` to the end, like
    `iter.collect::<Vec<u8>>()`, with a step bound `fuel`. -/
noncomputable def decodeCollect : Nat → PercentDecode → Result (List Nat)
  | 0, _ => fail .panic
  | fuel + 1, d => do
    let (r, d') ← PercentDecode.Insts.CoreIterTraitsIteratorIteratorU8.next d
    match r with
    | none => ok []
    | some b => do
      let rest ← decodeCollect fuel d'
      ok (b.val :: rest)

theorem decodeCollect_spec (fuel : Nat) (d : PercentDecode) (h : (remBytes d.bytes).length < fuel) :
    decodeCollect fuel d ⦃ out => out = decode (remBytes d.bytes) ⦄ := by
  induction fuel generalizing d with
  | zero => omega
  | succ n ih =>
    unfold decodeCollect
    step*
    simp_all [decode]

/-! ### Main theorems about the Rust code -/

/-- **Encoder correctness.** Collecting `percent_encode(input, set)` never
    panics and yields exactly the reference encoding. -/
theorem percent_encode_correct (input : Slice Std.U8) (set : ascii_set.AsciiSet) :
    (do let it ← percent_encode input set
        encodeCollect (input.length + 1) it)
      ⦃ out => out = encode set (bytes input) ⦄ := by
  unfold percent_encode
  simp only [bind_ok]
  exact encodeCollect_spec _ _ (by simp)

/-- **Decoder correctness.** Collecting `percent_decode(input)` never panics
    (in particular `h * 0x10 + l` never overflows) and yields exactly the
    reference decoding. -/
theorem percent_decode_correct (input : Slice Std.U8) :
    (do let d ← percent_decode input
        decodeCollect (input.length + 1) d)
      ⦃ out => out = decode (bytes input) ⦄ := by
  unfold percent_decode core.slice.Slice.iter
  simp only [bind_ok]
  have := decodeCollect_spec (input.length + 1) ⟨⟨input, 0⟩⟩ (by simp [remBytes])
  simpa [remBytes, bytes] using this

/-- **Output alphabet of the Rust encoder.** Every output byte is ASCII, and
    the only output bytes that are in the set are `%` and `0-9A-F`. -/
theorem percent_encode_output_allowed (input : Slice Std.U8) (set : ascii_set.AsciiSet) :
    (do let it ← percent_encode input set
        encodeCollect (input.length + 1) it)
      ⦃ out => ∀ c ∈ out, c < 128 ∧ (shouldEncode set c = true → isEscapeChar c = true) ⦄ := by
  apply WP.spec_mono (percent_encode_correct input set)
  intro out hout
  rw [hout]
  apply encode_output_allowed
  intro b hb
  simp only [bytes, List.mem_map] at hb
  obtain ⟨x, -, rfl⟩ := hb
  have := x.hBounds; simpa [UScalarTy.numBits] using this

/-- **Round trip on the Rust code.** If the set contains `%` (as
    `NON_ALPHANUMERIC` does), decoding the encoder's output with the Rust
    decoder gives back the input bytes. -/
theorem percent_roundtrip (input : Slice Std.U8) (set : ascii_set.AsciiSet)
    (hpct : shouldEncode set 37 = true)
    (encoded : Slice Std.U8) (henc : bytes encoded = encode set (bytes input)) :
    (do let d ← percent_decode encoded
        decodeCollect (encoded.length + 1) d)
      ⦃ out => out = bytes input ⦄ := by
  apply WP.spec_mono (percent_decode_correct encoded)
  intro out hout
  rw [hout, henc, decode_encode _ _ _ hpct]
  intro b hb
  simp only [bytes, List.mem_map] at hb
  obtain ⟨x, -, rfl⟩ := hb
  have := x.hBounds; simpa [UScalarTy.numBits] using this

end percent_encoding.Proofs
