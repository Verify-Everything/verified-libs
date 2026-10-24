/-
  The `alloc` feature: `Cow` conversions, `if_any`, `decode_utf8`,
  `decode_utf8_lossy`, and `Display`.
  Plain (non-`module`) file, like Proofs/Sets.lean.
-/
import Proofs.Traits

open Aeneas Aeneas.Std Result WP
open percent_encoding percent_encoding.Spec

namespace percent_encoding.Proofs

/-! ### Reference-level facts about `decode` -/

/-- With no `%`, decoding changes nothing. -/
theorem decode_no_pct (l : List Nat) (h : 37 ∉ l) : decode l = l := by
  induction l with
  | nil => simp [decode]
  | cons b l ih =>
    have hb : b ≠ 37 := fun e => h (e ▸ List.mem_cons_self)
    rw [decode_cons_of_ne _ _ hb, ih (fun m => h (List.mem_cons_of_mem _ m))]

/-- A prefix in which no `%` starts a valid escape decodes to itself, whatever follows. -/
theorem decode_append_noescape (pre rest : List Nat)
    (h : ∀ k (hk : k < pre.length), pre[k] = 37 → afterPct ((pre ++ rest).drop (k + 1)) = none) :
    decode (pre ++ rest) = pre ++ decode rest := by
  induction pre with
  | nil => simp
  | cons b pre ih =>
    have ih' := ih (fun k hk hp => by
      have := h (k + 1) (by simp; omega) (by simpa using hp)
      simpa [List.drop_succ_cons] using this)
    by_cases hb : b = 37
    · subst hb
      have h0 := h 0 (by simp) rfl
      simp only [List.cons_append, List.drop_succ_cons, List.drop_zero] at h0
      rw [List.cons_append, decode_pct, h0, ih']; rfl
    · rw [List.cons_append, decode_cons_of_ne _ _ hb, ih']; rfl

/-- A valid escape anywhere makes the output strictly shorter. -/
theorem decode_shorter (l : List Nat)
    (h : ∃ k, ∃ hk : k < l.length, l[k] = 37 ∧ afterPct (l.drop (k + 1)) ≠ none) :
    (decode l).length < l.length := by
  induction l using decode.induct with
  | case1 => obtain ⟨k, hk, -⟩ := h; simp at hk
  | case2 h' l' rest hv lv hh hl ih =>
    rw [decode]; simp only [hh, hl, List.length_cons]
    have := (decode_length_bounds rest).1; omega
  | case3 h' l' rest hnot ih =>
    rw [decode]
    split
    · rename_i hv lv hh hl; exact absurd hl (hnot hv lv hh)
    · obtain ⟨k, hk, hp, ha⟩ := h
      cases k with
      | zero =>
        exfalso; apply ha
        simp only [List.drop_succ_cons, List.drop_zero, afterPct]
      | succ k =>
        have := ih ⟨k, by simp at hk ⊢; omega, by simpa using hp, by simpa using ha⟩
        simp only [List.length_cons] at *; omega
  | case4 b rest hb ih =>
    rw [decode]
    · obtain ⟨k, hk, hp, ha⟩ := h
      cases k with
      | zero =>
        exfalso; apply ha
        simp only [List.getElem_cons_zero] at hp
        subst hp
        simp only [List.drop_succ_cons, List.drop_zero]
        match rest, hb with
        | [], _ => simp [afterPct]
        | [x], _ => simp [afterPct]
        | x :: y :: r, hb => exact (hb x y r rfl rfl).elim
      | succ k =>
        have := ih ⟨k, by simp at hk ⊢; omega, by simpa using hp, by simpa using ha⟩
        simp only [List.length_cons]; omega
    · exact hb

/-- Decoding is the identity exactly when no `%` starts a valid escape. -/
theorem decode_eq_self_iff (l : List Nat) :
    decode l = l ↔ ∀ k (hk : k < l.length), l[k] = 37 → afterPct (l.drop (k + 1)) = none := by
  constructor
  · intro h k hk hp
    by_contra hne
    have := decode_shorter l ⟨k, hk, hp, hne⟩
    rw [h] at this; omega
  · intro h
    simpa [decode] using decode_append_noescape l [] (by simpa using h)

/-! ### `position_of_percent` -/

@[step]
theorem position_of_percent_loop_spec (bs : Slice Std.U8) :
    position_of_percent_loop bs 0#usize ⦃ j => j.val ≤ bs.length ∧
        (∀ k < j.val, (bs.val[k]!).val ≠ 37) ∧
        (j.val < bs.length → (bs.val[j.val]!).val = 37) ⦄ := by
  unfold position_of_percent_loop
  apply loop.spec_decr_nat (fun (x : Std.Usize) => bs.length - x.val)
    (fun x => x.val ≤ bs.length ∧ ∀ k < x.val, (bs.val[k]!).val ≠ 37)
  · intro x ⟨hx, hall⟩
    unfold position_of_percent_loop.body
    step*
    · have hlt : x.val < bs.length := by scalar_tac
      refine ⟨by omega, fun k hk => ?_, by omega⟩
      by_cases hkx : k < x.val
      · exact hall k hkx
      · have : k = x.val := by omega
        subst this; rw [getElem!_pos bs.val x.val hlt]; simp_all
    · have hlt : x.val < bs.length := by scalar_tac
      refine ⟨hx, hall, fun _ => ?_⟩
      rw [getElem!_pos bs.val x.val hlt]; simp_all
  · simp

/-- `position_of_percent` finds the first `%`, if any. -/
@[step]
theorem position_of_percent_spec (bs : Slice Std.U8) :
    position_of_percent bs ⦃ r =>
      match r with
      | none => 37 ∉ bytes bs
      | some i => ∃ h : i.val < bs.length, (bs.val[i.val]).val = 37 ∧
          ∀ k < i.val, (bs.val[k]!).val ≠ 37 ⦄ := by
  unfold position_of_percent
  step*
  · have hall := i_post1
    refine ⟨by scalar_tac, ?_, hall⟩
    have hlt : i.val < bs.length := by scalar_tac
    have := i_post2 hlt
    rwa [getElem!_pos bs.val i.val hlt] at this
  · have hall := i_post1
    have hge : bs.length ≤ i.val := by scalar_tac
    simp only [bytes, List.mem_map, not_exists, not_and]
    intro x hx hx37
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have := hall k (by simp [Slice.length] at hk hge; omega)
    rw [getElem!_pos bs.val k hk] at this
    exact this hx37

/-! ### `Vec::extend` with the decoder, and `decode_from_percent` -/

/-- `vec.extend(PercentDecode { .. })` appends the decoding of what is left. -/
theorem vec_extend_decode_spec (v : alloc.vec.Vec Std.U8) (d : PercentDecode)
    (h : v.length + (remBytes d.bytes).length ≤ Usize.max) :
    alloc.vec.Vec.Insts.CoreIterTraitsCollectExtend.extend alloc.alloc.Global
      (core.iter.traits.collect.IntoIterator.Blanket
        PercentDecode.Insts.CoreIterTraitsIteratorIteratorU8) v d
    ⦃ v' => v'.val.map (·.val) = v.val.map (·.val) ++ decode (remBytes d.bytes) ⦄ := by
  unfold alloc.vec.Vec.Insts.CoreIterTraitsCollectExtend.extend
  simp only [core.iter.traits.collect.IntoIterator.Blanket.into_iter, bind_ok]
  apply loop.spec_decr_nat (fun (p : alloc.vec.Vec Std.U8 × PercentDecode) => (remBytes p.2.bytes).length)
    (fun p => p.1.val.map (·.val) ++ decode (remBytes p.2.bytes) = v.val.map (·.val) ++ decode (remBytes d.bytes) ∧
      p.1.length + (remBytes p.2.bytes).length ≤ Usize.max)
  · rintro ⟨w, e⟩ ⟨h1, h2⟩
    apply WP.spec_bind (decode_next_spec e)
    rintro ⟨r, e'⟩ ⟨-, hr⟩
    cases r with
    | none =>
      apply (WP.spec_ok _).2
      simp only [hr] at h1
      simpa [decode] using h1
    | some b =>
      obtain ⟨hlt, hdec⟩ := hr
      simp only
      apply WP.spec_bind (alloc.vec.Vec.push_spec w b (by simp [alloc.vec.Vec.length] at h2; omega))
      intro w' hw'
      apply (WP.spec_ok _).2
      refine ⟨⟨?_, ?_⟩, hlt⟩
      · simp only at h1 ⊢; rw [hw', ← h1, ← hdec]; simp
      · simp only [alloc.vec.Vec.length, hw', List.length_append, List.length_singleton] at h2 ⊢; omega
  · exact ⟨rfl, h⟩

theorem remBytes_iter0 (s : Slice Std.U8) : remBytes ⟨s, 0⟩ = bytes s := by
  simp [remBytes, bytes]

/-- One step of `if_any`: at a `%` (preceded by `pre`, followed by `after`),
    either two hex digits follow and the whole decoding is returned, or
    nothing happens. -/
theorem decode_from_percent_spec (initial after : Slice Std.U8) (pre : List Nat)
    (hsplit : bytes initial = pre ++ 37 :: bytes after) :
    decode_from_percent initial after ⦃ r =>
      match afterPct (bytes after) with
      | none => r = none
      | some v => ∃ vec, r = some vec ∧
          vec.val.map (·.val) = pre ++ v :: decode ((bytes after).drop 2) ⦄ := by
  have hlen : initial.length = pre.length + 1 + after.length := by
    have := congrArg List.length hsplit; simp [bytes] at this; simp [Slice.length]; omega
  have hpre : (initial.val.take pre.length).map (·.val) = pre := by
    have := congrArg (List.take pre.length) hsplit
    simpa [bytes, List.map_take] using this
  unfold decode_from_percent core.slice.Slice.iter
  rw [bind_ok]
  apply WP.spec_bind (after_percent_sign_spec ⟨after, 0⟩)
  rintro ⟨o, it1⟩ ⟨ho, hs, hi⟩
  rw [remBytes_iter0] at ho
  cases o with
  | none =>
    apply (WP.spec_ok _).2
    simp only [Option.map_none] at ho
    simp [← ho]
  | some b =>
    simp only [Option.isSome_some, ite_true] at hi
    simp only [Option.map_some] at ho
    simp only [← ho]
    have hafter : 2 ≤ after.length := by
      by_contra hc
      have : bytes after = [] ∨ ∃ x, bytes after = [x] := by
        match h : bytes after with
        | [] => exact Or.inl rfl
        | [x] => exact Or.inr ⟨x, rfl⟩
        | x :: y :: r => exfalso; have := congrArg List.length h; simp [bytes] at this; simp [Slice.length] at hc; omega
      rcases this with h | ⟨x, h⟩ <;> rw [h] at ho <;> simp [afterPct] at ho
    unfold core.slice.iter.Iter.Insts.CoreIterTraitsExact_sizeExactSizeIteratorSharedT.len
    simp only [bind_ok]
    have hv : (Std.Usize.ofNatCore (it1.slice.length - it1.i)
        (by have := it1.slice.property; scalar_tac)).val = after.length - 2 := by
      rw [Usize.ofNatCore_val_eq, hs, hi]
    step*
    · have hrem : remBytes it1 = (bytes after).drop 2 := by
        simp [remBytes, bytes, hs, hi, List.map_drop]
      have hil : initial.len.val = initial.length := by simp
      have hu : unchanged_bytes_len.val = pre.length := by
        rw [unchanged_bytes_len_post, i2_post, hv, hil, hlen]; omega
      have hs1 : s.val.map (·.val) = pre := by rw [s_post, hu]; simpa [List.slice] using hpre
      have hsl : s.val.length = pre.length := by rw [← hs1]; simp
      simp only [Slice.Insts.AllocBorrowToOwnedVec.to_owned, bind_ok]
      have hmax := initial.property
      apply WP.spec_bind (alloc.vec.Vec.push_spec ⟨s⟩ b (by
        simp [alloc.vec.Vec.val, hsl]; simp [Slice.length] at hlen; omega))
      intro d1 hd1
      have hrl : (remBytes it1).length = after.length - 2 := by
        rw [hrem]; simp [bytes, Slice.length]
      apply WP.spec_bind (vec_extend_decode_spec d1 { bytes := it1 } (by
        simp only [alloc.vec.Vec.length, hd1, List.length_append, List.length_singleton, hrl]
        simp [alloc.vec.Vec.val, hsl]; simp [Slice.length] at hlen; omega))
      intro d2 hd2
      apply (WP.spec_ok _).2
      refine ⟨d2, rfl, ?_⟩
      rw [hd2, hd1, ← hrem]
      simp [alloc.vec.Vec.val, hs1]

/-! ### `if_any` -/

/-- No `%` among the first `n` bytes of `L` starts a valid escape. -/
def NoEsc (L : List Nat) (n : Nat) : Prop :=
  ∀ k < n, L[k]? = some 37 → afterPct (L.drop (k + 1)) = none

theorem decode_of_noesc (pre rest : List Nat) (h : NoEsc (pre ++ rest) pre.length) :
    decode (pre ++ rest) = pre ++ decode rest :=
  decode_append_noescape pre rest (fun k hk hp => h k hk (by
    rw [List.getElem?_append_left hk, List.getElem?_eq_getElem hk, hp]))

/-- What `if_any` returns: `None` when decoding changes nothing, otherwise the
    decoding. -/
def ifAnyPost (L : List Nat) (r : Option (alloc.vec.Vec Std.U8)) : Prop :=
  match r with
  | none => decode L = L
  | some vec => vec.val.map (·.val) = decode L ∧ decode L ≠ L

theorem bytes_drop (s : Slice Std.U8) (n : Nat) : (s.val.drop n).map (·.val) = (bytes s).drop n := by
  simp [bytes, List.map_drop]

@[step]
theorem decode_if_any_spec (initial : Slice Std.U8) :
    decode_if_any initial ⦃ r => ifAnyPost (bytes initial) r ⦄ := by
  unfold decode_if_any decode_if_any_loop
  have hmax := initial.property
  let L := bytes initial
  apply loop.spec_decr_nat
    (fun (p : Slice Std.U8 × Option (alloc.vec.Vec Std.U8) × Bool) =>
      2 * p.1.length + (if p.2.2 then 0 else 1))
    (fun p => (p.2.2 = false → p.2.1 = none ∧ ∃ pre, L = pre ++ bytes p.1 ∧ NoEsc L pre.length) ∧
              (p.2.2 = true → ifAnyPost L p.2.1))
  · rintro ⟨rest, result, dn⟩ ⟨hnd, hd⟩
    unfold decode_if_any_loop.body
    cases dn with
    | true => simp only [ite_true]; apply (WP.spec_ok _).2; exact hd rfl
    | false =>
      obtain ⟨hres, pre, hL, hne⟩ := hnd rfl
      simp only at hres hL
      subst hres
      simp only [Bool.false_eq_true, ite_false]
      apply WP.spec_bind (position_of_percent_spec rest)
      rintro o ho
      cases o with
      | none =>
        apply (WP.spec_ok _).2
        refine ⟨⟨fun h => absurd h (by simp), fun _ => ?_⟩, by simp⟩
        simp only [ifAnyPost]
        rw [hL, decode_of_noesc pre _ (hL ▸ hne), decode_no_pct _ ho]
      | some i =>
        obtain ⟨hi, hi37, hbefore⟩ := ho
        simp only
        have hilen : i.val < rest.length := hi
        step*
        have hbr : bytes rest = (bytes rest).take i.val ++ 37 :: bytes s := by
          have h1 : (bytes rest).drop i.val = 37 :: bytes s := by
            rw [← bytes_drop, List.drop_eq_getElem_cons hi, List.map_cons]
            simp only [hi37, List.cons.injEq, true_and]
            simp only [bytes, s_post, i1_post]
          rw [← h1, List.take_append_drop]
        set pre' := pre ++ (bytes rest).take i.val with hpre'
        have hL' : bytes initial = pre' ++ 37 :: bytes s := by
          rw [hpre', List.append_assoc, ← hbr]; exact hL
        have hne' : NoEsc L pre'.length := by
          intro k hk hk37
          by_cases hkp : k < pre.length
          · exact hne k hkp hk37
          · exfalso
            have hk2 : k - pre.length < i.val := by simp [hpre'] at hk; omega
            have hlt : k - pre.length < rest.length := by omega
            have : L[k]? = some ((rest.val[k - pre.length]'(by simpa using hlt)).val) := by
              rw [hL, List.getElem?_append_right (by omega)]
              simp only [bytes]
              rw [List.getElem?_map, List.getElem?_eq_getElem]; rfl
            rw [this] at hk37
            have := hbefore (k - pre.length) hk2
            rw [getElem!_pos rest.val _ (by simpa using hlt)] at this
            exact this (Option.some.inj hk37)
        apply WP.spec_bind (decode_from_percent_spec initial s pre' hL')
        intro o1 ho1
        have hdecL : decode L = pre' ++ decode (37 :: bytes s) := by
          rw [show L = pre' ++ 37 :: bytes s from hL']
          exact decode_of_noesc _ _ (hL' ▸ hne')
        cases hap : afterPct (bytes s) with
        | none =>
          rw [hap] at ho1
          subst ho1
          simp only
          step*
          refine ⟨fun _ => ⟨pre' ++ [37], ?_, ?_⟩, by simp, ?_⟩
          · show bytes initial = _
            rw [hL']; simp [bytes, rest1_post, s_post]
          · intro k hk hk37
            by_cases hkp : k < pre'.length
            · exact hne' k hkp hk37
            · have hk' : k = pre'.length := by simp at hk; omega
              subst hk'
              rw [show L = pre' ++ 37 :: bytes s from hL']
              simpa [List.drop_append_of_le_length] using hap
          · simp only [rest1_post, List.length_drop] at *; simp [Slice.length] at *; omega
        | some v =>
          rw [hap] at ho1
          obtain ⟨vec, rfl, hvec⟩ := ho1
          apply (WP.spec_ok _).2
          simp only
          refine ⟨by simp, fun _ => ?_, by simp⟩
          simp only [ifAnyPost]
          have hd : decode L = pre' ++ v :: decode ((bytes s).drop 2) := by
            rw [hdecL, decode_pct, hap]
          refine ⟨by rw [hvec, ← hd], ?_⟩
          intro heq
          have hL'' : L = pre' ++ 37 :: bytes s := hL'
          have := decode_shorter L ⟨pre'.length, by rw [hL'']; simp, by simp [hL''], by
            rw [hL'']; simp [hap]⟩
          rw [heq] at this; omega
  · refine ⟨fun _ => ⟨rfl, [], by simp [L], by simp [NoEsc]⟩, by simp⟩

theorem as_slice_bytes (it : core.slice.iter.Iter Std.U8) :
    core.slice.iter.Iter.as_slice it ⦃ s => bytes s = remBytes it ⦄ := by
  unfold core.slice.iter.Iter.as_slice
  apply (WP.spec_ok _).2
  simp [bytes, remBytes, Slice.from_val, List.map_drop]

/-- `PercentDecode::if_any`: `None` exactly when decoding the remaining input
    changes nothing; otherwise the decoded bytes. -/
theorem if_any_spec (d : PercentDecode) :
    PercentDecode.if_any d ⦃ r => ifAnyPost (remBytes d.bytes) r ⦄ := by
  unfold PercentDecode.if_any
  apply WP.spec_bind (as_slice_bytes d.bytes)
  intro s hs
  rw [← hs]
  exact decode_if_any_spec s

/-- The bytes held by a `Cow<[u8]>`. -/
def cowSliceBytes : alloc.borrow.Cow (Slice Std.U8) (alloc.vec.Vec Std.U8) → List Nat
  | .Borrowed s => bytes s
  | .Owned v => v.val.map (·.val)

/-- `Cow::<[u8]>::from(percent_decode(..))` holds the decoding, and borrows
    the input exactly when decoding changes nothing. -/
theorem cow_from_decode_spec (d : PercentDecode) :
    alloc.borrow.CowASliceU8VecU8.Insts.CoreConvertFromPercentDecode.from d ⦃ c =>
      cowSliceBytes c = decode (remBytes d.bytes) ∧
      ((∃ s, c = .Borrowed s) ↔ decode (remBytes d.bytes) = remBytes d.bytes) ⦄ := by
  unfold alloc.borrow.CowASliceU8VecU8.Insts.CoreConvertFromPercentDecode.from
  apply WP.spec_bind (if_any_spec d)
  intro r hr
  cases r with
  | none =>
    simp only [ifAnyPost] at hr
    apply WP.spec_bind (as_slice_bytes d.bytes)
    intro s hs
    apply (WP.spec_ok _).2
    simp [cowSliceBytes, hs, hr]
  | some v =>
    simp only [ifAnyPost] at hr
    apply (WP.spec_ok _).2
    simp [cowSliceBytes, hr.1, hr.2]

/-! ### UTF-8 and `String` helpers -/

theorem u8_eq_of_val {a b : Std.U8} (h : a.val = b.val) : a = b := UScalar.eq_of_val_eq h

theorem stringBytes_ofValid (l : List Std.U8) (h : Utf8Valid l) : stringBytes (stringOfValid l h) = l := by
  simp only [stringBytes, stringOfValid, String.fromUTF8, u8sToBA]
  rw [List.map_map]
  conv => rhs; rw [← List.map_id l]
  apply List.map_congr_left
  intro b _
  apply u8_eq_of_val
  have hb : b.val < 256 := by have := b.hBounds; simpa [UScalarTy.numBits] using this
  simp [Usize.ofNatCore_val_eq, UScalar.ofNatCore_val_eq, Nat.mod_eq_of_lt hb]

theorem stringBytes_append (s t : String) : stringBytes (s ++ t) = stringBytes s ++ stringBytes t := by
  simp [stringBytes, ByteArray.data_append]

/-- The bytes held by a `Cow<str>`. -/
def cowStrBytes : alloc.borrow.Cow Str String → List Nat
  | .Borrowed s => bytes s
  | .Owned s => (stringBytes s).map (·.val)

/-- The raw bytes held by a `Cow<[u8]>`. -/
def cowSliceU8 : alloc.borrow.Cow (Slice Std.U8) (alloc.vec.Vec Std.U8) → List Std.U8
  | .Borrowed s => s.val
  | .Owned v => v.val

theorem cowSliceBytes_eq (c : alloc.borrow.Cow (Slice Std.U8) (alloc.vec.Vec Std.U8)) :
    cowSliceBytes c = (cowSliceU8 c).map (·.val) := by
  cases c <;> rfl

/-- **`decode_utf8`.** With `u` the decoded bytes: if they are valid UTF-8 the
    result is `Ok` holding exactly them (borrowed when nothing was decoded),
    otherwise `Err` with the error Rust's validator reports for `u`. -/
theorem decode_utf8_spec (d : PercentDecode) :
    PercentDecode.decode_utf8 d ⦃ r => ∃ u : List Std.U8,
      u.map (·.val) = decode (remBytes d.bytes) ∧
      match r with
      | .Ok c => Utf8Valid u ∧ cowStrBytes c = decode (remBytes d.bytes) ∧
          ((∃ s, c = .Borrowed s) ↔ decode (remBytes d.bytes) = remBytes d.bytes)
      | .Err e => ¬ Utf8Valid u ∧ e = ⟨u⟩ ⦄ := by
  unfold PercentDecode.decode_utf8 core.convert.IntoFrom.into
  apply WP.spec_bind (cow_from_decode_spec d)
  rintro c ⟨hc, hb⟩
  rw [cowSliceBytes_eq] at hc
  refine WP.spec_mono ?_ (fun r hr => ⟨cowSliceU8 c, hc, hr⟩)
  cases c with
  | Borrowed s =>
    simp only [cowSliceU8] at hc ⊢
    unfold core.str.converts.from_utf8
    by_cases hv : Utf8Valid s.val
    · rw [if_pos hv, bind_ok]
      simp only [alloc.borrow.CowAStrString.Insts.CoreConvertFromSharedAStr.from, bind_ok]
      apply (WP.spec_ok _).2
      refine ⟨hv, ?_, ⟨fun _ => hb.1 ⟨s, rfl⟩, fun _ => ⟨s, rfl⟩⟩⟩
      simp [cowStrBytes, bytes, hc]
    · rw [if_neg hv, bind_ok]
      apply (WP.spec_ok _).2
      exact ⟨hv, rfl⟩
  | Owned v =>
    simp only [cowSliceU8] at hc ⊢
    unfold alloc.string.String.from_utf8
    by_cases hv : Utf8Valid v.val
    · rw [dif_pos hv, bind_ok]
      simp only [alloc.borrow.CowAStrString.Insts.CoreConvertFromString.from, bind_ok]
      apply (WP.spec_ok _).2
      refine ⟨hv, ?_, by simpa using hb⟩
      simp [cowStrBytes, stringBytes_ofValid, hc]
    · rw [dif_neg hv, bind_ok]
      simp only [alloc.string.FromUtf8Error.utf8_error, bind_ok]
      apply (WP.spec_ok _).2
      exact ⟨hv, rfl⟩

/-- **`decode_utf8_lossy`.** With `u` the decoded bytes: valid UTF-8 comes back
    unchanged (borrowed exactly when nothing was decoded); invalid UTF-8 gives
    std's lossy decoding of `u`. -/
theorem decode_utf8_lossy_spec (d : PercentDecode) :
    PercentDecode.decode_utf8_lossy d ⦃ c => ∃ u : List Std.U8,
      u.map (·.val) = decode (remBytes d.bytes) ∧
      (Utf8Valid u → cowStrBytes c = decode (remBytes d.bytes) ∧
          ((∃ s, c = .Borrowed s) ↔ decode (remBytes d.bytes) = remBytes d.bytes)) ∧
      (¬ Utf8Valid u → c = .Owned (stdUtf8Lossy u)) ⦄ := by
  unfold PercentDecode.decode_utf8_lossy core.convert.IntoFrom.into
  apply WP.spec_bind (cow_from_decode_spec d)
  rintro c ⟨hc, hb⟩
  rw [cowSliceBytes_eq] at hc
  refine WP.spec_mono ?_ (fun r hr => ⟨cowSliceU8 c, hc, hr⟩)
  unfold percent_encoding.decode_utf8_lossy
  cases c with
  | Borrowed s =>
    simp only [cowSliceU8] at hc ⊢
    unfold alloc.string.String.from_utf8_lossy
    by_cases hv : Utf8Valid s.val
    · rw [if_pos hv]
      apply (WP.spec_ok _).2
      refine ⟨fun _ => ⟨by simp [cowStrBytes, bytes, hc], fun _ => hb.1 ⟨s, rfl⟩, fun _ => ⟨s, rfl⟩⟩,
        fun h => absurd hv h⟩
    · rw [if_neg hv]
      apply (WP.spec_ok _).2
      exact ⟨fun h => absurd h hv, fun _ => rfl⟩
  | Owned v =>
    simp only [cowSliceU8] at hc ⊢
    unfold alloc.string.String.from_utf8_lossy
    have hdv : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref, Slice.from_val]
    by_cases hv : Utf8Valid v.val
    · rw [if_pos (hdv ▸ hv), bind_ok]
      unfold alloc.string.String.from_utf8_unchecked
      rw [dif_pos hv, bind_ok]
      apply (WP.spec_ok _).2
      refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd hv h⟩
      · simp [cowStrBytes, stringBytes_ofValid, hc]
      · constructor
        · rintro ⟨_, h⟩; cases h
        · intro h; exact (hb.2 h).elim (fun _ h' => by cases h')
    · rw [if_neg (hdv ▸ hv), bind_ok]
      apply (WP.spec_ok _).2
      exact ⟨fun h => absurd h hv, fun _ => by rw [hdv]⟩

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

/-! ### `Cow<str>` from the encoder -/

theorem strBytes_ascii_u8 (c : Str) (h : ∀ x ∈ strBytes c, x < 128) : ∀ b ∈ c.val, b.val < 128 :=
  fun b hb => h b.val (by simp only [strBytes, bytes, List.mem_map]; exact ⟨b, hb, rfl⟩)

theorem push_str_ascii_spec (s : String) (c : Str) (h : ∀ x ∈ strBytes c, x < 128) :
    alloc.string.String.push_str s c ⦃ s' =>
      (stringBytes s').map (·.val) = (stringBytes s).map (·.val) ++ strBytes c ⦄ := by
  unfold alloc.string.String.push_str
  rw [dif_pos (utf8Valid_of_ascii _ (strBytes_ascii_u8 c h))]
  apply (WP.spec_ok _).2
  simp [stringBytes_append, stringBytes_ofValid, strBytes, bytes]

/-- `string.extend(percent_encode(..))` appends the encoding. -/
theorem string_extend_encode_spec (str : String) (it : PercentEncode) :
    alloc.string.String.Insts.CoreIterTraitsCollectExtendSharedAStr.extend
      (core.iter.traits.collect.IntoIterator.Blanket
        PercentEncode.Insts.CoreIterTraitsIteratorIteratorSharedAStr) str it
    ⦃ s' => (stringBytes s').map (·.val) =
        (stringBytes str).map (·.val) ++ encode it.ascii_set (bytes it.bytes) ⦄ := by
  unfold alloc.string.String.Insts.CoreIterTraitsCollectExtendSharedAStr.extend
  simp only [core.iter.traits.collect.IntoIterator.Blanket.into_iter, bind_ok]
  apply loop.spec_decr_nat (fun (p : String × PercentEncode) => p.2.bytes.length)
    (fun p => (stringBytes p.1).map (·.val) ++ encode p.2.ascii_set (bytes p.2.bytes) =
        (stringBytes str).map (·.val) ++ encode it.ascii_set (bytes it.bytes) ∧
      p.2.ascii_set = it.ascii_set)
  · rintro ⟨w, e⟩ ⟨h1, h2⟩
    apply WP.spec_bind (encode_next_spec e)
    rintro ⟨r, e'⟩ ⟨hset, hr⟩
    cases r with
    | none =>
      apply (WP.spec_ok _).2
      obtain ⟨hnil, -⟩ := hr
      simp only at h1 ⊢
      rw [← h1, show bytes e.bytes = [] by simp [bytes, hnil]]
      simp [encode]
    | some chunk =>
      obtain ⟨hlt, hcat, hasc⟩ := hr
      apply WP.spec_bind (push_str_ascii_spec w chunk hasc)
      intro w' hw'
      apply (WP.spec_ok _).2
      refine ⟨⟨?_, by simp only at h2 ⊢; rw [hset, h2]⟩, hlt⟩
      simp only at h1 ⊢
      rw [hw', hset, List.append_assoc, hcat, h1]
  · exact ⟨rfl, rfl⟩

theorem toStr_empty_val (h) : (toStr "" h).val = [] := by
  simp [toStr, Slice.from_val]

/-- **`Cow<str>::from(percent_encode(input, set))`** holds exactly the encoding. -/
theorem cow_from_encode_spec (it : PercentEncode) :
    alloc.borrow.CowAStrString.Insts.CoreConvertFromPercentEncode.from it ⦃ c =>
      cowStrBytes c = encode it.ascii_set (bytes it.bytes) ⦄ := by
  unfold alloc.borrow.CowAStrString.Insts.CoreConvertFromPercentEncode.from core.convert.IntoFrom.into
  apply WP.spec_bind (encode_next_spec it)
  rintro ⟨r1, it1⟩ ⟨hs1, hr1⟩
  cases r1 with
  | none =>
    obtain ⟨hnil, -⟩ := hr1
    simp only [alloc.borrow.CowAStrString.Insts.CoreConvertFromSharedAStr.from]
    apply (WP.spec_ok _).2
    simp [cowStrBytes, toStr_empty_val, bytes, hnil, encode]
  | some first =>
    obtain ⟨-, hcat1, hasc1⟩ := hr1
    simp only
    apply WP.spec_bind (encode_next_spec it1)
    rintro ⟨r2, it2⟩ ⟨hs2, hr2⟩
    cases r2 with
    | none =>
      obtain ⟨hnil, -⟩ := hr2
      simp only [alloc.borrow.CowAStrString.Insts.CoreConvertFromSharedAStr.from]
      apply (WP.spec_ok _).2
      rw [← hcat1, show bytes it1.bytes = [] by simp [bytes, hnil]]
      simp [cowStrBytes, strBytes, encode]
    | some second =>
      obtain ⟨-, hcat2, hasc2⟩ := hr2
      unfold Str.Insts.AllocBorrowToOwnedString.to_owned
      have hv := utf8Valid_of_ascii _ (strBytes_ascii_u8 first hasc1)
      rw [dif_pos hv]
      simp only [bind_ok]
      apply WP.spec_bind (push_str_ascii_spec _ second hasc2)
      intro s1 hs1'
      apply WP.spec_bind (string_extend_encode_spec s1 it2)
      intro s2 hs2'
      simp only [alloc.borrow.CowAStrString.Insts.CoreConvertFromString.from]
      apply (WP.spec_ok _).2
      simp only [cowStrBytes]
      rw [hs1] at hcat2
      rw [hs2', hs1', stringBytes_ofValid, hs2, hs1, ← hcat1, ← hcat2]
      simp [strBytes, bytes]

/-! ### `Display` -/

/-- **`write_chunks`, the body of `Display::fmt`, for any `fmt::Write` sink.**
    Model the sink's text by `out`. If each successful `write_str` appends its
    argument, then a successful `write_chunks` appends exactly the encoding.
    If moreover every `write_str` succeeds (`allOk`), so does `write_chunks`. -/
theorem write_chunks_spec {W : Type} (inst : core.fmt.Write W) (out : W → List Nat) (allOk : Prop)
    (hW : ∀ w s, inst.write_str w s ⦃ p =>
      (p.1 = .Ok () → out p.2 = out w ++ strBytes s) ∧ (allOk → p.1 = .Ok ()) ⦄)
    (bs : Slice Std.U8) (set : ascii_set.AsciiSet) (w : W) :
    write_chunks inst bs set w ⦃ p =>
      (p.1 = .Ok () → out p.2 = out w ++ encode set (bytes bs)) ∧ (allOk → p.1 = .Ok ()) ⦄ := by
  unfold write_chunks write_chunks_loop
  apply loop.spec_decr_nat
    (fun (p : W × Slice Std.U8 × core.result.Result Unit core.fmt.Error × Bool) =>
      2 * p.2.1.length + (if p.2.2.2 then 0 else 1))
    (fun p => (p.2.2.2 = false → p.2.2.1 = .Ok () ∧
                 out p.1 ++ encode set (bytes p.2.1) = out w ++ encode set (bytes bs)) ∧
              (p.2.2.2 = true → (p.2.2.1 = .Ok () → out p.1 = out w ++ encode set (bytes bs)) ∧
                 (allOk → p.2.2.1 = .Ok ())))
  · rintro ⟨sink, rest, result, dn⟩ ⟨hnd, hd⟩
    unfold write_chunks_loop.body
    cases dn with
    | true => simp only [ite_true]; apply (WP.spec_ok _).2; exact hd rfl
    | false =>
      obtain ⟨hres, hout⟩ := hnd rfl
      simp only at hres hout
      subst hres
      simp only [Bool.false_eq_true, ite_false]
      apply WP.spec_bind (next_chunk_spec rest set)
      intro o ho
      cases o with
      | none =>
        apply (WP.spec_ok _).2
        refine ⟨⟨fun h => absurd h (by simp), fun _ => ⟨fun _ => ?_, fun _ => rfl⟩⟩, by simp⟩
        simp only
        rw [← hout, show bytes rest = [] by simp [bytes, ho]]; simp [encode]
      | some p =>
        obtain ⟨chunk, remaining⟩ := p
        obtain ⟨hlt, hcat, -⟩ := ho
        simp only
        apply WP.spec_bind (hW sink chunk)
        rintro ⟨r, sink1⟩ ⟨hok, hall⟩
        cases r with
        | Ok u =>
          cases u
          apply (WP.spec_ok _).2
          refine ⟨⟨fun _ => ⟨rfl, ?_⟩, fun h => absurd h (by simp)⟩, by simp; omega⟩
          have h' := hok rfl
          simp only at h' ⊢
          rw [h', List.append_assoc, hcat, hout]
        | Err e =>
          apply (WP.spec_ok _).2
          refine ⟨⟨fun h => absurd h (by simp), fun _ => ⟨fun h => absurd h (by simp), fun h => hall h⟩⟩, ?_⟩
          simp [Slice.length] at hlt ⊢; omega
  · exact ⟨fun _ => ⟨rfl, rfl⟩, fun h => by cases h⟩

/-- A sink that collects the written bytes. -/
def bufWrite : core.fmt.Write (List Nat) := { write_str := fun buf s => ok (.Ok (), buf ++ strBytes s) }

/-- Writing a `PercentEncode` (what `Display`/`to_string` do) into a byte buffer
    succeeds and appends exactly the encoding. -/
theorem write_chunks_buffer (bs : Slice Std.U8) (set : ascii_set.AsciiSet) (buf : List Nat) :
    write_chunks bufWrite bs set buf ⦃ p => p.1 = .Ok () ∧ p.2 = buf ++ encode set (bytes bs) ⦄ := by
  apply WP.spec_mono (write_chunks_spec bufWrite id True (fun w s => by
    apply (WP.spec_ok _).2; simp) bs set buf)
  rintro ⟨r, b⟩ ⟨h1, h2⟩
  have hr := h2 trivial
  exact ⟨hr, h1 hr⟩

/-- If every `write_str` succeeds, `write_chunks` succeeds (no output tracking). -/
theorem write_chunks_ok {W : Type} (inst : core.fmt.Write W)
    (hW : ∀ w s, inst.write_str w s ⦃ p => p.1 = .Ok () ⦄)
    (bs : Slice Std.U8) (set : ascii_set.AsciiSet) (w : W) :
    write_chunks inst bs set w ⦃ p => p.1 = .Ok () ⦄ := by
  unfold write_chunks write_chunks_loop
  apply loop.spec_decr_nat
    (fun (p : W × Slice Std.U8 × core.result.Result Unit core.fmt.Error × Bool) =>
      2 * p.2.1.length + (if p.2.2.2 then 0 else 1))
    (fun p => p.2.2.1 = .Ok ())
  · rintro ⟨sink, rest, result, dn⟩ hres
    simp only at hres
    subst hres
    unfold write_chunks_loop.body
    cases dn with
    | true => simp only [ite_true]; apply (WP.spec_ok _).2; rfl
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      apply WP.spec_bind (next_chunk_spec rest set)
      intro o ho
      cases o with
      | none => apply (WP.spec_ok _).2; simp
      | some p =>
        obtain ⟨chunk, remaining⟩ := p
        obtain ⟨hlt, -, -⟩ := ho
        simp only
        apply WP.spec_bind (hW sink chunk)
        rintro ⟨r, sink1⟩ hr
        simp only at hr
        subst hr
        apply (WP.spec_ok _).2
        simp; omega
  · rfl

/-- `Display::fmt` on a real `Formatter` never panics, terminates and returns `Ok`
    (Aeneas models `Formatter::write_str` as always succeeding; it does not model
    the text, which `write_chunks_spec` covers for any sink). -/
theorem display_fmt_spec (it : PercentEncode) (f : core.fmt.Formatter) :
    PercentEncode.Insts.CoreFmtDisplay.fmt it f ⦃ p => p.1 = .Ok () ⦄ := by
  unfold PercentEncode.Insts.CoreFmtDisplay.fmt
  apply write_chunks_ok
  intro w s
  simp only [core.fmt.Formatter.Insts.CoreFmtWrite, core.fmt.Formatter.Insts.CoreFmtWrite.write_str,
    core.fmt.Formatter.write_str]
  apply (WP.spec_ok _).2; rfl

/-! ### Derived `Debug` (`AsciiSet`, `PercentEncode`)

The derived bodies hand the struct name and each field to std's
`debug_struct_fieldN_finish`; Aeneas models that helper without its text
output, so what can be checked is the call itself and that it never panics. -/

theorem asciiSet_debug_call (s : ascii_set.AsciiSet) (f : core.fmt.Formatter) :
    ascii_set.AsciiSet.Insts.CoreFmtDebug.fmt s f =
      core.fmt.Formatter.debug_struct_field1_finish f (toStr "AsciiSet") (toStr "mask")
        (Dyn.mk _ (core.fmt.DebugShared (Array.Insts.CoreFmtDebug 4#usize core.fmt.DebugU32)) s.mask) := rfl

theorem asciiSet_debug_ok (s : ascii_set.AsciiSet) (f : core.fmt.Formatter) :
    ascii_set.AsciiSet.Insts.CoreFmtDebug.fmt s f ⦃ p => p.1 = .Ok () ∧ p.2 = f ⦄ := by
  rw [asciiSet_debug_call]; apply (WP.spec_ok _).2; simp

theorem percentEncode_debug_call (it : PercentEncode) (f : core.fmt.Formatter) :
    PercentEncode.Insts.CoreFmtDebug.fmt it f =
      core.fmt.Formatter.debug_struct_field2_finish f (toStr "PercentEncode")
        (toStr "bytes")
        (Dyn.mk _ (core.fmt.DebugShared (Slice.Insts.CoreFmtDebug core.fmt.DebugU8)) it.bytes)
        (toStr "ascii_set")
        (Dyn.mk _ (core.fmt.DebugShared (core.fmt.DebugShared ascii_set.AsciiSet.Insts.CoreFmtDebug))
          it.ascii_set) := rfl

theorem percentEncode_debug_ok (it : PercentEncode) (f : core.fmt.Formatter) :
    PercentEncode.Insts.CoreFmtDebug.fmt it f ⦃ p => p.1 = .Ok () ∧ p.2 = f ⦄ := by
  rw [percentEncode_debug_call]; apply (WP.spec_ok _).2; simp

/-- **`decode_utf8_lossy` (the private free function), for any `Cow<[u8]>` input.**
    Valid UTF-8 comes back with the same bytes and the same variant; invalid
    UTF-8 gives std's lossy decoding as an owned string. -/
theorem free_decode_utf8_lossy_spec (c : alloc.borrow.Cow (Slice Std.U8) (alloc.vec.Vec Std.U8)) :
    percent_encoding.decode_utf8_lossy c ⦃ r =>
      (Utf8Valid (cowSliceU8 c) → cowStrBytes r = (cowSliceU8 c).map (·.val) ∧
          ((∃ s, r = .Borrowed s) ↔ (∃ s, c = .Borrowed s))) ∧
      (¬ Utf8Valid (cowSliceU8 c) → r = .Owned (stdUtf8Lossy (cowSliceU8 c))) ⦄ := by
  unfold percent_encoding.decode_utf8_lossy
  cases c with
  | Borrowed s =>
    simp only [cowSliceU8]
    unfold alloc.string.String.from_utf8_lossy
    by_cases hv : Utf8Valid s.val
    · rw [if_pos hv]
      apply (WP.spec_ok _).2
      exact ⟨fun _ => ⟨by simp [cowStrBytes, bytes], fun _ => ⟨s, rfl⟩, fun _ => ⟨s, rfl⟩⟩,
        fun h => absurd hv h⟩
    · rw [if_neg hv]
      apply (WP.spec_ok _).2
      exact ⟨fun h => absurd h hv, fun _ => rfl⟩
  | Owned v =>
    simp only [cowSliceU8]
    unfold alloc.string.String.from_utf8_lossy
    have hdv : (alloc.vec.Vec.deref v).val = v.val := by simp [alloc.vec.Vec.deref, Slice.from_val]
    by_cases hv : Utf8Valid v.val
    · rw [if_pos (hdv ▸ hv), bind_ok]
      unfold alloc.string.String.from_utf8_unchecked
      rw [dif_pos hv, bind_ok]
      apply (WP.spec_ok _).2
      refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd hv h⟩
      · simp [cowStrBytes, stringBytes_ofValid]
      · constructor
        · rintro ⟨_, h⟩; cases h
        · rintro ⟨_, h⟩; cases h
    · rw [if_neg (hdv ▸ hv), bind_ok]
      apply (WP.spec_ok _).2
      exact ⟨fun h => absurd h hv, fun _ => by rw [hdv]⟩

/-- `_static_assert` (generated by the `static_assert!` macro) only names
    `mem::transmute` at array types whose sizes the compiler checks; at run
    time it does nothing and cannot fail. -/
theorem static_assert_spec : ascii_set._static_assert = ok () := by
  unfold ascii_set._static_assert; rfl
