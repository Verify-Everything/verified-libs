// Gate 1, aarch64 half of patches/0002-simd-readable-by-aeneas.patch (crc32fast 1.5.3,
// src/specialized/aarch64.rs). The original upstream bodies and the patched bodies are both proved
// to meet one exact spec, so they agree on every input:
//   calculate   original: align_to, chunks_exact(4) + zip loops   spec: calc_ok
//               patched:  split_quads, index loops
//   crc_quads   original: `for chunk in &mut quad_iter`           spec: !fold_d(!crc, quads)
//               patched:  `while let Some(chunk) = quad_iter.next()`
//   split_quads (patched only) is `align_to` itself               spec: the align_to contract
// Bodies marked `// verbatim:` are checked against the pinned sources by ../check_verbatim.py:
// only `#[invariant]`/`#[variant]` attributes and ghost `snapshot!`/`proof_assert!` lines differ.
// Trusted facts are marked T1-T4 below and listed in ../README.md.
#![allow(unused, non_snake_case, unused_unsafe)]
use creusot_std::prelude::*;
use creusot_std::std::slice::{ChunksExactExt, SliceExt};
use creusot_std::std::iter::ZipExt;
use core::slice;
use core::slice::ChunksExact;

// ---------------------------------------------------------------- T1: CPU instructions
// The two CRC32 instructions are deterministic functions of their inputs. Nothing else is assumed
// (their meaning is proved in Lean against the bit-at-a-time CRC and cross-checked under qemu).
pub mod arch {
    use creusot_std::prelude::*;

    #[logic(opaque)]
    pub fn crc32d_l(crc: u32, data: u64) -> u32 {
        dead
    }

    #[trusted]
    #[ensures(result == crc32d_l(crc, data))]
    pub unsafe fn __crc32d(crc: u32, data: u64) -> u32 {
        unreachable!()
    }
}

// ---------------------------------------------------------------- T2: unchanged callees
// `crc_bytes` and `combine` are the same code in both versions; equivalence needs only that they
// are deterministic. Their meaning is proved in Lean (crc_bytes_eq, combine_eq).
#[logic(opaque)]
pub fn crc_bytes_l(crc: u32, bytes: Seq<u8>) -> u32 {
    dead
}

#[trusted]
#[ensures(result == crc_bytes_l(crc, bytes@))]
unsafe fn crc_bytes(crc: u32, bytes: &[u8]) -> u32 {
    unreachable!()
}

pub mod combine {
    use creusot_std::prelude::*;

    // The length is passed as its numeric value (a u64 is determined by it).
    #[logic(opaque)]
    pub fn combine_l(crc1: u32, crc2: u32, len2: Int) -> u32 {
        dead
    }

    #[trusted]
    #[ensures(result == combine_l(crc1, crc2, len2@))]
    pub(crate) fn combine(crc1: u32, crc2: u32, len2: u64) -> u32 {
        unreachable!()
    }
}

const MIN_TRIPLE_QUADS: usize = 192;

// ---------------------------------------------------------------- T3: std contracts
// `align_to` splits a slice into a prefix, whole `U`s, and a suffix that together are the input
// (std docs). Where it splits depends on the address, which Creusot's `&[T]` does not carry, so
// the split is an opaque function of the slice, applied to the same `data` in both versions. The
// Lean proof models it the same way (a64.splitPre/splitMid) and holds for every split.
#[logic(opaque)]
pub fn align_pre<T, U>(s: Seq<T>) -> Seq<T> {
    dead
}
#[logic(opaque)]
pub fn align_mid<T, U>(s: Seq<T>) -> Seq<U> {
    dead
}
#[logic(opaque)]
pub fn align_post<T, U>(s: Seq<T>) -> Seq<T> {
    dead
}

extern_spec! {
    impl<T> [T] {
        #[ensures(result.0@ == align_pre::<T, U>(self@))]
        #[ensures(result.1@ == align_mid::<T, U>(self@))]
        #[ensures(result.2@ == align_post::<T, U>(self@))]
        #[ensures(result.0@.len() * size_of_logic::<T>() + result.1@.len() * size_of_logic::<U>()
                  + result.2@.len() * size_of_logic::<T>() == self@.len() * size_of_logic::<T>())]
        unsafe fn align_to<U>(&self) -> (&[T], &[U], &[T]);
    }

    // std: `fold` calls `f` on each remaining item in order, threading the accumulator.
    // Stated for closures whose call leaves their state unchanged (here `|acc, &q| ..`).
    impl<'a, T> Iterator for slice::Iter<'a, T> {
        #[requires(forall<b: B, x: &'a T> f.precondition((b, x)))]
        #[requires(forall<b: B, x: &'a T, g: F, r: B> f.postcondition_mut((b, x), g, r) ==> g == f)]
        #[ensures(exists<accs: Seq<B>> accs.len() == self@@.len() + 1 && accs[0] == init
            && (forall<j: Int> 0 <= j && j < self@@.len() ==>
                    f.postcondition_mut((accs[j], self@.to_ref_seq()[j]), f, accs[j + 1]))
            && result == accs[self@@.len()])]
        fn fold<B, F>(self, init: B, f: F) -> B
        where
            Self: Sized,
            F: FnMut(B, &'a T) -> B;
    }
}

#[cfg(creusot)]
use creusot_std::std::mem::size_of_logic;

// ---------------------------------------------------------------- the common spec
// CRC32 instruction applied to each word of `s` in order, starting from `c`.
#[logic(open)]
#[variant(s.len())]
pub fn fold_d(c: u32, s: Seq<u64>) -> u32 {
    pearlite! {
        if s.len() == 0 { c }
        else { arch::crc32d_l(fold_d(c, s.subsequence(0, s.len() - 1)), s[s.len() - 1]) }
    }
}

// One more word: fold_d over s[0..k+1] is one crc32d step after fold_d over s[0..k].
#[logic]
#[ensures(forall<c: u32, k: Int> 0 <= k && k < s.len() ==>
    fold_d(c, s.subsequence(0, k + 1)) == arch::crc32d_l(fold_d(c, s.subsequence(0, k)), s[k]))]
pub fn fold_steps(s: Seq<u64>) {
    pearlite! {
        proof_assert! { forall<k: Int> 0 <= k && k < s.len() ==>
            s.subsequence(0, k + 1).subsequence(0, k).ext_eq(s.subsequence(0, k)) };
        ()
    }
}

#[logic]
#[ensures(s.subsequence(0, s.len()) == s)]
pub fn sub_full<T>(s: Seq<T>) {
    pearlite! { proof_assert! { s.subsequence(0, s.len()).ext_eq(s) }; () }
}

// Any chain accs[0..=j] with accs[i+1] = crc32d(accs[i], s[base + i]) that starts at
// fold_d(c, s[0..base]) ends at fold_d(c, s[0..base+j]). (Used for `fold`, whose spec gives such a chain.)
#[logic]
#[variant(j)]
#[requires(0 <= base && 0 <= j && base + j <= s.len())]
#[ensures(forall<accs: Seq<u32>> j < accs.len() && accs[0] == fold_d(c, s.subsequence(0, base))
    && (forall<i: Int> 0 <= i && i < j ==> accs[i + 1] == arch::crc32d_l(accs[i], s[base + i]))
    ==> accs[j] == fold_d(c, s.subsequence(0, base + j)))]
pub fn chain(c: u32, s: Seq<u64>, base: Int, j: Int) {
    pearlite! {
        if j == 0 { () } else { let _ = chain(c, s, base, j - 1); fold_steps(s) }
    }
}

// The exact result of `calculate`, given where `align_to` splits `data`.
#[logic(open)]
pub fn triple(r1: u32, q: Seq<u64>) -> u32 {
    pearlite! {
        let n3 = q.len() / 3;
        let bl = n3 * 8;
        let c0 = fold_d(!r1, q.subsequence(0, n3));
        let c1 = fold_d(!0u32, q.subsequence(n3, 2 * n3));
        let c2 = fold_d(!0u32, q.subsequence(2 * n3, 3 * n3));
        let r = combine::combine_l(combine::combine_l(!c0, !c1, bl), !c2, bl);
        !fold_d(!r, q.subsequence(3 * n3, q.len()))
    }
}

#[logic(open)]
pub fn calc_ok(crc: u32, data: Seq<u8>, res: u32) -> bool {
    pearlite! {
        let r1 = crc_bytes_l(crc, align_pre::<u8, u64>(data));
        let q = align_mid::<u8, u64>(data);
        let post = align_post::<u8, u64>(data);
        if q.len() >= 192 {
            res == crc_bytes_l(triple(r1, q), post)
        } else {
            res == crc_bytes_l(!fold_d(!r1, q), post)
        }
    }
}

// calc_ok is `res == <expression of crc and data>` in both branches, so two results that both
// meet it are equal: that is the equivalence.

// ---------------------------------------------------------------- ChunksExact laws, re-proved here
// The creusot-std patch (../creusot-std-chunks.patch) states these laws for ChunksExact; Creusot
// takes laws of a dependency as axioms, so the same statements are proved here.
#[logic]
#[ensures(it.produces(Seq::empty(), it))]
pub fn chunks_refl<'a>(it: ChunksExact<'a, u64>) {
    pearlite! { proof_assert! { Seq::<&'a [u64]>::empty().concat(it.chunks()).ext_eq(it.chunks()) }; () }
}

#[logic]
#[requires(a.produces(ab, b))]
#[requires(b.produces(bc, c))]
#[ensures(a.produces(ab.concat(bc), c))]
pub fn chunks_trans<'a>(a: ChunksExact<'a, u64>, ab: Seq<&'a [u64]>, b: ChunksExact<'a, u64>,
                        bc: Seq<&'a [u64]>, c: ChunksExact<'a, u64>) {
    pearlite! { proof_assert! { ab.concat(bc).concat(c.chunks()).ext_eq(ab.concat(bc.concat(c.chunks()))) }; () }
}

// ---------------------------------------------------------------- original upstream code
pub mod orig {
    use super::*;
    use crate::arch;

    #[ensures(result == !fold_d(!crc, quads@))]
    // verbatim: upstream src/specialized/aarch64.rs unsafe fn crc_quads(crc: u32, quads: &[u64]) -> u32 {
    unsafe fn crc_quads(crc: u32, quads: &[u64]) -> u32 {
        let mut c = !crc;

        // unrolling increases performance by a lot
        let mut quad_iter = quads.chunks_exact(8);
        snapshot! { fold_steps(quads@) };
        let q0 = snapshot!(quad_iter);
        #[invariant(produced.len() <= q0.chunks().len())]
        #[invariant(forall<i: Int> 0 <= i && i < produced.len() ==> produced[i] == q0.chunks()[i])]
        #[invariant(c == fold_d(!crc, quads@.subsequence(0, 8 * produced.len())))]
        #[variant(q0.chunks().len() - produced.len())]
        for chunk in &mut quad_iter {
            proof_assert! { chunk == q0.chunks()[produced.len() - 1] };
            proof_assert! { chunk@ == quads@.subsequence(8 * (produced.len() - 1), 8 * produced.len()) };
            c = arch::__crc32d(c, chunk[0]);
            c = arch::__crc32d(c, chunk[1]);
            c = arch::__crc32d(c, chunk[2]);
            c = arch::__crc32d(c, chunk[3]);
            c = arch::__crc32d(c, chunk[4]);
            c = arch::__crc32d(c, chunk[5]);
            c = arch::__crc32d(c, chunk[6]);
            c = arch::__crc32d(c, chunk[7]);
        }
        proof_assert! { quad_iter.rem() == q0.rem() };
        snapshot! { chain(!crc, quads@, 8 * q0.chunks().len(), quads@.len() - 8 * q0.chunks().len()) };
        snapshot! { sub_full(quads@) };
        c = quad_iter
            .remainder()
            .iter()
            .fold(c, |acc, &q| arch::__crc32d(acc, q));

        !c
    }

    #[ensures(calc_ok(crc, data@, result))]
    // verbatim: upstream src/specialized/aarch64.rs pub unsafe fn calculate(crc: u32, data: &[u8]) -> u32 {
    pub unsafe fn calculate(crc: u32, data: &[u8]) -> u32 {
        let (pre_quad, quads, post_quad) = data.align_to::<u64>();

        // Running (finalized) CRC.
        let mut r = crc;

        // Unaligned leading bytes.
        r = crc_bytes(r, pre_quad);

        if quads.len() >= MIN_TRIPLE_QUADS {
            // A single `crc32d` chain is latency-bound: each instruction depends on the previous
            // result. Splitting the aligned region into three equal, contiguous blocks and advancing
            // three independent accumulators in lockstep keeps several `crc32d` in flight, then
            // `combine` reassembles them (appending the zero-seeded later blocks to the first).
            let n3 = quads.len() / 3;
            let block_len = (n3 * 8) as u64;

            let a = &quads[0..n3];
            let b = &quads[n3..2 * n3];
            let c = &quads[2 * n3..3 * n3];

            // Internal (bit-inverted) states. A carries the running CRC; B and C start from zero.
            let mut c0 = !r;
            let mut c1 = !0u32;
            let mut c2 = !0u32;

            // Unroll each stream by 4 while keeping the three chains independent.
            let mut chunks_a = a.chunks_exact(4);
            let mut chunks_b = b.chunks_exact(4);
            let mut chunks_c = c.chunks_exact(4);
            snapshot! { fold_steps(a@) };
            snapshot! { fold_steps(b@) };
            snapshot! { fold_steps(c@) };
            let r0 = snapshot!(r);
            let ca0 = snapshot!(chunks_a);
            let cb0 = snapshot!(chunks_b);
            let cc0 = snapshot!(chunks_c);
            proof_assert! { cb0.chunks().len() == ca0.chunks().len() && cc0.chunks().len() == ca0.chunks().len() };
            #[invariant(produced.len() <= ca0.chunks().len())]
            #[invariant(forall<i: Int> 0 <= i && i < produced.len() ==>
                produced[i].0.0 == ca0.chunks()[i] && produced[i].0.1 == cb0.chunks()[i]
                && produced[i].1 == cc0.chunks()[i])]
            #[invariant((*iter.iter_a().iter_a()).chunks().len() == ca0.chunks().len() - produced.len())]
            #[invariant((*iter.iter_a().iter_b()).chunks().len() == ca0.chunks().len() - produced.len())]
            #[invariant((*iter.iter_b()).chunks().len() == ca0.chunks().len() - produced.len())]
            #[invariant((*iter.iter_a().iter_b()).rem() == cb0.rem() && (*iter.iter_b()).rem() == cc0.rem())]
            #[invariant(^iter.iter_a().iter_b() == ^(*iter_old).iter_a().iter_b())]
            #[invariant(^iter.iter_b() == ^(*iter_old).iter_b())]
            #[invariant(c0 == fold_d(!*r0, a@.subsequence(0, 4 * produced.len())))]
            #[invariant(c1 == fold_d(!0u32, b@.subsequence(0, 4 * produced.len())))]
            #[invariant(c2 == fold_d(!0u32, c@.subsequence(0, 4 * produced.len())))]
            #[variant(ca0.chunks().len() - produced.len())]
            for ((qa, qb), qc) in (&mut chunks_a).zip(&mut chunks_b).zip(&mut chunks_c) {
                let base = snapshot!(4 * (produced.len() - 1));
                proof_assert! { qa == ca0.chunks()[produced.len() - 1] };
                proof_assert! { qb == cb0.chunks()[produced.len() - 1] };
                proof_assert! { qc == cc0.chunks()[produced.len() - 1] };
                proof_assert! { qa@ == a@.subsequence(*base, *base + 4) };
                proof_assert! { qb@ == b@.subsequence(*base, *base + 4) };
                proof_assert! { qc@ == c@.subsequence(*base, *base + 4) };
                #[invariant(c0 == fold_d(!*r0, a@.subsequence(0, *base + produced.len())))]
                #[invariant(c1 == fold_d(!0u32, b@.subsequence(0, *base + produced.len())))]
                #[invariant(c2 == fold_d(!0u32, c@.subsequence(0, *base + produced.len())))]
                #[variant(4 - produced.len())]
                for k in 0..4 {
                    c0 = arch::__crc32d(c0, qa[k]);
                    c1 = arch::__crc32d(c1, qb[k]);
                    c2 = arch::__crc32d(c2, qc[k]);
                }
            }
            proof_assert! { chunks_a.rem() == ca0.rem() };
            proof_assert! { chunks_b.rem() == cb0.rem() };
            proof_assert! { chunks_c.rem() == cc0.rem() };
            let base = snapshot!(4 * ca0.chunks().len());
            let ra = snapshot!(ca0.rem());
            let rb = snapshot!(cb0.rem());
            let rc = snapshot!(cc0.rem());
            proof_assert! { ra@ == a@.subsequence(*base, n3@) };
            proof_assert! { rb@ == b@.subsequence(*base, n3@) };
            proof_assert! { rc@ == c@.subsequence(*base, n3@) };
            proof_assert! { c0 == fold_d(!*r0, a@.subsequence(0, *base)) };
            #[invariant(*base + produced.len() <= n3@)]
            #[invariant(forall<i: Int> 0 <= i && i < produced.len() ==>
                *produced[i].0.0 == ra@[i] && *produced[i].0.1 == rb@[i] && *produced[i].1 == rc@[i])]
            #[invariant(c0 == fold_d(!*r0, a@.subsequence(0, *base + produced.len())))]
            #[invariant(c1 == fold_d(!0u32, b@.subsequence(0, *base + produced.len())))]
            #[invariant(c2 == fold_d(!0u32, c@.subsequence(0, *base + produced.len())))]
            #[variant(n3@ - *base - produced.len())]
            for ((&qa, &qb), &qc) in chunks_a
                .remainder()
                .iter()
                .zip(chunks_b.remainder())
                .zip(chunks_c.remainder())
            {
                proof_assert! { qa == ra@[produced.len() - 1] };
                proof_assert! { qb == rb@[produced.len() - 1] };
                proof_assert! { qc == rc@[produced.len() - 1] };
                proof_assert! { qa == a@[*base + produced.len() - 1] };
                proof_assert! { qb == b@[*base + produced.len() - 1] };
                proof_assert! { qc == c@[*base + produced.len() - 1] };
                c0 = arch::__crc32d(c0, qa);
                c1 = arch::__crc32d(c1, qb);
                c2 = arch::__crc32d(c2, qc);
            }
            snapshot! { sub_full(a@) };
            snapshot! { sub_full(b@) };
            snapshot! { sub_full(c@) };
            proof_assert! { c0 == fold_d(!*r0, a@) && c1 == fold_d(!0u32, b@) && c2 == fold_d(!0u32, c@) };

            r = crate::combine::combine(!c0, !c1, block_len);
            r = crate::combine::combine(r, !c2, block_len);

            // Words left over after the three equal blocks.
            r = crc_quads(r, &quads[3 * n3..]);
        } else {
            r = crc_quads(r, quads);
        }

        // Unaligned trailing bytes.
        crc_bytes(r, post_quad)
    }
}

// ---------------------------------------------------------------- patched code (what Lean proves)
pub mod patched {
    use super::*;
    use crate::arch;

    #[ensures(result.0@ == align_pre::<u8, u64>(data@))]
    #[ensures(result.1@ == align_mid::<u8, u64>(data@))]
    #[ensures(result.2@ == align_post::<u8, u64>(data@))]
    #[ensures(result.0@.len() + result.1@.len() * 8 + result.2@.len() == data@.len())]
    // verbatim: patched src/specialized/aarch64.rs fn split_quads(data: &[u8]) -> (&[u8], &[u64], &[u8]) {
    fn split_quads(data: &[u8]) -> (&[u8], &[u64], &[u8]) {
        // SAFETY: every bit pattern is a valid `u64`.
        unsafe { data.align_to::<u64>() }
    }

    #[ensures(result == !fold_d(!crc, quads@))]
    // verbatim: patched src/specialized/aarch64.rs unsafe fn crc_quads(crc: u32, quads: &[u64]) -> u32 {
    unsafe fn crc_quads(crc: u32, quads: &[u64]) -> u32 {
        let mut c = !crc;

        // unrolling increases performance by a lot
        let mut quad_iter = quads.chunks_exact(8);
        snapshot! { fold_steps(quads@) };
        let q0 = snapshot!(quad_iter);
        let mut done = snapshot!(Seq::<&[u64]>::empty());
        #[invariant(q0.produces(*done, quad_iter))]
        #[invariant(c == fold_d(!crc, quads@.subsequence(0, 8 * done.len())))]
        #[variant(quad_iter.chunks().len())]
        // Verification patch: `for chunk in &mut quad_iter` written as the `while let` it stands for.
        while let Some(chunk) = quad_iter.next() {
            proof_assert! { chunk == q0.chunks()[done.len()] };
            proof_assert! { chunk@ == quads@.subsequence(8 * done.len(), 8 * done.len() + 8) };
            c = arch::__crc32d(c, chunk[0]);
            c = arch::__crc32d(c, chunk[1]);
            c = arch::__crc32d(c, chunk[2]);
            c = arch::__crc32d(c, chunk[3]);
            c = arch::__crc32d(c, chunk[4]);
            c = arch::__crc32d(c, chunk[5]);
            c = arch::__crc32d(c, chunk[6]);
            c = arch::__crc32d(c, chunk[7]);
            done = snapshot!((*done).concat(Seq::singleton(chunk)));
        }
        proof_assert! { done.len() == q0.chunks().len() && quad_iter.rem() == q0.rem() };
        snapshot! { chain(!crc, quads@, 8 * q0.chunks().len(), quads@.len() - 8 * q0.chunks().len()) };
        snapshot! { sub_full(quads@) };
        c = quad_iter
            .remainder()
            .iter()
            .fold(c, |acc, &q| arch::__crc32d(acc, q));

        !c
    }

    #[ensures(calc_ok(crc, data@, result))]
    // verbatim: patched src/specialized/aarch64.rs pub unsafe fn calculate(crc: u32, data: &[u8]) -> u32 {
    pub unsafe fn calculate(crc: u32, data: &[u8]) -> u32 {
        let (pre_quad, quads, post_quad) = split_quads(data);

        // Running (finalized) CRC.
        let mut r = crc;

        // Unaligned leading bytes.
        r = crc_bytes(r, pre_quad);

        if quads.len() >= MIN_TRIPLE_QUADS {
            // A single `crc32d` chain is latency-bound: each instruction depends on the previous
            // result. Splitting the aligned region into three equal, contiguous blocks and advancing
            // three independent accumulators in lockstep keeps several `crc32d` in flight, then
            // `combine` reassembles them (appending the zero-seeded later blocks to the first).
            let n3 = quads.len() / 3;
            let block_len = (n3 * 8) as u64;

            let a = &quads[0..n3];
            let b = &quads[n3..2 * n3];
            let c = &quads[2 * n3..3 * n3];

            // Internal (bit-inverted) states. A carries the running CRC; B and C start from zero.
            let mut c0 = !r;
            let mut c1 = !0u32;
            let mut c2 = !0u32;

            // Unroll each stream by 4 while keeping the three chains independent.
            // Verification patch: the `chunks_exact(4)` + `zip` loops written with an index (Aeneas
            // cannot translate `for` over `&mut` iterators). `a`, `b`, `c` all have length `n3`, so
            // this makes the same `__crc32d` calls in the same order: full chunks of 4, then the
            // `n3 % 4` remainder words.
            let mut i = 0;
            snapshot! { fold_steps(a@) };
            snapshot! { fold_steps(b@) };
            snapshot! { fold_steps(c@) };
            let r0 = snapshot!(r);
            #[invariant(i@ <= n3@)]
            #[invariant(c0 == fold_d(!*r0, a@.subsequence(0, i@)))]
            #[invariant(c1 == fold_d(!0u32, b@.subsequence(0, i@)))]
            #[invariant(c2 == fold_d(!0u32, c@.subsequence(0, i@)))]
            #[variant(n3@ - i@)]
            while i + 4 <= n3 {
                #[invariant(c0 == fold_d(!*r0, a@.subsequence(0, i@ + produced.len())))]
                #[invariant(c1 == fold_d(!0u32, b@.subsequence(0, i@ + produced.len())))]
                #[invariant(c2 == fold_d(!0u32, c@.subsequence(0, i@ + produced.len())))]
                #[variant(4 - produced.len())]
                for k in 0..4 {
                    c0 = arch::__crc32d(c0, a[i + k]);
                    c1 = arch::__crc32d(c1, b[i + k]);
                    c2 = arch::__crc32d(c2, c[i + k]);
                }
                i += 4;
            }
            #[invariant(i@ <= n3@)]
            #[invariant(c0 == fold_d(!*r0, a@.subsequence(0, i@)))]
            #[invariant(c1 == fold_d(!0u32, b@.subsequence(0, i@)))]
            #[invariant(c2 == fold_d(!0u32, c@.subsequence(0, i@)))]
            #[variant(n3@ - i@)]
            while i < n3 {
                c0 = arch::__crc32d(c0, a[i]);
                c1 = arch::__crc32d(c1, b[i]);
                c2 = arch::__crc32d(c2, c[i]);
                i += 1;
            }
            snapshot! { sub_full(a@) };
            snapshot! { sub_full(b@) };
            snapshot! { sub_full(c@) };

            r = crate::combine::combine(!c0, !c1, block_len);
            r = crate::combine::combine(r, !c2, block_len);

            // Words left over after the three equal blocks.
            r = crc_quads(r, &quads[3 * n3..]);
        } else {
            r = crc_quads(r, quads);
        }

        // Unaligned trailing bytes.
        crc_bytes(r, post_quad)
    }
}
