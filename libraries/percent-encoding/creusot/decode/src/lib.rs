// Gate 1, decoder side (percent-encoding 2.3.2). For each function rewritten by
// rust/aeneas-friendly.patch, the original upstream body (mod orig) and the patched body
// (mod patched) are both proved to meet one exact spec, so they agree on every input:
//   Iterator for PercentDecode::next   Option::map with a closure vs match           spec: dstep
//   PercentDecode::if_any              while any(..) with early return vs decode_if_any  spec: if_any_ok
// `after_percent_sign`, identical in both trees, is proved here too (including no overflow).
// Bodies marked `// verbatim:` are checked by check_verbatim.py. Trusted facts: see README.md.
#![allow(unused)]
use creusot_std::prelude::{Clone, *};
use core::slice;

// ---------------------------------------------------------------- trusted std facts
// char::from(u8): the char with that code point (every u8 is one).
#[trusted]
#[logic(opaque)]
#[ensures(result@ == b@)]
pub fn char_from(b: u8) -> char {
    dead
}

// char::to_digit(radix): opaque, except that a digit is always below the radix (std docs).
#[trusted]
#[logic(opaque)]
#[ensures(match result { Some(d) => d@ < radix@, None => true })]
pub fn digit(c: char, radix: u32) -> Option<u32> {
    dead
}

extern_spec! {
    impl<'a, T> Clone for slice::Iter<'a, T> {
        #[check(ghost)]
        #[ensures(result == *self)]
        fn clone(&self) -> slice::Iter<'a, T>;
    }
    impl From<u8> for char {
        #[check(ghost)]
        #[ensures(result == char_from(b))]
        fn from(b: u8) -> char;
    }
    impl char {
        #[check(ghost)]
        #[ensures(result == digit(self, radix))]
        fn to_digit(self, radix: u32) -> Option<u32>;
    }
    impl<T: Clone> ToOwned for [T] {
        #[ensures(result@.len() == self@.len())]
        #[ensures(forall<i> 0 <= i && i < self@.len() ==> T::clone.postcondition((&self@[i],), result@[i]))]
        fn to_owned(&self) -> Vec<T>;
    }
    // std: `any` consumes items up to and including the first one where `f` is true.
    // Stated for closures whose call leaves their state unchanged (here `|&b| b == b'%'`).
    impl<'a, T> Iterator for slice::Iter<'a, T> {
        #[requires(forall<x: &'a T> f.precondition((x,)))]
        #[requires(forall<x: &'a T, g: F, r: bool> f.postcondition_mut((x,), g, r) ==> g == f)]
        #[ensures(exists<k: Int> 0 <= k && k <= (*self)@@.len()
            && (^self)@@ == (*self)@@.subsequence(k, (*self)@@.len())
            && (forall<j: Int> 0 <= j && j < k && !(result && j == k - 1) ==>
                    f.postcondition_mut(((*self)@.to_ref_seq()[j],), f, false))
            && (result ==> k >= 1 && f.postcondition_mut(((*self)@.to_ref_seq()[k - 1],), f, true))
            && (!result ==> k == (*self)@@.len()))]
        fn any<F>(&mut self, f: F) -> bool
        where
            Self: Sized,
            F: FnMut(&'a T) -> bool;
    }
}

// ---------------------------------------------------------------- one decoding step
// Value of "%XY" given X and Y, if both are hex digits.
#[logic(open)]
pub fn hex2(a: u8, b: u8) -> Option<Int> {
    pearlite! {
        match (digit(char_from(a), 16u32), digit(char_from(b), 16u32)) {
            (Some(h), Some(l)) => Some(h@ * 16 + l@),
            _ => None,
        }
    }
}

// One decoding step on the remaining input: the byte produced and the rest.
#[logic(open)]
pub fn dstep(s: Seq<u8>) -> Option<(Int, Seq<u8>)> {
    pearlite! {
        if s.len() == 0 { None }
        else if s[0]@ == 37 && s.len() >= 3 && hex2(s[1], s[2]) != None {
            match hex2(s[1], s[2]) { Some(v) => Some((v, s.subsequence(3, s.len()))), None => None }
        } else { Some((s[0]@, s.tail())) }
    }
}

// One step of a byte-slice iterator: the first element, then the tail.
#[logic]
#[ensures(forall<it: slice::Iter<'a, u8>, r: &'a u8, it2: slice::Iter<'a, u8>>
    it.produces(Seq::singleton(r), it2) ==>
    it@@.len() > 0 && *r == it@@[0] && it2@@ == it@@.tail())]
pub fn iter_step<'a>() {
    pearlite! {
        proof_assert! { forall<it: slice::Iter<'a, u8>, r: &'a u8, it2: slice::Iter<'a, u8>>
            it.produces(Seq::singleton(r), it2) ==>
              it@@.len() == 1 + it2@@.len()
              && (forall<i: Int> 0 <= i && i < it2@@.len() ==> it2@@[i] == it@@.tail()[i])
              && it2@@.ext_eq(it@@.tail()) };
        ()
    }
}

// Index facts about the tail of a byte sequence.
#[logic]
#[ensures(forall<s: Seq<u8>> s.len() > 0 ==>
    s.tail().len() == s.len() - 1
    && (forall<i: Int> 0 <= i && i < s.len() - 1 ==> s.tail()[i] == s[i + 1])
    && (s.len() >= 3 ==> s.tail().subsequence(2, s.tail().len()) == s.subsequence(3, s.len())))]
pub fn tail_facts() {
    pearlite! {
        proof_assert! { forall<s: Seq<u8>> s.len() >= 3 ==>
            s.tail().subsequence(2, s.tail().len()).ext_eq(s.subsequence(3, s.len())) };
        ()
    }
}

// ---------------------------------------------------------------- the whole decoding
// State after n steps (None if the iterator stopped earlier) and the n-th byte produced.
#[logic(open)]
#[variant(n)]
pub fn dstate(s: Seq<u8>, n: Int) -> Option<Seq<u8>> {
    pearlite! {
        if n <= 0 { Some(s) } else { match dstep(s) { None => None, Some((_, r)) => dstate(r, n - 1) } }
    }
}

#[logic(open)]
#[variant(n)]
pub fn dval(s: Seq<u8>, n: Int) -> Int {
    pearlite! {
        match dstep(s) { None => 0, Some((v, r)) => if n <= 0 { v } else { dval(r, n - 1) } }
    }
}

#[logic]
#[variant(n)]
#[requires(n >= 0)]
#[ensures(match dstate(s, n) {
    None => true,
    Some(r) => forall<m: Int> m >= 0 ==> dstate(s, n + m) == dstate(r, m) && dval(s, n + m) == dval(r, m)
})]
pub fn dcompose(s: Seq<u8>, n: Int) {
    pearlite! {
        if n == 0 { () } else { match dstep(s) { None => (), Some((_, r)) => dcompose(r, n - 1) } }
    }
}

// Number of bytes the decoder produces.
#[logic(open)]
#[variant(s.len())]
pub fn dcount(s: Seq<u8>) -> Int {
    pearlite! { match dstep(s) { None => 0, Some((_, r)) => 1 + dcount(r) } }
}

#[logic]
#[variant(s.len())]
#[ensures(dcount(s) >= 0)]
#[ensures(dstate(s, dcount(s)) == Some(Seq::empty()))]
#[ensures(forall<n: Int> n >= 0 ==> match dstate(s, n) {
    None => n > dcount(s), Some(r) => n <= dcount(s) && (r.len() == 0 ==> n == dcount(s)) })]
pub fn dcount_spec(s: Seq<u8>) {
    pearlite! {
        match dstep(s) {
            None => { proof_assert! { s == Seq::empty() }; () },
            Some((_, r)) => dcount_spec(r),
        }
    }
}

// `v` is the full decoding of `s`.
#[logic(open)]
pub fn decodes(s: Seq<u8>, v: Seq<u8>) -> bool {
    pearlite! { v.len() == dcount(s) && forall<j: Int> 0 <= j && j < v.len() ==> v[j]@ == dval(s, j) }
}

// ---------------------------------------------------------------- if_any
// Index of the first '%' followed by two hex digits, at or after i (s.len() if none).
#[logic(open)]
#[variant(s.len() - i)]
pub fn first_pct(s: Seq<u8>, i: Int) -> Int {
    pearlite! {
        if i < 0 || i >= s.len() { s.len() }
        else if s[i]@ == 37 && i + 2 < s.len() && hex2(s[i + 1], s[i + 2]) != None { i }
        else { first_pct(s, i + 1) }
    }
}

#[logic]
#[variant(s.len() - i)]
#[requires(0 <= i)]
#[ensures(i <= first_pct(s, i) || i >= s.len())]
#[ensures(first_pct(s, i) <= s.len())]
#[ensures(first_pct(s, i) < s.len() ==> s[first_pct(s, i)]@ == 37
    && first_pct(s, i) + 2 < s.len() && hex2(s[first_pct(s, i) + 1], s[first_pct(s, i) + 2]) != None)]
#[ensures(forall<j: Int> i <= j && j < s.len() && s[j]@ != 37 ==> first_pct(s, j) == first_pct(s, j + 1))]
#[ensures(forall<a: Int, b: Int> i <= a && a <= b && b <= s.len()
    && (forall<j: Int> a <= j && j < b ==> s[j]@ != 37) ==> first_pct(s, a) == first_pct(s, b))]
pub fn first_pct_spec(s: Seq<u8>, i: Int) {
    pearlite! { if i >= s.len() { () } else { first_pct_spec(s, i + 1) } }
}

#[logic(open)]
pub fn opt_view(r: Option<Vec<u8>>) -> Option<Seq<u8>> {
    pearlite! { match r { None => None, Some(v) => Some(v@) } }
}

// decode_from_percent's result for a '%' at index q of s.
#[logic(open)]
pub fn dfp_ok(s: Seq<u8>, q: Int, r: Option<Seq<u8>>) -> bool {
    pearlite! {
        match r {
            None => !(q + 2 < s.len() && hex2(s[q + 1], s[q + 2]) != None),
            Some(v) => q + 2 < s.len() && {
                let rest = s.subsequence(q + 3, s.len());
                v.len() == q + 1 + dcount(rest)
                && (forall<j: Int> 0 <= j && j < q ==> v[j] == s[j])
                && hex2(s[q + 1], s[q + 2]) == Some(v[q]@)
                && (forall<j: Int> 0 <= j && j < dcount(rest) ==> v[q + 1 + j]@ == dval(rest, j))
            }
        }
    }
}

// position_of_percent on the suffix r = s[p..], read in terms of s.
#[logic]
#[requires(0 <= p && p <= s.len())]
#[ensures((forall<j: Int> 0 <= j && j < s.subsequence(p, s.len()).len() ==> s.subsequence(p, s.len())[j]@ != 37)
    ==> first_pct(s, p) == s.len())]
#[ensures(forall<i: Int> 0 <= i && i < s.subsequence(p, s.len()).len() && s.subsequence(p, s.len())[i]@ == 37
    && (forall<j: Int> 0 <= j && j < i ==> s.subsequence(p, s.len())[j]@ != 37) ==>
        s[p + i]@ == 37 && first_pct(s, p) == first_pct(s, p + i)
        && s.subsequence(p, s.len()).subsequence(i + 1, s.subsequence(p, s.len()).len()) == s.subsequence(p + i + 1, s.len()))]
pub fn pos_lemma(s: Seq<u8>, p: Int) {
    pearlite! {
        let _ = first_pct_spec(s, 0);
        proof_assert! { forall<j: Int> 0 <= j && j < s.len() - p ==> s.subsequence(p, s.len())[j] == s[p + j] };
        proof_assert! { forall<i: Int> 0 <= i && i < s.len() - p ==>
            s.subsequence(p, s.len()).subsequence(i + 1, s.len() - p).ext_eq(s.subsequence(p + i + 1, s.len())) };
        proof_assert! { forall<j: Int> p <= j && j < s.len() ==> s[j] == s.subsequence(p, s.len())[j - p] };
        proof_assert! { (forall<j: Int> 0 <= j && j < s.len() - p ==> s.subsequence(p, s.len())[j]@ != 37)
            ==> (forall<j: Int> p <= j && j < s.len() ==> s[j]@ != 37) };
        proof_assert! { forall<i: Int> 0 <= i && i < s.len() - p
            && (forall<j: Int> 0 <= j && j < i ==> s.subsequence(p, s.len())[j]@ != 37)
            ==> (forall<j: Int> p <= j && j < p + i ==> s[j]@ != 37) };
        ()
    }
}

// What if_any returns for input s: None when decoding changes nothing, else the decoding.
#[logic(open)]
pub fn if_any_ok(s: Seq<u8>, r: Option<Seq<u8>>) -> bool {
    pearlite! {
        let i = first_pct(s, 0);
        if i >= s.len() { r == None } else {
            match r {
                None => false,
                Some(v) => {
                    let rest = s.subsequence(i + 3, s.len());
                    v.len() == i + 1 + dcount(rest)
                    && (forall<j: Int> 0 <= j && j < i ==> v[j] == s[j])
                    && hex2(s[i + 1], s[i + 2]) == Some(v[i]@)
                    && (forall<j: Int> 0 <= j && j < dcount(rest) ==> v[i + 1 + j]@ == dval(rest, j))
                }
            }
        }
    }
}

// ---------------------------------------------------------------- shared callee (verbatim)
#[ensures(match result {
    Some(v) => (*iter)@@.len() >= 2 && hex2((*iter)@@[0], (*iter)@@[1]) == Some(v@)
               && (^iter)@@ == (*iter)@@.subsequence(2, (*iter)@@.len()),
    None => !((*iter)@@.len() >= 2 && hex2((*iter)@@[0], (*iter)@@[1]) != None) && ^iter == *iter,
})]
// verbatim: both src/lib.rs fn after_percent_sign(iter: &mut slice::Iter<'_, u8>) -> Option<u8> {
fn after_percent_sign(iter: &mut slice::Iter<'_, u8>) -> Option<u8> {
    let mut cloned_iter = iter.clone();
    let h = char::from(*cloned_iter.next()?).to_digit(16)?;
    let l = char::from(*cloned_iter.next()?).to_digit(16)?;
    *iter = cloned_iter;
    Some(h as u8 * 0x10 + l as u8)
}

// ---------------------------------------------------------------- original upstream code
pub mod orig {
    use super::*;

    pub struct PercentDecode<'a> {
        bytes: slice::Iter<'a, u8>,
    }

    impl<'a> IteratorSpec for PercentDecode<'a> {
        #[logic(open(self), prophetic)]
        fn produces(self, visited: Seq<u8>, o: Self) -> bool {
            pearlite! {
                dstate(self.bytes@@, visited.len()) == Some(o.bytes@@)
                && forall<i: Int> 0 <= i && i < visited.len() ==> visited[i]@ == dval(self.bytes@@, i)
            }
        }

        #[logic(open(self), prophetic)]
        fn completed(&mut self) -> bool {
            pearlite! { (*self).bytes@@.len() == 0 && resolve(self) }
        }

        #[logic(law)]
        #[ensures(self.produces(Seq::empty(), self))]
        fn produces_refl(self) {}

        #[logic(law)]
        #[requires(a.produces(ab, b))]
        #[requires(b.produces(bc, c))]
        #[ensures(a.produces(ab.concat(bc), c))]
        fn produces_trans(a: Self, ab: Seq<u8>, b: Self, bc: Seq<u8>, c: Self) {
            pearlite! { dcompose(a.bytes@@, ab.len()) }
        }
    }

    impl Iterator for PercentDecode<'_> {
        type Item = u8;

        #[ensures(match result {
            None => dstep(self.bytes@@) == None,
            Some(v) => dstep(self.bytes@@) == Some((v@, (^self).bytes@@)),
        })]
        #[ensures(match result { None => self.completed(), Some(v) => (*self).produces(Seq::singleton(v), ^self) })]
        // verbatim: upstream src/lib.rs fn next(&mut self) -> Option<u8> {
        fn next(&mut self) -> Option<u8> {
            snapshot! { iter_step() };
            snapshot! { tail_facts() };
            self.bytes.next().map(|&byte| {
                if byte == b'%' {
                    after_percent_sign(&mut self.bytes).unwrap_or(byte)
                } else {
                    byte
                }
            })
        }
    }

    impl<'a> PercentDecode<'a> {
        #[ensures(if_any_ok(self.bytes@@, opt_view(result)))]
        // verbatim: upstream src/lib.rs fn if_any(&self) -> Option<Vec<u8>> {
        fn if_any(&self) -> Option<Vec<u8>> {
            snapshot! { first_pct_spec(self.bytes@@, 0) };
            snapshot! { tail_facts() };
            let mut bytes_iter = self.bytes.clone();
            let mut prev = snapshot!(bytes_iter);
            #[invariant(*prev == bytes_iter)]
            #[invariant(bytes_iter@@.len() <= self.bytes@@.len())]
            #[invariant(bytes_iter@@ == self.bytes@@.subsequence(self.bytes@@.len() - bytes_iter@@.len(), self.bytes@@.len()))]
            #[invariant(first_pct(self.bytes@@, 0) == first_pct(self.bytes@@, self.bytes@@.len() - bytes_iter@@.len()))]
            #[variant(bytes_iter@@.len())]
            while bytes_iter.any(|&b| b == b'%') {
                proof_assert! { bytes_iter@@.len() < prev@@.len() };
                proof_assert! { forall<j: Int> 0 <= j && j < prev@@.len() - bytes_iter@@.len() - 1 ==> prev@@[j]@ != 37 };
                proof_assert! { prev@@[prev@@.len() - bytes_iter@@.len() - 1]@ == 37 };
                proof_assert! { bytes_iter@@.len() < self.bytes@@.len() };
                proof_assert! { bytes_iter@@ == self.bytes@@.subsequence(self.bytes@@.len() - bytes_iter@@.len(), self.bytes@@.len()) };
                proof_assert! { self.bytes@@[self.bytes@@.len() - bytes_iter@@.len() - 1]@ == 37 };
                proof_assert! { prev@@ == self.bytes@@.subsequence((self.bytes@@.len() - prev@@.len()), self.bytes@@.len()) };
                proof_assert! { forall<j: Int> (self.bytes@@.len() - prev@@.len()) <= j && j < (self.bytes@@.len() - bytes_iter@@.len() - 1) ==> self.bytes@@[j] == prev@@[j - (self.bytes@@.len() - prev@@.len())] };
                proof_assert! { forall<j: Int> (self.bytes@@.len() - prev@@.len()) <= j && j < (self.bytes@@.len() - bytes_iter@@.len() - 1) ==> self.bytes@@[j]@ != 37 };
                proof_assert! { first_pct(self.bytes@@, (self.bytes@@.len() - prev@@.len())) == first_pct(self.bytes@@, (self.bytes@@.len() - bytes_iter@@.len() - 1)) };
                proof_assert! { first_pct(self.bytes@@, 0) == first_pct(self.bytes@@, self.bytes@@.len() - bytes_iter@@.len() - 1) };
                if let Some(decoded_byte) = after_percent_sign(&mut bytes_iter) {
                    let initial_bytes = self.bytes.as_slice();
                    proof_assert! { bytes_iter@@ == self.bytes@@.subsequence(first_pct(self.bytes@@, 0) + 3, self.bytes@@.len()) };
                    let unchanged_bytes_len = initial_bytes.len() - bytes_iter.len() - 3;
                    proof_assert! { unchanged_bytes_len@ == first_pct(self.bytes@@, 0) };
                    let mut decoded = initial_bytes[..unchanged_bytes_len].to_owned();
                    proof_assert! { decoded@.len() == first_pct(self.bytes@@, 0) && forall<j: Int> 0 <= j && j < first_pct(self.bytes@@, 0) ==> decoded@[j] == self.bytes@@[j] };
                    decoded.push(decoded_byte);
                    proof_assert! { decoded@.len() == first_pct(self.bytes@@, 0) + 1 && decoded@[first_pct(self.bytes@@, 0)] == decoded_byte };
                    snapshot! { dcount_spec(bytes_iter@@) };
                    let pre = snapshot!(decoded@);
                    decoded.extend(PercentDecode { bytes: bytes_iter });
                    proof_assert! { forall<j: Int> 0 <= j && j < pre.len() ==> decoded@[j] == pre[j] };
                    proof_assert! { decoded@.len() == first_pct(self.bytes@@, 0) + 1 + dcount(self.bytes@@.subsequence(first_pct(self.bytes@@, 0) + 3, self.bytes@@.len())) };
                    proof_assert! { forall<j: Int> 0 <= j && j < dcount(self.bytes@@.subsequence(first_pct(self.bytes@@, 0) + 3, self.bytes@@.len())) ==> decoded@[first_pct(self.bytes@@, 0) + 1 + j]@ == dval(self.bytes@@.subsequence(first_pct(self.bytes@@, 0) + 3, self.bytes@@.len()), j) };
                    proof_assert! { hex2(self.bytes@@[first_pct(self.bytes@@, 0) + 1], self.bytes@@[first_pct(self.bytes@@, 0) + 2]) == Some(decoded_byte@) };
                    proof_assert! { forall<j: Int> 0 <= j && j < first_pct(self.bytes@@, 0) ==> decoded@[j] == self.bytes@@[j] };
                    proof_assert! { decoded@[first_pct(self.bytes@@, 0)] == decoded_byte };
                    return Some(decoded);
                }
                prev = snapshot!(bytes_iter);
            }
            proof_assert! { forall<j: Int> 0 <= j && j < prev@@.len() ==> prev@@[j]@ != 37 };
            proof_assert! { bytes_iter@@.len() == 0 };
            proof_assert! { prev@@ == self.bytes@@.subsequence((self.bytes@@.len() - prev@@.len()), self.bytes@@.len()) };
            proof_assert! { forall<j: Int> (self.bytes@@.len() - prev@@.len()) <= j && j < self.bytes@@.len() ==> self.bytes@@[j] == prev@@[j - (self.bytes@@.len() - prev@@.len())] };
            proof_assert! { forall<j: Int> (self.bytes@@.len() - prev@@.len()) <= j && j < self.bytes@@.len() ==> self.bytes@@[j]@ != 37 };
            proof_assert! { first_pct(self.bytes@@, (self.bytes@@.len() - prev@@.len())) == first_pct(self.bytes@@, self.bytes@@.len()) };
            proof_assert! { first_pct(self.bytes@@, 0) == self.bytes@@.len() };
            // Nothing to decode
            None
        }
    }
}

// ---------------------------------------------------------------- patched code
pub mod patched {
    use super::*;

    pub struct PercentDecode<'a> {
        bytes: slice::Iter<'a, u8>,
    }

    impl<'a> IteratorSpec for PercentDecode<'a> {
        #[logic(open(self), prophetic)]
        fn produces(self, visited: Seq<u8>, o: Self) -> bool {
            pearlite! {
                dstate(self.bytes@@, visited.len()) == Some(o.bytes@@)
                && forall<i: Int> 0 <= i && i < visited.len() ==> visited[i]@ == dval(self.bytes@@, i)
            }
        }

        #[logic(open(self), prophetic)]
        fn completed(&mut self) -> bool {
            pearlite! { (*self).bytes@@.len() == 0 && resolve(self) }
        }

        #[logic(law)]
        #[ensures(self.produces(Seq::empty(), self))]
        fn produces_refl(self) {}

        #[logic(law)]
        #[requires(a.produces(ab, b))]
        #[requires(b.produces(bc, c))]
        #[ensures(a.produces(ab.concat(bc), c))]
        fn produces_trans(a: Self, ab: Seq<u8>, b: Self, bc: Seq<u8>, c: Self) {
            pearlite! { dcompose(a.bytes@@, ab.len()) }
        }
    }

    impl Iterator for PercentDecode<'_> {
        type Item = u8;

        #[ensures(match result {
            None => dstep(self.bytes@@) == None,
            Some(v) => dstep(self.bytes@@) == Some((v@, (^self).bytes@@)),
        })]
        #[ensures(match result { None => self.completed(), Some(v) => (*self).produces(Seq::singleton(v), ^self) })]
        // verbatim: patched src/lib.rs fn next(&mut self) -> Option<u8> {
        fn next(&mut self) -> Option<u8> {
            snapshot! { iter_step() };
            snapshot! { tail_facts() };
            // AENEAS PATCH: `Option::map` with a closure is replaced by a `match`.
            match self.bytes.next() {
                Some(&byte) => Some(if byte == b'%' {
                    after_percent_sign(&mut self.bytes).unwrap_or(byte)
                } else {
                    byte
                }),
                None => None,
            }
        }
    }

    impl<'a> PercentDecode<'a> {
        #[ensures(if_any_ok(self.bytes@@, opt_view(result)))]
        // verbatim: patched src/lib.rs fn if_any(&self) -> Option<Vec<u8>> {
        fn if_any(&self) -> Option<Vec<u8>> {
            // AENEAS PATCH: the body moved to `decode_if_any` (below), which takes
            // the remaining input as a slice.
            decode_if_any(self.bytes.as_slice())
        }
    }

    #[ensures(if_any_ok(initial_bytes@, opt_view(result)))]
    // verbatim: patched src/lib.rs fn decode_if_any(initial_bytes: &[u8]) -> Option<Vec<u8>> {
    fn decode_if_any(initial_bytes: &[u8]) -> Option<Vec<u8>> {
        snapshot! { first_pct_spec(initial_bytes@, 0) };
        let mut rest = initial_bytes;
        let mut result = None;
        let mut done = false;
        #[invariant(rest@.len() <= initial_bytes@.len())]
        #[invariant(rest@ == initial_bytes@.subsequence(initial_bytes@.len() - rest@.len(), initial_bytes@.len()))]
        #[invariant(!done ==> result == None
            && first_pct(initial_bytes@, 0) == first_pct(initial_bytes@, initial_bytes@.len() - rest@.len()))]
        #[invariant(done ==> if_any_ok(initial_bytes@, opt_view(result)))]
        #[variant(rest@.len() * 2 + if done { 0 } else { 1 })]
        while !done {
            snapshot! { pos_lemma(initial_bytes@, initial_bytes@.len() - rest@.len()) };
            match position_of_percent(rest) {
                // Nothing to decode
                None => done = true,
                Some(i) => {
                    match decode_from_percent(initial_bytes, &rest[i + 1..]) {
                        Some(decoded) => {
                            result = Some(decoded);
                            done = true;
                        }
                        // `after_percent_sign` failed and consumed nothing.
                        None => rest = &rest[i + 1..],
                    }
                }
            }
        }
        result
    }

    #[requires(after@.len() < initial_bytes@.len() && initial_bytes@[(initial_bytes@.len() - after@.len() - 1)]@ == 37
        && after@ == initial_bytes@.subsequence((initial_bytes@.len() - after@.len() - 1) + 1, initial_bytes@.len()))]
    #[ensures(dfp_ok(initial_bytes@, (initial_bytes@.len() - after@.len() - 1), opt_view(result)))]
    // verbatim: patched src/lib.rs fn decode_from_percent(initial_bytes: &[u8], after: &[u8]) -> Option<Vec<u8>> {
    fn decode_from_percent(initial_bytes: &[u8], after: &[u8]) -> Option<Vec<u8>> {
        let mut bytes_iter = after.iter();
        match after_percent_sign(&mut bytes_iter) {
            Some(decoded_byte) => {
                let unchanged_bytes_len = initial_bytes.len() - bytes_iter.len() - 3;
                let mut decoded = initial_bytes[..unchanged_bytes_len].to_owned();
                proof_assert! { unchanged_bytes_len@ == (initial_bytes@.len() - after@.len() - 1) };
                proof_assert! { bytes_iter@@ == initial_bytes@.subsequence((initial_bytes@.len() - after@.len() - 1) + 3, initial_bytes@.len()) };
                proof_assert! { decoded@.len() == (initial_bytes@.len() - after@.len() - 1) && forall<j: Int> 0 <= j && j < (initial_bytes@.len() - after@.len() - 1) ==> decoded@[j] == initial_bytes@[j] };
                decoded.push(decoded_byte);
                proof_assert! { decoded@.len() == (initial_bytes@.len() - after@.len() - 1) + 1 && decoded@[(initial_bytes@.len() - after@.len() - 1)] == decoded_byte };
                snapshot! { dcount_spec(bytes_iter@@) };
                let pre = snapshot!(decoded@);
                decoded.extend(PercentDecode { bytes: bytes_iter });
                proof_assert! { forall<j: Int> 0 <= j && j < pre.len() ==> decoded@[j] == pre[j] };
                proof_assert! { decoded@.len() == (initial_bytes@.len() - after@.len() - 1) + 1 + dcount(initial_bytes@.subsequence((initial_bytes@.len() - after@.len() - 1) + 3, initial_bytes@.len())) };
                proof_assert! { forall<j: Int> 0 <= j && j < dcount(initial_bytes@.subsequence((initial_bytes@.len() - after@.len() - 1) + 3, initial_bytes@.len())) ==> decoded@[(initial_bytes@.len() - after@.len() - 1) + 1 + j]@ == dval(initial_bytes@.subsequence((initial_bytes@.len() - after@.len() - 1) + 3, initial_bytes@.len()), j) };
                proof_assert! { forall<j: Int> 0 <= j && j < (initial_bytes@.len() - after@.len() - 1) ==> decoded@[j] == initial_bytes@[j] };
                Some(decoded)
            }
            None => None,
        }
    }

    #[ensures(match result {
        None => forall<j: Int> 0 <= j && j < bytes@.len() ==> bytes@[j]@ != 37,
        Some(i) => i@ < bytes@.len() && bytes@[i@]@ == 37
                   && forall<j: Int> 0 <= j && j < i@ ==> bytes@[j]@ != 37,
    })]
    // verbatim: patched src/lib.rs fn position_of_percent(bytes: &[u8]) -> Option<usize> {
    fn position_of_percent(bytes: &[u8]) -> Option<usize> {
        let mut i = 0;
        #[invariant(i@ <= bytes@.len())]
        #[invariant(forall<j: Int> 0 <= j && j < i@ ==> bytes@[j]@ != 37)]
        #[variant(bytes@.len() - i@)]
        while i < bytes.len() && bytes[i] != b'%' {
            i += 1;
        }
        if i < bytes.len() {
            Some(i)
        } else {
            None
        }
    }
}
