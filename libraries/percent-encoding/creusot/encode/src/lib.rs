// Gate 1, encoder side (percent-encoding 2.3.2). For each function rewritten by
// rust/aeneas-friendly.patch, the original upstream body and the patched body are both proved to
// meet one exact spec, so they agree on every input:
//   Iterator for PercentEncode::next   original vs patched next + next_chunk   spec: chunk_ok / step
//   Display for PercentEncode::fmt     original vs patched fmt + write_chunks  spec: display_ok
// Bodies marked `// verbatim:` are checked against the pinned sources by check_verbatim.py: only
// spec attributes, `#[invariant]`/`#[variant]` and ghost `snapshot!`/`proof_assert!` lines differ.
// Trusted facts are marked T1-T4 below and listed in README.md.
#![allow(unused)]
use creusot_std::prelude::{Clone, *};
use core::str;
use creusot_std::std::string::injective_to_bytes;
use creusot_std::std::slice::SliceIndexSpec;
use creusot_std::std::fmt::{sink_after, sink_ok};
use core::fmt;
use core::fmt::Write;

// ---------------------------------------------------------------- trusted facts (listed in CLAIM)
// T1 (UTF-8 definition): every byte b < 128 is the code point of a char whose UTF-8 encoding is
// the single byte b.
#[trusted]
#[logic(opaque)]
#[ensures(b@ < 128 ==> result@ == b@ && result.to_utf8() == Seq::singleton(b))]
pub fn ascii_char(b: u8) -> char {
    dead
}

// T2 (std contracts, as documented).
extern_spec! {
    mod core {
        mod str {
            #[check(ghost)]
            #[requires(exists<s: Seq<char>> s.to_bytes() == v@)]
            #[ensures(result@.to_bytes() == v@)]
            unsafe fn from_utf8_unchecked(v: &[u8]) -> &str;
        }
    }
    impl<T> [T] {
        #[check(ghost)]
        #[ensures(match result {
            Some((first, tail)) => self@.len() > 0 && *first == self@[0] && tail@ == self@.tail(),
            None => self@.len() == 0,
        })]
        fn split_first(&self) -> Option<(&T, &[T])>;
    }
    mod core { mod fmt {
        trait Write {
            #[ensures(&^self == sink_after(&*self, s@))]
            #[ensures((result == Ok(())) == sink_ok(&*self, s@))]
            fn write_str(&mut self, s: &str) -> fmt::Result;
        }
    } }
    impl u8 {
        #[check(ghost)]
        #[ensures(result == (self@ < 128))]
        fn is_ascii(&self) -> bool;
    }
    // std: `impl Index<I> for [T; N] where [T]: Index<I>` forwards to the slice impl.
    impl<T, I, const N: usize> core::ops::Index<I> for [T; N]
    where
        [T]: core::ops::Index<I>,
        I: SliceIndexSpec<[T], Output = <[T] as core::ops::Index<I>>::Output>,
    {
        #[check(ghost)]
        #[requires(ix.in_bounds(self@))]
        #[ensures(ix.has_value(self@, *result))]
        fn index(&self, ix: I) -> &<[T] as core::ops::Index<I>>::Output;
    }
}

// ---------------------------------------------------------------- ASCII bytes are valid UTF-8
#[logic(open)]
#[variant(s.len())]
pub fn ascii_str(s: Seq<u8>) -> Seq<char> {
    pearlite! {
        if s.len() == 0 { Seq::empty() }
        else { Seq::singleton(ascii_char(s[0])).concat(ascii_str(s.tail())) }
    }
}

#[logic]
#[variant(s.len())]
#[requires(forall<i: Int> 0 <= i && i < s.len() ==> s[i]@ < 128)]
#[ensures(ascii_str(s).to_bytes() == s)]
pub fn ascii_str_bytes(s: Seq<u8>) {
    pearlite! {
        if s.len() == 0 { () } else {
            let _ = ascii_str_bytes(s.tail());
            let t = ascii_str(s.tail());
            proof_assert! { Seq::singleton(ascii_char(s[0])).concat(t).tail() == t };
            proof_assert! { Seq::singleton(ascii_char(s[0])).concat(t)[0] == ascii_char(s[0]) };
            proof_assert! { Seq::singleton(s[0]).concat(s.tail()) == s };
            ()
        }
    }
}

#[logic]
#[requires(forall<i: Int> 0 <= i && i < s.len() ==> s[i]@ < 128)]
#[ensures(exists<t: Seq<char>> t.to_bytes() == s)]
pub fn ascii_valid(s: Seq<u8>) {
    pearlite! { ascii_str_bytes(s) }
}

// ---------------------------------------------------------------- callees, shared by both versions
pub struct AsciiSet {
    mask: [u32; 4],
}

impl AsciiSet {
    // Which ASCII bytes the set contains. Opaque on purpose: equivalence needs only that both
    // versions ask the same question of the same set. Its meaning is proved in Lean (contains_spec).
    #[logic(opaque)]
    pub fn contains_l(self, b: u8) -> bool {
        dead
    }

    #[logic(open)]
    pub fn enc(self, b: u8) -> bool {
        pearlite! { !(b@ < 128) || self.contains_l(b) }
    }

    // T3: `contains` is a pure function of (set, byte) (a `const fn` reading one array element).
    #[trusted]
    #[ensures(result == self.contains_l(byte))]
    pub(crate) const fn contains(&self, byte: u8) -> bool {
        let chunk = self.mask[byte as usize / 32];
        let mask = 1 << (byte as usize % 32);
        (chunk & mask) != 0
    }

    #[ensures(result == self.enc(byte))]
    // verbatim: upstream src/ascii_set.rs pub(crate) fn should_percent_encode(&self, byte: u8) -> bool {
    pub(crate) fn should_percent_encode(&self, byte: u8) -> bool {
        !byte.is_ascii() || self.contains(byte)
    }
}

// T3: percent_encode_byte is a pure function of the byte (a static table lookup).
#[logic(opaque)]
pub fn peb(b: u8) -> Seq<char> {
    dead
}

#[trusted]
#[ensures(result@ == peb(byte))]
pub fn percent_encode_byte(byte: u8) -> &'static str {
    unreachable!()
}

// ---------------------------------------------------------------- the common spec
// Length of the leading run of bytes the set does not encode.
#[logic(open)]
#[variant(s.len())]
#[ensures(0 <= result && result <= s.len())]
pub fn run(set: AsciiSet, s: Seq<u8>) -> Int {
    pearlite! {
        if s.len() == 0 { 0 } else if set.enc(s[0]) { 0 } else { 1 + run(set, s.tail()) }
    }
}

// Characterisation of `run` as "first index i with enc(s[i]), or len".
#[logic]
#[variant(s.len())]
#[requires(0 <= k && k <= s.len())]
#[requires(forall<j: Int> 0 <= j && j < k ==> !set.enc(s[j]))]
#[requires(k == s.len() || set.enc(s[k]))]
#[ensures(run(set, s) == k)]
pub fn run_is(set: AsciiSet, s: Seq<u8>, k: Int) {
    pearlite! { if k == 0 { () } else { run_is(set, s.tail(), k - 1) } }
}

// What one call yields from `bytes`: None iff empty; otherwise the chunk and the rest.
#[logic(open)]
pub fn chunk_ok(set: AsciiSet, bytes: Seq<u8>, res: Option<Seq<char>>, rest: Seq<u8>) -> bool {
    pearlite! {
        match res {
            None => bytes.len() == 0 && rest == bytes,
            Some(c) => bytes.len() > 0 && if set.enc(bytes[0]) {
                c == peb(bytes[0]) && rest == bytes.tail()
            } else {
                let k = 1 + run(set, bytes.tail());
                c.to_bytes() == bytes.subsequence(0, k)
                  && rest == bytes.subsequence(k, bytes.len())
            }
        }
    }
}

// ---------------------------------------------------------------- one step, as a function
#[logic(open)]
pub fn step(set: AsciiSet, b: Seq<u8>) -> Option<(Seq<char>, Seq<u8>)> {
    pearlite! {
        if b.len() == 0 { None }
        else if set.enc(b[0]) { Some((peb(b[0]), b.tail())) }
        else {
            let k = 1 + run(set, b.tail());
            Some((ascii_str(b.subsequence(0, k)), b.subsequence(k, b.len())))
        }
    }
}

#[logic]
#[variant(s.len())]
#[ensures(forall<j: Int> 0 <= j && j < run(set, s) ==> !set.enc(s[j]))]
pub fn run_prefix(set: AsciiSet, s: Seq<u8>) {
    pearlite! {
        if s.len() == 0 { () } else if set.enc(s[0]) { () } else {
            let _ = run_prefix(set, s.tail());
            proof_assert! { forall<j: Int> 1 <= j && j < s.len() ==> s[j] == s.tail()[j - 1] };
            ()
        }
    }
}

// Facts about the chunk at the front of `b` that turn `chunk_ok` into `step`.
#[logic]
#[ensures(b.len() > 0 && !set.enc(b[0]) ==>
    ascii_str(b.subsequence(0, 1 + run(set, b.tail()))).to_bytes() == b.subsequence(0, 1 + run(set, b.tail())))]
#[ensures(forall<r: Option<Seq<char>>, rest: Seq<u8>> chunk_ok(set, b, r, rest) ==>
    match r { None => step(set, b) == None, Some(c) => step(set, b) == Some((c, rest)) })]
pub fn front_facts(set: AsciiSet, b: Seq<u8>) {
    pearlite! {
        let _ = injective_to_bytes();
        if b.len() > 0 && !set.enc(b[0]) {
            let k = 1 + run(set, b.tail());
            let _ = run_prefix(set, b.tail());
            proof_assert! { forall<j: Int> 1 <= j && j < b.len() ==> b[j] == b.tail()[j - 1] };
            proof_assert! { forall<j: Int> 0 <= j && j < k ==> !set.enc(b[j]) };
            proof_assert! { forall<j: Int> 0 <= j && j < k ==> b.subsequence(0, k)[j]@ < 128 };
            ascii_str_bytes(b.subsequence(0, k))
        } else { () }
    }
}

// State after n steps from b (None if the iterator stopped earlier), and the n-th chunk.
#[logic(open)]
#[variant(n)]
pub fn state_after(set: AsciiSet, b: Seq<u8>, n: Int) -> Option<Seq<u8>> {
    pearlite! {
        if n <= 0 { Some(b) } else {
            match step(set, b) { None => None, Some((_, r)) => state_after(set, r, n - 1) }
        }
    }
}

#[logic(open)]
#[variant(n)]
pub fn chunk_at(set: AsciiSet, b: Seq<u8>, n: Int) -> Seq<char> {
    pearlite! {
        match step(set, b) {
            None => Seq::empty(),
            Some((c, r)) => if n <= 0 { c } else { chunk_at(set, r, n - 1) }
        }
    }
}

#[logic]
#[variant(n)]
#[requires(n >= 0)]
#[ensures(match state_after(set, b, n) {
    None => true,
    Some(r) => forall<m: Int> m >= 0 ==>
        state_after(set, b, n + m) == state_after(set, r, m) && chunk_at(set, b, n + m) == chunk_at(set, r, m)
})]
pub fn compose(set: AsciiSet, b: Seq<u8>, n: Int) {
    pearlite! {
        if n == 0 { () } else {
            match step(set, b) { None => (), Some((_, r)) => compose(set, r, n - 1) }
        }
    }
}

// One more step from the state after n steps.
#[logic]
#[requires(n >= 0)]
#[ensures(match state_after(set, b, n) {
    None => true,
    Some(r) => match step(set, r) {
        None => r.len() == 0 && state_after(set, b, n + 1) == None,
        Some((c, r2)) => state_after(set, b, n + 1) == Some(r2) && chunk_at(set, b, n) == c,
    }
})]
pub fn step_after(set: AsciiSet, b: Seq<u8>, n: Int) {
    pearlite! {
        let _ = compose(set, b, n);
        match state_after(set, b, n) {
            None => (),
            Some(r) => { proof_assert! { chunk_at(set, b, n + 0) == chunk_at(set, r, 0) && n + 0 == n }; proof_assert! { chunk_at(set, b, n) == chunk_at(set, r, 0) }; proof_assert! { state_after(set, r, 1) == match step(set, r) { None => None, Some((_, r2)) => state_after(set, r2, 0) } }; () }
        }
    }
}

// Number of chunks: the iterator yields exactly count(b) items.
#[logic(open)]
#[variant(b.len())]
pub fn count(set: AsciiSet, b: Seq<u8>) -> Int {
    pearlite! {
        match step(set, b) { None => 0, Some((_, r)) => 1 + count(set, r) }
    }
}

#[logic]
#[variant(b.len())]
#[ensures(count(set, b) >= 0)]
#[ensures(state_after(set, b, count(set, b)) == Some(Seq::empty()))]
#[ensures(forall<n: Int> n >= 0 ==> match state_after(set, b, n) {
    None => n > count(set, b), Some(r) => n <= count(set, b) && (r.len() == 0 ==> n == count(set, b)) })]
pub fn count_spec(set: AsciiSet, b: Seq<u8>) {
    pearlite! {
        match step(set, b) {
            None => { proof_assert! { b == Seq::empty() }; () },
            Some((_, r)) => count_spec(set, r),
        }
    }
}

// ---------------------------------------------------------------- writing the chunks to a sink
// wr_n(w, ..., n): sink state and success after writing chunks 0..n, stopping at the first error.
#[logic(open)]
#[variant(n)]
pub fn wr_n<'w, W: ?Sized>(w: &'w W, set: AsciiSet, b: Seq<u8>, n: Int) -> (&'w W, bool) {
    pearlite! {
        if n <= 0 { (w, true) } else {
            let (w1, ok) = wr_n(w, set, b, n - 1);
            if !ok { (w1, false) } else {
                let c = chunk_at(set, b, n - 1);
                (sink_after(w1, c), sink_ok(w1, c))
            }
        }
    }
}

#[logic]
#[variant(m - n)]
#[requires(0 <= n && n <= m)]
#[requires(!wr_n(w, set, b, n).1)]
#[ensures(wr_n(w, set, b, m) == wr_n(w, set, b, n))]
pub fn wr_err_stable<W: ?Sized>(w: &W, set: AsciiSet, b: Seq<u8>, n: Int, m: Int) {
    pearlite! { if n == m { () } else { wr_err_stable(w, set, b, n, m - 1) } }
}

// ---------------------------------------------------------------- original upstream code
#[derive(Clone)]
pub struct PercentEncode<'a> {
    bytes: &'a [u8],
    ascii_set: &'static AsciiSet,
}

impl<'a> IteratorSpec for PercentEncode<'a> {
    #[logic(open(self), prophetic)]
    fn produces(self, visited: Seq<&'a str>, o: Self) -> bool {
        pearlite! {
            self.ascii_set == o.ascii_set
            && state_after(*self.ascii_set, self.bytes@, visited.len()) == Some(o.bytes@)
            && forall<i: Int> 0 <= i && i < visited.len() ==> visited[i]@ == chunk_at(*self.ascii_set, self.bytes@, i)
        }
    }

    #[logic(open(self), prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { (*self).bytes@.len() == 0 && resolve(self) }
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<&'a str>, b: Self, bc: Seq<&'a str>, c: Self) {
        pearlite! { compose(*a.ascii_set, a.bytes@, ab.len()) }
    }
}

impl<'a> Iterator for PercentEncode<'a> {
    type Item = &'a str;

    #[ensures((^self).ascii_set == self.ascii_set)]
    #[ensures(chunk_ok(*self.ascii_set, self.bytes@, match result { None => None, Some(c) => Some(c@) }, (^self).bytes@))]
    #[ensures(match result { None => self.completed(), Some(v) => (*self).produces(Seq::singleton(v), ^self) })]
    // verbatim: upstream src/lib.rs fn next(&mut self) -> Option<&'a str> {
    fn next(&mut self) -> Option<&'a str> {
        snapshot! { front_facts(*self.ascii_set, self.bytes@) };
        if let Some((&first_byte, remaining)) = self.bytes.split_first() {
            if self.ascii_set.should_percent_encode(first_byte) {
                self.bytes = remaining;
                Some(percent_encode_byte(first_byte))
            } else {
                // The unsafe blocks here are appropriate because the bytes are
                // confirmed as a subset of UTF-8 in should_percent_encode.
                #[invariant(produced.len() <= remaining@.len())]
                #[variant(remaining@.len() - produced.len())]
                #[invariant(forall<k: Int> 0 <= k && k < produced.len() ==> produced[k].0@ == k && *produced[k].1 == remaining@[k])]
                #[invariant(forall<j: Int> 0 <= j && j < produced.len() ==> !self.ascii_set.enc(remaining@[j]))]
                for (i, &byte) in remaining.iter().enumerate() {
                    if self.ascii_set.should_percent_encode(byte) {
                        // 1 for first_byte + i for previous iterations of this loop
                        let (unchanged_slice, remaining) = self.bytes.split_at(1 + i);
                        proof_assert! { i@ == produced.len() - 1 && i@ < self.bytes@.len() - 1 };
                        proof_assert! { byte == self.bytes@.tail()[i@] };
                        proof_assert! { forall<j: Int> 0 <= j && j < i@ ==> !self.ascii_set.enc(self.bytes@.tail()[j]) };
                        proof_assert! { forall<j: Int> 0 <= j && j < 1 + i@ ==> unchanged_slice@[j] == self.bytes@[j] };
                        proof_assert! { !self.ascii_set.enc(self.bytes@[0]) };
                        proof_assert! { forall<j: Int> 1 <= j && j < self.bytes@.len() ==> self.bytes@[j] == self.bytes@.tail()[j - 1] };
                        proof_assert! { forall<j: Int> 0 <= j && j < 1 + i@ ==> !self.ascii_set.enc(self.bytes@[j]) };
                        proof_assert! { forall<j: Int> 0 <= j && j < 1 + i@ ==> unchanged_slice@[j]@ < 128 };
                        snapshot! { run_is(*self.ascii_set, self.bytes@.tail(), i@) };
                        snapshot! { ascii_valid(unchanged_slice@) };
                        self.bytes = remaining;
                        return Some(unsafe { str::from_utf8_unchecked(unchanged_slice) });
                    }
                }
                let unchanged_slice = self.bytes;
                proof_assert! { forall<j: Int> 0 <= j && j < self.bytes@.len() - 1 ==> !self.ascii_set.enc(self.bytes@.tail()[j]) };
                proof_assert! { !self.ascii_set.enc(self.bytes@[0]) };
                proof_assert! { forall<j: Int> 1 <= j && j < self.bytes@.len() ==> self.bytes@[j] == self.bytes@.tail()[j - 1] };
                proof_assert! { forall<j: Int> 0 <= j && j < self.bytes@.len() ==> !self.ascii_set.enc(self.bytes@[j]) };
                proof_assert! { forall<j: Int> 0 <= j && j < self.bytes@.len() ==> self.bytes@[j]@ < 128 };
                snapshot! { run_is(*self.ascii_set, self.bytes@.tail(), self.bytes@.len() - 1) };
                snapshot! { ascii_valid(unchanged_slice@) };
                self.bytes = &[][..];
                proof_assert! { self.bytes@ == Seq::empty() };
                proof_assert! { 1 + run(*self.ascii_set, unchanged_slice@.tail()) == unchanged_slice@.len() };
                proof_assert! { unchanged_slice@.subsequence(0, unchanged_slice@.len()) == unchanged_slice@ };
                proof_assert! { unchanged_slice@.subsequence(unchanged_slice@.len(), unchanged_slice@.len()) == self.bytes@ };
                Some(unsafe { str::from_utf8_unchecked(unchanged_slice) })
            }
        } else {
            None
        }
    }
}

// The spec both Display::fmt versions meet: write every chunk in order, stop at the first error.
#[logic(open)]
pub fn display_ok<W: ?Sized>(set: AsciiSet, b: Seq<u8>, before: &W, after: &W, ok: bool) -> bool {
    pearlite! { (after, ok) == wr_n(before, set, b, count(set, b)) }
}

impl fmt::Display for PercentEncode<'_> {
    #[ensures(display_ok(*self.ascii_set, self.bytes@, &*formatter, &^formatter, result == Ok(())))]
    // verbatim: upstream src/lib.rs fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let f0 = snapshot!(&*formatter);
        snapshot! { count_spec(*self.ascii_set, self.bytes@) };
        #[invariant(wr_n(*f0, *self.ascii_set, self.bytes@, produced.len()) == (&*formatter, true))]
        #[variant(count(*self.ascii_set, self.bytes@) - produced.len())]
        for c in (*self).clone() {
            snapshot! { compose(*self.ascii_set, self.bytes@, produced.len() - 1) };
            snapshot! { wr_err_stable_imp(*f0, *self.ascii_set, self.bytes@, produced.len(), count(*self.ascii_set, self.bytes@)) };
            formatter.write_str(c)?
        }
        Ok(())
    }
}

// ---------------------------------------------------------------- patched code
pub struct PercentEncodeP<'a> {
    bytes: &'a [u8],
    ascii_set: &'static AsciiSet,
}

#[ensures(match result {
    None => chunk_ok(*set, bytes@, None, bytes@),
    Some((c, rest)) => chunk_ok(*set, bytes@, Some(c@), rest@),
})]
// verbatim: patched src/lib.rs fn next_chunk<'a>(bytes: &'a [u8], set: &AsciiSet) -> Option<(&'a str, &'a [u8])> {
fn next_chunk<'a>(bytes: &'a [u8], set: &AsciiSet) -> Option<(&'a str, &'a [u8])> {
    if let Some((&first_byte, remaining)) = bytes.split_first() {
        if set.should_percent_encode(first_byte) {
            Some((percent_encode_byte(first_byte), remaining))
        } else {
            // AENEAS PATCH: the original `for ... enumerate()` loop with an
            // early `return` is replaced by a `while` loop that finds the
            // same index. When no byte needs encoding, i == remaining.len()
            // and split_at returns (whole slice, empty slice), which is what
            // the original fall-through branch returned.
            let mut i = 0;
            #[invariant(i@ <= remaining@.len())]
            #[invariant(forall<j: Int> 0 <= j && j < i@ ==> !set.enc(remaining@[j]))]
            #[variant(remaining@.len() - i@)]
            while i < remaining.len() && !set.should_percent_encode(remaining[i]) {
                i += 1;
            }
            snapshot! { run_is(*set, bytes@.tail(), i@) };
            let (unchanged_slice, remaining) = bytes.split_at(1 + i);
            proof_assert! { forall<j: Int> 0 <= j && j < 1 + i@ ==> unchanged_slice@[j] == bytes@[j] };
            proof_assert! { forall<j: Int> 1 <= j && j < 1 + i@ ==> bytes@[j] == bytes@.tail()[j - 1] };
            proof_assert! { forall<j: Int> 0 <= j && j < 1 + i@ ==> unchanged_slice@[j]@ < 128 };
            snapshot! { ascii_valid(unchanged_slice@) };
            // The unsafe block is appropriate because the bytes are
            // confirmed as a subset of UTF-8 in should_percent_encode.
            Some((unsafe { str::from_utf8_unchecked(unchanged_slice) }, remaining))
        }
    } else {
        None
    }
}

impl<'a> PercentEncodeP<'a> {
    #[ensures((^self).ascii_set == self.ascii_set)]
    #[ensures(chunk_ok(*self.ascii_set, self.bytes@, match result { None => None, Some(c) => Some(c@) }, (^self).bytes@))]
    // verbatim: patched src/lib.rs fn next(&mut self) -> Option<&'a str> {
    fn next(&mut self) -> Option<&'a str> {
        // AENEAS PATCH: the body moved to `next_chunk` (below), which takes the
        // set as a plain `&AsciiSet`; `Display` reuses it. Aeneas cannot
        // translate loops that pass on the `&'static AsciiSet` field.
        match next_chunk(self.bytes, self.ascii_set) {
            Some((chunk, remaining)) => {
                self.bytes = remaining;
                Some(chunk)
            }
            None => None,
        }
    }
}

impl fmt::Display for PercentEncodeP<'_> {
    #[ensures(display_ok(*self.ascii_set, self.bytes@, &*formatter, &^formatter, result == Ok(())))]
    // verbatim: patched src/lib.rs fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        // AENEAS PATCH: the `for` loop with `?` is moved into `write_chunks`,
        // a `while` loop over any `fmt::Write` sink (`Formatter` is one), so the
        // written text can be specified. Same calls, same order, same result.
        write_chunks(self.bytes, self.ascii_set, formatter)
    }
}

// AENEAS PATCH: helper for `Display`; see above.
#[ensures(display_ok(*set, bytes@, &*sink, &^sink, result == Ok(())))]
// verbatim: patched src/lib.rs fn write_chunks<W: fmt::Write + ?Sized>(bytes: &[u8], set: &AsciiSet, sink: &mut W) -> fmt::Result {
fn write_chunks<W: fmt::Write + ?Sized>(bytes: &[u8], set: &AsciiSet, sink: &mut W) -> fmt::Result {
    let w0 = snapshot!(&*sink);
    snapshot! { count_spec(*set, bytes@) };
    let mut n = snapshot!(0);
    let mut rest = bytes;
    let mut result = Ok(());
    let mut done = false;
    #[invariant(*n >= 0 && state_after(*set, bytes@, *n) == Some(rest@))]
    #[invariant(!done ==> wr_n(*w0, *set, bytes@, *n) == (&*sink, true) && result == Ok(()))]
    #[invariant(done ==> display_ok(*set, bytes@, *w0, &*sink, result == Ok(())))]
    #[variant(rest@.len() * 2 + if done { 0 } else { 1 })]
    while !done {
        snapshot! { front_facts(*set, rest@) };
        snapshot! { step_after(*set, bytes@, *n) };
        match next_chunk(rest, set) {
            Some((chunk, remaining)) => {
                rest = remaining;
                n = snapshot!(*n + 1);
                snapshot! { wr_err_stable_imp(*w0, *set, bytes@, *n, count(*set, bytes@)) };
                if let Err(e) = sink.write_str(chunk) {
                    result = Err(e);
                    done = true;
                }
            }
            None => done = true,
        }
    }
    result
}

#[logic]
#[ensures(0 <= n && n <= m && !wr_n(w, set, b, n).1 ==> wr_n(w, set, b, m) == wr_n(w, set, b, n))]
pub fn wr_err_stable_imp<W: ?Sized>(w: &W, set: AsciiSet, b: Seq<u8>, n: Int, m: Int) {
    pearlite! { if 0 <= n && n <= m && !wr_n(w, set, b, n).1 { wr_err_stable(w, set, b, n, m) } else { () } }
}

// ---------------------------------------------------------------- the equivalence
// chunk_ok determines the result and the new state, so both versions agree on every input.
#[logic]
#[requires(chunk_ok(set, b, r1, s1))]
#[requires(chunk_ok(set, b, r2, s2))]
#[ensures(r1 == r2 && s1 == s2)]
pub fn chunk_ok_functional(set: AsciiSet, b: Seq<u8>, r1: Option<Seq<char>>, s1: Seq<u8>, r2: Option<Seq<char>>, s2: Seq<u8>) {
    pearlite! { let _ = injective_to_bytes(); () }
}
