// Gate 1, decoder side (percent-encoding 2.3.2): the original `PercentDecode::next`
// (`Option::map` with a closure that captures `&mut self.bytes`) and the patched `match` version
// meet the same exact spec `dstep`, so they agree on every input. `after_percent_sign`, which is
// identical in both trees, is proved here too (including no overflow in `h * 0x10 + l`).
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
}

// ---------------------------------------------------------------- spec
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
pub struct PercentDecode<'a> {
    bytes: slice::Iter<'a, u8>,
}

impl PercentDecode<'_> {
    #[ensures(match result {
        None => dstep(self.bytes@@) == None,
        Some(v) => dstep(self.bytes@@) == Some((v@, (^self).bytes@@)),
    })]
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

// ---------------------------------------------------------------- patched code
pub struct PercentDecodeP<'a> {
    bytes: slice::Iter<'a, u8>,
}

impl PercentDecodeP<'_> {
    #[ensures(match result {
        None => dstep(self.bytes@@) == None,
        Some(v) => dstep(self.bytes@@) == Some((v@, (^self).bytes@@)),
    })]
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
