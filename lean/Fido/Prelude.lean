/-! Rocq-stdlib-shaped helpers the port needs — the one module with no `.v` counterpart (lean/README.md). -/
namespace Fido

/-- Rocq `ascii` is an 8-bit byte; `UInt8` is exactly that (`UInt8.ofNat` wraps modulo 256 like
    `ascii_of_nat`, and `toNat < 256` holds by type). Rocq `string` is a cons-list of `ascii`; keeping it a list
    keeps every induction one-to-one with the `.v`. -/
abbrev Str := List UInt8

/-- `str! "abc"` elaborates to the byte-list literal `[97, 98, 99]`: a constructive `Str` literal holding the
    literal's UTF-8 bytes, which for the ASCII literals of this theory are its Rocq bytes exactly.
    (`String.toList` on a literal reaches `Classical.choice` in this toolchain; the macro leaves no trace.) -/
macro "str!" s:str : term => do
  let lits ← s.getString.toUTF8.toList.toArray.mapM fun b => `(term| ($(Lean.quote b.toNat) : UInt8))
  `([$lits,*])

/-- `byte! 'a'` is the byte `97 : UInt8` — Rocq's `"a"%char` — at elaboration time. -/
macro "byte!" c:char : term => `(term| ($(Lean.quote c.getChar.toNat) : UInt8))

end Fido
