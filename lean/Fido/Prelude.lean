/-! Rocq-stdlib-shaped helpers the port needs — the one module with no `.v` counterpart (lean/README.md). -/
namespace Fido

/-- Rocq `string` is a cons-list of `ascii`; keeping it a list keeps every induction one-to-one with the `.v`. -/
abbrev Str := List Char

/-- `str! "abc"` elaborates to the char-list literal `['a', 'b', 'c']`: a constructive `Str` literal.
    (`String.toList` on a literal reaches `Classical.choice` in this toolchain; the macro leaves no trace.) -/
macro "str!" s:str : term => do
  let lits ← s.getString.toList.toArray.mapM fun c => `(term| $(Lean.quote c))
  `([$lits,*])

end Fido
