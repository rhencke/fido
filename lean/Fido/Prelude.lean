/-! Rocq-stdlib-shaped helpers the port needs — the one module with no `.v` counterpart (lean/README.md). -/
namespace Fido

/-- Rocq `string` is a cons-list of `ascii`; keeping it a list keeps every induction one-to-one with the `.v`. -/
abbrev Str := List Char

end Fido
