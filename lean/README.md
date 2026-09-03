# Fido — Lean 4 port (proof of concept)

**Not part of the certified path.** `make check` never builds or reads this tree; nothing here is an authority
for anything. It exists to answer one question with measurements: how does a faithful Lean 4 rendering of the
same theory compare on cold build time, and where does the port stop being faithful.

## Layout

`Fido/X.lean` mirrors `X.v` (`Fido/Index/Model.lean` mirrors `Index/Model.v`). `Fido.lean` imports every ported
module in dependency order — `make lean-bench` times them one process at a time in that order, the analogue of
one `rocq c` per file. `Audit.lean` prints the axiom closure of every `Fido.*` constant (`make lean-audit`).

## Conventions (the type mapping is the port's contract)

| Rocq | Lean | note |
|---|---|---|
| `nat` | `Nat` | |
| `Z` | `Int` | |
| `positive` | `Nat` with `0 < n` carried | bit-recursion becomes recursion on `n / 2` |
| `string` | `List Char` (`abbrev Str`) | Rocq's `string` is a cons-list; `String.mk` only at the render boundary |
| `ascii` | `Char` | Rocq's is 8-bit; where a proof relied on `< 256`, the bound is stated |
| `bool`/`Prop`/`list`/`option` | `Bool`/`Prop`/`List`/`Option` | |
| `Record`/`Inductive` | `structure`/`inductive` | same field and constructor names |
| `CoInductive` | greatest-fixed-point predicate (explicit invariant) | Lean 4 has no coinductives |
| `vm_compute; reflexivity` | `decide` (kernel) | never `native_decide` |
| `Floats.SpecFloat` | ported `SFdiv` subset (`Fido/SpecFloat.lean`) | Lean core has no IEEE-754 spec model |

`Fido/Prelude.lean` is the one module with no `.v` counterpart: it holds the Rocq-stdlib-shaped helpers
(`Str`). Each module declares `namespace Fido.X` (so the audit's `Fido.*` filter sees every constant) and
importers write `open Fido` once, so Rocq's qualified style (`Version.render`, `Names.equalb`) reads the same.

Every `Definition`/`Lemma`/`Theorem` keeps its name and its statement up to that mapping. Proofs are idiomatic
Lean (`omega`, `simp`, `decide`, structural induction); a proof may not weaken, split or drop a statement. No
`sorry`. Divergences that could not be avoided are listed at the top of the module in a `/-! divergences -/`
block. The audit forbids `sorryAx` and `Lean.ofReduceBool`; every other axiom it reports is a finding.

## Toolchain

`lean.Dockerfile`: `debian:bookworm-slim` by digest + the official `v4.33.1` release tarball by sha256. The host
runs only `make lean-*` (Docker inside); no Lean on the host.
