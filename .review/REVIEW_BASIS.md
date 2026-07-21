# C4 Accepted Review Basis — Human Contract Review

checkpoint: C4 — source type names, compiler resolution, and unified numeric conversions
contract: .review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md
contract_sha256: 9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4
baseline: 8c9212a8c814c7a99a5e3ef1970a0ae32425a918
human_authorization: C4-source-type-resolution-1

The C4 directive itself IS the accepted human Contract Review (Rob's decision; the automatic Codex review
path is disabled).  Do not preserve the C3 review basis as current authority — git history is its archive.

## Accepted C4 claim surface (directive §15)

1. **Intrinsic source identity** — every live conversion target carries a valid bounded source identifier;
   only the exact sixteen approved target names are representable; source spelling is retained independently of
   the semantic type.
2. **Compiler-owned binding** — raw syntax carries no semantic target tag; `GoCompile` alone resolves current
   source type names through the current predeclared context; `byte`/`rune` keep source identity and resolve to
   `uint8`/`int32` semantics.
3. **One indexed semantic path** — every type-name occurrence has one retained identity and one exact fact;
   conversion expression facts consume retained type-name + operand facts; one `elaborate` result mints the
   only compilation capability.
4. **One conversion authority** — every explicit constant conversion routes through `GoTypes.convert_const`;
   the old family-specific source constructors and peer paths are deleted; success and failure stay exact.
5. **Source-correct output and diagnostics** — rendering and reports preserve the selected source names; a
   semantic alias never forces a canonical semantic spelling; all prior generated source bytes are unchanged.
6. **Trust and scope** — no assumptions, trusted parser, host semantic code, second AST, custom collection, or
   later-language scope; C5 work stays absent except the explicit alias-timing amendment in this contract.

## Blocking defect classes (directive §16)
The full list in §16 is binding.  In brief: a semantic tag in raw conversion syntax; old + new constructors
coexisting; arbitrary/qualified names becoming representable without call/scope semantics; representing
`bool`/`string`/`uintptr`/interfaces/user types then rejecting valid cases; name lookup outside the one
compiler authority; rendering a spelling from the semantic type; losing `byte`/`rune` spelling in diagnostics;
type-name facts that copy syntax / accept foreign keys / omit live refs / recompute on query; recomputing an
already-indexed operand; a hidden second source-name resolver in `GoTypes`; a specification helper acting as a
peer production compiler; a second AST walk / type side index / parser / sort / custom map / copied tree;
soundness/completeness replaced by examples/bounds/fuel; a rejected program minting
`CompilableProgram`/`SafeProgram`/`DirectoryImage`; generated-byte drift; any C5 rune-literal/`uintptr` work;
conflicting C4/C5 authority in permanent docs.

## Evidence required at human Implementation Review (directive §17)
The report + repository must supply the contract path/hash/baseline/candidate range; a file-level change
summary; the one source-name authority + its identifier/name exactness theorems; the exact index
child/ref/domain facts for type-name occurrences; the compiler resolver + total exact type-name fact query;
universal resolver facts for all sixteen names; the `byte`/`uint8` and `rune`/`int32` source-distinct /
semantic-equal proofs; the exact production expression-fact theorem vs the declarative source semantics;
invalid-conversion soundness/completeness/multiplicity/ordering/anchor proofs; renderer/denotation proofs over
source type names; evidence the public renderer/materializer still consumes only `SafeProgram` from the one
retained elaboration; the full pinned-Go differential; zero project assumptions + the updated readable gate;
standard-collection + no-second-traversal audits; exact generated-byte comparison; all build/e2e/check/regen/
staged-hook results; a full-tree old-constructor + stale-authority search; current permanent documentation.

## Forbidden overreach (directive §18)
The full §18 list is binding: no `uintptr`; no rune literal/constant kind; no user types, variables, calls,
selectors, params, results, imports, qualified names; no unresolved-name diagnostics for unrepresentable
names; no `bool`/`string`/interface/pointer/array/struct/function/slice/map/channel conversion targets; no
shadowing machinery with no live declaration; no typed/resolved AST; no second AST/parser/token tree/host
parser; no source semantics in OCaml/shell/Docker/Go; no second compiler/checker/renderer/emitter/publication
path; no custom collections where the standard library suffices; no fuel/bounds/admitted/axioms/test-only
correctness; no C6-reserved module reorganization; no unrelated cleanup.

## Use
This basis exists because C4's Contract Review is Rob's directive itself (Codex review disabled).  The human
Implementation Review still independently assesses correctness, missing roots, competing authorities,
under-implementation, and over-implementation.  This basis is not a waiver for defects outside its finding list.
