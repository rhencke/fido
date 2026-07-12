# Fido — Architecture Charter (binding)

Read before any structural change. This governs. It describes the INTENDED roots and the current reset —
not a shipping pipeline. There is no emitted Go right now, and that is correct.

## The law of this repository

Ruthless correctness or ruthless deletion — no middle state. Do not build a floor on an unsettled
foundation. If twenty local proofs/guards/comments cover one missing root, replace the root and delete the
leaves. "Trusted," "works," "stable output," "axiom-free," and "conservative" are NOT substitutes for
semantic correctness. A green boolean checker that accepts an undefined type is not progress; a printer
grammar that validates itself is not progress. Loss of breadth is irrelevant — unproved breadth was never
progress.

## Where we are (checkpoint 65 reset)

Deleted, and staying deleted: the handwritten OCaml backend + extraction plugin; the **false compile/emit
authority** (`GoCompile` was a boolean `check p = true` that fail-open-accepted an unresolved named type —
`[]Foo{}` with `Foo` undefined — which Go rejects; `GoTypes`/`GoEmit` inherited it); and the **disconnected
runtime island** (`GoNumeric`/`GoRuntimeTypes`/`GoPanic`/`GoEffects`/`GoSlice`, which preserved rejected
foundations and was not even on the emission path).

Surviving: a syntax layer (`digits`, `GoAst`, `GoPrint`) that compiles zero-axiom but rests on a rejected
syntax root — kept only until the reset reaches it, described honestly in `PROGRESS.md`, claiming nothing.

## The intended roots (pour in order; each before the floor above it)

1. **`TargetConfig`** — the one authority for int/uint width and pinned target facts. No hard-coded numeric
   assumptions scattered across modules.
2. **`CertifiedType` — one type universe.** Identity, underlying type, zero value, comparability, map-key
   admissibility, printed tokens, and runtime identity all DERIVE from one descriptor. Invalid Go types are
   unrepresentable or rejected by elaboration. No parallel "runtime tag" vs "syntax type" universes. A
   surface name may exist only if elaboration resolves it to a certified descriptor before printing.
3. **An independent Go grammar.** `GoLex`/`GoGrammar` define valid Go token derivations WITHOUT reference to
   any printer policy (`unop_paren`/`binop_prec` must not appear in the grammar). Then the printer is proved
   *adequate*: `PrintsExpr e toks` and `GoExprGrammar … toks e'` gives `e' = erase e`. One token stream, one
   verified renderer (`typed AST → canonical tokens → bytes`), and `lex (render toks) = toks`; the string
   output is a projection of the tokens, not a second AST recursion. No formatter rewrites the rendered bytes.
4. **A compile environment + declarative elaboration.** `CompileEnv` (keywords; shadowable universe/
   predeclared bindings; package/type/value namespaces), `ResolveName`, `ElaborateType`, `TypeExpr`,
   `TypeStmt` — declarative judgments producing a **typed IR** (`TypedProgram`) in which static invalidity is
   unrepresentable. An executable `elaborate_check : Program -> option ProgramIR` proved SOUND against the
   relation (and complete for the admitted closed subset). The public compile authority is this proof-bearing
   relation, never a boolean equality.
5. **Runtime roots, as consumers require them:** a typed object store + value well-formedness; one native
   representation each for slice/map/channel (nil/cap/backing, finite maps, finite channels); accurate
   control/panic/blocking/model-fault with structured runtime errors; no `FunctionalExtensionality`.
6. **Emission last.** Only after elaboration soundness + grammar adequacy + token render/lex inverse + an
   exact byte theorem exist, restore a closed extraction output through a proof-bearing typed certificate
   (`emit_typed : TypedProgram -> bytes`, or `compile_emit : Program -> option CertifiedArtifact` whose
   success internally performs proved elaboration). Never extract a foreign-callable function whose
   proof-carrying argument handwritten OCaml can construct after proof erasure.

## Trust base (say it exactly)

Trusted: Rocq and its kernel; the two Docker base images (digest-pinned) plus the opam-repo state and apt
packages they install (pinning/snapshotting those is a residual build-trust task in `PROGRESS.md`); and —
when emission returns — the Rocq extraction transform, `ExtrOcamlNativeString`, the OCaml compiler/runtime,
one tiny transparent output glue file, and the Go toolchain (Go's parse of the bytes is trusted; the
Go-subset recognition theorem is the grammar-adequacy goal above). No handwritten semantic OCaml exists
(`tools/ocaml-origin-gate.sh`).

Proved: the surviving syntax layer's *declared* `Print Assumptions` surfaces print no assumptions — that is
what the axiom gate establishes, NOT that every definition is globally assumption-free (the precise
public-surface gate is a build-trust task). "No assumptions" is never evidence that a theorem's *statement*
is the right correctness theorem — the deleted `GoCompile` was axiom-free and still wrong.

## What must never come back

A handwritten OCaml backend or any of its jobs (term inspection, type reconstruction, name-based
recognition, lowering, AST construction, printer decisions, import selection, control-flow synthesis,
validation, fallback, byte rewriting); a boolean equality as a compile authority; an unresolved named type
in the admitted target IR; a signed integer literal constructor; a grammar defined by the printer's own
decisions; two parallel string/token printer recursions; the dead executable parser; the rejected runtime
island. Git carries the history; do not resurrect from memory — re-admit each feature only when the roots
make its proof obligations natural.
