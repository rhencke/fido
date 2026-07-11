# Fido — operating law for a theorem-first repository

**Verified model components with a TRUSTED extraction backend** — the honest headline, *never*
"formally verified Go." Theorems are proved in Rocq; every `*.go` is a proof artifact extracted
from `*.v` — never hand-written, never edited. **Current state and gates: `PROGRESS.md`.
Architecture charter (binding): `ARCHITECTURE.md`.**

## The law

**There is no transition. There is only the intended architecture and things that should be
deleted.**

Nobody depends on this repository. There is no backwards-compatibility obligation, no migration
path to preserve, no transition artifact. A weak, half-baked, legacy, demo-only, or
convenience-oriented approach is deleted unless it is (a) part of the intended theorem-first
architecture, (b) an explicitly unsupported frontier, or (c) an isolated integration/log-diff
test that cannot be mistaken for proof evidence.

**MVP 1.0 = the smallest theorem-complete vertical slice using the strongest proof architecture
we know how to build.** Not the fastest demo, not the broadest feature sample, not the easiest
milestone. **Cut supported scope before weakening proof strength.**

**Cost is not a constraint; incorrectness is fatal.** Time and tokens are free — never trade
correctness, generality, or expressive strength for a cheaper path. Given a choice between a
cheaper/less-expressive mechanism and a harder/more-general/more-correct one, take the harder one:
this is a research project exploring the strongest guarantees the current art allows, not a
collection of half-measures. (This is not license to shortcut — it is the opposite: do the harder,
more-correct thing.) **Plans and directives are best-effort guidance, not gospel.** When a plan
conflicts with reality — a stronger proof, a better generalization, a more correct formulation —
follow the stronger path and honor the plan's higher-level intent; a plan detail never outranks a
more-correct mechanism. (Surface the divergence and why; don't silently abandon the ask.)

- This is a theorem-first research repo, not a product with legacy customers.
- The certified path contains only architecture we would defend long term.
- A smaller certified subset beats a broader trusted/demo subset.
- Expressiveness expands by proof principles, never by lists of examples.
- Demos are integration/log-diff checks only — never proof evidence.
- Tests catch regressions; they do not certify semantics, safety, termination, divergence,
  supportedness, or Go adequacy.
- Public correctness claims must be backed by manifest-gated theorem surfaces; an ungated
  internal theorem is not public evidence.
- Unsupported features are rejected, unrepresentable, or explicitly fenced — never modeled with
  stubs, dummy panics, conservative approximations, or examples.
- No second authority: syntax, semantics, emission, safety, termination, and divergence each
  have exactly one authoritative definition. Never add code beside a weaker path — delete the
  weaker path.

## Mandatory change classification

Before making any change, classify it as exactly one of:

1. **Certified theorem path**
2. **Proved restriction** (admissibility / rejection with a sealed boundary)
3. **Explicit unsupported frontier**
4. **Integration/log-diff test for theorem-backed behavior**
5. **Isolated research note** that cannot be imported by, or cited as, proof evidence

If a change fits none of these, do not make it. For any architecture change, also answer: What
correctness claim does this strengthen? What theorem surface exposes it? What unsupported
behavior does it reject? What weaker path did it make obsolete — and what code is deleted
because of it? Does it create a second authority? Could it be mistaken for proof evidence when
it is only integration evidence?

## Deletion pressure

Every architecture-expanding change looks for obsolete code to delete; if nothing can be
deleted, say why no parallel proof path or second authority was created.

Bad reasons to keep code: it is impressive; it still runs; it might be useful later; it helps
demos; it preserves a migration path; it documents an old approach through active code; it makes
feature coverage look broader. Good reasons: certified path, proved restriction, explicit
unsupported frontier, isolated theorem-backed integration test, isolated research note.

**Bad taste:** keeping a legacy plugin path because it emits impressive Go · growing
`builtins.v` instead of splitting final-purpose modules · hiding dependencies behind
`preamble.v` · making printer correctness depend on executable-parser implementation details ·
replacing fuel with renamed allowances/depth caps/bounded runners · treating panic stubs as
semantics for unsupported behavior · demos for unsupported features called progress · defining a
relation without its determinism/disjointness/classification facts · letting `GoCompile`
sound like semantic safety · stale comments preserving old architectures as active mental
models · adding code beside a weaker path instead of deleting it.

**Good taste:** delete the weak path and shrink the supported subset · unfueled
relational/coinductive semantics as authority before executable tooling · canonical
grammar/injectivity over parser implementation behavior · plugin hooks in a module named as
plugin hooks · unsupported features unrepresentable or rejected · a small theorem-complete
vertical slice over a demo garden · public claims moved into manifest-gated surfaces ·
god-files split into modules whose names express proof responsibilities · scope cut before
proof strength.

## Standing technical law

1. **Never edit `*.go`.** Extracted from `*.v` (the `*.v` is committed; the generated `*.go` is
   NOT committed — `make extract` regenerates it, gitignored, and `make check` re-verifies, so it
   can never drift). Change the `.v` / plugin and re-extract.
2. **Model honestly — faithful or fail-loud, never plausible-but-wrong.** The plugin's
   `unsupported` ABORTS extraction for anything it can't lower correctly. ⚠️ **NEVER add a
   raw/opaque/string-rescue escape hatch to a structured AST** (`LESSONS.md` postmortem):
   structured-or-fail-loud; an unrepresentable construct is REJECTED mechanically, never
   preserved as text.
3. **Zero project axioms — every GATED `Print Assumptions` surface is EMPTY; preserve it.** The
   whole model is `Definition`s/`Record`s over concrete Rocq data. Model every new builtin as a
   `Definition`/`Record` — never `Axiom`/`Parameter`/`Admitted`, never a kernel primitive
   (`PrimInt63`/`PrimFloat` are axioms too). Run `Print Assumptions` after significant results.
   (This is the MODEL's trust base; the plugin is a separate trusted TCB — gap #10.)
4. **No fuel, ever.** No gas, step budgets, max-depths, bounded runners, cycle caps, parser or
   recursion allowances, or renamed equivalents anywhere in the certified path
   (`plugin/fuel-gate.sh` enforces mechanically; the manifest is EMPTY — keep it so). A
   ranked/well-founded structural measure is acceptable ONLY as a termination proof from
   decreasing structure — never as an externally supplied execution budget: the measure
   certifies descent inside the proof; no caller passes a bound and no semantics observes one.
   A bounded run is not a proof; a timeout is not nontermination. Divergence is proved by a
   real relation — coinduction, an invariant, a finite-graph cycle theorem, a formal
   certificate.
5. **Partial/unsafe ops are safe-by-construction or proof-gated.** Prefer evidence-carrying APIs
   (demand `i < len`, `d <> 0`, non-nil) or check-and-branch (comma-ok / `option`). Never
   *accidentally* write a Rocq program that needs a nil deref.
6. **Naming is a correctness claim.** `GoCompile` is syntactic admissibility ONLY — it
   implies no semantic safety, panic-freedom, termination/divergence classification,
   race-freedom, memory safety, or real-Go adequacy unless separately proved and exposed
   through a manifest-gated surface. Never let a syntactic gate sound like `SafeProgram`.
7. **Imports are on hold.** Emit `package main`, no `import` block; defer any builtin needing
   one — do NOT approximate it.

## The trusted plugin

`plugin/go.ml` is **trusted and therefore not part of the intended MVP proof architecture**. Do
not grow it. Do not route official MVP claims through it. Bypass it with the certified emission
path (`GoAst` → `GoPrint` → `GoCompile` → `GoEmit` — the ONLY blessed emit, certificate-required;
`ARCHITECTURE.md` governs the spine), isolate it as a research/integration tool, or delete the
pieces superseded by certified architecture. Trusted plugin output never inherits certified
claims it has not earned: the official MVP output comes from the certified theorem path, and a
broad generated `main.go` from the trusted plugin is not stronger than a tiny certified emitted
artifact. Do not preserve plugin behavior because it emits impressive Go. (Today: no theorem
relates the plugin's emitted Go to the source term — gap #10; the extracted printer is wired in
for only a SMALL expression class, single-sourced in `PROGRESS.md`, and even there the plugin
CONSTRUCTS the `GExpr` unverified.)

## Syntax authority

The syntax authority is **relational/canonical grammar plus canonical-token injectivity and
lexical faithfulness** — target shapes: `CanonExpr : Prec -> GExpr -> list Token -> Prop`
(likewise `CanonStmt`/`CanonProgram`), `gprint_expr_canonical`/`gprint_stmt_canonical`/
`gprint_program_canonical`, `canon_expr_unique`/`canon_stmt_unique`/`canon_program_unique`,
`lex_gprint_expr`/`lex_gprint_stmt`/`lex_gprint_program`. Printer correctness is proved against
the canonical grammar. Executable parsers, if kept, are **derived tooling** proved
**complete** against the relational grammar — never the authority, never the foundation of
printer correctness. (Soundness in the `parse ts -> CanonExpr` direction is NOT generally
attainable: the current Acc-structural parser accepts redundant parens, so it is
complete-not-sound — `parse_complete` holds, `parse_sound` is FALSE as stated. The parser is
fuel-free but implementation-centered; the canonical layer is the stronger endpoint.)

## CFG law

CFGs are in the MVP only when backed by formal CFG syntax, well-formedness, unfueled
terminating evaluation, coinductive divergence, determinism/uniqueness, eval/diverge
disjointness, and certificate-checked termination/divergence (`GoCFG.v` is exactly this layer;
`GoCFG.blocks_cfg_surface` is its gate). Otherwise CFGs are outside the MVP. Emission-only
markers never live in semantic modules: a name that exists only because the plugin lowers it
belongs in `GoExtractionHooks.v` or gets deleted. "Panics if evaluated model-side" is a hook
guard in an isolated hook module — never a certified semantic definition.

## Demos and tests

`main.v` and `expected_output.txt` are high-level integration/log-diff checks only — useful
regression tools, never proof evidence. They cannot certify semantics, safety, supportedness,
termination, divergence, Go adequacy, or MVP readiness. A demo may illustrate a theorem-backed
feature; it cannot make an unsupported feature supported. Demos of uncertified/legacy behavior
are deleted or isolated; new demos exercise theorem-backed behavior through the certified path.
Never add a demo that previews unsupported semantics and call it progress.

## Workflow & commands

Verify-then-bless after an intended change: **`make check`** (re-extracts, runs, diffs vs the
golden — confirm the delta is exactly what you intended) → **`make golden`** (bless
`expected_output.txt`) → commit → re-index. **Run/verify ONLY through make targets — never a
bare `go run`** (it can validate stale Go). After every successful commit, re-index the
codebase-memory MCP (`index_repository`, mode `fast`) if connected.

```
make build         # full Docker build → static binary
make extract       # pull generated Go into the repo (runs gofmt -w)
make check         # extract + run + diff vs expected_output.txt   ← the verify step
make golden        # extract + show delta + bless expected_output.txt
make run-local     # extract + go run (no Docker; needs a host Go)
make negtest       # fail-closed harness: assert each negtests/*.v ABORTS extraction
make install-hooks # activate the pre-commit hook (once after clone)
```

## Files

- **The model modules** (the COMPLETED builtins split — `builtins.v` is DELETED):
  `GoNumeric.v` (records + the pure op layer + min/max
  + float comparisons), `GoRuntimeTypes.v` (tags/GoAny/zero values/runtime comparability),
  `GoEffects.v` (World/Outcome/IO/effect laws, output, block-scoped defer, int range),
  `GoPanic.v` (panic payloads), `GoSlice.v` (pure-list slices/arrays/variadics/slice range),
  `GoMap.v`, `GoChan.v` (channels + the go-mem story), `GoHeap.v` (the ref heap: locals,
  pointers, nil-safety, SliceH aliasing, the struct heap), `GoSession.v`, `GoString.v`
  (strings/UTF-8/ComparableW), `GoSwitch.v` (type asserts + every switch combinator),
  `GoComplex.v`, plus `GoCFG.v` and `GoExtractionHooks.v` (ONLY names the plugin lowers by
  name). Plugin-recognized hooks stay isolated from semantic definitions; semantic modules
  never export hooks as authority. `preamble.v` declares the ML plugins ONLY — narrow imports
  everywhere, never a re-export fog. Plugin ownership is the exact-dirpath `model_dirpaths`
  whitelist (`from_model`), hooks separate (`from_hooks`).
- `GoAst`/`GoPrint`/`GoTypes`/`GoCompile`/`GoEmit` — the certified-emission spine; `GoSem*` slices
  behavior (the `cmd.v` bridge; bridge or retire `unified.v`/`concurrency.v`, never fork a
  second universe); `cmd.v` — the effect evaluator the bridge agrees with;
  `unified.v`/`concurrency.v` — proof-only.
- `main.v` — extraction driver (`Go Main Extraction`) + integration demos (see "Demos").
- `plugin/go.ml` (+ `g_go_extraction.mlg`) — the trusted extraction backend (see "The trusted
  plugin"). Ops recognized by name; their `.v` bodies suppressed.
- `SPEC_CONFORMANCE.md` — the Go-spec conformance ledger. `EXPECTED_ASSUMPTIONS.txt` — the
  asserted axiom set (EMPTY; the manifest gate fails the build on drift).
- `negtests/` — the fail-closed harness (each `*.v` MUST abort extraction; first line
  `(* EXPECT: <substring> *)`).

Gotchas: **`gofmt` is load-bearing** (`make extract` runs it; do not remove). **Extraction is a
side effect of compiling `main.v`** — dune doesn't track it; the build forces re-extraction; do
NOT "fix" a missing `.go` by touching `main.v`. **The generated `*.go` is gitignored + never committed:**
`make extract` regenerates it and `make check` re-verifies, so it can never drift. **Pre-commit
hook** (`make install-hooks`) re-extracts on any `.v`/plugin change and SEALS the tree — a commit fails
fail-closed if any `*.go` is ever tracked (`make check` enforces the same seal for CI).

## Where the detail lives

- **`ARCHITECTURE.md`** — ★ the binding charter. Read before any structural change; it governs.
- **`PROGRESS.md`** — the live status ledger (GREEN/RED/NEXT, trust base, the single-sourced
  gate list). Update it when a claim changes.
- **`LESSONS.md`** — expensive mistakes. Read before lifting a printer/parser into Rocq or
  adding any "escape hatch."
- **`git log`** — the archive; commit messages carry rationale. History lives there, never in
  active code or docs.
