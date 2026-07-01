# Fido

**Verified model components with a TRUSTED extraction backend** — the honest claim, *not* "formally verified
Go." Theorems are proved in Rocq; each `*.go` is a **proof artifact extracted from `*.v`** — never hand-written,
never edited. The plugin (`plugin/go.ml`) is **trusted and unverified**: no theorem relates its emitted Go to
the source term (gap #10), so the golden tests are the only end-to-end check. The AST-first spine
(`GoAst`/`GoPrint`/`GoTypes`/`GoSafe`/`GoEmit`) is the path toward closing that gap. The extracted printer is
wired into the LIVE plugin for only a SMALL expression class (single-sourced in `PROGRESS.md`), and even there
the TRUSTED plugin CONSTRUCTS the `GExpr` and only the VERIFIED `gprint` PRINTS it — the construction is NOT
verified. The behavioral-safety emission cert is only a NARROW seed (`emit_panic_free`, panic-only, OFF the
main path), not a full gate on the emitted output. Do not headline this as "formally verified Go."
**Current state, goal, and roadmap: `PROGRESS.md`.**

## Architecture direction — `ARCHITECTURE.md` GOVERNS (binding; read it)

Fido is an **AST-first, proof-gated emission** architecture; `ARCHITECTURE.md` is binding and wins when in
doubt. Spine: **`GoAst`** (structured syntax) → **`GoPrint`** (printing + expression round-trip / program
injectivity; SYNTAX only) → **`GoSem`** (behavior; slice 1 — the `cmd.v` bridge; must bridge or retire
`unified.v`/`concurrency.v`, never fork a second universe; NO completeness / NO BehaviorSafe) → **`GoSafe`**
(`SupportedProgram` syntactic gate now; `BehaviorSafe` later) → **`GoEmit`** (the ONLY blessed emit; requires a
certificate — `EmittableProgram` now; NO official `emit : Program -> string`). `plugin/go.ml` is
trusted/transitional and is NOT grown; `relooper.v` is demoted. **Naming is a correctness claim** — never call
a syntactic gate `SafeProgram`.

## Rules that shape every change

**Slow is fine; incorrect is not.** No overclaim, no stale docs; proofs go on the emission path, not beside it.

1. **Never edit `*.go`.** It is extracted from `*.v` (both committed; `*.go` always re-derivable). Change the
   `.v` / plugin and re-extract.
2. **Model honestly — faithful or fail-loud, never plausible-but-wrong.** Small scope is fine; *wrong* or
   *partial* semantics is not. The plugin's `unsupported` ABORTS extraction for anything it can't lower
   correctly. ⚠️ **NEVER add a raw / opaque / string-rescue escape hatch to a structured AST** (`LESSONS.md`
   postmortem): build structured-or-fail-loud; a construct that can't be represented structurally yet is
   REJECTED mechanically, never preserved as text.
3. **Zero axioms — the model's trust base is EMPTY; preserve it.** The whole IO/heap/channel/session and
   numeric model is `Definition`s / `Record`s over concrete Rocq data (`Z`, `nat` locations,
   `SpecFloat.spec_float`); every law is a derived theorem. Model every new builtin as a `Definition` /
   `Record` — **never** an `Axiom` / `Parameter` / `Admitted`, and never a kernel PRIMITIVE
   (`PrimInt63`/`PrimFloat`, which are axioms too). Run `Print Assumptions <thm>` after a significant result and
   keep it empty. (This is the MODEL's trust base; the plugin is a separate, still-trusted TCB — gap #10.)
4. **Partial / unsafe ops are safe-by-construction or proof-gated.** The unsafe primitives (nil deref, OOB,
   div-by-zero, send-on-closed, failed assertion) are modelled, but their unsafe use is forbidden: prefer an
   **evidence-carrying** API (demand `i < len`, `d <> 0`, non-nil, then extract to the raw op) or a
   **check-and-branch** (comma-ok / `option`). Never *accidentally* write a Rocq program that needs a nil deref.
5. **Imports are on hold.** Emit `package main`, no `import` block. Defer any builtin that needs one
   (`math.Abs`, `fmt`, stdlib) — do NOT approximate it. Finish the no-import layer first.

## Workflow & commands

Verify-then-bless after an intended change: **`make check`** (re-extracts, runs, diffs vs the golden — confirm
the delta is exactly what you intended) → **`make golden`** (bless `expected_output.txt`) → commit → re-index.
**Run / verify ONLY through these targets — never a bare `go run`** (it bypasses extraction and can validate
stale Go). After every successful commit, re-index the codebase-memory MCP (`index_repository`, mode `fast`) if
it is connected — the index is a static snapshot with no self-update.

```
make build         # full Docker build → static binary
make extract       # pull generated Go into the repo (runs gofmt -w)
make check         # extract + run + diff vs expected_output.txt   ← the verify step
make golden        # extract + show delta + bless expected_output.txt
make run-local     # extract + go run (no Docker; needs a host Go)
make negtest       # fail-closed harness: assert each negtests/*.v ABORTS extraction (host rocq)
make install-hooks # activate the pre-commit hook (once after clone)
```

The demos in `main.v` are the test suite; `expected_output.txt` is the golden runtime output.

## Files

- `builtins.v` — the modelled Go layer (in scope via `preamble.v`). `main.v` — extraction driver
  (`Go Main Extraction`) + the demos that test it. `cmd.v` — the effect evaluator (`run_cmd`, the authority
  the bridge agrees with). `preamble.v`, `dune`/`dune-project` — shared preamble + Docker build.
- `plugin/go.ml` (+ `g_go_extraction.mlg`) — the Rocq → MiniML → Go extraction plugin. Ops recognized by name,
  their `.v` bodies suppressed. **Trusted and unverified** (gap #10).
- `GoAst`/`GoPrint`/`GoTypes`/`GoSafe`/`GoEmit` — the certified-emission spine (see `ARCHITECTURE.md`).
- `GoSem.v` + `GoSemUnified.v` + `cmd_unified.v` — GoSem slice 1 (the `cmd.v` bridge into `unified.v`);
  `GoSemSafe.v` — the first behavioral-safety PROPERTIES (panic-freedom, incl. a decidable gate-SHAPE
  predicate) + a NARROW panic-only emission cert (`emit_panic_free`, OFF the main path), NOT a full
  BehaviorSafe gate. Status in `PROGRESS.md`. All NOT extracted (`emit_panic_free` builds Go source but is not run).
- `unified.v` — proof-only: the `ustep` operational semantics (race-freedom + liveness/deadlock proved on it),
  NOT the certified-emission path. `concurrency.v` — proof-only: calculus-agnostic trace / happens-before /
  race / bounded-deadlock theory. `relooper.v` — demoted.
- `SPEC_CONFORMANCE.md` — the Go-spec conformance ledger. `EXPECTED_ASSUMPTIONS.txt` — the asserted axiom set
  (EMPTY; the manifest gate fails the build on drift; regenerate via `manifest-axioms.sh` if intentionally
  changed).
- `negtests/` — the fail-closed harness: each `*.v` hits a fail-closed site and MUST abort extraction (first
  line `(* EXPECT: <substring> *)`); runs in the Docker prover stage and via `make negtest`.

Gotchas:
- **`gofmt` is load-bearing.** `make extract` runs `gofmt -w` (the plugin emits non-canonical whitespace). Do
  not remove it.
- **Extraction is a side effect of compiling `main.v`;** dune doesn't track it. The build nukes stale `*.go`
  and forces re-extraction — do NOT "fix" a missing `.go` by touching `main.v`.
- **Pre-commit hook** (`make install-hooks`): when a `.v`/`plugin/` file is staged it re-extracts + auto-stages
  the Go (a broken proof aborts the commit), so committed `*.go` can't drift from prover output.

## Where the detail lives

- **`ARCHITECTURE.md`** — ★ the binding charter (spine, residual TCB, per-patch rules). Read before any
  structural change; it governs.
- **`PROGRESS.md`** — the live status ledger (architecture, GREEN / RED / NEXT, trust base, gates). Update it
  when a feature lands or a claim changes.
- **`SPEC_CONFORMANCE.md`** — the Go-spec conformance ledger.
- **`LESSONS.md`** — expensive mistakes (the `SRaw` raw-string-hatch teardown). Read before lifting a
  printer/parser into Rocq or adding any "escape hatch."
- **`git log`** — commit messages carry the detailed rationale.
