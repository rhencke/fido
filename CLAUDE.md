# Fido

**Verified model components with a TRUSTED extraction backend** (the honest claim — *not* yet "formally
verified Go"). Theorems are proved in Rocq (Coq); the `*.go` is a **proof artifact extracted from `*.v`** —
never hand-written, never edited. ⚠️ The plugin (`plugin/go.ml`) is **trusted and unverified**: no theorem
relates the emitted Go to the source term (gap #10), so the golden tests are the only end-to-end check. The
AST-first spine (`GoAst`/`GoPrint`/`GoTypes`/`GoSafe`/`GoEmit`) is the path toward closing that gap — a clean
zero-axiom printer with a proven EXPRESSION round-trip (programs/statements: print-injectivity only — no
parser yet), self-consistent with its own Rocq grammar (NOT a Go-parser-acceptance proof), and gated
certified emission. ⚠️ But the extracted printer is wired into the LIVE plugin for only a SMALL expression
class (a binop tree over runtime locals + integer literals + a fixed set of runtime numeric conversions and
fixed-width arithmetic as bridging-binop operands — the exact list is single-sourced in `PROGRESS.md`, not
re-enumerated here). And even there the split is narrow: the TRUSTED plugin CONSTRUCTS the `GExpr` (chooses the
AST) and only the VERIFIED `gprint` PRINTS it — the construction is NOT verified (the proofs cover AST→string
serialization only, NOT the MiniML→AST construction that feeds it). Everything else is trusted OCaml `pp_expr`,
likewise unverified in its construction; so the live `main.go` is NOT verified Go. There is no behavioral-safety
layer yet. Until gap #10 closes and `GoSem`-backed safety exists, do not headline this as "formally verified
Go." Current state: `PROGRESS.md`.

**Goal — a long-term TARGET, NOT today's state:** faithfully model *all* of Go in Rocq and lower it to
ordinary Go, with the safety properties Go's compiler can't prove — no nil deref, use-after-close,
out-of-bounds, send-on-closed, failed assertion, data race, silent overflow — as the **behavioral-safety
target**, to be ruled out at compile time before behaviorally safe Go is emitted, *once `GoSem`/`BehaviorSafe`
exist*. ⚠️ TODAY the certified-emission spine gates SUPPORTED SYNTACTIC emission ONLY (`SupportedProgram`);
there is NO behavioral-safety gate yet. `PROGRESS.md` is the authority for goal, current status, and roadmap.

## ★ Architecture direction — `ARCHITECTURE.md` GOVERNS (binding; read it)

As of 2026-06-28 Fido is course-correcting to an **AST-first, proof-gated emission** architecture; the
standing charter **`ARCHITECTURE.md`** is binding on every change and wins when in doubt. Spine: **`GoAst`**
(structured Go syntax) → **`GoPrint`** (printing + expression parse round-trip / program print-injectivity —
SYNTAX only) → **`GoSem`** (behavior;
SLICE 1 landed — the `cmd.v` bridge + real println/print/panic effect denotation + denotation⊆gate soundness;
it must continue to bridge the existing proof-only semantics `unified.v`/`concurrency.v` (or retire them), not
fork a second; NO completeness / NO BehaviorSafe yet) →
**`GoSafe`** (`SupportedProgram` syntactic gate now; `BehaviorSafe` later) → **`GoEmit`** (the ONLY blessed
emit, requires a certificate — `EmittableProgram` now, `SafeProgram` later; NO official
`emit : Program -> string`). The clean printer/parser work + `ConvTy` groundwork ARE now `GoAst` + `GoPrint`
(the split landed in spine commit 1; do not reintroduce a parallel syntax universe); `plugin/go.ml` is trusted/transitional and is NOT grown;
`relooper.v` is demoted. **Naming is a correctness claim** — never call a syntactic gate `SafeProgram`.
Residual TCB TODAY (named, not implicit): Rocq kernel · the string→`.go` extraction step · the Go toolchain ·
trusted foreign imports · **the trusted, unverified plugin `plugin/go.ml`** that lowers `main.go` (gap #10 —
the current adequacy gap). FUTURE (NOT today's TCB, since no GoSem-BACKED EMISSION exists yet — GoSem slice 1
denotes programs but does not gate emission): once emission goes through a GoSem-backed certificate, the plugin
is replaced by a `GoSem`≈real-Go adequacy assumption (gap #10's heir).

## Rules that shape every change

1. **Never edit `*.go`.** It is extracted from `*.v`. Change the `.v` / plugin and
   re-extract. (`*.v` and `*.go` are both committed; `*.go` is always re-derivable.)
2. **Model honestly — faithful or fail-loud, never plausible-but-wrong.** Small
   scope is fine; *wrong* or *partial* semantics is not. "It's hard" means do the
   work, not model less. The plugin's `unsupported` ABORTS extraction for anything
   it can't lower correctly — the meta-invariant. The only acceptable deviations
   are principled and bounded (a deliberate safety guarantee) — and documented as such.
   ⚠️ **NEVER add a raw / opaque / string-rescue escape hatch to a structured AST**
   (see the `LESSONS.md` postmortem). Build structured-or-fail-loud; if a construct
   can't be represented structurally yet, REJECT it mechanically, never preserve it as text.
3. **Zero axioms — the model's trust base is now EMPTY; preserve it.** The whole IO /
   heap / channel / session AND numeric (int/float) model is `Definition`s / `Record`s
   over concrete Rocq data (`Z` for integers, `SpecFloat.spec_float` for IEEE-754
   floats, a concrete `World` / `Outcome`); every law is a *derived theorem*. As of
   commit 445aca3, `Print Assumptions main_effect` is **"Closed under the global
   context" — ZERO axioms** (the old `PrimInt63.*` / `PrimFloat.*` substrate is gone:
   integers are `Z`, locations `nat`, floats `spec_float`). Model every new builtin as
   a `Definition` / `Record`, **never** an `Axiom` / `Parameter` / `Admitted` AND never
   a kernel PRIMITIVE (`PrimInt63` / `PrimFloat`) — those are axioms too; model in
   `Z` / `spec_float`. Run `Print Assumptions <thm>` after a significant result and keep
   it empty. (This is the MODEL's logical trust base; the extraction plugin is a
   SEPARATE, still-trusted/unverified TCB — gap #10.)
4. **Partial / unsafe ops are safe-by-construction or proof-gated.** The unsafe
   primitives (nil deref, OOB, div-by-zero, send-on-closed, failed assertion) are
   modelled, but their unsafe use is forbidden: prefer an **evidence-carrying** API
   (demand `i < len`, `d <> 0`, non-nil; then extract to the raw op) or a
   **check-and-branch** (comma-ok / `option`, as `map_get_opt`). Raw panicking
   forms survive only as explicitly-marked escape hatches (in `IO`, `catch`-able).
   You should never *accidentally* write a Rocq program that needs a nil deref.
5. **Imports are on hold.** Emit `package main`, no `import` block. Defer any
   builtin that needs one (`math.Abs`, `fmt`, stdlib) — do NOT approximate it (no
   hand-rolled `abs` that mishandles `-0.0`). Finish the no-import layer first.

## Workflow & commands

Verify-then-bless after an intended change: **`make check`** (re-extracts, runs,
diffs vs the golden — confirm the delta is exactly what you intended) →
**`make golden`** (re-shows the delta + blesses `expected_output.txt`) → commit →
**re-index**. The diff lives in the Makefile; don't diff by hand. **Run / verify
ONLY through these targets — never a bare `go run`** (it bypasses extraction and
can validate stale Go).

**After every successful commit, re-index the codebase-memory MCP**
(`index_repository`, mode `fast`). The index is a static snapshot — it has no
self-update and can't hook git — so a commit silently staling it is the default
unless you re-index. (Only relevant when that MCP is connected; a git hook can't
do this — re-indexing is an MCP call the agent must make, not a shell command.)

```
make build         # full Docker build → static binary
make extract       # pull generated Go into the repo (runs gofmt -w)
make check         # extract + run + diff vs expected_output.txt   ← the verify step
make golden        # extract + show delta + bless expected_output.txt
make run-local     # extract + go run (no Docker; needs a host Go)
make negtest       # fail-closed regression harness: assert each negtests/*.v ABORTS extraction (host rocq)
make install-hooks # activate the pre-commit hook (once after clone)
```

`expected_output.txt` is the golden runtime output — a cheap end-to-end check that
a Rocq / plugin change didn't alter observable behaviour anywhere. The demos in
`main.v` are the test suite.

## Architecture

- `builtins.v` — the modelled Go layer (always in scope via `preamble.v`).
- `main.v` — extraction driver (`Go Main Extraction`) + the demos that test it.
- `plugin/go.ml` (+ `g_go_extraction.mlg`) — the Rocq → MiniML → Go extraction
  plugin (~3000 lines, incl. the relooper). Ops are recognized **by name** and
  their `.v` bodies suppressed. **Trusted and unverified** — no theorem relates the
  emitted Go to the source term; golden tests are the only check (a real gap, not
  overclaimed — see `PROGRESS.md` Known gaps #10).
- `concurrency.v` — proof-only (emits no Go): trace-based happens-before, the rich
  `rstep`/`rstepC` concurrency calculi, ownership/race-freedom, the bounded deadlock
  theory. The trace/hb/race theory is calculus-AGNOSTIC — which is what lets
  `unified.v` reuse it.
- `unified.v` — proof-only (emits no Go): an EXISTING closed-world operational semantics
  that unifies the admitted effects into one calculus — a single command language `UCmd`
  carrying ALL effects (goroutines/channels/heap/panic/defer/output), one config `UConfig`,
  one step relation `ustep` (faithful defer+panic: a panicking goroutine still runs its
  remaining defers). Race-freedom (`uprivate_disc_reachable_race_free`) and liveness/deadlock
  (`uready_can_step` / `ustuck_blocked`) are PROVED on it, reusing concurrency.v's trace theory.
  ⚠️ It is NOT the semantics of the certified-emission path — GoSem (slice 1 bridges `cmd.v`) must still
  bridge or retire it before behavioral safety enters certified emission. The shallow `IO`/`World`, the
  `cmd.v` effect evaluator, and `rstep` are earlier, NARROWER fragments.
- `cmd_unified.v` — proof-only (emits no Go): the FIRST slice of that bridge. `cmd_to_ucmd` totally
  translates `cmd.v`'s command tree into `unified.v`'s output/panic/return/defer fragment, and
  `cmd_to_ucmd_runs` proves output-preservation + run-to-done for the DEFER-FREE fragment (the one GoSem
  slice 1 denotes), so that fragment's `cmd.v` denotation runs under the SAME `ustep` race-freedom holds on.
  Defer + channel/heap/spawn effects are later slices. Zero axioms.
- `preamble.v`, `dune` / `dune-project` — shared preamble; Docker build of plugin +
  theories.
- `SPEC_CONFORMANCE.md` — the Go-spec conformance ledger.
- `EXPECTED_ASSUMPTIONS.txt` — the asserted trust base: the exact axiom set the gated `Print
  Assumptions` cones may depend on — `main_effect` (the extracted model) AND GoSem's
  `gosem_trust_surface` (the bundled certified GoSem results). As of 445aca3 this file is
  **EMPTY** — the model is axiom-free ("Closed under the global context"); the old
  PrimInt63/PrimFloat substrate is gone (integers `Z`, locations `nat`, floats `spec_float`).
  The Dockerfile's prover stage extracts EVERY module's `Axioms:` report (via the shared
  `plugin/manifest-axioms.sh`) and diffs it against this file, FAILING the build on any drift
  (ANY axiom now reappearing is a regression). If a change *intentionally* alters the trust
  base, regenerate it (C-locale sort, from a fresh local build):
  `rm -f _build/default/main.vo _build/default/GoSem.vo && dune build 2>&1 | sh plugin/manifest-axioms.sh | LC_ALL=C sort -u > EXPECTED_ASSUMPTIONS.txt`
- `negtests/` — the fail-closed regression harness (`make negtest`, review #4 R10). Each
  `negtests/*.v` is a program that hits a fail-CLOSED backend site; its first line declares
  `(* EXPECT: <substring> *)`, the `unsupported` message extraction MUST abort with. `run.sh`
  compiles each and asserts the abort — a fixture that EXTRACTS instead means a fail-closed
  site reopened (plausible-but-wrong Go where rule 2 demands a loud abort), the defect class
  the happy-path golden CANNOT see. Runs NON-bypassably in the Docker prover stage on every
  `make check`/`make extract` (after the axiom-manifest gate), AND locally via `make negtest`
  (host `rocq`). The fixtures live outside the Fido theory's `(modules …)`, so `dune build`
  never compiles them as theory modules — the harness compiles each explicitly, expecting the abort.

Gotchas (don't relearn these the hard way):

- **`gofmt` is load-bearing.** `make extract` runs `gofmt -w`; the plugin emits
  valid but non-canonical whitespace. **Do not remove the `gofmt -w` step.**
- **Extraction-driver recompile.** Generated `*.go` is a *side effect* of compiling
  `main.v`; dune doesn't track it. The build nukes stale `*.go` and forces
  re-extraction. Do NOT "fix" a missing `.go` by touching `main.v` — that masks the
  real cause.
- **Pre-commit hook** (`make install-hooks`): when a `.v` / `plugin/` file is
  staged it re-extracts and auto-stages the Go (a broken proof aborts the commit),
  so committed `*.go` can never drift from prover output.

## Where the detail lives

CLAUDE.md is deliberately short. Read these on demand:

- **`ARCHITECTURE.md`** — ★ the standing, BINDING charter: the AST-first certified-emission direction
  (`GoAst`/`GoPrint`/`GoTypes`/`GoSafe`/`GoEmit`, with `GoSem` slice-1 landed), the residual-TCB statement, and the
  per-patch rules. Read it before any structural change; it governs.
- **`PROGRESS.md`** — the short live status ledger: current architecture, GREEN / RED / NEXT, the known
  trust base, and the current gates. **Update it when a feature lands or a claim changes.**
- **`SPEC_CONFORMANCE.md`** — the Go-spec conformance ledger (per spec section: the
  rule cited, our behaviour, ✓ conforms / ⚠ bounded deviation / ✗ fails loud, and
  the machine-checked witness). A primitive is "done" only when its section is
  honored here.
- **`LESSONS.md`** — hard-won, expensive mistakes (the `SRaw` raw-string-hatch teardown).
  Read before lifting a printer/parser into Rocq or adding any "escape hatch" constructor.
- **`git log`** — what changed when; commit messages carry the detailed rationale.
