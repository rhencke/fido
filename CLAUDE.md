# Fido

**Verified model components with a TRUSTED extraction backend** (the honest claim — *not* yet "formally
verified Go"). Theorems are proved in Rocq (Coq); the `*.go` is a **proof artifact extracted from `*.v`** by
the plugin — never hand-written, never edited. ⚠️ The plugin (`plugin/go.ml`) is **trusted and unverified**:
no theorem relates the emitted Go to the source term, so the golden tests are the only end-to-end check. FOUR
external reviews (2026-06-21 model-layer; 2026-06-22 backend; 2026-06-22 review #3; 2026-06-23 review #4) found
the backend **failing OPEN** at a series of sites — emitting plausible-but-wrong Go (`nil`/`any`/block-zero/
`return`, a dropped branch, a dropped `recv`/comma-ok CPS continuation, an uncast narrow boundary, a
non-injective identifier) where rule 2 demands a fail-loud `unsupported`. **Every enumerated fail-OPEN site has
since been CLOSED** — the fail-closed sweep (incl. R1 `emit_block` block-body, R2 `recv_ok` + the whole comma-ok
CPS class, the narrow-destination class across all 7 boundaries, raw-CFG entry/terminator validation,
identifier-collision detection at extraction, full-width-int constant forcing, platform-`uint` distinctness)
makes the backend fail LOUD instead, and `go vet` now gates `make check`. ⚠️ But review #4's meta-lesson stands:
a golden-on-one-happy-path can't see an *un-demoed* defect CLASS, so "all sites closed" means "all sites we found
and demoed" — the trusted/unverified status holds. The remaining work is the deep **verified-printer architecture**
(a compiler-correctness theorem connecting source/MiniML semantics to emitted Go — gap #10), **stronger gates** (a
permanent negative-fixture harness, a Print-Assumptions manifest, CI), and a few **latent typed-lowering residuals**
(e.g. narrow `Ref` type-identity). Until gap #10 closes, do not headline this as "formally verified Go" — see
PROGRESS.md "RELEASE REVIEW #3 / #4".

**Goal:** model *all* of Go faithfully in Rocq and lower it to ordinary Go, with
safety properties Go's compiler can't prove — no nil deref, use-after-close,
out-of-bounds, send-on-closed, failed assertion, data race, or silent overflow —
ruled out at compile time before any Go is emitted. Rocq supplies the guarantees;
Go supplies the runtime and primitives (channels, goroutines, maps, slices). Built
incrementally; the long-term target is concurrent programs (session types, race /
deadlock freedom grounded in happens-before, per go.dev/ref/mem). The full vision,
status, and roadmap live in `PROGRESS.md`.

## Rules that shape every change

1. **Never edit `*.go`.** It is extracted from `*.v`. Change the `.v` / plugin and
   re-extract. (`*.v` and `*.go` are both committed; `*.go` is always re-derivable.)
2. **Model honestly — faithful or fail-loud, never plausible-but-wrong.** Small
   scope is fine; *wrong* or *partial* semantics is not. "It's hard" means do the
   work, not model less. The plugin's `unsupported` ABORTS extraction for anything
   it can't lower correctly — the meta-invariant. The only acceptable deviations
   are principled and bounded (a deliberate safety guarantee, or a substrate limit
   like Rocq's 63-bit primitive int) — and documented as such.
3. **Zero Fido axioms — preserve it.** The whole IO / heap / channel / session
   model is `Definition`s over a concrete `World` / `Outcome`; every law is a
   *derived theorem*. The trust base is EXACTLY Rocq's own primitives (`int` /
   `float`, `PrimInt63.*` / `PrimFloat.*`). Model every new builtin as a
   `Definition` / `Record`, **never** an `Axiom` / `Parameter` / `Admitted` (even
   hard cases — e.g. a soft-float `float32`). Run `Print Assumptions <thm>` after a
   significant result and state the base honestly.
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
- `concurrency.v` — proof-only (emits no Go): trace-based happens-before.
- `preamble.v`, `dune` / `dune-project` — shared preamble; Docker build of plugin +
  theories.
- `SPEC_CONFORMANCE.md` — the Go-spec conformance ledger.

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

- **`PROGRESS.md`** — the full vision and principles, the incremental ladder (what
  is modelled, feature by feature), the correctness-debt tiers, known gaps, the
  wish list, and the concurrency research plan. The living status doc — **update
  the ladder there when a feature lands.**
- **`SPEC_CONFORMANCE.md`** — the Go-spec conformance ledger (per spec section: the
  rule cited, our behaviour, ✓ conforms / ⚠ bounded deviation / ✗ fails loud, and
  the machine-checked witness). A primitive is "done" only when its section is
  honored here.
- **`git log`** — what changed when; commit messages carry the detailed rationale.
