# Fido

A theorem-first experiment in a **proved** Go generator. An untrusted proposer (an LLM) may write a raw Go
program (as an AST) and arbitrary supporting lemmas; **Fido emits Go only after Rocq proves the whole
program compile-admissible and safe.** It will never be "formally verified Go" — Go's own toolchain is
trusted — but the path from AST to bytes is built from proved layers, and the last mile is a differential
integration check against `go build ./...`.

## What actually works today

One complete vertical slice, proved **and** executed end to end. A witness exercising every admitted
primitive — bool, the ten integer types (incl. the `-(2^63)` boundary), exact float32/float64 constants,
exact complex64/complex128 constants, and byte-sequence strings (empty, ASCII, quote, backslash, tab, CR,
NL) — is the tracked canonical artifact **`main.go`** (not copied into this README, so it cannot drift;
`make check` and the pre-commit hook verify it byte-exact against the pristine `generated-module` layer, and
its reviewed stdout/stderr/exit are `e2e/golden.*`).

That program is produced from proved bytes, synchronized into a directory tree, built by `go build ./...`,
and run with
its stdout/stderr/exit compared byte-for-byte to reviewed goldens — alongside a boundary-byte string witness
(bytes `0x00`/`0x1f`/`0x7f`/`0x80`/`0xff`, checked byte-exact via an `od` hex oracle) and representative
differential fixtures (a multi-package tree accepted; no-main and duplicate-main trees rejected; `go list
./...` matches the emitted package set) that exercise the whole-program rules against real Go.

The float lines exercise exact float32/float64 **constants**: a bare default-`float64` literal and its
`float32` conversion, explicit conversions, an exact float→int and int→float constant, the
**direct-vs-nested** double-rounding scar shown as exact `uint64` integer observations
(`uint64(float32(2305843146652647425.0e+0))` prints `2305843284091600896` but
`uint64(float32(float64(2305843146652647425.0e+0)))` prints `2305843009213693952` — direct binary32
rounding differs from binary64-then-binary32), and an underflow to `+0`. A bare float denotes its **exact
rational**; a conversion rounds **once** at the destination format (F32 directly at binary32, never through
F64). Float printing is Go's runtime `%e` format and is integration evidence only. It is still exact float
**constants** — no float arithmetic and no imports.

The complex lines exercise exact complex64/complex128 **constants**: a bare complex128-default literal
`complex(1.5, -2.5)`, its complex64/complex128 conversions, zero-imaginary complex→int/float32 conversions,
and the **component** double-round scar as an exact `uint64` observation (direct `complex64` vs nested
`complex128`-then-`complex64`). An untyped complex constant is an exact **pair of rational components** (real
and imaginary); its default type is complex128; complex64/complex128 components are float32/float64; a complex
conversion rounds **each component once**, and a scalar↔complex conversion follows Go's zero-imaginary rule.
Go prints a complex as `(real+imagi)` — integration evidence only. It is still exact complex **constants** —
no complex arithmetic, no `real`/`imag`, no imports.

- **One program representation.** A `GoProgram` is an intrinsic `ModuleSpec` (a narrow canonical module
  path + a singleton Go version — the facts of the generated module, **not** a target config) paired with a
  **possibly-empty** verified finite map from intrinsic `FilePath` keys to one raw file AST per file (a raw
  string is **not** a path). A raw file is a source-shaped `GoSourceFile` — a **source-owned package clause**,
  an intrinsically-empty import section, and its declarations; package **grouping**, entry-point status, and
  import **resolution** are compilation results. There is no second tree and no separate IR.
- **One type authority.** Each raw literal denotes an exact **untyped** constant (`GoConst`); `GoTypes` — the
  single type authority, evidence over the same AST (universe `TBool` / the integer family `TInteger` (ten
  members) / `TFloat` (`float32`/`float64`) / `TComplex` (`complex64`/`complex128`) / `TString`) — resolves it
  in a use context (an untyped int defaults to `int` and its range is checked; a bare float to `float64`; a
  bare complex to `complex128`; every string representable as `TString`). An explicit conversion is a **typed**
  constant of the destination type, routed through one target-directed `convert_const` authority (integer
  conversions value-preserving + range-checked at every nesting layer; float/complex conversions round once —
  each complex component once; scalar↔complex by Go's zero-imaginary rule). A literal is not a typed value,
  and there is no typed AST or second IR.
- **Exact, whole-program compilation = the pinned one-shot `go build ./...` acceptance.** `GoCompile p :=
  fresh_build_preflight_ok p /\ SourceProgramValid p`: it groups files by directory into `package main`
  packages, requires the source valid (typed through `GoTypes`, plus the two factored package rules —
  name uniqueness and main-package entry), AND models cmd/go's default-OUTPUT behaviour (a sole main package
  whose default executable name collides with an existing root directory is rejected). Two claims stay
  distinct: (A) the checker matches the formal judgment — PROVED; (B) it matches `go build ./...` — the GOAL,
  exercised by a differential matrix, never a kernel theorem about `cmd/go`.
- **Real semantics + faithful rendering.** `GoSafe` evaluates to real Go values that carry the **same**
  `GoType` and are range-well-formed; evaluation is partial (a compiler-invalid conversion has no value), so a
  resolved expression provably evaluates to a well-formed value of its resolved type. `GoRender` proves
  `render_const_info_denotes` (a spelling denotes exactly the ConstInfo GoTypes computes) and
  `render_resolved_expr_denotes`, plus all-ASCII and the header as the exact first line, and renders the
  `go.mod` directly from the `ModuleSpec`. Every layer is proved **axiom-free** in a pinned Rocq 9.2.0
  container — asserted by a whole-certified-theory assumption-closure audit, not just per-surface `Print
  Assumptions`.
- **A transport boundary, not a backend.** The image is an abstract `DirectoryImage` (the exact `go.mod` bytes
  plus a possibly-empty map of `.go` bytes) carrying a proof both came from rendering one `SafeProgram`.
  Publication is ONE validate-before-publish workflow, never a standalone publish command: the SOLE Rocq
  transport vernac `Fido Materialize` writes the authoritative pristine bytes into a fresh disposable root, the
  pinned `go build ./...` **validates** that tree, and only THEN does the internal sink (its own test driver +
  the `make regenerate` apply CLI) publish the SAME validated bytes — a failed build prevents publication.
  There is NO public `Fido Emit`. `Fido Materialize`'s guards run before any effect (typecheck the image type
  + reject a non-empty assumption closure, so a postulated proof cannot cross). The sink is a generic
  **ownership-aware dirty-directory synchronizer** that **rejects foreign Go/module inputs** rather than merge
  them, stages the complete image into reserved sibling temps, installs by atomic rename, and
  two-phase-recovers abandoned temps fail-closed. No handwritten OCaml walks a program.
- **The generated module is a tracked, reviewed artifact.** One pristine content-addressed Buildx
  `generated-module` layer is the output authority; the canonical `go.mod` + `main.go` are committed
  (Fido-headed) so the example builds/runs without Rocq or Docker, while the `.v`/proof sources stay
  authoritative. `make regenerate` rewrites them through the SAME validate-before-publish workflow (the
  deployed path IS the tested path); `make check` verifies the WORKING TREE byte-exact against the pristine
  layer, and a pre-commit hook verifies the proposed STAGED commit the same way (a prototype boundary offering
  reasonable assurance for a cooperating developer, not tamper resistance; `--no-verify` bypasses it).

The admitted fragment is deliberately tiny; anything else is **unrepresentable**, not stubbed. Imports are
absent and unrepresentable — a permanent closed-world contract governs their eventual introduction.

## Verify it

All Rocq/Go runs go through the pinned toolchain via `buildx` (host Rocq is unsupported):

```
make check       # gates + pinned-Rocq proof (complete whole-theory audit) + pinned-Go whole-tree e2e vs goldens + tracked-generated byte compare
make regenerate  # fresh go build ./... validates the pristine, THEN re-applies the SAME bytes into the repo via the sink
```

## Where to read next

- `ARCHITECTURE.md` — the binding charter. · `PROGRESS.md` — what is proved+executed and the frontier. ·
  `PAINFUL_LESSONS.md` — the mistakes that shaped this design. · `CLAUDE.md` — the operating law.
