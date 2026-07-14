# Fido

A theorem-first experiment in a **proved** Go generator. An untrusted proposer (an LLM) may write a raw Go
program (as an AST) and arbitrary supporting lemmas; **Fido emits Go only after Rocq proves the whole
program compile-admissible and safe.** It will never be "formally verified Go" — Go's own toolchain is
trusted — but the path from AST to bytes is built from proved layers, and the last mile is a differential
integration check against `go build ./...`.

## What actually works today

One complete vertical slice, proved **and** executed end to end. A witness exercising every admitted
primitive:

```go
// fido generated.  do not edit.

package main

func main() {
	println(true, 42, -1, -9223372036854775808)
	println()
	println(false)
}
```

is produced from proved bytes, synchronized into a directory tree, built by `go build ./...`, and run with
its stdout/stderr/exit compared byte-for-byte to reviewed goldens — alongside representative differential
fixtures (a multi-package tree accepted; no-main and duplicate-main trees rejected; `go list ./...` matches
the emitted package set) that exercise the whole-program rules against real Go.

- **One program representation.** A `GoProgram` is an intrinsic `ModuleSpec` (a narrow canonical module
  path + a singleton Go version — the facts of the generated module, **not** a target config) paired with a
  **possibly-empty** verified finite map from intrinsic `FilePath` keys to one raw file AST per file (a raw
  string is **not** a path — Go package discovery depends on it, so only a narrow canonical grammar is
  representable). The empty file map is a valid module-only program. A raw file is just top-level
  declarations; **package clauses, package names, and entry-point status are compilation results**, not raw
  metadata. There is no second tree and no separate IR.
- **One type authority.** Each raw literal denotes an exact **untyped** constant (`GoConst`); `GoTypes` —
  the single type authority, evidence over the same AST, universe exactly `TBool`/`TInt` — resolves it in a
  use context (choosing a default type and checking 64-bit representability). A literal is not a typed
  value, and there is no typed AST or second IR: `ResolveExpr` is a judgment over the raw syntax, reflected
  by a decision proved sound, complete, and deterministic.
- **Exact, whole-program compilation.** `GoCompile` consumes the whole map: it groups files by directory
  into `package main` packages, requires exactly one `main` per package, requires the whole program is typed
  through `GoTypes`, and rejects the whole program on any invalid package. It is a declarative judgment with
  a proof-producing sound + complete decision, aimed at matching `go build ./...` for every representable
  program. Two claims stay distinct: (A) the checker matches the formal judgment — PROVED; (B) it matches
  `go build ./...` — the GOAL, exercised differentially, never a kernel theorem about `cmd/go`.
- **Real semantics + faithful rendering.** `GoSafe` evaluates to real Go values (`VInt : Z`, so `0` and
  `-0` agree) that carry the **same** `GoType`, and evaluation is that one constant interpretation mapped to
  a value — a resolved expression provably evaluates to a value of its resolved type. `GoRender` proves
  `render_expr_denotes` — the rendered spelling denotes exactly the value — and `render_resolved_expr_denotes`
  (that value also has the resolved type), plus all-ASCII, no illegal leading zero, and the header as the
  exact first line, and renders the `go.mod` directly from the `ModuleSpec` (exact bytes, header first line,
  ASCII). Every layer is proved **axiom-free** in a pinned Rocq 9.2.0 container — asserted by a
  whole-certified-theory assumption-closure audit, not just per-surface `Print Assumptions`.
- **A transport boundary, not a backend.** The image is an abstract `DirectoryImage` — the exact `go.mod`
  bytes plus a (possibly-empty) map of `.go` bytes — carrying a proof both came from rendering one
  `SafeProgram`. One general Rocq command, `Fido Emit <image> To "<dir>"`, guards provenance before any
  effect — it typechecks the image type and rejects a non-empty assumption closure (kernel queries, so a
  postulated axiom/variable proof cannot cross), then decodes only the final `(go.mod, entries)` transport
  and hands it to a generic **ownership-aware dirty-directory synchronizer**. The sink **rejects foreign
  Go/module inputs** (a foreign `.go` in the Go-discovered namespace, a foreign/nested `go.mod`, a nested
  `.fido`) rather than merge them — skipping the opaque dot/underscore/`testdata`/`vendor` trees `go build
  ./...` itself ignores — then stages the complete image into RESERVED sibling temps `<final>.fido-tmp-v1`
  and installs by atomic rename (nested mounts supported; EXDEV fails loud). It validates the root against
  prefix symlinks, reserves `.fido/` (marker + a git-style lock only — no records, no nonce), owns installed
  `.go`/`go.mod` by their header first line, never follows symlinks, and two-phase-recovers abandoned temps
  (whose suffix-stripped path maps to a Fido final path) fail-closed. No handwritten OCaml walks a program.
- **The generated module is a tracked, reviewed artifact.** One pristine content-addressed Buildx
  `generated-module` layer is the output authority; the canonical `go.mod` + `main.go` are committed
  (Fido-headed) so the example builds/runs without Rocq or Docker, while the `.v`/proof sources stay
  authoritative. `make regenerate` rewrites them through the same sink; `make check` verifies the WORKING TREE
  byte-exact against the pristine layer, and a pre-commit hook verifies the proposed STAGED commit the same way
  (a prototype boundary offering reasonable assurance for a cooperating developer, not tamper resistance;
  `--no-verify` bypasses it).

The admitted fragment is deliberately tiny; anything else is **unrepresentable**, not stubbed. Imports are
absent and unrepresentable — a permanent closed-world contract governs their eventual introduction.

## Verify it

All Rocq/Go runs go through the pinned toolchain via `buildx` (host Rocq is unsupported):

```
make check       # gates + pinned-Rocq proof (complete whole-theory audit) + pinned-Go whole-tree e2e vs goldens + tracked-generated byte compare
make regenerate  # rebuild + re-apply the tracked canonical module into the repo via the same sink
```

## Where to read next

- `ARCHITECTURE.md` — the binding charter. · `PROGRESS.md` — what is proved+executed and the frontier. ·
  `PAINFUL_LESSONS.md` — the mistakes that shaped this design. · `CLAUDE.md` — the operating law.
