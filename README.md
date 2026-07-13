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

- **One program representation.** A `GoProgram` is a **nonempty** verified finite map from intrinsic
  `FilePath` keys to one raw file AST per file (a raw string is **not** a path — Go package discovery
  depends on it, so only a narrow canonical grammar is representable). A raw file is just top-level
  declarations; **package clauses, package names, and entry-point status are compilation results**, not raw
  metadata. There is no second tree and no separate IR.
- **Exact, whole-program compilation.** `GoCompile` consumes the whole map: it groups files by directory
  into `package main` packages, requires exactly one `main` per package, and rejects the whole program on
  any invalid package. It is a declarative judgment with a proof-producing sound + complete decision, aimed
  at matching `go build ./...` for every representable program. Two claims stay distinct: (A) the checker
  matches the formal judgment — PROVED; (B) it matches `go build ./...` — the GOAL, exercised
  differentially, never a kernel theorem about `cmd/go`.
- **Real semantics + faithful rendering.** `GoSafe` evaluates to real Go values (`VInt : Z`, so `0` and
  `-0` agree). `GoRender` proves `render_expr_denotes` — the rendered spelling denotes exactly the value —
  plus all-ASCII, no illegal leading zero, and the header as the exact first line. Every layer is proved
  **axiom-free** in a pinned Rocq 9.2.0 container.
- **A transport boundary, not a backend.** The image is an abstract `DirectoryImage` carrying a proof it
  came from rendering a `SafeProgram`. One general Rocq command, `Fido Emit <image> To "<dir>"`, guards
  provenance before any effect — it typechecks the image type and rejects a non-empty assumption closure
  (kernel queries, so a postulated axiom/variable proof cannot cross), then decodes only the final
  (path, bytes) data and hands it to a generic **ownership-aware dirty-directory synchronizer** (a
  persistent control dir + lock; the root path is validated against prefix symlinks; `.fido/` is a reserved
  namespace; installed `.go` owned by its header first line, transient staging through ONE fixed slot
  `.fido/staging/tmp` — atomically `O_EXCL`-created then renamed, with fail-closed recover-all-or-reject
  that accepts only the empty-or-one-slot state; foreign entries OUTSIDE `.fido/` are preserved — except a
  `.go` forging the exact header, which is indistinguishable from a stale generated file and is the one
  accepted limit; symlinks
  never followed). No handwritten OCaml walks a program.

The admitted fragment is deliberately tiny; anything else is **unrepresentable**, not stubbed. Imports are
absent and unrepresentable — a permanent closed-world contract governs their eventual introduction.

## Verify it

All Rocq/Go runs go through the pinned toolchain via `buildx` (host Rocq is unsupported):

```
make check   # gates + pinned-Rocq proof (axiom-free) + pinned-Go whole-tree e2e (go build ./... + goldens)
```

## Where to read next

- `ARCHITECTURE.md` — the binding charter. · `PROGRESS.md` — what is proved+executed and the frontier. ·
  `PAINFUL_LESSONS.md` — the mistakes that shaped this design. · `CLAUDE.md` — the operating law.
