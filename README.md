# Fido

A theorem-first experiment in a **proved** Go generator. An untrusted proposer (an LLM) may write a raw Go
AST and arbitrary supporting lemmas; **Fido emits `.go` only after Rocq proves the program
compile-admissible and safe.** It will never be "formally verified Go" — Go's own toolchain is trusted — but
the path from AST to bytes is built from proved layers, and the last mile is an integration check.

## What actually works today

One complete vertical slice, proved **and** executed end to end. A witness exercising every admitted
primitive:

```go
package main

func main() {
	println(true, 42, -1, -9223372036854775808)
	println()
	println(false)
}
```

is produced from proved bytes and synchronized into a directory, then built + run by the pinned Go toolchain;
its stdout/stderr/exit are compared byte-for-byte to reviewed goldens. Every emitted file begins with the
exact line `// fido generated.  do not edit.` — part of the Rocq-rendered bytes.

- **One program representation.** A `GoProgram` is a verified finite map from relative paths to raw file ASTs
  (`package main`/`func main` are structural, not identifiers; the builtin `println` is the statement).
  Duplicate paths are unrepresentable. `GoCompile`/`GoSafe` are EVIDENCE over that same program — there is no
  second "compiled" tree and no raw package hierarchy; compilation adds facts, never another tree.
- **Exact, whole-program compilation.** `GoCompile` is exact compiler admissibility for the representable
  domain (the obligations are: the single file is at the canonical build path `main.go`, and every integer is
  representable) — a declarative judgment with a proof-producing sound + complete decision, never a boolean.
  A rejected program is genuinely compiler-invalid — an out-of-range integer, or a key the Go build wouldn't
  compile (a non-`.go` name, a traversing/absolute/nested path) — rejected in Rocq, never left for the writer.
  Two honest claims stay distinct: (A) the checker matches the formal judgment — PROVED; (B) accepted
  programs are accepted by real Go — the GOAL, exercised by the e2e, never a kernel theorem.
- **Real semantics.** `GoSafe` evaluates to real Go values (`VInt : Z`, so `0` and `-0` agree). `GoRender`
  proves its output is all-ASCII, that the emitted decimal denotes exactly the value, that it never has an
  illegal leading zero, and that the header is the exact first line. Every layer is proved **axiom-free** in a
  pinned Rocq 9.2.0 container.
- **A dumb sink.** All semantic work is in Rocq; standard extraction produces the final `(path, bytes)` image
  plus the ownership header; one handwritten OCaml **dirty-directory synchronizer** installs it (lock +
  `lstat`-preflight + staging + atomic rename), cleaning its own stale output while refusing to touch any
  foreign entry. No handwritten code walks or decodes Rocq terms — it understands only the filesystem.

The admitted fragment is deliberately tiny: one program → one `package main` file → one `func main()`,
straight-line builtin `println` over bool/int literals. Anything else is **unrepresentable**, not stubbed.

## Verify it

All Rocq/Go runs go through the pinned toolchain via `buildx` (host Rocq is unsupported):

```
make check   # gates + pinned-Rocq proof (axiom-free) + pinned-Go e2e (extract + build/run vs goldens)
```

## Where to read next

- `ARCHITECTURE.md` — the binding charter. · `PROGRESS.md` — what is proved+executed and the frontier. ·
  `PAINFUL_LESSONS.md` — the mistakes that shaped this design. · `CLAUDE.md` — the operating law.
