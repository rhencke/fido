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

is produced from proved bytes and built + run by the pinned Go toolchain; its stdout/stderr/exit are compared
byte-for-byte to reviewed goldens.

- **One AST.** `GoAST` is the only program representation (`package main`/`func main` are structural, not
  identifiers; the builtin `println` is the statement). `GoCompile`/`GoSafe` are EVIDENCE over that same
  tree — there is no second "compiled" syntax tree.
- **Exact compilation.** `GoCompile` is exact compiler admissibility for the representable domain (the only
  obligation left is integer representability) — a declarative judgment with a sound + complete + decidable
  decision, never a boolean. A program it rejects is genuinely compiler-invalid (an out-of-range integer),
  never a valid Go program outside the slice.
- **Real semantics.** `GoSafe` evaluates to real Go values (`VInt : Z`, so `0` and `-0` agree). `GoRender`
  proves its output is all-ASCII, that the emitted decimal denotes exactly the value, and that it never has
  an illegal leading zero. Every layer is proved **axiom-free** in a pinned Rocq 9.2.0 container.
- **A dumb writer.** All semantic work is in Rocq; standard extraction produces the final
  `(path, bytes)` image; a ~15-line handwritten OCaml writer does only file I/O. No handwritten code walks or
  decodes Rocq terms.

The admitted fragment is deliberately tiny: `package main`, one `func main()`, straight-line builtin
`println` over bool/int literals. Anything else is **unrepresentable**, not stubbed.

## Verify it

All Rocq/Go runs go through the pinned toolchain via `buildx` (host Rocq is unsupported):

```
make check   # gates + pinned-Rocq proof (axiom-free) + pinned-Go e2e (extract + build/run vs goldens)
```

## Where to read next

- `ARCHITECTURE.md` — the binding charter. · `PROGRESS.md` — what is proved+executed and the frontier. ·
  `PAINFUL_LESSONS.md` — the mistakes that shaped this design. · `CLAUDE.md` — the operating law.
