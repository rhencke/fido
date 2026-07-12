# Fido

A theorem-first experiment in a **proved** Go generator. An untrusted proposer (an LLM) may write a raw Go
AST and arbitrary supporting lemmas; **Fido emits `.go` only after Rocq proves the program
compile-admissible and safe.** It will never be "formally verified Go" — Go's own toolchain is trusted — but
the path from AST to bytes is proved, and the last mile is an integration check, not a claim.

## What actually works today

One complete vertical slice, proved **and** executed end to end:

```
package main

func main() {
	println(true)
}
```

- The pipeline is `GoAST → GoCompile → GoSafe → GoRender → GoEmit` — the AST *is* the IR; "compiled" and
  "safe" are proofs about one program value, not extra trees. Every layer is proved **axiom-free** in a
  pinned Rocq 9.2.0 container.
- `GoCompile` is exact static admissibility: a declarative relation with an executable checker proved
  **sound, complete, and deterministic** (never a boolean). `GoSafe` is a real no-panic property of an
  operational semantics. `GoRender` is a direct AST→string printer (no lexer/parser/round-trip) with proved
  faithful escaping and all-ASCII output.
- A **one-file transparent transport plugin** (`Fido Emit`) writes the proved bytes to a real `main.go`, and
  the digest-pinned Go toolchain builds + runs it; stdout/stderr/exit are compared byte-for-byte to reviewed
  goldens.

The admitted fragment is deliberately tiny: `package main`, one `func main()`, straight-line builtin
`println` over primitive literals (bool / string / unsigned-magnitude int). Anything else is
**unrepresentable**, not stubbed — a compiler-invalid candidate is rejected in Rocq before any `.go` exists.

## Verify it

All Rocq/Go runs go through the pinned toolchain via `buildx` (host Rocq is unsupported — a different
version could judge proofs differently):

```
make check   # gates + pinned-Rocq proof (axiom-free) + pinned-Go e2e (emit + build/run vs goldens)
```

## Where to read next

- `ARCHITECTURE.md` — the binding charter (layers, responsibilities, trust boundary).
- `PROGRESS.md` — what is proved+executed and the next frontier.
- `PAINFUL_LESSONS.md` — the mistakes that shaped this design, so they don't recur.
- `CLAUDE.md` — the operating law for working in this repository.
