# Fido — Certified Emission Charter (binding)

Read before any structural change. This governs.

## What Fido is

A **proved Go generator**. Everything that decides the emitted program lives in Rocq and is proved; the
only OCaml is standard extraction output plus a build-generated one-line writer that prints proved bytes.

The certified pipeline, in one line:

```
Rocq: GoAst ──▶ GoPrint ──▶ GoTypes ──▶ GoCompile ──▶ GoEmit.demo_emit (: string, bytes proved)
        │
   standard Rocq extraction ──▶ emit_demo.ml ──▶ (build-generated) print_string ──▶ spine_demo.go
        │
   pinned Go toolchain: gofmt -l (no-op) + go build + go vet  ── trusted last-mile check
```

- `GoAst` — the Go syntax: `GExpr` / `GoTy` / operators, and `classify`. No parenthesis nodes; precedence
  and associativity are structural.
- `GoPrint` — the printer (`gprint` / `print_ty` / `print_stmt` / `print_program`), a proof-only
  lexer/parser, and the round-trip + **injectivity** theorems. The **relational canonical grammar**
  (`CanonExpr` / `CanonStmt` / `CanonProgram`, with `canon_*_unique` and `lex_gprint_*`) is the syntax
  authority; the executable parser is derived tooling, proved **complete** against the grammar and
  **not** sound (it accepts redundant parens) — nothing certified depends on it.
- `GoTypes` — the type-category checker; one authority shared by the compiler (and any future semantics).
- `GoCompile` — **static/syntactic admissibility only**. It proves nothing about runtime behavior.
- `GoEmit` — the certified emitter; `demo_emit` is the closed output and `demo_emit_bytes` proves its exact
  bytes.

Foundation: `digits` (the one decimal authority), `GoNumeric` (numerics over `Z`, deliberately not
`Sint63`, to stay axiom-free), `GoRuntimeTypes`, `GoPanic`, `GoEffects`, `GoSlice`.

## Trust base (say this exactly)

- **Trusted:** the Go toolchain (there is NO theorem that Go parses the emitted bytes as the same AST — the
  Go-subset recognition gap is open and Go is trusted), the pinned toolchain images, Rocq/its kernel, and
  the build-generated one-line writer (pure transport of a proved string; it decides nothing).
- **Proved (zero project axioms):** the spine's printer injectivity / canonical-grammar uniqueness,
  `GoCompile` admissibility, and `GoEmit.demo_emit_bytes`. `make check` asserts zero axioms via Rocq's own
  `Print Assumptions`.
- **Not claimed:** semantic safety, panic-freedom, termination/divergence, and real-Go behavioral adequacy.
  `GoCompile` is a *syntactic* gate; naming never implies more (rule 7).

## What is deleted, and stays deleted

The handwritten OCaml backend and the custom extraction plugin (name-based lowering, MiniML/term
inspection, `Go Main Extraction`, an OCaml printer/renderer, emission-only pseudo-semantics, and a broad
demo corpus produced by an unproved backend). Stable output from an unproved backend proves only that the
unproved backend was stable. `tools/ocaml-origin-gate.sh` is the fail-closed tripwire against reintroducing
any of it.

## The root frontier (build each root before the floor above it)

The spine's type/effect foundation is being reset into single authorities. A file that materially depends on
a rejected root is **deleted**, not kept as "transitional" — it reappears rebuilt on the correct root.

1. **One `TargetConfig` + one certified type universe** — identity/underlying/zero/comparability/map-key/
   tokens/renderability derived from ONE descriptor; invalid Go types unrepresentable or rejected by
   elaboration; no parallel "runtime tag" vs "syntax type" universes.
2. **One independent Go grammar, one token stream, one renderer** — the printer proved against a grammar
   defined independently of its own token function; unary/separator rules from real precedence + a
   `needs_separator` token law, not conservative paren tables; full statement/program lexical faithfulness.
3. **Proof-producing compile/elaboration into a typed IR** — `Elaborates` / `TypedProgram` making static
   invalidity unrepresentable, with soundness (and completeness for the supported subset) — not a boolean
   wrapper as the final authority.
4. **A typed object store + value well-formedness** — one `StoreTyping`/`ValueWF` (model faults unreachable
   for well-typed configs); one native slice/map/channel representation each (no ghost counts, no
   `option nat` "unbounded", no pure-list-as-native-slice).
5. **Accurate control / panic / blocking / model-fault** — atomic (Returned | genuine Panicked) split from a
   scheduler relation (block/resume/deadlock/divergence) split from unreachable model faults; structured
   runtime panic values, never strings; no `FunctionalExtensionality`.
6. **One semantics and one safe-emission boundary** — one operational semantics, one lowering to the Go AST,
   one `SafeProgram`-shaped certificate through which official output is emitted. A compile-only certificate
   never inherits behavioral wording.

## Emission discipline

The official output is a generated Rocq function applied to a **closed** value (`GoEmit.demo_emit : string`),
never a foreign-callable `f : Program -> string` whose argument handwritten OCaml constructs (extraction
erases proof fields, so a foreign API is not automatically safe). `gofmt` sits OUTSIDE the byte theorem as a
NO-OP check only — the printer is gofmt-stable; a `gofmt -l` hit is a printer bug.
