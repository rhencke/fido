# Fido — Architecture Charter (binding)

Read before any structural change. This governs. It describes the intended architecture and its
responsibilities — not a shipping product. The design is intentionally minimal: **the AST *is* the IR**;
"compiled" and "safe" are proofs about one program value, not additional trees.

## The law of this repository

Ruthless correctness or ruthless deletion — no middle state. Incomplete scope is acceptable; incorrect,
conservative, duplicated, or "known issue" code in the certified path is not. Do not build a floor on an
unsettled foundation. Cut representable scope before weakening a proof. When twenty local proofs/guards
compensate for one missing root, replace the root and delete the leaves. "Trusted," "works," "stable
output," and "axiom-free" are NOT substitutes for semantic correctness — a green boolean checker is not a
compile authority; a printer that validates itself is not a grammar.

## The pipeline

```
  GoAST          raw proposed Go tree — unproved, possibly compiler-invalid (this IS where an untrusted
                 proposer writes a program).  No unsupported syntax (absent, never narrowed), no paren node.

  GoCompile      exact static/compiler admissibility for the representable domain, PLUS the decorated
                 CompiledFile (the same program with ambiguity replaced by checked facts).

  GoSafe         a real operational semantics + the universal safety floor (no panic) over the CompiledFile;
                 SafeProgram is the emission certificate.

  GoRender       the DIRECT precedence-aware renderer: CompiledFile → string.  No tokens / lexer / parser /
                 round-trip / second AST.

  GoEmit         a Rocq-defined multi-file DirectoryImage (relative paths + exact bytes), path-safety proved.

  Fido Emit      one tiny transparent transport plugin: reduce the proved DirectoryImage in Rocq, decode
                 path+bytes, write files.  Decides nothing.

  pinned Go      the digest-pinned toolchain builds + runs the emitted program.  Integration evidence only,
                 never proof.
```

Data flow: raw `GoAST` → proved `CompilesFile` → decorated `CompiledFile` → `BehaviorSafe` proof →
`SafeProgram` → direct `GoRender` → `DirectoryImage` → `Fido Emit` writes files → pinned Go build/run.

**There is no additional IR.** No `Surface`/`TypedIR`/`GoSyntax`/token/grammar/`CertifiedArtifact` layer.
`CompiledFile` is the same Go tree with resolved facts; `SafeProgram` is a certificate over it; the renderer
consumes it directly.

## Responsibility table (does / does NOT)

| Layer | Does | Does NOT |
|---|---|---|
| **GoAST** | hold the one raw proposed tree; validated idents, unsigned int magnitudes (`ENeg` for negatives), charset-checked strings | represent unsupported syntax; carry a parenthesis node; encode a signed literal |
| **GoCompile** | own the declarative `CompilesFile` relation + a sound/complete/deterministic executable `go_compile` producing a decorated `CompiledFile`; resolve idents→`CBool`, callee→the `println` builtin, carry intrinsic int-representability; erase back to the raw tree | be a boolean `check=true`; leave any unresolved name for later layers; *prove* adequacy to the real Go compiler (that is the e2e) |
| **GoSafe** | define an operational semantics (`Outcome`, print-event trace, `eval_file`) and the universal floor `BehaviorSafe` (the run does not panic), proved for the fragment; bundle `SafeProgram` (raw ↔ compiled ↔ safe) | use "safe" as a synonym for "compiles"; duplicate the tree; fork the compiler/semantics/renderer |
| **GoRender** | traverse `CompiledFile` directly to bytes; legal literal spelling/escaping, canonical spacing; prove `escape_faithful` + `render_all_ascii` structurally | tokenize/lex/parse; round-trip AST→text→AST; resolve names, infer types, reject, or invoke a formatter to repair |
| **GoEmit** | produce a Rocq-defined `DirectoryImage`; prove every path relative, separator/NUL-free, `.go`, unique; accept only `SafeProgram` | map rejection to an empty file; add VFS metadata |
| **Fido Emit** (`plugin/g_fido.mlg`) | reduce the proved `DirectoryImage`, structurally decode path+bytes, write verbatim/atomically; fail loud on any unexpected shape | inspect program structure, resolve names, choose files, validate, or fall back |

## Extensibility (refinement, not forks)

`GoSafe` is the floor, not the ceiling. Users/LLMs define stronger predicates over the SAME `CompiledFile`
(`Definition MyInvariant (c : CompiledFile) := …`) and package refinements that project back to
`SafeProgram` for emission — without modifying or forking `GoCompile`, `GoSafe`, `GoRender`, or the plugin.
Rocq decides whether the added proofs are valid; the core stays authoritative.

## Growing the language (the discipline)

Every new AST constructor enters only when it has, complete: exact `GoCompile` rules (constructor absent
otherwise), operational meaning in `GoSafe`, the safety obligation, renderer support with its structural
proof, and — where observable — an e2e witness. No conservative "known narrowing." Shrink the representable
language before weakening `GoCompile`.

## Trust base (say it exactly)

Trusted: Rocq and its kernel; the two Docker base images and the pinned Go image (all digest-pinned) plus
the opam-repo state and apt packages they install (snapshotting those is a residual build-trust task,
`PROGRESS.md`); the **one tiny transport glue** (`plugin/g_fido.mlg` — its constr-decode + file-write is
handwritten OCaml, hence trusted, not proved); and the Go toolchain (Go's parse/compile/run of the emitted
bytes is trusted — the Go-subset adequacy of `GoCompile`/`GoRender` is checked by the e2e, not proved).

Proved (axiom-free, asserted every build by `gate/axiom_gate.v`): the public surfaces of GoCompile
(sound/complete/deterministic/erase, decidable), GoSafe (no-panic, faithfulness), GoRender
(escape-faithful, all-ASCII), GoEmit (path safety), and the leaf authorities. "No assumptions" is never
evidence that a theorem's *statement* is the right correctness theorem.

## What must never come back

A handwritten OCaml backend or any of its jobs (term inspection, type reconstruction, name-based lowering,
AST construction, printer decisions, import selection, control-flow synthesis, validation, fallback, byte
rewriting); a **second** handwritten glue file; a boolean equality as the compile authority; a lexer,
parser, tokenizer, text IR, or AST→text→AST round-trip in the certified/production path; a self-mirroring
grammar defined by the printer's own decisions; a signed integer literal; an unresolved named type in the
compiled tree; a raw/string-rescue escape hatch. Git carries the history; re-admit a feature only when the
roots make its proof obligations natural.
