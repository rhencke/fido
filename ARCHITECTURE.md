# Fido — Architecture Charter (binding)

Read before any structural change. This governs. The design is intentionally minimal: there is **one
program representation** — a `GoProgram` (a finite map from relative paths to raw file ASTs). `GoCompile`/
`GoSafe` are EVIDENCE over that same program (never copies), and the handwritten OCaml is a dumb
filesystem synchronizer.

## The law of this repository

Ruthless correctness or ruthless deletion — no middle state. Incomplete scope is acceptable; incorrect,
conservative, duplicated, self-validating, or half-built code in the certified path is not. Cut representable
scope before weakening a proof. When twenty local proofs/guards compensate for one missing root, replace the
root and delete the leaves. A green boolean checker is not a compile authority; a printer's own inverse is
not a Go-semantics theorem; axiom-free is not correct.

## The pipeline

```
  GoProgram      the ONE program representation: fmap RelativePath GoFileAST — a verified finite map
                 (FMap) whose keys are unique BY CONSTRUCTION (a NoDup-keys proof; duplicate paths are
                 unrepresentable, lookup is deterministic, equality is extensional-by-lookup, no imposed
                 order).  A GoFileAST is RAW syntax only: MainFile (package main + func main() STRUCTURAL)
                 of SPrintln statements (the builtin println IS the statement) over EBool | EInt | ENeg.
                 No identifiers; no unsupported syntax (absent, never narrowed).  Package grouping,
                 imports, entry, symbols, types are COMPILATION RESULTS — never baked into the raw file.

  GoCompile      EXACT whole-PROGRAM static/compiler admissibility as EVIDENCE over that same program.
                 CompilationFacts p is the (currently empty) home for derived static facts; it never
                 becomes a second tree.  A declarative judgment GoCompile p (facts) + a proof-producing
                 go_compile : GoProgram -> option CompilableProgram (sound + complete + reflected by
                 prog_ok_iff).  CompilableProgram wraps the SAME program + its facts + the compile proof.

  GoSafe         the exact ABSTRACT println-trace semantics with REAL values (VBool/VInt Z) + the safety
                 capability SafeProgram over CompilableProgram.  GoSafe is trivial TODAY (the fragment has
                 no unsafe op) and honestly documented as such; it is the PERMANENT extension point for
                 guarantees beyond compiler acceptance.  No panic algebra until a panic-capable constructor.

  GoRender       the direct GoFileAST → bytes renderer.  Every file begins with the exact generated header
                 `// fido generated.  do not edit.` (part of the Rocq-rendered bytes).  Proved: all-ASCII,
                 the emitted decimal denotes exactly the value, no illegal leading zero, header present.

  GoEmit         the public capability render_program : SafeProgram -> DirectoryImage, where
                 DirectoryImage := fmap string is a TRUE finite map (path -> exact bytes).  One image entry
                 per program file; acceptance and image production are all-or-nothing.

  extraction     standard Rocq extraction turns the image entries into an ordinary OCaml
                 (string * string) list (unique keys by construction).

  sink           ONE handwritten OCaml dirty-directory synchronizer installs that image into a target
                 directory (staging + per-file atomic rename), cleaning its own stale output and never
                 touching foreign files.  Understands ONLY the filesystem.

  pinned Go      the digest-pinned toolchain builds + runs the emitted program.  Integration only.
```

**There is no second tree.** No `CompiledExpr`/`CompiledStmt`/`CompiledFile`, no raw `GoPackage` hierarchy,
no erasure forest, no Surface/TypedIR/GoSyntax/token/grammar/`CertifiedArtifact` layer. `GoCompile` produces
a certificate over the one `GoProgram`; `GoSafe` is a certificate over that; the renderer traverses it
directly. The permanent root is a PROGRAM, not a file: even the one-file MVP is expressed as a proved subset
over the finite-map program structure (`go_compile` accepts iff there is exactly one main-file key whose
statements are all admissible).

## Two honest claims (never conflate)

- **(A) KERNEL-internal exactness — PROVED.** The executable checker succeeds exactly for the formal
  `GoCompile` judgment (`prog_ok_iff`; `go_compile` returns a `CompilableProgram` iff it holds), and the
  renderer/semantics facts hold. Asserted axiom-free every build by `gate/axiom_gate.v`.
- **(B) EXTERNAL Go-compiler adequacy — the GOAL, not a kernel theorem.** That every accepted, rendered
  program is accepted by the real Go compiler is exercised by the pinned e2e toolchain, never proved about
  `cmd/compile`. Do not overclaim "equivalent to go build".

## Responsibility table (does / does NOT)

| Layer | Does | Does NOT |
|---|---|---|
| **FMap** | the one finite-map spine (path→file, path→bytes); unique keys by construction; deterministic lookup; extensional-by-lookup equality | impose a key order; use list+dedup; permit a duplicate key |
| **Ints** | the ONE 64-bit integer authority (`int_min`/`int_max`/`uint_max`) | parameterize by Go release / GOOS / GOARCH / word size (no TargetConfig) |
| **GoAST** | hold the ONE program (finite map) + raw file ASTs; structural package/func/println; bool + unsigned int magnitudes (`ENeg` for negatives) | carry identifiers, a second tree, a raw `GoPackage`, compiled facts in raw syntax, or a signed literal |
| **GoCompile** | own `GoCompile : forall p, CompilationFacts p -> Prop` (integer representability) + a proof-producing sound/complete `go_compile`; `CompilableProgram` = wrapper over the SAME program | copy the syntax; be a boolean; reject valid Go it can represent; prove completeness against a mirror relation |
| **GoSafe** | real `GoValue` (`VInt : Z`), exact abstract `eval_file`, `SafeProgram` over `CompilableProgram` (0 = -0); honest `GoSafe := True` today | observe source spelling as "value"; keep an unused `Panicked`/`Outcome` placeholder; circularly reference compilation; fork anything |
| **GoRender** | render each `GoFileAST` to bytes with the generated header; prove all-ASCII, decimal-denotes-value, no-leading-zero, header-present | tokenize/lex/parse/round-trip; resolve names; reject; invoke a formatter |
| **GoEmit** | `render_program : SafeProgram -> DirectoryImage` (finite map path→bytes); one entry per file | build a generic path predicate over arbitrary strings; produce a partial image |
| **extraction + sink** | Rocq generates the `(string*string) list`; the sink syncs it to a directory | let handwritten OCaml decode/inspect/lower/render/validate/choose anything about a program |

## The handwritten-OCaml boundary (hard)

**Handwritten OCaml is a filesystem exhaust pipe.** It receives only final relative paths and exact contents
and makes a target directory's Fido-owned files equal that image. It does not receive, inspect, validate,
lower, render, or understand programs; it walks no Rocq terms; it chooses no paths or contents; it has no
fallback. All structural decoding (Coq `string`/`list`/`prod` → OCaml) is GENERATED by standard extraction.
A file is Fido-owned iff its first line is the exact generated header (an on-disk ownership MARKER, not
program understanding). If that boundary cannot be met, delete the sink and the e2e rather than keep a
handwritten decoder — incomplete integration is acceptable, a false transport foundation is not.

The sink is a real **dirty-directory synchronizer** (not a fresh-dir writer): it takes an exclusive lock,
cleans abandoned staging, discovers existing header-owned files, preflights every path (rejecting symlink
traversal and refusing to overwrite any non-Fido file), stages all bytes INSIDE the target, installs by
per-file atomic rename, deletes stale Fido-owned files by header + desired-key-set (never timestamps/manifest,
never a foreign file or a directory), releases the lock, and reports success only after a complete sync. It
may be larger than a one-liner, but it understands ONLY the filesystem — no semantic logic, no gofmt, no
compilation.

The Rocq side computes and certifies the complete image and guarantees: every path is the finite map's key
(unique, deterministic); contents are final exact bytes with the header; a rejected program yields no
`SafeProgram` and hence no image; successful emission needs no postprocessing.

## Growing the language

Every new AST constructor enters only when it has, COMPLETE at that time: exact `GoCompile` rules
(constructor absent otherwise), exact operational meaning in `GoSafe`, renderer support with its
value/syntax proofs, and — where observable — an e2e witness. No "known narrowing". Shrink the representable
language before weakening `GoCompile`. Multi-file / cross-file reasoning (file A imports file B, both owned)
is the reason the root is a program map; imports remain on hold (only change needing sign-off).
Identifiers/functions return only via evidence over the ONE program — never a parallel syntax hierarchy.

## Trust base (say it exactly)

Trusted: Rocq and its kernel; the two Docker base images and the pinned Go image (all digest-pinned) plus the
opam-repo state and apt packages they install (snapshotting those is a residual build-trust task); the **one
filesystem sink** (`e2e/writer.ml` — file I/O only, no term walking, hence trusted-not-proved); and the Go
toolchain (its parse/compile/run of the emitted bytes is trusted — the Go-subset adequacy of
`GoCompile`/`GoRender`, claim (B), is checked by the e2e, not proved). The extraction-generated OCaml is
standard Rocq extraction of proved definitions.

Proved (axiom-free, asserted every build by `gate/axiom_gate.v`): the Ints boundary values; FMap's
deterministic lookup (duplicate keys unrepresentable); GoCompile claim (A) — `prog_ok_iff`, `go_compile`
sound + complete, rejection ⇒ no `CompilableProgram`, the accept/reject boundary facts, duplicate paths
unrepresentable; GoSafe's zero-sign-agnostic value fact; GoRender's all-ASCII + decimal-faithful +
no-leading-zero + header-present + boundary faithfulness; GoEmit's image keys/header/ASCII/one-file facts.
"No assumptions" is never evidence that a theorem's STATEMENT is the right one.

## What must never come back

A handwritten OCaml backend or a plugin that decodes Rocq terms; a SECOND program-AST hierarchy, a raw
`GoPackage` tree, or an erasure forest to call a copy "the same"; compiled facts baked into raw syntax; a
`TargetConfig` re-parameterization before 32-bit support is deliberately chosen; a boolean as the compile
authority, or a subset filter posing as compiler admissibility; a lexer/parser/tokenizer/round-trip in the
certified path; a self-mirroring grammar; a signed integer literal; a raw/string-rescue escape hatch; an
unused panic/control placeholder; a witness-specific writer or a fresh-dir-only writer that cannot
synchronize a dirty directory. Git carries the history; re-admit a feature only when the roots make its proof
obligations natural.
