# Fido — status

A foundation reset (checkpoint 65) is in progress; checkpoint 66 is pouring the first FINAL-quality vertical
slice (no imports, builtin `println` only). The live frontier only; `ARCHITECTURE.md` is the charter,
`git log` is the history.

## The checkpoint-66 slice (in progress)

The admitted language: `package main` + one `func main()` + straight-line builtin `println` over primitive
literals (bool / string / nonneg int; negatives ONLY as unary minus over a nonneg literal). Imports, user
functions, variables, and control flow are UNREPRESENTABLE (no constructors). Negatives die in Rocq —
**zero expected Go compile failures**, ever.

GREEN (proved, in the pinned container):
- **`TargetConfig`** — the one authority for pinned target facts (int width 64 → exact `int_min`/`int_max`;
  the bootstrapping `println` exists on this target).
- **`CoreType`** — the closed primitive descriptor (`PBool|PInt|PString`) deriving literal validity
  (`str_ok` charset; `int_lit_ok`/`neg_lit_ok` with exact constant-overflow bounds — `-(2^63)` admitted,
  `2^63` bare rejected) and `println` admissibility.
- **`Surface` → `TypedIR`** — raw candidate syntax vs. an IR where static invalidity is unrepresentable
  (evidence-carrying literal nodes; `TPrintln` is the RESOLVED builtin — no string names in the IR).
- **`CompileEnv` + `Elaborate`** — the declarative compile authority (`ElabProgram`, NOT a boolean) with an
  executable elaborator proved **sound AND complete** (`elab_program_sound`/`_complete`); 12 rejection
  theorems pin the invalid classes (unresolved/qualified callee, wrong package, value-statement, call
  argument, nested/typed-wrong negation, negative literal node, constant overflow both signs, bad string
  bytes) + the `-(2^63)` boundary acceptance.
- **`Semantics`** — structured events (`EPrintln` over `PrimValue`), total evaluation; determinism,
  totality, type preservation, and value-in-int-range proved. `println` FORMATTING is deliberately not
  modelled (implementation-specific — a pinned-toolchain integration fact only).

- **`GoToken` + `GoLex` + `GoGrammar`** — the subset token universe; a fuel-free structural lexer faithful
  to Go's rules on the subset (keywords/identifiers, nonneg decimals with the leading-zero rejection,
  interpreted strings with exactly the four escapes, ASI at line ends per the spec rule); the admitted
  grammar over post-ASI tokens, written INDEPENDENTLY of the renderer (no renderer function appears in it).
- **`GoRender`** — canonical tokens + the ONE token renderer (all layout: blank line after package, tab
  indents, statement-per-line). Proved: `program_tokens_grammar` (the canonical stream derives every typed
  program in the independent grammar) and **`render_lex_inverse`** (`lex (render_program p) = Some
  (program_tokens p)` for ALL typed programs — every canonical semicolon really comes back via ASI, and no
  rendered lexemes fuse). Decimal digits come from the one authority (`digits.v`, extended with
  `pos_digits_last`: no leading zero). HONEST SCOPE: grammar adequacy to the REAL Go parser is the pinned
  toolchain e2e's integration claim, not a theorem.

RED / NEXT (in order): `CertifiedArtifact` (bytes reachable only through the proved chain: elaboration +
trace + grammar + tokens + render), the 5 positive witnesses with exact byte theorems, the
Rocq-compile-fail negative harness, and the per-witness e2e (emit → pinned `go build` → run → separate
stdout/stderr goldens). **e2e is RED until at least one theorem-backed witness emits, compiles, runs, and
matches its goldens. No MVP 1.0 while red.**

## Where we are (the resets that got here)

The handwritten OCaml backend and extraction plugin are gone (checkpoint 64). Checkpoint 65 then deleted the
**false compile/emit authority** and the **disconnected runtime island**, because both rested on rejected
roots:

- `GoCompile` was **fail-open**: `go_compile_check` accepted an unresolved named type
  (`[]Foo{}` with `Foo` undefined) that the Go compiler rejects. A boolean checker with no declarative Go
  static semantics and no soundness theorem is not compiler-admissibility. So `GoCompile`, `GoTypes`, and
  `GoEmit` (which inherited it) are **deleted** — with them the "certified emission" claim.
- The runtime island (`GoNumeric`, `GoRuntimeTypes`, `GoPanic`, `GoEffects`, `GoSlice`) was **not imported**
  by the emission path and preserved already-rejected foundations (hard-coded target numerics instead of one
  `TargetConfig`; a parallel runtime type-tag universe; string runtime panics; blocking/model-faults as
  recoverable `OPanic`; a pure-list slice that cannot model nil/cap/backing). **Deleted.**

**There is no certified emission and no compile authority** — a green demo on a false compile certificate is
not progress. The only Go produced is a **minimal e2e smoke test** (`e2e/e2e.v`): one hand-built program is
printed by the surviving `print_program` (its exact bytes Rocq-checked by `reflexivity`), and the pinned Go
toolchain confirms it is gofmt-clean + `go build`s + `go vet`s. This is a last-mile integration alarm for
that ONE program — NOT a compiler-soundness or certified-emission claim for arbitrary programs.

## What survives (and is NOT a certified authority)

`digits.v` (the decimal-rendering authority), `GoAst.v`, `GoPrint.v` — the syntax layer. It compiles in the
pinned-Rocq container (`make check` → buildx prover stage → `dune build`; host Rocq is not supported), and
the gated `Print Assumptions` surfaces are **axiom-free** (`gate/axiom_gate.v`, Rocq's own output — see the
trust base for exactly what that gates). It is scheduled for the **syntax-root reset** and makes **no
Go-adequacy claim**. Known defects to fix in that reset (do NOT
patch in place):

- `GoAst.EInt : Z` encodes a *signed* literal; Go has no signed integer literal (`-5` is unary-minus applied
  to the literal `5`). Negatives must arise from unary minus over a nonnegative literal, unrepresentable
  otherwise.
- `GoAst.GTNamed` is an unresolved name with no type environment; it must not exist in an admitted target IR
  until real name-resolving elaboration exists.
- `GoPrint.CanonExpr` is a canonical **encoding** relation defined in terms of the printer's own policy
  (`unop_paren`/`binop_prec`) — it self-mirrors `gtokens`, so it is **not** an independent Go grammar and
  does not prove Go-parse adequacy. The unary-precedence commentary is wrong (`^a.b` parses `^(a.b)`, and
  `-5` needs no parens). The executable parser is complete-not-sound and not needed by any emission path.

## The trust base

Trusted: Rocq and its kernel; the two Docker base images (`ocaml/opam` + `debian`, now **digest-pinned** in
the Dockerfile) **plus the opam-repo state and the apt packages they install** (pinning/snapshotting those is
a residual build-trust task). No handwritten OCaml exists (`tools/ocaml-origin-gate.sh` enforces zero tracked
`*.ml`/`*.mli`/`*.mlg`).

Exactly what the LIVE build gate enforces: `dune build` type-checks the modules, then `gate/axiom_gate.v` —
**the sole Print-Assumptions target, compiled fresh EVERY build** against the dune-built `.vo` (so a warm or
gate-poisoned `_build` cache can never skip it) — runs `Print Assumptions` on every declared public surface
(GoPrint's 122 + the cp66 slice's compile/semantics/grammar/renderer theorems; count-checked, so the list
is the authority).
The build fails on any `^Axioms:` line AND unless exactly as many `Closed under the global context` lines
appear as the gate file declares (a vacuous/partial gate log is a FAILURE, fail-closed both ways). Modules with no
declared surface are NOT gated (axiom-freedom there holds by inspection — no `Axiom`/`Parameter`/`Admitted`, Stdlib-only imports — but is not build-gated). The
axiom-DECLARATION scan (no `Axiom`/`Parameter`/`Admitted`/top-level `Variable` in any `.v`) runs ONLY in the
**pre-commit hook**, not in `make check` or the container build, so it is bypassable (`--no-verify`) and
absent in CI — moving it into `make check` is a build-trust task. Never read "no assumptions" as proof that a
theorem's *statement* is the right theorem (the deleted `GoCompile` was axiom-free and still wrong).

## RED / NEXT — pour the roots before any floor (do NOT add features)

1. **`TargetConfig`** — one authority for int/uint width and pinned target facts.
2. **One certified type universe** (`CertifiedType`) — identity/underlying/zero/comparability/map-key/tokens
   derived from ONE descriptor; invalid types unrepresentable or rejected by elaboration.
3. **An independent Go grammar** (`GoLex`/`GoGrammar`) defined WITHOUT reference to printer policy; the
   printer proved *adequate* to it. One token stream + one verified renderer (`typed AST → tokens → bytes`),
   no parallel `gprint`/`gtokens` recursions.
4. **A compile environment + declarative resolution/typing** (`CompileEnv`, `ResolveName`, `ElaborateType`,
   `TypeExpr`/`TypeStmt`) into a **typed IR** (`TypedProgram`) where static invalidity is unrepresentable;
   an executable `elaborate_check` proved *sound* (and complete on the admitted closed subset).
5. **A typed store + value-WF**, one native representation each for slice/map/channel, accurate
   control/panic/blocking/model-fault, structured runtime errors — as consumers require them.
6. **Restore a closed extraction output only after** the root chain (elaboration soundness, grammar
   adequacy, token render/lex inverse, exact byte theorem) exists; emit through a proof-bearing typed
   certificate, never a boolean.

## Build-trust tasks (do while the source graph is small)

Done: the two base images are digest-pinned; the opam retry loop fails closed (`test installed = true`); the
prover stage verifies `rocq`/`ocamlc` are present before compiling. Still open: pin/snapshot the opam repo
and verify installed package *versions*;
make one Dune module graph authoritative (no second hardcoded shell module list) with a real `_build` `.vo`
cache in the mounted BuildKit cache; one public-surface assumptions module as the sole axiom-gate target
(instead of the `^Axioms:` grep over declared surfaces); one tiny tracked glue file **iff/when** emission
returns (there is none now).
