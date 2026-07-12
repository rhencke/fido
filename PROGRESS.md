# Fido — status

A foundation reset (checkpoint 65) is in progress. The live frontier only; `ARCHITECTURE.md` is the charter,
`git log` is the history.

## Where we are

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

**There is NO emitted Go this round, by design** — a smaller root-only repository beats a green extraction
demo resting on a false compile certificate.

## What survives (and is NOT a certified authority)

`digits.v` (the decimal-rendering authority), `GoAst.v`, `GoPrint.v` — the syntax layer. It compiles
standalone, and its declared `Print Assumptions` surfaces are **axiom-free** (`make check` via
`tools/spine-gate.sh`, Rocq's own output — see the trust base for exactly what that gates). It is scheduled
for the **syntax-root reset** and makes **no Go-adequacy claim**. Known defects to fix in that reset (do NOT
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

Exactly what the LIVE build gate enforces (`spine-gate`, run by `make check` and the Docker prover): the
three files type-check, and it greps `^Axioms:` over the compile log — so it establishes only that the
theorems with an explicit `Print Assumptions` print no assumptions. That is **GoPrint's 123 declared
surfaces only**; `digits.v` and `GoAst.v` declare NONE, so the build gate says NOTHING about their
axiom-freedom (it holds by inspection — no `Axiom`/`Parameter`/`Admitted`, Stdlib-only imports — but is not
build-gated). The axiom-DECLARATION scan (no `Axiom`/`Parameter`/`Admitted`/top-level `Variable` in any `.v`)
runs ONLY in the **pre-commit hook**, not in `make check` or the container build, so it is bypassable
(`--no-verify`) and absent in CI. The precise fix — one public-surface module that `Print Assumptions` every
root theorem, gated in the build as the sole target (and moving the declaration scan into `make check`) — is
a build-trust task, deferred with the syntax-root reset. Never read "no assumptions" as proof that a
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
