# Fido AST-First Certified Emission Charter

Standing architectural charter for Fido — binding on Claude Code, Codex review, and human review. It
supersedes the ad-hoc "lower arbitrary Rocq through a trusted plugin" center of gravity.

> **Fido moves toward an AST-first, proof-gated Go emission architecture.**

```text
GoAst    says what Go-shaped syntax can be written.
GoPrint  proves the AST prints (and parses back) correctly — SYNTAX ONLY.
GoSem    says what the AST means — PLANNED, not built; will bridge the authoritative semantics (unified.v).
GoSafe   says which programs are supported now, and — later — which are behaviorally safe.
GoEmit   is the ONLY blessed emission path; it requires the appropriate certificate.
```

The central rule:

```text
Raw structured Go ASTs may represent unsafe programs.
Only CERTIFIED ASTs may be emitted through the official path.
Early on the certificate is "supported subset" (syntactic). It becomes "behaviorally safe" only when
GoSem-backed theorems exist — and the NAME of the certificate must never claim more than is proved.
```

Treat all existing code as provisional until it fits this architecture. Optimize for **architectural truth
over preserving old momentum.**

---

## 1. Non-negotiable project standard

Primary goal: **merciless correctness.** Supported constructs must be exact w.r.t. the intended Rocq-Go
semantics. Unsupported constructs must be mechanically rejected or clearly outside the core. No documentation
may weaken a correctness claim.

Secondary goal: **simplify, generalize, remove dead weight** — subordinate to correctness. Good
simplification makes invariants structural, removes duplicate authorities, deletes obsolete scaffolding, and
makes bad states unrepresentable or un-emittable. Bad simplification proves less or models less while
pretending the claim stayed the same.

---

## 2. The architectural spine

```text
GoAst   says what can be written.
GoPrint proves syntax printing/parsing correctness ONLY.
GoSem   defines behavior.
GoSafe  defines supportedness now, behavioral safety later.
GoEmit  is the only blessed emission path and requires the appropriate certificate.

Printer proofs are SYNTAX proofs. They do NOT imply race freedom, memory safety, termination, session
correctness, or GoSem correctness. Safety proofs are BEHAVIORAL. Emission COMPOSES the two.
```

**`GoAst.v` — structured Go syntax.** Identifiers, literals, types, expressions, statements, programs.
`GoAst` may represent unsafe programs, but it must **not** contain raw syntax strings for Go structure.
Allowed: semantic string *contents* for string literals (printed through an escaping printer); validated
identifiers. Forbidden: raw expression/statement/type/declaration strings; "opaque Go syntax" / "trusted
raw" constructors; any constructor that smuggles source text to avoid modeling syntax. If a construct is
supported it gets a constructor; otherwise it is unrepresentable or rejected by the builder.

**`GoPrint.v` — printing + syntax round-trip (imports `GoAst`).** Owns printing and the syntax round-trip
theorems (`parse_str (gprint 0 e) = Some (e,[])`, `print_program_inj`, …). Purely syntactic — no safety
claims belong here. The parser used by printer proofs is a real lexer + recursive-descent/precedence parser,
not a maze of string splits.

**`GoSem.v` — semantics (imports `GoAst`) — PLANNED, NOT BUILT.** GoSem will be the AST's behavioral
semantics for the supported subset (happens-before, blocking, panics, output, defer, channels, …). The
authoritative operational semantics TODAY is `unified.v` (the proven `ustep`, race-freedom + liveness);
GoSem does **not** exist and holds no authority yet. When built it must **bridge the existing proven
semantics** — `unified.v`, `concurrency.v` (trace / happens-before / race / bounded-deadlock theory), and
`cmd.v` (effect evaluator) — so there stays ONE authority, never a second semantic universe that can drift.
No behavioral-safety claim is active until GoSem exists.

**`GoTypes.v` — shared constant-aware type-category checker (imports ONLY `GoAst`).** The bottom of the
type-category layer: `ptype : GExpr -> option PTy` (the structural, constant-aware category assignment —
splitting int/float, constant/runtime, carrying constant values so overflow / div-or-shift-by-zero are
decided from the folded value) and its numeric/conversion combinators, plus the value-position wrapper
`svalue`. Factored out of `GoSafe` so the layers above it consult ONE authority (GoSafe for
`SupportedProgram`; GoSem, when built, for blank-assign RHS validity). No theorems — adds no axioms.
**`ptype` is a CONSERVATIVE supported-subset classifier, NOT Go's typechecker.** No new rule may be added
unless it (a) rejects a real CLOSED bad program currently accepted, or (b) admits a needed supported demo.

**`GoSafe.v` — supportedness now, behavioral safety later (imports `GoAst` + `GoTypes`).** Adds the
statement-shape / supported-syntax layer (`stmt_ok`, `supported_program`, `SupportedProgram`) on top of
`GoTypes`. **Phase 1 is SYNTACTIC supportedness and must be NAMED as such** — calling it `SafeProgram` would
repeat the exact overclaim this refactor kills (Rule 5).

```text
SupportedProgram  -- syntactic: in the supported subset; no unmodeled constructs; no raw escape hatches.
BehaviorSafe      -- semantic (reserved for when GoSem-backed theorems exist): no nil deref / OOB /
                     send-on-closed / illegal close / data race; happens-before consistency; session safety.
```

Safety must become the **ticket required by the emitter**, not a theorem sitting near an AST.

**`GoEmit.v` — the only blessed emission path (imports `GoAst`, `GoPrint`, `GoSafe`).**

```coq
Record EmittableProgram := { ep_program : GoAst.Program; ep_supported : GoSafe.SupportedProgram ep_program }.
Definition emit_supported (p : EmittableProgram) : string := GoPrint.print_program p.(ep_program).
(* Later, once GoSem is built and BehaviorSafe is real: a SafeProgram = EmittableProgram +
   BehaviorSafe, emitted by emit_safe. *)
```

`emit_supported` is a printer/supported-subset milestone — NOT behaviorally safe. Do **not** export an
official `emit : GoAst.Program -> string`; that makes the certificate decorative. Raw printing for tests must
be named like a loaded gun, must not be the extraction path, and must not back any safety claim.

---

## 2a. Residual trust base (state it; never leave it implicit)

The correctness of an *emitted* program rests on, and only on:

1. The **Rocq kernel** and the trusted stdlib lemmas the proofs use.
2. The **extraction / file-emission step** turning the final `string` into a `.go` file (plain OCaml string
   extraction — the mechanism that produces `printer.ml`; NOT `go.ml` lowering).
3. The **Go compiler / runtime / toolchain**.
4. **Trusted foreign Go imports** and monitored boundary assumptions.
5. An **adequacy assumption connecting `GoSem` to actual Go behavior** ("real Go realizes `GoSem`") — the
   heir to the old "gap #10," unfalsifiable inside Rocq, named in the honesty ledger, never assumed silently.

Today the main output is still produced by the **trusted legacy plugin** `plugin/go.ml` (gap #10) — itself
part of the TCB until the certified path subsumes it. `GoPrint` proves the bytes; items 3 and 5 are why this
is "Go with proofs," not "Go without trust."

---

## 3. Why this course correction exists

The previous architecture lowered arbitrary Rocq-ish code through a trusted OCaml plugin into Go text — fast
demos, repeated trust-boundary problems. The `SRaw` raw-expression-string escape hatch is the cautionary
tale: added "for convenience," it grew helpers/validators/scanner/parser/tests around it, looking ever more
formal while preserving the wrong abstraction. See `LESSONS.md` for the postmortem. The rule that prevents
recurrence:

```text
If a construct is syntax, represent it structurally.
If it cannot be represented structurally yet, reject it. Do not rescue old source strings.
```

---

## 4. Legacy status and transition discipline

`plugin/go.ml` is **trusted legacy scaffolding.** It may remain only to keep demos building while the
AST-first path matures; it **may not define the correctness claim.**

- New architectural work must **reduce** reliance on Legacy, not improve it. A patch that makes `go.ml`'s
  lowering nicer is moving the wrong direction.
- The old path builds demos; the new path defines the claim. Old path gets deleted as the new path subsumes
  it — never maintained in parallel indefinitely.
- No parallel universes: do not grow a second expression/semantic universe beside the spine.

Honest current status: the spine (`GoAst`/`GoPrint`/`GoTypes`/`GoSafe`/`GoEmit`) compiles zero-axiom and
`main.v` builds a `GoAst.Program` with a real `func main` body emitted ONLY through `EmittableProgram`; but
the repo's main `main.go` is STILL the legacy plugin path (GoPrint drives only the var-OP-var binop class
live), and there is no GoSem, so no behavioral safety. Detailed feature state lives in `PROGRESS.md`.

---

## 5. Relooper — demoted

`relooper.v` is proven and should not be deleted casually, but it is **not** part of the first
AST-certified-emission path (direct `GoAst` construction → `GoPrint` → `GoEmit`, not CFG recovery). It is an
optional future lowering component (a higher-level CFG language → GoAst). Do not spend time on relooper
integration until the AST-first emission path is established.

---

## 6. Phases

```text
Phase 0  Freeze the direction.                                                              DONE
Phase 1  Extract the Front seed into GoAst/GoPrint (rename, not copy; no second universe).   DONE
Phase 2  Create GoSafe (SupportedProgram) + GoEmit (EmittableProgram; no raw emit).          DONE
Phase 3  main.v builds GoAst.Program and emits ONLY through the certificate.                 DONE
Phase 4  Grow the AST/printer form-by-form (each: represented, printed, round-tripped/       DONE (for now)
         injective, gate-honest). GoStmt forms + EConv + slice/map literals + EStr landed.   — frozen; tighten not grow
Phase 5  Grow safety via GoSem: BRIDGE unified.v/concurrency.v/cmd.v in (no second universe),  NEXT
         widen toward BehaviorSafe → SafeProgram → emit_safe, wire the certified path to main.
```

Proceed in small structural steps. Every patch should either move a concept into the correct module, delete
an old wrong path, make a bad path unreachable, strengthen the proof-gated emission boundary, or shrink
trusted legacy code. **Do not add parallel universes. Do not add "future foundation" unless it replaces or
deletes something.**

---

## 7. Rules for Claude Code

**Rule 1 — No raw syntax in core AST.** Forbidden in core modules: `RawExpr`, `RawStmt`, `RawDecl`,
`RawType`, `OpaqueExpr`, `TrustedExpr`, `SRaw`, `raw_ok`, raw source strings. Semantic strings are okay only
when the printer escapes them (string-literal contents).

**Rule 2 — No string-rescue path.** Forbidden: `old printer -> string -> validator/parser -> new printer`.
The generator builds AST directly; the lexer/parser exists for proof and testing, never to rescue old output.

**Rule 3 — No official raw emitter.** Forbidden on the blessed path: `emit : GoAst.Program -> string`. The
official emitter requires `EmittableProgram` (later `SafeProgram`).

**Rule 4 — No decorative safety/support proofs.** The emitted output must go THROUGH the certificate
(`GoEmit.emit_supported {| ep_program := p; ep_supported := p_ok |}`), not `print_program p` beside a lemma.

**Rule 5 — No documentation as correctness.** Docs may *describe* a limitation; they may not make it
acceptable in the core. If a bad case exists, make it impossible, reject it, or move it outside the core.
**Naming is a correctness claim:** do not name a syntactic gate `SafeProgram`.

**Rule 6 — Deletion is progress.** Every structural patch should preferably delete something; report `wc -l`,
old-architecture-term greps, dead-helper counts. A patch that only adds scaffolding is suspect.

**Rule 7 — Review archaeology belongs in `LESSONS.md`.** Active comments explain invariants, not the social
history of a bug. Good: "Identifier-led `T(x)` is syntactic application; call-vs-conversion is semantic." Bad:
"Review #9 amendment 3 forced this after SRaw...".

---

## 8. Review checklist for every patch

1. Which module did this move toward the target architecture?
2. What old path became unreachable / what code was deleted?
3. Did this create a new parallel syntax/semantic universe?
4. Does any theorem prove something not used by the live path?
5. Does any official emitter bypass the certificate (`EmittableProgram`/`SafeProgram`)?
6. Did docs (or names) overclaim?
7. Did the patch reduce trusted code, preserve it, or increase it? What grep/build gate prevents regression?

---

## 9. Acceptance gates

**[live]** = enforced every build; **[on-land]** = activates when its module lands; **[review]** = human/Codex
discipline.

```text
[live]     No project Axioms / Admitted / admit.                 (axiom-manifest gate + Print Assumptions)
[live]     Generated printer artifact (plugin/printer.ml) in sync. (make printer-verify + Docker stage)
[live]     No raw-syntax constructor NAMES in source.             (plugin/smart-ctor-gate.sh)
[live]     Official emit only via GoEmit's certificate API; no direct print_program call outside GoEmit.
[on-land]  Print Assumptions for every public safety theorem (once BehaviorSafe exists).
[review]   The Phase-1 gate is named SupportedProgram, NOT SafeProgram, until GoSem-backed BehaviorSafe exists.
[review]   Docs and NAMES do not claim more than the live path proves.
```

The smart-ctor gate is a **name-regression tripwire over hand-written sources** (`*.v` + `plugin/go.ml` + the
`.mlg` glue; the generated `printer.ml` and docs are out of scope) — it catches KNOWN forbidden names, NOT a
differently-named raw hatch. The actual STRUCTURAL guarantees are properties of the definitions: `GoAst`'s
constructors take only validated/semantic payloads (raw syntax unrepresentable), and `GoEmit` exports only
certificate-requiring emitters (a raw emit is a type error, not a text match) — enforced by review of those
definitions, not by grep.

---

## 10. What not to do

Do not grow a second expression/semantic universe beside the spine. Do not wire the old plugin printer into
`GoEmit`. Do not use the parser to rescue legacy old-printer strings. Do not revive `SRaw`. Do not make
`SupportedProgram`/`BehaviorSafe` an axiom. Do not create a convenient unsafe `emit` and promise nobody will
use it. Do not claim "safe Go" for any program that did not pass through the behavioral certificate.

---

## Standing bottom line

Do not verify around a bad abstraction. Do not document — or *name* — a shortcut into respectability. Do not
let a proof sit beside the path; put it on the path. Build the AST honestly. Print it boringly. Certify it
explicitly. Emit only certified programs.
