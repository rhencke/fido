# Fido AST-First Certified Emission Charter

Standing architectural charter for Fido — binding on Claude Code, Codex review, and human review. It
supersedes the ad-hoc "lower arbitrary Rocq through a trusted plugin" center of gravity.

> **Fido moves toward an AST-first, proof-gated Go emission architecture.**

```text
GoAst    says what Go-shaped syntax can be written.
GoPrint  proves printing is faithful (expressions round-trip; programs/statements print injectively) — SYNTAX ONLY.
GoSem    says what the AST means — SLICE 1 landed (cmd.v bridge + println/print/panic effect denotation + denotation⊆gate soundness); completeness + behavioral safety NOT built.
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
GoPrint proves printing faithfulness ONLY (expression round-trip + program/statement print-injectivity).
GoSem   defines behavior — SLICE 1 (cmd.v bridge + effect denotation + denotation⊆gate soundness); NOT complete, no BehaviorSafe yet.
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

**`GoPrint.v` — printing + syntax faithfulness (imports `GoAst`).** Owns printing and its faithfulness
theorems, at TWO distinct strengths — do not conflate them:
- **Expressions: a full parse round-trip** `parse_str (gprint 0 e) = Some (e, [])` (+ `gprint_inj`), over a
  real lexer + recursive-descent/precedence parser. This is self-consistency of the **Rocq grammar** — it
  proves the printer and this parser invert each other, NOT that Go's own compiler accepts the output.
- **Programs / statements: print-INJECTIVITY only** (`print_program_inj`, `print_stmt_inj`) — distinct ASTs
  print to distinct text. There is NO program/statement parser and NO parse round-trip at that level yet
  (statement re-parse has ASI/semicolon subtleties; deferred). Injectivity is weaker than a round-trip and
  is NOT Go-syntax acceptance.

Purely syntactic — no safety claims belong here.

**`GoSem.v` — semantics (imports `GoAst`/`GoTypes`/`GoSafe`/`cmd`/`preamble`) — SLICE 1 LANDED, growing.**
GoSem will be the AST's behavioral semantics for the supported subset (happens-before, blocking, panics,
output, defer, channels, …). TODAY it is SLICE 1: `denote_program : Program -> option (Cmd unit)` BRIDGES a
program into `cmd.v`'s already-proven command tree (reusing `cbind`/`denote`/`run_cmd`, NOT a second universe),
with REAL observable effects — `println`/`print` -> `COut` (faithful: the same `w_log` the model's
`println`/`print` produce), `panic` -> `CPan` — over `eval_value` (slice 1: string literals plus
gated/default-in-range untyped integer constants and supported typed integer constants — literals, conversions
`int64(3)`, arithmetic `1+2`, complement `^x` — EXCLUDING `GTUint`, plus exact-integer-valued float constants
`float64(3)`/`-float32(5)` boxed to the canonical binary64/binary32 value, plus a constant bool built from
NUMERIC or STRING-LITERAL comparisons (`1==1`, `3<5`, `"a"<"b"` — string order DELEGATED to the model's `str_ltb`)
combined by `==`/`!=`/`&&`/`||`/`!`, plus the identity `bool(x)` conversion (comparability validated by `ptype`,
value computed in GoSem by the self-sealed `eval_bool`), all via the model's value ctors, failing closed at the
boundary on an out-of-range/out-of-interval value); and `gosem_sound` proves the gate connection
(`denote_program p <> None -> SupportedProgram p`: no meaning given to invalid Go, because the effect arm
consults `expr_stmt_ok`). NOT done: `eval_value` for a comparison with a NON-literal string operand / runtime
values (a bool/numeric with a `len(..)`/`int(x)`
operand) / fractional floats / non-literal strings / `GTUint`, the COMPLETENESS converse
(supported ⇒ denotes), and ANY behavioral-safety
claim — slice 1 is denotation⊆gate, NOT `BehaviorSafe`. `unified.v` is an EXISTING
proof-only operational semantics (the proven `ustep`, race-freedom + liveness) — **not** the certified path's;
as GoSem grows it must **bridge or retire** `unified.v`, `concurrency.v` (trace / happens-before / race /
bounded-deadlock theory) — slice 1 already bridges `cmd.v` — so there is ONE behavioral authority, never a
second universe that can drift.

**`GoTypes.v` — shared constant-aware type-category checker (imports ONLY `GoAst`).** The bottom of the
type-category layer: `ptype : GExpr -> option PTy` (the structural, constant-aware category assignment —
splitting int/float, constant/runtime, carrying constant values so overflow / div-or-shift-by-zero are
decided from the folded value) and its numeric/conversion combinators, plus the value-position wrapper
`svalue`. Factored out of `GoSafe` so the layers above it consult ONE authority (GoSafe for
`SupportedProgram`; GoSem's slice 1 consults `svalue`/`expr_stmt_ok` for its denotation). No theorems — adds no axioms.
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
(* Later, once GoSem is COMPLETE (slice 1 denotes only a subset) and BehaviorSafe is real:
   a SafeProgram = EmittableProgram + BehaviorSafe, emitted by emit_safe. *)
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
5. **The trusted, unverified plugin `plugin/go.ml`** — TODAY's main output (`main.go`) is lowered by it, and
   no theorem relates its output to the source term (**gap #10**). This is the current adequacy gap and is in
   the TCB until the certified path subsumes it.

`GoPrint` proves the bytes; items 3 and 5 are why this is "Go with proofs," not "Go without trust." FUTURE
(not today's TCB): once emission goes through a GoSem-backed certificate, item 5's plugin is replaced by an
**adequacy assumption connecting `GoSem` to actual Go behavior** ("real Go realizes `GoSem`") — gap #10's
heir, unfalsifiable inside Rocq, to be named in the honesty ledger. No GoSem-BACKED EMISSION exists yet (GoSem
slice 1 denotes programs but does not gate emission), so that assumption is **not** part of the current trust base.

---

## 3. Why this course correction exists

The previous architecture lowered arbitrary Rocq-ish code through a trusted OCaml plugin into Go text — fast
demos, repeated trust-boundary problems, and a raw-string escape hatch that grew an ecosystem around the
wrong abstraction (see `LESSONS.md` for the postmortem). The rule that prevents recurrence:

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
the repo's main `main.go` is STILL the legacy plugin path. The extracted printer `printer.ml` is wired into
that live path for only a small expression class (a binop tree over runtime locals + integer literals + a
fixed set of runtime numeric conversions and fixed-width arithmetic as bridging-binop operands — the exact
list is single-sourced in `PROGRESS.md`, not re-enumerated here); every other shape is printed by the trusted
OCaml `pp_expr`. And even for that class
the printer proofs cover only AST→string serialization
(`gprint`'s round-trip / injectivity): they do NOT cover the trusted MiniML→`GExpr` CONSTRUCTION in `go.ml`
that builds the AST, so the live emission is not "verified Go." GoSem is a slice-1 bridge (effect denotation +
denotation⊆gate soundness), NOT behavioral safety — so there is still no behavioral safety.
Detailed feature state lives in `PROGRESS.md`.

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
Phase 1  Extract the printer/parser seed into GoAst/GoPrint (rename, not copy; no 2nd universe). DONE
Phase 2  Create GoSafe (SupportedProgram) + GoEmit (EmittableProgram; no raw emit).          DONE
Phase 3  main.v builds GoAst.Program and emits ONLY through the certificate.                 DONE
Phase 4  Grow the AST/printer form-by-form (each: represented, printed, round-tripped/       DONE (for now)
         injective, gate-honest). GoStmt forms + EConv + slice/map literals + EStr landed.   — frozen; tighten not grow
Phase 5  Grow safety via GoSem: BRIDGE unified.v/concurrency.v/cmd.v in (no second universe),  IN PROGRESS
         widen toward BehaviorSafe → SafeProgram → emit_safe, wire the certified path to main.
         ↳ SLICE 1 landed: denote_program -> cmd.v Cmd with real println/print/panic effects + gosem_sound
           (denotation⊆gate), faithful to the model; NEXT = eval non-literals, completeness, then BehaviorSafe.
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
naming a past review round / a deleted experiment as the reason a line exists.

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
[live]     No axioms in any gated cone (main_effect + gosem_trust_surface). (axiom-manifest gate over Print Assumptions; pre-commit declaration tripwire)
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
`GoEmit`. Do not use the parser to rescue legacy old-printer strings, or revive a raw-string hatch (Rule 1).
Do not make `SupportedProgram`/`BehaviorSafe` an axiom. Do not create a convenient unsafe `emit` and promise
nobody will use it. Do not claim "safe Go" for any program that did not pass through the behavioral certificate.

---

## Standing bottom line

Do not verify around a bad abstraction. Do not document — or *name* — a shortcut into respectability. Do not
let a proof sit beside the path; put it on the path. Build the AST honestly. Print it boringly. Certify it
explicitly. Emit only certified programs.
