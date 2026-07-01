# Fido AST-First Certified Emission Charter

Standing architectural charter for Fido — binding on Claude Code, Codex review, and human review. It
supersedes the ad-hoc "lower arbitrary Rocq through a trusted plugin" center of gravity.

> **Fido moves toward an AST-first, proof-gated Go emission architecture.** The spine (GoAst → GoPrint →
> GoSem → GoSafe → GoEmit) is defined in §2.

The central rule:

```text
Raw structured Go ASTs may represent unsafe programs.
Only CERTIFIED ASTs may be emitted through the official path.
Early on the certificate is "supported subset" (syntactic). It becomes "behaviorally safe" only when
GoSem-backed SAFETY theorems back the certificate (FIRST proof-only properties, `panic_free_runs_ret` and its
operational lift `panic_free_runs_ret_ustep`, exist but do NOT back it / gate emission) — and the NAME of the
certificate must never claim more than is proved.
```

Treat all existing code as provisional until it fits this architecture. Optimize for **architectural truth
over preserving old momentum.**

---

## 1. Non-negotiable project standard

Primary goal: **merciless correctness.** Supported constructs must be exact w.r.t. the intended Rocq-Go
semantics; unsupported constructs must be mechanically rejected or clearly outside the core. No documentation
may weaken a correctness claim.

Secondary goal: **simplify, generalize, remove dead weight** — subordinate to correctness. Good simplification
makes invariants structural, removes duplicate authorities, and makes bad states unrepresentable. Bad
simplification proves or models less while pretending the claim stayed the same.

---

## 2. The architectural spine

```text
GoAst   says what can be written.
GoPrint proves printing faithfulness ONLY (expression round-trip + program/statement print-injectivity).
GoSem   defines behavior — SLICE 1 (cmd.v bridge + denotation⊆gate soundness); NOT complete, no BehaviorSafe yet.
GoSafe  defines supportedness now, behavioral safety later.
GoEmit  is the only blessed emission path and requires the appropriate certificate.

Printer proofs are SYNTAX proofs. They do NOT imply race freedom, memory safety, termination, session
correctness, or GoSem correctness. Safety proofs are BEHAVIORAL. Emission COMPOSES the two.
```

**`GoAst.v` — structured Go syntax.** Identifiers, literals, types, expressions, statements, programs. May
represent unsafe programs, but must **not** contain raw syntax strings for Go structure. Allowed: string
literal *contents* (printed through an escaping printer) and validated identifiers. Forbidden: raw
expr/stmt/type/decl strings and any constructor smuggling source text. A supported construct gets a
constructor; else it is unrepresentable or rejected by the builder.

**`GoPrint.v` — printing + syntax faithfulness (imports `GoAst`).** Printing + its faithfulness theorems, at
TWO strengths (don't conflate): **expressions** get a full parse round-trip `parse_str (gprint 0 e) = Some
(e, [])` (+ `gprint_inj`) over a real lexer + precedence parser — self-consistency of the **Rocq grammar**,
NOT Go-compiler acceptance; **programs/statements** get print-INJECTIVITY only
(`print_program_inj`/`print_stmt_inj`) — no parser / round-trip at that level yet (ASI/semicolon subtleties
deferred). Purely syntactic — no safety claims here.

**`GoSem.v` — behavioral bridge from `GoAst` into the existing proof models (imports `GoAst`/`GoTypes`/
`GoSafe`/`cmd`) — SLICE 1.** `denote_program : Program -> option (Cmd unit)` bridges into `cmd.v`'s proven
command tree (no second universe): print/println → `COut` (the model's own `w_log`), panic → `CPan`, return,
blank constant-assignment, over a PARTIAL `eval_value` (constants only; exact coverage in `GoSem.v`, not
here). `gosem_sound`: denotation ⊆ `SupportedProgram`. Certified surface: the `Print Assumptions`-gated
`gosem_*_surface` tuples (exact list single-sourced in PROGRESS.md "Current gates"). NO completeness, NO
`BehaviorSafe`. As GoSem grows it must **bridge or retire** `unified.v` (proven `ustep` /
race-freedom / liveness) and `concurrency.v` (trace / happens-before / race / deadlock) — ONE behavioral
authority, never a second universe.

**`GoTypes.v` — shared constant-aware type-category checker (imports ONLY `GoAst`).** `ptype : GExpr -> option
PTy` (structural constant-aware category assignment — int/float, constant/runtime, carrying constant values
so overflow / div-or-shift-by-zero are decided from the folded value) + its combinators + the value-position
wrapper `svalue`. Factored below `GoSafe` so the layers consult ONE authority. No theorems — adds no axioms.
**`ptype` is a CONSERVATIVE supported-subset classifier, NOT Go's typechecker.** No new rule unless it (a)
rejects a real CLOSED bad program currently accepted, or (b) admits a needed supported demo.

**`GoSafe.v` — supportedness now, behavioral safety later (imports `GoAst` + `GoTypes`).** Adds the
statement-shape / supported-syntax layer (`stmt_ok`, `supported_program`, `SupportedProgram`) on top of
`GoTypes`. **Phase 1 is SYNTACTIC supportedness and must be NAMED as such** — calling it `SafeProgram` would
repeat the exact overclaim this refactor kills (Rule 5).

```text
SupportedProgram  -- syntactic: in the supported subset; no unmodeled constructs; no raw escape hatches.
BehaviorSafe      -- semantic GATE (reserved; not yet defined — first proof-only properties
                     `panic_free_runs_ret`(+`_ustep`) exist but are NOT this gate): no nil deref / OOB /
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

`emit_supported` is a printer/supported-subset milestone — NOT behaviorally safe. Do **not** export a raw
`emit : GoAst.Program -> string` (that makes the certificate decorative). Raw printing for tests must not be
the extraction path or back any safety claim.

---

## 2a. Residual trust base (state it; never leave it implicit)

The correctness of an *emitted* program rests on, and only on:

1. The **Rocq kernel** and the trusted stdlib lemmas the proofs use.
2. The **extraction / file-emission step** turning the final `string` into a `.go` file (plain OCaml string
   extraction producing `printer.ml`; NOT `go.ml` lowering).
3. The **Go compiler / runtime / toolchain**.
4. **Trusted foreign Go imports** and monitored boundary assumptions.
5. **The trusted, unverified plugin `plugin/go.ml`** — TODAY's main output (`main.go`) is lowered by it, and
   no theorem relates its output to the source term (**gap #10**). This is the current adequacy gap and is in
   the TCB until the certified path subsumes it.

`GoPrint` proves the bytes; items 3 and 5 are why this is "Go with proofs," not "Go without trust." FUTURE
(not today's TCB): once emission goes through a GoSem-backed certificate, item 5's plugin is replaced by an
**adequacy assumption** ("real Go realizes `GoSem`") — gap #10's heir. No GoSem-backed emission exists yet, so
that assumption is **not** part of the current trust base.

---

## 3. Legacy status and transition discipline

`plugin/go.ml` is **trusted legacy scaffolding.** It may remain only to keep demos building while the
AST-first path matures; it **may not define the correctness claim.**

- New architectural work must **reduce** reliance on Legacy, not improve it. A patch that makes `go.ml`'s
  lowering nicer is moving the wrong direction.
- The old path builds demos; the new path defines the claim. Old path gets deleted as the new path subsumes
  it — never maintained in parallel indefinitely.
- No parallel universes: do not grow a second expression/semantic universe beside the spine.

Honest current status: the spine (`GoAst`/`GoPrint`/`GoTypes`/`GoSafe`/`GoEmit`) compiles zero-axiom and
`main.v` builds a `GoAst.Program` emitted ONLY through `EmittableProgram`; but the repo's `main.go` is STILL
the legacy plugin path. The extracted `printer.ml` is wired into that path for only a small expression class
(single-sourced in `PROGRESS.md`); every other shape is trusted `pp_expr`. Even there the printer proofs cover
only AST→string serialization, NOT the trusted MiniML→`GExpr` CONSTRUCTION in `go.ml`, so the live emission is
not "verified Go." GoSem is a slice-1 bridge, NOT behavioral safety. Detailed feature state: `PROGRESS.md`.

---

## 4. Relooper — demoted

`relooper.v` is proven and should not be deleted casually, but it is **not** part of the first
AST-certified-emission path (direct `GoAst` construction → `GoPrint` → `GoEmit`, not CFG recovery). It is an
optional future lowering component (a higher-level CFG language → GoAst). Do not spend time on relooper
integration until the AST-first emission path is established.

---

## 5. Phases

```text
Phase 0  Freeze the direction.                                                              DONE
Phase 1  Extract the printer/parser seed into GoAst/GoPrint (rename, not copy; no 2nd universe). DONE
Phase 2  Create GoSafe (SupportedProgram) + GoEmit (EmittableProgram; no raw emit).          DONE
Phase 3  main.v builds GoAst.Program and emits ONLY through the certificate.                 DONE
Phase 4  Grow the AST/printer form-by-form (each: represented, printed, round-tripped/       ONGOING
         injective, gate-honest). GoStmt forms (incl. `defer <call>`) + EConv + slice/map    (post-consolidation)
         literals + EStr landed; each new form is print-injective + gate-honest.
Phase 5  Grow safety via GoSem: BRIDGE unified.v/concurrency.v/cmd.v in (no second universe),  IN PROGRESS
         widen toward BehaviorSafe → SafeProgram → emit_safe, wire the certified path to main.
         ↳ SLICE 1 landed (denote_program -> cmd.v with real effects + gosem_sound); NEXT = eval
           non-literals, completeness, then BehaviorSafe.
```

Proceed in small structural steps. Every patch should either move a concept into the correct module, delete
an old wrong path, make a bad path unreachable, strengthen the proof-gated emission boundary, or shrink
trusted legacy code. **Do not add parallel universes. Do not add "future foundation" unless it replaces or
deletes something.**

---

## 6. Rules for Claude Code

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

## 7. Review checklist for every patch

1. Which module did this move toward the target architecture?
2. What old path became unreachable / what code was deleted?
3. Did this create a new parallel syntax/semantic universe?
4. Does any theorem prove something not used by the live path?
5. Does any official emitter bypass the certificate (`EmittableProgram`/`SafeProgram`)?
6. Did docs (or names) overclaim?
7. Did the patch reduce trusted code, preserve it, or increase it? What grep/build gate prevents regression?

---

## 8. Acceptance gates

**[live]** = enforced every build; **[on-land]** = activates when its module lands; **[review]** = human/Codex
discipline.

```text
[live]     No axioms in any gated Print Assumptions surface (manifest + printer + emit flows — see PROGRESS.md "Current gates"; pre-commit declaration tripwire)
[live]     Generated printer artifact (plugin/printer.ml) in sync. (make printer-verify + Docker stage)
[live]     No raw-syntax constructor NAMES in source.             (plugin/smart-ctor-gate.sh)
[live]     Official emit only via GoEmit's certificate API; no direct print_program call outside GoEmit.
[live]     Print Assumptions for every public safety theorem (the panic-free property `panic_free_runs_ret` and its operational lift `panic_free_runs_ret_ustep` are manifest-gated now; the full BehaviorSafe theorems land later).
[review]   The Phase-1 gate is named SupportedProgram, NOT SafeProgram, until GoSem-backed BehaviorSafe exists.
[review]   Docs and NAMES do not claim more than the live path proves.
```

The smart-ctor gate is a **name-regression tripwire over hand-written sources**, catching KNOWN forbidden
names, NOT a differently-named raw hatch. The real guarantees are structural: `GoAst`'s constructors take only
validated/semantic payloads (raw syntax unrepresentable) and `GoEmit` exports only certificate-requiring
emitters (a raw emit is a type error) — enforced by review of the definitions, not by grep.

---

## 9. What not to do

No second universe beside the spine; no old plugin printer wired into `GoEmit`; no parser used to rescue
old-printer strings or a raw-string hatch (Rule 1); no `SupportedProgram`/`BehaviorSafe` axiom; no convenient
unsafe `emit`; no "safe Go" claim for a program that skipped the behavioral certificate.

---

## Standing bottom line

Do not verify around a bad abstraction. Do not document — or *name* — a shortcut into respectability. Do not
let a proof sit beside the path; put it on the path. Build the AST honestly. Print it boringly. Certify it
explicitly. Emit only certified programs.
