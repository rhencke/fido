# Fido AST-First Certified Emission Charter

This is the standing architectural charter for Fido — binding on Claude Code, Codex review, and human
review. It supersedes the ad-hoc "lower arbitrary Rocq through a trusted plugin" center of gravity.

Fido is **not** being refactored from a finished, stable system. It is being course-corrected from a
fast-moving prototype that proved several ideas promising but also exposed a dangerous pattern: plausible
local fixes preserve the wrong abstraction and then grow an ecosystem around it (the `SRaw` episode, §4).

The new direction is explicit:

> **Fido moves toward an AST-first, proof-gated Go emission architecture.**

The long-term shape:

```text
GoAst    says what Go-shaped syntax can be written.
GoPrint  proves the AST prints (and parses back) correctly — SYNTAX ONLY.
GoSem    says what the AST means (the ONE authoritative semantics).
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

This is a course correction, not a victory lap. Treat all existing code as provisional until it fits this
architecture. Optimize for **architectural truth over preserving old momentum.**

---

## 1. Non-negotiable project standard

Primary goal: **merciless correctness.** Supported constructs must be exact with respect to the intended
Rocq-Go semantics. Unsupported constructs must be mechanically rejected or clearly outside the core. No
documentation may weaken a correctness claim.

Secondary goal: **simplify, generalize, remove dead weight** — but subordinate to correctness. Do not
simplify by weakening the model, collapsing semantically different cases, deleting necessary checks, or
hiding trusted behavior. Good simplification makes invariants structural, removes duplicate authorities,
deletes obsolete scaffolding, and makes bad states unrepresentable or un-emittable. Bad simplification
proves less or models less while pretending the claim stayed the same.

---

## 2. The architectural spine

Layer separation — memorize the boundaries:

```text
GoAst   says what can be written.
GoPrint proves syntax printing/parsing correctness ONLY.
GoSem   defines behavior.
GoSafe  defines supportedness now, behavioral safety later.
GoEmit  is the only blessed emission path and requires the appropriate certificate.

Printer proofs are SYNTAX proofs. They do NOT imply race freedom, memory safety, termination, session
correctness, or GoSem correctness.
Safety proofs are BEHAVIORAL proofs. They do NOT imply printer correctness.
Emission COMPOSES the two.
```

### `GoAst.v` — structured Go syntax

Identifiers, literals, types, expressions, lvalues, statements, blocks, declarations, functions,
packages/programs. `GoAst` may represent unsafe programs — the AST is syntax, not a safety proof — but it
must **not** contain raw syntax strings for Go structure.

Allowed: semantic string *contents* for string literals (printed through an escaping printer); validated
identifiers; structured/validated import paths; validated comment payloads.

Forbidden: raw expression/statement/type/declaration strings; "opaque Go syntax" constructors; "trusted
raw" constructors; any constructor that smuggles source text to avoid modeling syntax.

If a construct is supported, it gets a constructor. If it is not supported, it is unrepresentable in the
supported path or rejected by the builder.

### `GoPrint.v` — printing + syntax round-trip (imports `GoAst`)

Owns printing and the syntax round-trip theorems. The printer's job is **purely syntactic**; it does not
care whether a program is race-free, deadlock-free, session-safe, or memory-safe.

Good printer theorems: `parse_expr (print_expr e) = Some e`, `parse_program (print_program p) = Some p`, or
a staged `GoSubsetAccepts (print_program p)`. Bad printer "theorems": `print_program p is safe` /
`is race-free` — those belong in `GoSem` / `GoSafe`, not here.

The parser used by printer proofs is a real lexer/parser: `text -> tokens -> recursive descent / precedence
parser -> AST`. A parser is not a maze of string splits. Niklaus Wirth should look at this subsystem and
nod.

### `GoSem.v` — semantics (imports `GoAst`)

Operational/denotational semantics for the supported AST subset: happens-before, blocking, panics, output,
defer, allocation, maps, slices, channels, goroutines, select.

**`GoSem` is the MIGRATION / BRIDGE point for existing semantic work — NOT a greenfield duplicate.** Fido
already has substantial proven semantics: `unified.v` (the authoritative closed-world `ustep` operational
semantics carrying every effect, with race-freedom and liveness/deadlock proved), `concurrency.v` (the
calculus-agnostic trace / happens-before / race theory and the bounded deadlock theory), and `cmd.v` (the
effect evaluator). These must be **moved into or bridged to `GoSem`**, or explicitly retired. The end state
is **one authoritative operational semantics** for safety claims — never two semantic universes that can
drift (that is the duplicate-authority failure this charter forbids). Do not let the printer carry semantic
obligations: the printer prints; semantics interprets.

### `GoSafe.v` — supportedness now, behavioral safety later (imports `GoAst`, and `GoSem` once it exists)

Defines the predicates the emitter gates on.

**Phase 1 is SYNTACTIC supportedness, and must be NAMED as such** — a syntactic/well-formed/supported-subset
check is *not* behavioral safety, and calling it `SafeProgram` would repeat the exact overclaim this
refactor exists to kill (see Rule 5). Use:

```text
SupportedProgram   -- syntactic: in the supported subset, no unmodeled constructs, no raw escape hatches.
```

Reserve the behavioral names for when `GoSem`-backed theorems actually exist:

```text
BehaviorSafe       -- semantic: no nil deref / OOB / send-on-closed / illegal close / data race;
                      happens-before consistency; session/protocol safety; ownership discipline;
                      termination/deadlock-freedom for selected fragments.
```

Safety is not a theorem merely sitting near an AST. It must become the **ticket required by the emitter.**

### `GoEmit.v` — the only blessed emission path (imports `GoAst`, `GoPrint`, `GoSafe`)

```coq
Record EmittableProgram := {
  ep_program  : GoAst.Program;
  ep_supported : GoSafe.SupportedProgram ep_program;
}.
Definition emit_supported (p : EmittableProgram) : string :=
  GoPrint.print_program p.(ep_program).

(* Later, once GoSem is authoritative and BehaviorSafe is real: *)
Record SafeProgram := {
  sp_emittable : EmittableProgram;
  sp_safe      : GoSafe.BehaviorSafe sp_emittable.(ep_program);
}.
Definition emit_safe (p : SafeProgram) : string :=
  GoPrint.print_program p.(sp_emittable).(ep_program).
```

`emit_supported` is acceptable as a **printer / supported-subset milestone**, but it must NOT be described
as behaviorally safe. The long-term blessed safety path is `emit_safe`.

Do **not** export an official `emit : GoAst.Program -> string` — that makes the certificate decorative. If
raw printing is needed for tests, name it like a loaded gun (`unsafe_print_program_for_tests`); it must not
be the extraction path and must not back any demo claiming Fido safety.

---

## 2a. Residual trust base (state it; never leave it implicit)

After this refactor the correctness of an *emitted* program rests on, and only on:

1. **The Rocq kernel** and the trusted Rocq stdlib lemmas the proofs use.
2. **The extraction / file-emission step** that turns the final `string` into a `.go` file on disk (plain
   OCaml string extraction — the same mechanism that already produces `printer.ml`; NOT `go.ml` lowering).
3. **The Go compiler / runtime / toolchain** that compiles and runs the emitted source.
4. **Trusted foreign Go imports** and any monitored boundary assumptions about external code.
5. **An adequacy assumption/theorem connecting `GoSem` to actual Go behavior** for the supported subset —
   i.e. "real Go realizes `GoSem`." This is unfalsifiable inside Rocq today and is the heir to the old
   "gap #10." It must be named in the honesty ledger, never assumed silently.

`GoPrint` proves the bytes; items 3 and 5 are why this is "Go with proofs," not "Go without trust."

---

## 3. The core slogan

```text
GoAst says what can be written.
GoPrint says it prints correctly (syntax).
GoSem says what it means.
GoSafe says what is supported now / safe later.
GoEmit refuses everything without the certificate.
```

---

## 4. Why this course correction exists

The previous architecture lowered arbitrary Rocq-ish code through a trusted OCaml plugin into Go text. Fast
demos, repeated trust-boundary problems. The `SRaw` episode is the cautionary tale: a raw expression-string
escape hatch added "for convenience" grew helpers, validators, scanner predicates, parser fragments, tests,
comments, and proof scaffolding around it — looking ever more formal while preserving the wrong abstraction.

The rule that prevents the recurrence:

```text
If a construct is syntax, represent it structurally.
If it cannot be represented structurally yet, reject it.
Do not rescue old source strings.
```

---

## 5. Legacy status and transition discipline

The existing plugin/lowering path (`plugin/go.ml`) is **trusted legacy scaffolding.** It may remain only to
keep demos building while the AST-first path matures. It **may not define the correctness claim.**

Transition discipline (the transition is itself a parallel-universe hazard — handle it deliberately):

- `Front` **moves** into `GoAst`/`GoPrint` (rename, not copy). There must NOT be two expression universes
  (`Front` beside `GoAst`) that can drift. Do not keep growing `Front`.
- New architectural work must **reduce** reliance on Legacy, not improve it. A patch that makes `go.ml`'s
  lowering nicer is moving the wrong direction.
- The old path builds demos; the new path defines the claim. Old path gets deleted as the new path subsumes
  it — not maintained in parallel indefinitely.

Honest current status:

```text
Legacy:    plugin/go.ml lowering is trusted and transitional.
New path:  GoAst + GoPrint + GoSem + GoSafe + GoEmit is the intended architecture.
Landed:    main.v builds a GoAst.Program with a REAL func main body and emits it ONLY through
           EmittableProgram (commit 2 = empty main; f2b6003 = a GoStmt body, println(1)).
Goal now:  Phase 4 — keep growing the AST/printer: more GoStmt forms (assignment, var, control
           flow) + the parked EConv.  (Program-printer injectivity print_program_inj landed 34e4a6c;
           2nd statement form GsReturn landed 6e2ba11.)
```

---

## 6. Relooper status — demoted

`relooper.v` is promising and its proven work should not be deleted casually, but it is **not** part of the
first AST-certified-emission path. The initial path is **direct `GoAst` construction -> `GoPrint` ->
`GoEmit`**, not CFG recovery.

```text
relooper.v = optional FUTURE lowering component (a higher-level CFG language -> GoAst).
  not required for GoAst / GoPrint / GoSafe / GoEmit / the first certified emitter.
```

Do not spend time on relooper integration until the AST-first emission path exists.

---

## 7. Immediate refactor direction

> **STATUS (2026-06-28): Phases 0–3 are DONE; Phase 4 is in progress.** The charter is committed;
> `goprint.v`/`Module Front` were SPLIT and RETIRED into `GoAst.v` (syntax) + `GoPrint.v` (printer) (spine
> commit 1, f7d9383); then `GoSafe.v` (`SupportedProgram`) + `GoEmit.v` (`EmittableProgram` + `emit_supported`,
> no raw `emit : Program -> string`) landed with a `GoAst.Program` and the first proof-gated certified emission,
> and `main.v` builds+emits a program through that blessed path (spine commit 2, 32af69f — Phases 2 AND 3).
> **Phase 4 (grow the AST/printer) is now underway:** (f2b6003) added a `GoStmt` AST + a real `func main` body
> — `GsExprStmt`/`println(1)`, printed via the machine-checked `gprint`; then (34e4a6c) proved
> `print_program_inj` — program-printer INJECTIVITY: distinct `GoAst.Program`s emit distinct Go source (via
> `no_nl_gprint` + a newline delimiter-split, the float-hex `no_p`/`split_p` technique).  NB this is print
> injectivity only, NOT a parse round-trip and NOT Go-syntax acceptance.  Then (6e2ba11) added the 2nd statement
> form `GsReturn` (`print_stmt_inj` now multi-constructor, the `GsExprStmt`/`GsReturn` cross case closed by
> `gprint_neq_return` — "return" lexes to the `TReturn` keyword token, which the expression parser rejects, so
> `parse_str "return" = None`). **Then a course correction (external review 2026-06-28): `SupportedProgram`
> was too weak — it checked only the package name, so it certified INVALID Go like `func main(){ 1 }`.** Fixed:
> `SupportedProgram` is now a DECIDABLE supported-subset gate (`supported_program` = `pkg=main` ∧
> `forallb stmt_ok body`, where a bare expression statement must be a call) — a regression locks out the
> bad program, and GoSafe/GoEmit joined the explicit zero-axiom gate (`make emit-verify`) + a
> print_program-discipline tripwire. Still ahead in Phase 4: more `GoStmt` forms (assignment, var, control
> flow) and the parked `EConv`. **Blessed-path file emission DEMONSTRATED:** `make emit-demo` extracts
> `GoEmit.demo_emit` and writes a real `emitdemo/spine_demo.go` that the Go toolchain ACCEPTS (gofmt-clean +
> `go vet`) — the end-to-end check connecting the proven bytes to the compiler. **Still RED:** that is a
> SEPARATE demo; the repo's MAIN output `main.go` is STILL the legacy `plugin/go.ml` path (extracted
> `Printer.gprint`, flat/transitional), NOT certificate-gated — so do not claim main.go is blessed; no GoSem
> behavioral safety yet. All golden byte-identical, zero axioms. Every "Front" below names that now-retired
> seed (the completed migration's source), NOT a current structure.

Not a giant rewrite in one patch. Proceed in small, structural steps. Every patch should either: move a
concept into the correct module, delete an old wrong path, make a bad path unreachable, create/strengthen
the proof-gated emission boundary, or shrink trusted legacy code. **Do not add parallel universes. Do not
add "future foundation" unless it replaces or deletes something.**

- **Phase 0 — Freeze the direction. ✅ DONE (cf5fea2).** Charter committed; PROGRESS.md ledger points here.
- **Phase 1 — Extract the `Front` seed into `GoAst`/`GoPrint`. ✅ DONE (commit 1, f7d9383).** The syntax
  moved into `GoAst.v`, the printer/parser/round-trip into `GoPrint.v`; `Module Front` retired — no second
  expression universe. (`Front` was the migration name for the pre-split seed.)
- **Phase 2 — Create `GoSafe.v` + `GoEmit.v` early. ✅ DONE (commit 2, 32af69f).** `SupportedProgram` is the
  Phase-1 syntactic gate; the invariant holds: **the official emitter accepts only `EmittableProgram` (later
  `SafeProgram`)** — there is no raw `emit : Program -> string`.
- **Phase 3 — `main.v` builds Go AST programs. ✅ DONE (commit 2, 32af69f).** `spine_prog`/`spine_cert`/
  `spine_emit` in `main.v` build a `GoAst.Program` and emit it ONLY through the blessed path:
  ```coq
  Definition p_raw  : GoAst.Program := ...
  Lemma p_supported : GoSafe.SupportedProgram p_raw. Proof. ... Qed.
  Definition p_em   : GoEmit.EmittableProgram := {| ep_program := p_raw; ep_supported := p_supported |}.
  Definition p_out  := GoEmit.emit_supported p_em.
  ```
  Unsupported ASTs can exist; they just cannot be emitted through `GoEmit`.
- **Phase 4 — Grow the AST and printer. ⏳ IN PROGRESS (f2b6003 = first increment).** Each supported form:
  represented in `GoAst`, printed in `GoPrint`, round-tripped / injectivity-proven, used by a small example.
  No raw constructors. No string-splitting in place of a lexer/parser. Landed: `GoStmt` + `GsExprStmt` (a real
  `func main` body, `println(1)`) with `print_stmt_inj` (f2b6003); whole-program print INJECTIVITY
  `print_program_inj` (34e4a6c — `no_nl_gprint` + a newline delimiter-split; injectivity only, not Go-syntax
  acceptance); the 2nd statement form
  `GsReturn` (6e2ba11 — `print_stmt_inj` multi-constructor via `gprint_neq_return`). Next: more `GoStmt` forms
  (assignment, var, control flow); the parked `EConv` / `ConvTy` conversion work re-lands HERE inside
  `GoAst`/`GoPrint`.
- **Phase 5 — Grow safety via `GoSem`.** Bridge the existing `unified.v`/`concurrency.v`/`cmd.v` theory in.
  Widen: sequential support → mutable locals → heap/slices/maps → ownership → goroutines with resource
  splitting → channels with capacity/close-state → happens-before & race freedom → sessions → termination/
  deadlock-freedom for selected fragments. Each widening adds a certified example and never weakens the gate.

---

## 8. Rules for Claude Code

**Rule 1 — No raw syntax in core AST.** Forbidden in core modules: `RawExpr`, `RawStmt`, `RawDecl`,
`RawType`, `OpaqueExpr`, `TrustedExpr`, `SRaw`, `raw_ok`, raw source strings. Semantic strings are okay only
when the printer escapes them (e.g. string-literal contents).

**Rule 2 — No string-rescue path.** Forbidden: `old printer -> string -> validator/parser -> new printer`.
The generator builds AST directly. The lexer/parser exists for proof and testing, never to rescue old
string output.

**Rule 3 — No official raw emitter.** Forbidden on the blessed path: `emit : GoAst.Program -> string`. The
official emitter requires `EmittableProgram` (later `SafeProgram`).

**Rule 4 — No decorative safety/support proofs.** This is insufficient:
```coq
Definition p : GoAst.Program := ...   Lemma p_ok : SupportedProgram p.   Definition out := GoPrint.print_program p.
```
The emitted output must go through the certificate: `Definition em := {| ep_program := p; ep_supported := p_ok |}.
Definition out := GoEmit.emit_supported em.`

**Rule 5 — No documentation as correctness.** Docs may *describe* a limitation; they may not make it
acceptable in the core. Suspicious phrases: "known limitation", "plugin never emits this", "trusted
fallback", "future stage", "fail-loud", "documented shortcut", "proof-only", "no theorem depends on this".
If a bad case exists, make it impossible, reject it, or move it outside the core. **Naming is a correctness
claim too:** do not name a syntactic gate `SafeProgram`.

**Rule 6 — Deletion is progress.** Every structural patch should preferably delete something. Report `wc -l`
of affected files, greps for old-architecture terms, fallback counts, dead-helper counts. A patch that only
adds scaffolding is suspect.

**Rule 7 — Review archaeology belongs in `LESSONS.md`.** Active comments explain invariants, not the social
history of a bug. Good: "Identifier-led `T(x)` is syntactic application; call-vs-conversion is semantic."
Bad: "Review #9 amendment 3 forced this after SRaw...".

---

## 9. Review checklist for every patch

1. Which module did this move toward the target architecture?
2. What old path became unreachable?
3. What code was deleted?
4. Did this create a new parallel syntax/semantic universe?
5. Does any theorem prove something not used by the live path?
6. Does any official emitter bypass the certificate (`EmittableProgram`/`SafeProgram`)?
7. Did docs (or names) overclaim?
8. Did the patch reduce trusted code, preserve it, or increase it?
9. What exact grep/build gate prevents regression?

Codex/human review should reject patches that cannot answer these concretely.

---

## 10. Acceptance gates

This is the TARGET gate set. Each line is tagged with what enforces it: **[live]** = enforced on every build
TODAY; **[on-land]** = activates when its module lands (do not claim it before then); **[review]** =
discipline enforced by human/Codex review, not a build step.

```text
[live]     No project Axioms / Admitted / admit.            (axiom-manifest gate + Print Assumptions)
[live]     Generated printer artifact (plugin/printer.ml) in sync.   (make printer-verify + Docker stage)
[live]     No raw-syntax constructor NAMES in source.        (plugin/smart-ctor-gate.sh — see (a) below)
[on-land]  Print Assumptions for every public safety/emitter theorem (once GoSafe/GoEmit exist).
[on-land]  Generated EMITTER artifact in sync (once GoEmit is extracted).
[on-land]  No official emit from raw GoAst.Program — STRUCTURAL via GoEmit's API (once GoEmit lands).
[on-land]  No legacy string-rescue path in the new emitter (once the emitter exists).
[review]   The Phase-1 gate is named SupportedProgram, NOT SafeProgram, until GoSem-backed BehaviorSafe exists.
[review]   Docs and NAMES do not claim more than the live path proves.
```

Two kinds of grep, and they must NOT be conflated:

**(a) Name-regression TRIPWIRE — live, but NOT structural protection.** The enumerated forbidden raw-syntax
ctor names (`SRaw`, `raw_ok`, `RawExpr`, `RawStmt`, `RawDecl`, `RawType`, `OpaqueExpr`, `TrustedExpr`, plus
the SRaw-era `build_atom`/…) are grepped by `plugin/smart-ctor-gate.sh` over the hand-written sources only
(`*.v` + `plugin/go.ml` + the `.mlg` glue; the generated `plugin/printer.ml` and all docs are out of scope).
It runs in the pre-commit hook AND non-bypassably in the Docker prover stage on every `make check`; it is
clean today and FAILS the build if any of those NAMES reappears. (Do NOT replace it with a tree-wide
`grep -RInE … .` — that self-fails on the docs and `printer.ml`, which name these patterns on purpose.)
**This is a regression tripwire for KNOWN names, not a guarantee of no-raw-syntax** — a grep cannot stop a
differently-named raw hatch (a new string-carrying `GExpr`/`Program` constructor under any other name).

The actual STRUCTURAL guarantee against raw syntax is a property of the **AST definition itself**: `GoAst`'s
constructors take only validated/semantic payloads (literal contents, validated identifiers) and never a raw
expr/stmt/type/decl string — so raw syntax is *unrepresentable*, enforced by review of the `GoAst` inductive
when it lands, not by this grep. Likewise the "no raw emit" rule (`emit : GoAst.Program -> string`) is
structural — `GoEmit` exports only certificate-requiring emitters (`emit_supported : EmittableProgram ->
string`; later `emit_safe`) and never `emit : Program -> string`, so a raw emit is a *type error*, not a text
match (a grep for it is deliberately NOT used: that signature appears in honest comments and would self-fail).

**(b) Review HEURISTIC — NOT a pass/fail gate.** The "suspicious phrases" scan below is a prompt for human/
Codex scrutiny per Rule 5, not an acceptance gate: honest documentation and comments legitimately use these
words (e.g. `proof-only` correctly describes `concurrency.v`/`relooper.v`; honest TCB notes say `trusted
fallback`/`known limitation`). It matches dozens of legitimate source lines today and is EXPECTED to be
non-empty. Treat each hit as "read this and check it is not an overclaim," never as "fail the build."

```sh
# review aid only — non-empty is normal; judge each hit, do not gate on it
grep -nE 'plugin never emits|known limitation|proof-only|future stage|trusted fallback' $SRC
```

---

## 11. The first concrete task after committing this charter

Do not start with concurrency, the relooper, or full safety. Start by creating the module spine.

Minimum first structural commit: `GoAst.v`, `GoPrint.v`, `GoSafe.v`, `GoEmit.v`. **Move/rename** the current
clean `Front` expression AST + printer/parser/round-trip into `GoAst`/`GoPrint` (do not copy into a second
universe). Define a tiny `GoAst.Program`; a deliberately tiny `GoSafe.SupportedProgram`; the
`EmittableProgram` record; `GoEmit.emit_supported : EmittableProgram -> string`. Add one tiny emittable
example in `main.v` that emits ONLY through `GoEmit`. Do not add new grammar features yet. Do not revive raw
syntax, string splitting, or old `Front` growth.

Skeleton (module signatures; bodies grow from the moved `Front` work):

```coq
Module GoAst.
  (* Broad structured Go syntax. Can represent unsafe programs. *)
  Parameter Program : Type.   (* replaced by the real inductive, seeded from Front *)
End GoAst.

Module GoPrint.
  Parameter print_program : GoAst.Program -> string.
  (* Printer/parser theorems live here. Syntax only. No safety claims. *)
End GoPrint.

Module GoSafe.
  (* Phase 1: syntactic / support gate, NOT behavioral safety. *)
  Parameter SupportedProgram : GoAst.Program -> Prop.
  (* Later, once GoSem is authoritative: *)
  Parameter BehaviorSafe : GoAst.Program -> Prop.
End GoSafe.

Module GoEmit.
  Record EmittableProgram := {
    ep_program   : GoAst.Program;
    ep_supported : GoSafe.SupportedProgram ep_program;
  }.
  Definition emit_supported (p : EmittableProgram) : string :=
    GoPrint.print_program p.(ep_program).

  Record SafeProgram := {
    sp_emittable : EmittableProgram;
    sp_safe      : GoSafe.BehaviorSafe sp_emittable.(ep_program);
  }.
  Definition emit_safe (p : SafeProgram) : string :=
    GoPrint.print_program p.(sp_emittable).(ep_program).
End GoEmit.
```

(`Parameter` here is illustration of the SHAPE only; the real modules contain concrete `Definition`s /
`Inductive`s — the zero-axiom rule forbids leaving `Parameter`/`Axiom` in the trust base.)

---

## 12. What not to do next

Do not keep building `Front` beside `GoAst`. Do not wire the old plugin printer into `GoEmit`. Do not use
the parser to parse legacy old-printer strings. Do not revive `SRaw`. Do not make `SupportedProgram`/
`BehaviorSafe` an axiom. Do not create a convenient unsafe `emit` and promise nobody will use it. Do not
spend time on relooper integration until the AST-first emission path exists. Do not claim "safe Go" for any
program that did not pass through the (behavioral) certificate.

---

## 13. Long-term vision

`main.v` defines arbitrary Go programs as structured ASTs — including unsafe ones — but only programs that
satisfy Fido's safety predicate can be emitted through the official path:

```text
raw AST expressiveness  +  proof-gated extraction  +  verified syntax printing.
```

The final system makes the distinction impossible to miss:

```text
GoPrint.print_program : raw syntax printer, internal / for proofs.
GoEmit.emit_safe      : official safe emission, requires the behavioral certificate.
```

If a user wants the guarantee, they use `GoEmit.emit_safe`.

---

## 14. Standing bottom line

Do not verify around a bad abstraction. Do not document — or *name* — a shortcut into respectability. Do not
let a proof sit beside the path; put it on the path. Build the AST honestly. Print it boringly. Certify it
explicitly. Emit only certified programs.
