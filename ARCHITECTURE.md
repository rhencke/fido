# Fido AST-First Certified Emission Charter

Standing architectural charter — binding on Claude Code, Codex review, and human review.

The central rule:

```text
Raw structured Go ASTs may represent Go-shaped programs that do not compile.
Only CERTIFIED ASTs may be emitted through the official path.
The certificate is "statically compiler-admissible" (GoCompile: the front-end obligations —
names/scopes/forms/constants). It becomes "behaviorally safe" only when GoSem-backed SAFETY
theorems (a SEPARATE layer — GoSemSafe / future GoSafe) back it — a FIRST NARROW one exists
(§2a), but the general behaviorally-safe certificate for the main output does NOT — and the
NAME of the certificate must never claim more than is proved.
```

Treat all existing code as provisional until it fits this architecture. **Architectural
truth over preserving old momentum.**

---

## 1. Non-negotiable project standard

Primary goal: **merciless correctness.** Supported constructs must be exact w.r.t. the
intended Rocq-Go semantics; unsupported constructs must be mechanically rejected or clearly
outside the core. No documentation may weaken a correctness claim.

Secondary goal: **simplify, generalize, remove dead weight** — subordinate to correctness.
Good simplification makes invariants structural, removes duplicate authorities, and makes
bad states unrepresentable. Bad simplification proves or models less while pretending the
claim stayed the same.

---

## 2. The architectural spine

```text
GoAst     — this represents a SYNTACTICALLY VALID program (well-formed Go syntax); it may not compile.
GoPrint   proves printing faithfulness ONLY (parser-free type/expression/statement/program token uniqueness via the canonical grammar; string-level print-injectivity siblings too).
GoCompile — this program WOULD COMPILE: the front-end obligations for the emitted subset (names
          resolve, scopes valid, forms legal, locals used, constants fit).
GoSem     — the SEMANTICS atop a compilable program: runtime meaning, only for programs GoCompile
          admits — SLICE 1 (cmd.v bridge + denotation⊆gate); NOT complete.
GoSemSafe / future GoSafe  — SAFETY atop the semantics: behavioral safety, only for programs GoSem
          gives meaning.  A SEPARATE layer, never GoCompile.
GoEmit    is the only blessed emission path and requires the appropriate certificate (GoCompile now).

The Go compiler may compile our program, but it must not be the FIRST component to understand it —
GoCompile proves the front-end obligations. Printer proofs are SYNTAX proofs — they do NOT imply
static admissibility, race freedom, memory safety, termination, session correctness, or GoSem
correctness. Static admissibility is GoCompile; behavioral safety is BEHAVIORAL. Emission COMPOSES them.
```

**`GoAst.v` — structured Go syntax.** May represent unsafe programs, but must **not**
contain raw syntax strings for Go structure. Allowed: string-literal *contents* (printed
through an escaping printer) and validated identifiers. Forbidden: raw
expr/stmt/type/decl strings and any constructor smuggling source text. A supported
construct gets a constructor; else it is unrepresentable or rejected by the builder.

**`GoPrint.v` — printing + syntax faithfulness (imports `GoAst`).** The intended syntax
AUTHORITY is the relational/canonical grammar layer (`CanonExpr`-shaped relations +
`gprint_*_canonical` + `canon_*_unique` + lexical faithfulness — CLAUDE.md "Syntax
authority"). It now EXISTS for **types, expressions, statements, and whole programs**: `CanonTy`/`CanonExpr`/
`CanonStmt`/`CanonProgram` relations, `gprint_expr_canonical`/`gprint_stmt_canonical`/`gprint_program_canonical`
(the printer inhabits the grammar), `lex_gprint_expr` (lexical faithfulness, expression-level),
`canon_ty_unique` (type-level token uniqueness, PARSER-FREE via `gttokens_ty_inj`), `canon_expr_unique`
(expression-level, via `gtokens_inj`), `canon_stmt_unique` (statement-level, via `stmt_tokens_inj`), and
`canon_program_unique` (program-level, via `program_tokens_inj` — the body a `TSemi`-separated statement list
split by `semi_free_split`). So the authority is now the canonical grammar for types, expressions, statements,
AND programs: printer injectivity is PARSER-FREE throughout — `gprint_inj` off `gtokens_inj` + `gtokens_lex`,
`print_ty_inj` off `gttokens_ty_inj` + `lex_print_ty`. The executable parser is DERIVED TOOLING — the
self-consistency round-trips (`parse_print_roundtrip`, `parse_gty_print_ty`) AND completeness against the
grammar (`parse_complete` : `CanonExpr 0 e ts -> parse ts = Some (e, nil)`, Phase 5) — evidence the parser
is COMPLETE for the grammar (Rocq-grammar self-consistency; COMPLETE-not-SOUND — it accepts non-canonical streams like redundant parens, so `parse_sound` is FALSE as stated), NOT Go-compiler acceptance and NOT the printer-injectivity authority
(nothing depends on either now). The statement/program DISJOINTNESS lemmas (`gprint_neq_return`/…) are
PARSER-FREE too — LEXICAL (a keyword form fails to `lex` or leads with `TReturn`, which no expression's tokens
do). The STATEMENT and PROGRAM canonical layers are now DONE: `CanonStmt`/`CanonProgram` + their
canonicity/functionality/uniqueness (token uniqueness PARSER-FREE via `stmt_tokens_inj`/`program_tokens_inj`,
resting on `gtokens_no_stmt`). LEXICAL faithfulness (`lex (print_stmt s) = Some (stmt_tokens s)`) is PROVED
for the 3 lex-supported statement forms (`lex_print_stmt_exprstmt`/`_return`/`_returnval`, via `gtokens_lex`/
`lex_return`/`lex_return_app`). Still OPEN: the `:=`/`=`/`defer` statement forms (needing new lexer arms) and
the program level `lex_gprint_program` (a `TPackage`-keyword arm — "package" is a keyword that fails to lex
today, `lex_package` — plus an ASI pass emitting `TSemi`); `print_stmt_inj`/`print_program_inj`
remain the weaker STRING-injectivity siblings. Purely syntactic.

**`GoSem.v` — behavioral bridge from `GoAst` into the existing proof models — SLICE 1.**
`denote_program : Program -> option (Cmd unit)` bridges into `cmd.v`'s proven command tree
(no second universe), over a PARTIAL `eval_value` — coverage single-sourced in PROGRESS.md.
`gosem_sound`: denotation ⊆ `GoCompile`. Certified surface: the `Print
Assumptions`-gated `gosem_*_surface` tuples (list single-sourced in PROGRESS.md "Current
gates"). NO completeness, NO `BehaviorSafe`. As GoSem grows it must **bridge or retire**
`unified.v` and `concurrency.v` — ONE behavioral authority, never a second universe.

**`GoTypes.v` — shared constant-aware type-category checker (imports ONLY `GoAst`).**
`ptype : GExpr -> option PTy` (constant-aware category assignment, carrying constant
values so overflow / div-or-shift-by-zero are decided from the folded value) + combinators
+ the value-position wrapper `svalue`. No theorems — adds no axioms. **`ptype` is a
CONSERVATIVE supported-subset classifier, NOT Go's typechecker.** No new rule unless it
(a) rejects a real CLOSED bad program currently accepted, or (b) admits a needed demo.

**`GoCompile.v` — STATIC compiler-admissibility, the compiler front-end proof layer (imports
`GoAst` + `GoTypes`).**  The program gate is `go_compile_check`/`GoCompile`: package-main + the
scope-threaded body fold `body_okS` (over the sealed `ScopeS`; locals bind only via
`scope_declare`) + the final `scope_all_used`. `stmt_ok` is the CLOSED scope-free fragment
GoSem slice 1 is gated on (decl-free agreement: `body_okS_nil_declfree`). **This is STATIC
admissibility, NOT behavioral safety — a static gate never claims runtime safety (Rule 6).**
Today `GoCompile p := go_compile_check p = true` (the executable checker as authority); the
proof-bearing declarative `CompileExpr`/`CompileStmt`/`CompileBody` relation + checker soundness
is the next GoCompile phase (`plans/gocompile.md`) — NOT a decorative bool-alias.

```text
GoCompile  -- syntactic: in the supported subset; no unmodeled constructs; no raw escape hatches.
BehaviorSafe      -- semantic GATE (reserved; not yet defined): no nil deref / OOB /
                     send-on-closed / illegal close / data race; happens-before consistency; session safety.
```

Safety must become the **ticket required by the emitter**, not a theorem sitting near an AST.

**`GoEmit.v` — the only blessed emission path (imports `GoAst`, `GoPrint`, `GoCompile`).**

```coq
Record EmittableProgram := { ep_program : GoAst.Program; ep_compile : GoCompile.GoCompile ep_program }.
Definition emit_compiled (p : EmittableProgram) : string := GoPrint.print_program p.(ep_program).
(* Later, once GoSem is COMPLETE and BehaviorSafe is real:
   a SafeProgram = EmittableProgram + BehaviorSafe, emitted by emit_safe. *)
```

`emit_compiled` is a printer/compile-admissibility milestone — NOT behaviorally safe. Do
**not** export a raw `emit : GoAst.Program -> string`. Raw printing for tests must not be
the extraction path or back any safety claim.

---

## 2a. Residual trust base (state it; never leave it implicit)

The correctness of an *emitted* program rests on, and only on:

1. The **Rocq kernel** and the trusted stdlib lemmas the proofs use.
2. The **extraction / file-emission step** turning the final `string` into a `.go` file.
3. The **Go compiler / runtime / toolchain**.
4. **Trusted foreign Go imports** and monitored boundary assumptions.
5. **The trusted, unverified plugin `plugin/go.ml`** — TODAY's main output (`main.go`) is
   lowered by it; no theorem relates its output to the source term (**gap #10**).

`GoPrint` proves the bytes; items 3 and 5 are why this is "Go with proofs," not "Go
without trust." The FIRST GoSem-backed emission cert exists — `GoSemSafe.emit_panic_free`:
accepted iff the program denotes to `c` with `cmd_no_panic c` (denotable panics rejected
there; an ABSENT program by non-denotation) — but it does NOT emit the main/observed
output, so the future "real Go realizes GoSem" adequacy assumption is **not** yet part of
the trust base.

---

## 3. The trusted plugin and the deletion law

**There is no transition (CLAUDE.md's law governs).** `plugin/go.ml` is **trusted and
therefore not part of the intended proof architecture.** It never defines a correctness
claim, and nothing is preserved for a migration's sake — a weak path is deleted the moment
certified architecture supersedes it.

- No new architecture, safety claim, or demo touches `plugin/go.ml`; a patch that makes
  its lowering nicer is moving the wrong direction.
- No parallel universes beside the spine — no second authority for syntax, semantics,
  emission, safety, termination, or divergence.
- A feature is **covered** only when GoAst represents it, GoPrint emits it, GoCompile admits
  it appropriately, GoEmit emits it through the certificate, and GoSem/GoSemSafe models it
  exactly or rejects honestly — one layer alone is not coverage. Each certified feature
  names the trusted-path demos it supersedes and DELETES them in the same patch; a
  `go.ml` branch whose only load is superseded coverage is a deletion candidate. Live
  ledger: `DELETION.md`.

Honest current status: the spine compiles zero-axiom and `main.v` builds a
`GoAst.Program` emitted ONLY through `EmittableProgram`; but the repo's `main.go` is STILL
the legacy plugin path. The extracted `printer.ml` is wired into that path for only a
small expression class (single-sourced in PROGRESS.md); even there the printer proofs
cover AST→string serialization, NOT the trusted MiniML→`GExpr` CONSTRUCTION in `go.ml` —
the live emission is not "verified Go."

---

## 3a. GoSem physical layout

`GoSemCore.v` — the pure fold/float/constant layer (box/render, const ops,
`floats_checked`/`fsf_checked`, the dyadic↔SF* arc); NO evaluator. `GoSemDenote.v` — the
denotation layer (the evaluator with its `Local` core, the runtime/typed tiers and seals,
`denote_expr`/`denote_program`, `gosem_sound`). `GoSem.v` — the composition point:
re-exports both; holds fixture groups / demos / frontier and ALL gated public surfaces.

Rules: the evaluator's `Local` core stays sealed with every proof that computes through it
(public access would bypass the float boundary — negtest-sealed); grounding examples live
adjacent to the theorems they pin, in the earliest file that can express them; no file
reaches into another's internals; `denote_expr`/`denote_program` stay wherever keeps
`gosem_sound` in ONE file; `GoSemDenote.v` grows ONLY for approved semantic slices. Moves
are pure, golden byte-identical.

---

## 5. Phases

```text
Phase 0  Freeze the direction.                                                       DONE
Phase 1  Extract the printer/parser seed into GoAst/GoPrint.                         DONE
Phase 2  Create GoCompile (GoCompile) + GoEmit (EmittableProgram; no raw emit).  DONE
Phase 3  main.v builds GoAst.Program and emits ONLY through the certificate.         DONE
Phase 4  Grow the AST/printer form-by-form (represented, printed,                    ONGOING
         round-tripped/injective, gate-honest).
Phase 5  Grow safety via GoSem: BRIDGE unified.v/concurrency.v/cmd.v in, widen       IN PROGRESS
         toward BehaviorSafe → SafeProgram → emit_safe, wire the certified path to
         main. Slice 1 + converse DONE; the narrow panic-free cert (§2a) DONE.
         NEXT = eval non-literals, then full BehaviorSafe (nil deref/OOB/race).
```

Every patch should move a concept into the correct module, delete an old wrong path, make
a bad path unreachable, strengthen the proof-gated emission boundary, or shrink trusted
legacy code. **No parallel universes. No "future foundation" unless it replaces or
deletes something.**

---

## 6. Rules for Claude Code

**Rule 1 — No raw syntax in core AST.** Forbidden in core modules: `RawExpr`, `RawStmt`,
`RawDecl`, `RawType`, `OpaqueExpr`, `TrustedExpr`, `SRaw`, `raw_ok`, raw source strings.
Semantic strings only when the printer escapes them.

**Rule 2 — No string-rescue path.** Forbidden: `old printer -> string ->
validator/parser -> new printer`. The generator builds AST directly; the lexer/parser
exists for proof and testing, never to rescue old output.

**Rule 3 — No official raw emitter.** The official emitter requires `EmittableProgram`
(later `SafeProgram`).

**Rule 4 — No decorative safety/support proofs.** The emitted output goes THROUGH the
certificate, not `print_program p` beside a lemma.

**Rule 5 — No documentation as correctness.** Docs may *describe* a limitation; they may
not make it acceptable in the core. If a bad case exists, make it impossible, reject it,
or move it outside the core. **Naming is a correctness claim:** do not name a syntactic
gate `SafeProgram`.

**Rule 6 — Deletion is progress.** Every structural patch should preferably delete
something; report byte/grep deltas. A patch that only adds scaffolding is suspect.

**Rule 7 — Review archaeology belongs in `LESSONS.md`.** Active comments explain
invariants, not the social history of a bug.

---

## 7. Review checklist for every patch

1. Which module did this move toward the target architecture?
2. What old path became unreachable / what code was deleted?
3. Did this create a new parallel syntax/semantic universe?
4. Does any theorem prove something not used by the live path?
5. Does any official emitter bypass the certificate?
6. Did docs (or names) overclaim?
7. Did the patch reduce trusted code, preserve it, or increase it?

---

## 8. Acceptance gates

**[live]** = enforced every build; **[review]** = human/Codex discipline.

```text
[live]     No axioms in any gated Print Assumptions surface (manifest + printer + emit flows — see PROGRESS.md "Current gates").
[live]     Generated printer artifact (plugin/printer.ml) in sync.
[live]     No raw-syntax constructor NAMES in source (plugin/smart-ctor-gate.sh).
[live]     Official emit only via GoEmit's certificate API; no direct print_program call outside GoEmit.
[live]     Print Assumptions for every public safety theorem (list single-sourced in PROGRESS.md "Current gates").
[review]   The Phase-1 gate is named GoCompile, NOT SafeProgram, until GoSem-backed BehaviorSafe exists.
[review]   Docs and NAMES do not claim more than the live path proves.
```

The smart-ctor gate is a **name-regression tripwire**, NOT the guarantee. The real
guarantees are structural: `GoAst`'s constructors take only validated/semantic payloads
and `GoEmit` exports only certificate-requiring emitters — enforced by review of the
definitions, not by grep.

---

## 9. What not to do

No second universe beside the spine; no old plugin printer wired into `GoEmit`; no parser
used to rescue old-printer strings; no `GoCompile`/`BehaviorSafe` axiom; no
convenient unsafe `emit`; no "safe Go" claim for a program that skipped the behavioral
certificate.

---

## Standing bottom line

Do not verify around a bad abstraction. Do not document — or *name* — a shortcut into
respectability. Do not let a proof sit beside the path; put it on the path. Build the AST
honestly. Print it boringly. Certify it explicitly. Emit only certified programs.
