# GoSem locals — eval non-literals (`x := e`)

GOAL: ARCHITECTURE Phase 5's stated next step ("eval non-literals"): `GoStmt` grows short variable
declaration, the checker and the evaluator grow ONE environment, and the panic-free gate's reach
extends to variable-using programs judged at their TRUE runtime behavior.  (Runtime panics are
already reachable without names — `panic_free_gate_div` pins `_ = 1/len([]int{})` — so what this
arc adds is the NAME-carried class: values flowing through declared variables, a far larger
program family, judged by the same gate.)  This arc is BehaviorSafe GROWTH by fragment-widening; it does NOT define the
`BehaviorSafe` gate (reserved until hazards beyond panics — pointers/channels — are expressible;
naming is a correctness claim).

## The design crux — ENVIRONMENT, never substitution

A declared variable is RUNTIME-categorized at compile time: `x := 5` has type `int`, NOT an untyped
constant — Go's checker no longer folds it, so `x := 0; _ = 1 / x` COMPILES and panics at run time
while `_ = 1 / 0` is a COMPILE error.  A substitution pass (replace `x` by its literal at use sites)
is therefore semantically WRONG: it re-constantizes the use sites and flips runtime panics into
compile-time rejections.  The correct shape:

- checker scope state `Γ : Ident ⇀ (PTy × bool)` — category AND a USED flag, ONE state through ONE
  fold (rule 4's "declared and not used" is decided INSIDE the same fold that decides everything
  else — never a post-hoc validator bolted on after supportedness).  `x := e` binds `x` through the
  single named authority

  `bind_category : PTy -> option PTy`
  - `PtIntConst z ↦ if int_const_repr z GTInt then Some (PtRunInt GTInt) else None` — a short decl
    is a DEFAULTING value context, so it PRESERVES the existing default-`int` representability
    boundary (`svalue` GoTypes.v:700 / `printable_arg_ok` GoSafe.v:54: the conservative 32-bit
    range, sound on every Go target); dropping the value WITHOUT this check would certify
    `x := 9223372036854775808` (invalid Go: "constant overflows int").
  - `PtTIntConst t _ ↦ Some (PtRunInt t)`, `PtFloatConst t _ ↦ Some (PtRunFloat t)` — typed
    constants were already range-checked where their category was BUILT (conversion).
  - `PtRunInt t ↦ Some (PtRunInt t)`, `PtRunFloat t ↦ Some (PtRunFloat t)` — RUNTIME categories
    bind AS THEMSELVES.  This is the arc's core, not an edge: `x := len([]int{1})`, `y := x`,
    `x := int64(len([]int{1}))` all bind runtime values.
  - `PtBool`/`PtStr ↦ Some` (themselves — scalar categories; some members are value-less and are
    handled by the frontier discipline below, e.g. `string(200)` / a comparison over an
    eval-partial operand).
  - `PtAgg`/`PtMap ↦ None` — NAMED NARROWING: the evaluator has NO aggregate/map VALUES (the eval
    core yields scalar constants, "everything else is None" — `GoSemDenote.v:24`; the runtime
    tiers yield scalars), so admitting these categories would create checker-supported locals
    that can NEVER value — a structural hole, not a frontier.  Rejected by a written arm; Go
    permits slice/map locals, so this is a conformance-ledger narrowing, revisited only when
    aggregate values land in the evaluator.
  - `PtNil ↦ None` (`x := nil` is Go's "use of untyped nil" compile error).
  The match is over EVERY `PTy` constructor explicitly — a category is rejected by a written
  `None` arm, never by omission (wildcard-free, same discipline as every `Cmd` match).
- evaluator env `ρ : Ident ⇀ GoAny` — the short-decl denotation arm has EXACTLY the three
  `denote_expr` outcomes (`GoSemDenote.v:1762`: an expression denotes to `CRet v` or `CPan p`, or
  is absent), each with its own structural consequence:
  - `None` → the WHOLE program is ABSENT (option-threading; faithful-or-absent, no new machinery);
  - `Some (CPan p, _)` → the statement denotes the PANIC command and `ρ` does NOT extend — the RHS
    denoted, to a panic, not to a value (`x := 1 / len([]int{})` is the class: supported, denotes
    `CPan rt_div_zero`, rejected by `cmd_no_panic` ON the denotation);
  - `Some (CRet v, _)` → the ONLY case that extends `ρ` (with `v`), continuing the body.
  So CHECKER ADMISSION ≠ DENOTABILITY: `bind_category` is a SUPPORTEDNESS authority (conservative,
  syntactic; the two layers stay independent so evaluator growth never forces checker edits);
  which admitted bindings actually VALUE is decided by the evaluator, exactly as for every other
  supported expression today.  `EId x` resolves to `ρ x`; ops on the resolved value take the
  ALREADY-LANDED runtime tiers (GTInt R1–R8 / typed-runtime T1–T5).
- the agreement invariant `Γ ≈ ρ` (each binding's value tag matches its checker CATEGORY component;
  the used flag is supportedness-only, invisible to `ρ`) is the lemma spine along which
  `gosem_sound` re-proves — quantified over DENOTED runs (where `ρ` exists at all), never claiming
  a value for a checker-admitted binding the evaluator left absent.

RUNG 3 (LANDED): the expression checker's scope-aware twin is
state-threading — `type_expr : Γ -> GExpr -> option (PTy * Γ)` — resolving identifiers AND marking
their used flags in the SAME traversal (a read-only `ptype_env Γ e : option PTy` cannot mark uses;
it would force the second pass rule 4 forbids).  `ptype`'s `EId` case is ALREADY the scope hook
(landed: the `special_ident` match, `nil`-or-reject); closed `ptype` is then to be recovered as
the empty-env PROJECTION — the PROVEN bridge `GoSafe.type_expr_nil_ptype`
(`option_map fst (type_expr nil e) = ptype e`): at the empty scope no identifier resolves and no
flag can flip, so the traversals agree exactly, and any drift between the two spellings fails the
build at this theorem.  Every existing `ptype` theorem survives untouched.  The same shape lands
for the evaluator's ident resolution in `GoSemDenote` (rung 5).

## Go-faithfulness rules (each lands with a fixture; narrowings NAMED as narrowings)

1. use-before-declare / undeclared identifier → reject (today's `EId` behavior, kept).
2. redeclaration in the flat block (`x := 1; x := 2`) → reject (Go: "no new variables on left side
   of :=").
3. `x := nil` → reject (Go: "use of untyped nil").
4. DECLARED-BUT-UNUSED → reject.  Go's "declared and not used" is a COMPILE ERROR; without this rule
   the gate could certify Go that does not build (fail-open — forbidden).  STRUCTURAL: the used flag
   lives IN `Γ` (see above) and uses are marked RECURSIVELY through subexpressions by the same
   traversal that types them; the no-unused rejection is the fold's final step, not a second pass.
   `_ = x` counts as a use (Go's own idiom for it).
5. declaring a CHECKER-RECOGNIZED name → reject.  The single source is LANDED (rung 2): **GoAst's
   `SpecialName` inductive (`SnType t` / `SnNil` / `SnLen` / `SnCap` / `SnPrintln` / `SnPrint` /
   `SnPanic`) + the ONE table `special_ident : string -> option SpecialName`**, living in the layer
   both consumers import (the import order — GoTypes sees only GoAst; GoSafe sees GoTypes — is why
   a gate in either file would have duplicated the other's list).  `classify` is its `SnType`
   projection (`go_keyword`, Go's RESERVED words, is a separate concern and stays separate — a
   recognized name need not be a keyword).  LANDED consumers: GoTypes' recognizers (ptype's EId
   scope hook and the one-arg call head) and GoSafe's `stmt_call_ok`/`expr_stmt_ok`.  FUTURE
   consumer (rung 4, with the scope fold): the declaration gate
   `decl_ident_ok s := match special_ident s with None => true | Some _ => false end` — it does
   not exist yet and nothing routes through it today.  The SEMANTIC consumers (recognizers that choose behavior PER NAME) match
   wildcard-free exhaustively, so a new `SpecialName` constructor forces each of them mechanically;
   the declaration gate alone uses `Some _ => false` DELIBERATELY — it rejects every recognized
   name uniformly, a total rejection with no per-name decision that could drift by omission.  Where Go PERMITS the shadowing
   (e.g. `len := 1`, `int := 1` are legal Go) this is a conservative NARROWING, named as such;
   each fixture's LEDGER placement (bad_programs vs valid_unsupported_programs — their contracts
   differ) is ground-truthed against the real toolchain via `make go-verify` at landing, never
   guessed.
5b. `_` on the LHS (`_ := 1`) → reject: Go's "no new variables on left side of :=" (a `:=` must
   declare at least one NEW variable; `_` never counts) — `go_ident "_" = true`, so this needs a
   mechanical rule, not hope.
6. NO mutation in this arc (`x = e` deferred to a later arc).  Defer-argument capture (Go evaluates
   deferred args AT THE DEFER STATEMENT, not at run time) is unobservable without mutation; when
   assignment lands, capture-at-defer-site becomes an OBLIGATION with a distinguishing fixture.
7. scope = the flat `main` block with sequential visibility (GoStmt has no nesting today — no
   if/for blocks — so flat-block scoping is exact, not an approximation).

## The ladder (each rung an independently green `make check` commit)

0. **This plan** + the PROGRESS `NEXT` pointer.
1. **GoAst + GoPrint — LANDED**: `GsShortDecl : Ident -> GExpr -> GoStmt`, printed `x := e` (gofmt-clean);
   `print_stmt_inj`/`print_program_inj` extended (discriminator care: an expr-statement call
   `x(1)` also starts with an identifier — the split is at `" := "` vs `"("` after the ident).
   Every GoStmt match repo-wide gains the arm WILDCARD-FREE: `stmt_ok` arm `false`, `denote_stmt`
   arm `None` (representation before admission — fail-closed).  Zero golden risk: nothing
   constructs it yet.
2. **`SpecialName` single-source refactor — LANDED (behavior-identical)**: GoAst grows the `SpecialName` inductive + the `special_ident` table
   (rule 5); `classify` becomes the `SnType` projection; GoTypes' `nil`/`len`/`cap`/conversion-head
   recognizers and GoSafe's `stmt_call_ok` AND `expr_stmt_ok` rewire onto WILDCARD-FREE matches over it.  Every
   existing theorem re-checked; the checker's observable behavior (and the golden) is UNCHANGED —
   this rung only makes the name set single-sourced so the later gate cannot drift.
3. **GoTypes — LANDED**: the state-threading `type_expr : Scope -> GExpr -> option (PTy * Scope)`
   (resolve + mark in one traversal; ptype untouched — the two spellings are tied by the PROVEN
   bridge `GoSafe.type_expr_nil_ptype`, the anti-drift gate, placed in GoSafe because GoTypes is
   Definitions-only by charter) + `Scope`/`scope_get`/`scope_mark` + the `bind_category` authority
   (the `int_const_repr` defaulting premise, runtime categories binding as themselves, and the
   WRITTEN `None` arms: `PtNil`, `PtAgg`, `PtMap`).
4. **GoSafe**: scope-threaded supportedness — `supported_program`'s `forallb` becomes ONE fold over
   `Γ : Ident ⇀ (PTy × bool)` (bind via `bind_category`, declare-gate via `decl_ident_ok` from the
   `special_ident` table, uses marked BY `type_expr` itself, final no-unused rejection in the same
   fold); rules 1–5b land with NAMED fixtures.
   Good: `x := 1; _ = x; return`; the RUNTIME bindings `x := len([]int{1}); _ = x`,
   `x := 1; y := x; _ = y`, `x := int64(len([]int{1})); _ = x`; the NESTED uses `x := 1; _ = x + 1`
   and `x := 1; println(x)` (uses marked inside subexpressions, not just top-level).
   Bad: `x := 9223372036854775808; _ = x` (overflows every Go int); `x := 1; return` (declared and
   not used — rejected by the SAME fold, no second pass); `x := 1; x := 2; _ = x` (no new
   variables); `_ := 1`; `x := nil; _ = x` (untyped nil).
   Valid-unsupported: a ~40-bit-const decl (fits 64-bit gc, outside the conservative range);
   `len := 1` / `int := 1` / `nil := 1` (each with a `_ = <name>` use; rejected via
   `decl_ident_ok`; ledger per `make go-verify` ground truth); the AGGREGATE/MAP locals
   `x := []int{1}; _ = len(x)` and `m := map[int]int{1: 2}; _ = len(m)` — valid Go (`make
   go-verify` confirms), rejected by `bind_category`'s `PtAgg`/`PtMap` arms (the uses isolate
   that rejection from unused/undeclared noise), with `SPEC_CONFORMANCE.md` rows; their INVALID
   companions (e.g. an invalid-map-key literal on a decl RHS) stay in `bad_programs`.
   Each rejection fixture ISOLATES its rule — append the `_ = x` use everywhere the unused rule is
   not the one under test, so exactly ONE rule rejects.
5. **GoSemDenote**: the evaluator takes `ρ`; `denote_stmt`/`denote_body` thread `Γ ≈ ρ`;
   `denote_stmt_sound`/`gosem_sound`/`denote_program_dec` re-proved over the invariant.  SCOPE:
   locals widen NAME reach, not operation reach — a resolved variable feeds the EXISTING runtime
   value paths only; any op those paths don't cover stays absent (fail-closed, no new value
   semantics in this rung).  The LOCAL-FRONTIER suite is a MECHANICAL MAP over the EXISTING
   `undenoted_frontier` member list (`GoSem.v` — the REPRESENTATIVE witness list of the
   supported-but-undenoted gap; its own header says NON-EXHAUSTIVE and no coverage theorem bounds
   the gap — that warning STAYS): for EVERY member `m` in value position, pin `x := m; _ = x` as
   supported ∧ NOT denotable ∧ gate-`None` (the `panic_free_gate_absent` mechanism) — a `forallb`
   over the list itself, so the DECL SUITE cannot drift from the LIST (one member list for
   fixture generation; NOT a claim that the list covers the gap).  CLAIM BOUNDARY: every fixture
   quantifies over the LIST, never over "the gap"; the suite's completeness is exactly the
   list's, which remains representative.  WITNESS-WIDENING at this rung: for every scalar
   category `bind_category` admits, the list SHOULD contain a value-less member if one is
   expressible — it has `PtStr` (`runeconv_mb`) and the runtime-int/float holes today; ADD a
   value-less `PtBool` witness (e.g. a comparison over an eval-partial operand) TO THE LIST in
   this rung — extending the representative witnesses, never a side list.  DISTINCT from non-denotation: the PANICKING-RHS fixture `x := 1 / len([]int{}); _ = x`
   — supported ∧ DENOTES to `CPan rt_div_zero` ∧ rejected by `cmd_no_panic` on the denotation
   (`ρ` not extended; the three-outcome arm above is what these fixtures pin).  When an arc lands
   that makes a member denote, its pin BREAKS — swap in the next frontier member in the same
   commit (the standing frontier-pin discipline).
6. **Gate reach (GoSemSafe + ledgers)**: flagship demos — a local-using panic-free program
   ACCEPTED + EMITTED (and go-built, proving rule 4 keeps emission valid); `x := 0; _ = 1 / x`
   SUPPORTED + DENOTABLE + REJECTED by `cmd_no_panic` on its `rt_div_zero` `CPan` (extending
   `panic_free_gate_div`'s denoted-panic class to name-carried values); a typed-width wrap demo
   if the T-tier ops cover it.  `SPEC_CONFORMANCE.md` rows for rules 1–5b.

## Standing rules (inherited from the bridge arc's landing checklist, verbatim)

Ground every new projection in the existing authority and USE it the same tick; public statements
in PUBLIC vocabulary; a real result is `Theorem` + `Print Assumptions` + surface registration.  At
every landing: delete newly-subsumed material (hypothesis-strength test, ALL siblings), sweep
status/framing prose repo-wide, boundary-word grep as the LAST pre-commit step.  Work the
invariant (`Γ ≈ ρ`) on paper before coding the rung-4 threading.
