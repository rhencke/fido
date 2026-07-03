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

- checker scope state: `ScopeS` — WELL-FORMEDNESS sealed by sig (names valid/unrecognized/
  non-blank/distinct; entry categories `BoundCat` = `bind_category`'s image); `scope_declare` is
  the declaration path (binds from the RHS `PTy` internally); construction PROVENANCE is the
  scoped fold's property (`body_okS` declares only via `scope_declare`; the program gate
  `supported_program` runs it from `scope_empty` and adds `scope_all_used`) —
  category AND a USED flag, ONE state through ONE
  fold (rule 4's "declared and not used" is decided INSIDE the same fold that decides everything
  else — never a post-hoc validator bolted on after supportedness).  `x := e` binds `x` through the
  single named authority

  `bind_category : PTy -> option BoundCat` (the sealed image)
  - `PtIntConst z ↦ if int_const_repr z GTInt then Some (PtRunInt GTInt) else None` — a short decl
    is a DEFAULTING value context, so it PRESERVES the existing default-`int` representability
    boundary (`svalue` / `printable_arg_ok`: the conservative 32-bit
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
state-threading — `type_expr : ScopeS -> GExpr -> option (PTy * ScopeS)` — resolving identifiers
AND marking their used flags in the SAME traversal (a read-only checker cannot mark uses; it
would force the second pass rule 4 forbids).  `ptype`'s `EId` case is ALREADY the scope hook
(landed: the `special_ident` match, `nil`-or-reject); closed `ptype` is then to be recovered as
the empty-scope PROJECTION — the PROVEN bridge `GoSafe.type_expr_nil_ptype`
(`option_map fst (type_expr scope_empty e) = ptype e`): at `scope_empty` no LOCAL binding
resolves and no used flag can flip, while the `special_ident` fall-through branch mirrors closed
`ptype` exactly ([nil] included) — so the traversals agree, and any drift between the two spellings fails the
build at this theorem.  Every existing `ptype` theorem survives untouched.  The same shape lands
for the evaluator's ident resolution in `GoSemDenote` (LANDED at rung 5b: the `EId` arms).

## Go-faithfulness rules (each lands with a fixture; narrowings NAMED as narrowings)

1. use-before-declare / undeclared identifier → reject (today's `EId` behavior, kept).
2. redeclaration in the flat block (`x := 1; x := 2`) → reject (Go: "no new variables on left side
   of :=").
3. `x := nil` → reject (Go: "use of untyped nil").
4. DECLARED-BUT-UNUSED → reject.  Go's "declared and not used" is a COMPILE ERROR; without this rule
   the gate could certify Go that does not build (fail-open — forbidden).  STRUCTURAL: the used flag
   lives IN the checker's `ScopeS` state (see above) and uses are marked RECURSIVELY through subexpressions by the same
   traversal that types them; the no-unused rejection is the fold's final step, not a second pass.
   `_ = x` counts as a use (Go's own idiom for it).
5. declaring a CHECKER-RECOGNIZED name → reject.  The single source is LANDED (rung 2): **GoAst's
   `SpecialName` inductive (`SnType t` / `SnNil` / `SnLen` / `SnCap` / `SnPrintln` / `SnPrint` /
   `SnPanic`) + the ONE table `special_ident : string -> option SpecialName`**, living in the layer
   both consumers import (the import order — GoTypes sees only GoAst; GoSafe sees GoTypes — is why
   a gate in either file would have duplicated the other's list).  `classify` is its `SnType`
   projection (`go_keyword`, Go's RESERVED words, is a separate concern and stays separate — a
   recognized name need not be a keyword).  LANDED consumers: GoTypes' recognizers (ptype's EId
   scope hook and the one-arg call head), GoSafe's `stmt_call_ok`/`expr_stmt_ok`, and — landed
   with rung 3's sealed scope boundary — the declaration gate `decl_ident_ok` (uniform rejection
   of every recognized name, plus the blank identifier), enforced INSIDE `scope_declare` (the one
   insertion path) rather than by caller discipline.  The rung-4 fold declares exclusively
   through `scope_declare`.  The SEMANTIC consumers (recognizers that choose behavior PER NAME) match
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
3. **LANDED (in GoSafe — the seal needs lemmas; GoTypes stays Definitions-only)**: the
   state-threading `type_expr : ScopeS -> GExpr -> option (PTy * ScopeS)`, the sealed
   `ScopeS`/`BoundCat`/`scope_declare`/`scope_markS` layer, and the proven bridge
   `type_expr_nil_ptype` — the exact shape and claim boundary live in the crux section above
   (single authority; not re-stated here).
4. **GoSafe — LANDED**: scope-threaded supportedness — `supported_program` runs ONE fold
   (`stmt_okS`/`body_okS`) over the sealed `ScopeS` (declarations exclusively through
   `scope_declare`; uses marked BY `type_expr` itself; final no-unused rejection `scope_all_used`
   in the same fold — this fold IS the provenance boundary the crux notes); rules 1–5b landed with
   NAMED fixtures, every ledger placement ground-truthed via `make go-verify` (which also moved
   the misplaced `println(2^40)` / `_ = 2^40` rows to valid-unsupported — 64-bit gc compiles
   them).  `stmt_ok` stays as the CLOSED scope-free fragment (GoSemDenote's slice-1 gate); the
   decl-free bridge `body_okS_nil_declfree` (+ `supported_program_of_stmt_ok`) pins agreement and
   repairs `gosem_sound`.  The rung-4/5 seam is pinned: `shortdecl_supported_undenoted`
   (supported ∧ not denotable — flips at rung 5c).
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
   semantics in this rung).
   ARCHITECTURE (worked 2026-07-03; the survey facts that force it): the engines dispatch on
   CLOSED `ptype` INTERNALLY (`reval_int`'s guard + `rexit_with`'s three guards), and `ptype` is
   `None` on any expression containing a bound `EId` — so threading `ρ` alone cannot work, and
   `GExpr`-substitution stays WRONG at the evaluator exactly as at the checker (substituting
   `EInt 0` into `1/x` makes `ptype` REJECT: absence instead of the true `CPan rt_div_zero`).
   Chosen shape — the file's own `_with` idiom, NO twin, NO bridge obligation, definitional
   closed recovery: re-parameterize `reval_int` as `reval_int_with (tc : GExpr -> option PTy)
   (leaf : string -> option GoAny)` (and give `rexit_with` the same two); the CLOSED functions
   keep their names as instantiations (`reval_int := reval_int_with ptype (fun _ => None)` —
   `ptype` reduction preserved after one unfold; the ~64 unfold/cbn proof sites repair
   mechanically; equation lemmas restated once).  `eval_value`/`floats_checked` stay FULLY
   CLOSED (constants fold; locals never fold).  The env instance: `tc := fun e => option_map fst
   (type_expr Gs e)`, `leaf := env_get ρ`; `EId` is a new SHAPE ARM under each guard (the guard
   resolves the binding's category via `tc`, the arm reads `leaf`).  Needs: `tc` is
   MARK-INSENSITIVE (`scope_markS` flips only flags — categories stable).  `ρ : list
   (string * GoAny)` suffices: value tags are width-precise (`box_int`: `GTInt ↦ TInt64`,
   `GTInt64 ↦ TI64`, per-width tags), so `tag_of_cat` is injective on the bindable categories
   and `Γ ≈ ρ` states per-binding tag agreement.  Statement layer: `denote_stmt`/`denote_body`
   take `(Gs : ScopeS, ρ)`; the `GsShortDecl` arm has the three outcomes (above), extending BOTH
   `Gs` (via `scope_declare`, mirroring `stmt_okS`) and `ρ` (on `CRet` only); a TERMINATOR's
   dead-tail check becomes the SUFFIX FOLD (`body_okS Gs rest` + `scope_all_used` on its result
   — marks accumulate in `Gs`, so the suffix fold ends at `supported_program`'s own final scope,
   keeping denote ⊆ `supported_program` exactly); `denote_program` runs from
   `(scope_empty, nil)`.  Sub-ladder, each an independently green commit: **5a — LANDED** the
   `_with`/`_tc` re-parameterization (behavior-identical; the family is SEALED `Local`, negtest-
   pinned per face); **5b — LANDED** the `EId` shape arms + `tcat`/mark-insensitivity + the env
   instance `denote_expr_env` with the closed coincidence `denote_expr_env_nil` and the env pins
   (`env_eid_pins`/`env_float_pins`, surfaced); **5c** the env statement layer +
   `Γ ≈ ρ` + the re-proofs + the SEAM-PIN FLIPS (`shortdecl_supported_undenoted` and
   `shortdecl_deadtail_supported_undenoted` swap in the SAME commit they flip) + the
   panicking-RHS and runtime-binding fixtures; **5d** the frontier suite below.  The LOCAL-FRONTIER suite is a MECHANICAL MAP over the EXISTING
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
