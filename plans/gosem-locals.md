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

- checker env `Γ : Ident ⇀ PTy` — `x := e` binds `x` to the DEFAULTED, VALUE-DROPPED category of
  `ptype e`: `PtIntConst _ → PtRunInt GTInt` (untyped-const default), `PtTIntConst t _ → PtRunInt t`,
  `PtFloatConst t _ → PtRunFloat t`, `PtBool`/`PtStr`/`PtAgg`/`PtMap` bind as themselves,
  `PtNil` REJECTED (`x := nil` is Go's "use of untyped nil" compile error).
- evaluator env `ρ : Ident ⇀ GoAny` — the world is closed, so the exact value IS known and carried;
  `EId x` resolves to `ρ x`; ops on the resolved value take the ALREADY-LANDED runtime tiers
  (GTInt R1–R8 / typed-runtime T1–T5).
- the agreement invariant `Γ ≈ ρ` (each binding's value tag matches its checker category) is the
  lemma spine along which `gosem_sound` re-proves.

`ptype` becomes the Γ-parameterized fixpoint with `ptype := ptype_env []` — its `EId` case is
ALREADY the scope hook ("SCOPE is realized in the [EId] case"; today: `nil`-or-reject).  ONE
authority generalized then specialized at the empty env; no parallel checker.  Same shape for the
evaluator's ident resolution in `GoSemDenote`.

## Go-faithfulness rules (each lands with a fixture; narrowings NAMED as narrowings)

1. use-before-declare / undeclared identifier → reject (today's `EId` behavior, kept).
2. redeclaration in the flat block (`x := 1; x := 2`) → reject (Go: "no new variables on left side
   of :=").
3. `x := nil` → reject (Go: "use of untyped nil").
4. DECLARED-BUT-UNUSED → reject.  Go's "declared and not used" is a COMPILE ERROR; without this rule
   the gate could certify Go that does not build (fail-open — forbidden).  `_ = x` counts as a use
   (Go's own idiom for it).
5. declaring a recognized builtin callee name (`println`/`print`/`panic`) → conservative
   supported-subset REJECTION (Go PERMITS the shadowing; we narrow — never claim Go rejects it).
6. NO mutation in this arc (`x = e` deferred to a later arc).  Defer-argument capture (Go evaluates
   deferred args AT THE DEFER STATEMENT, not at run time) is unobservable without mutation; when
   assignment lands, capture-at-defer-site becomes an OBLIGATION with a distinguishing fixture.
7. scope = the flat `main` block with sequential visibility (GoStmt has no nesting today — no
   if/for blocks — so flat-block scoping is exact, not an approximation).

## The ladder (each rung an independently green `make check` commit)

0. **This plan** + the PROGRESS `NEXT` pointer.
1. **GoAst + GoPrint**: `GsShortDecl : Ident -> GExpr -> GoStmt`, printed `x := e` (gofmt-clean);
   `print_stmt_inj`/`print_program_inj` extended (discriminator care: an expr-statement call
   `x(1)` also starts with an identifier — the split is at `" := "` vs `"("` after the ident).
   Every GoStmt match repo-wide gains the arm WILDCARD-FREE: `stmt_ok` arm `false`, `denote_stmt`
   arm `None` (representation before admission — fail-closed).  Zero golden risk: nothing
   constructs it yet.
2. **GoTypes**: `ptype_env`/`svalue` Γ-parameterization + the binding-category defaulting table
   above (with the `PtNil` rejection); existing theorems lift at `[]`.
3. **GoSafe**: scope-threaded supportedness — `supported_program`'s `forallb` becomes the Γ-fold;
   rules 1–5 land with fixtures in the three ledgers (`bad_programs` for the Go compile errors,
   `valid_unsupported_programs` for the rule-5 narrowing, `good_programs` for accepted locals).
4. **GoSemDenote**: the evaluator takes `ρ`; `denote_stmt`/`denote_body` thread `Γ ≈ ρ`;
   `denote_stmt_sound`/`gosem_sound`/`denote_program_dec` re-proved over the invariant.  SCOPE:
   locals widen NAME reach, not operation reach — a resolved variable feeds the EXISTING runtime
   value paths only; any op those paths don't cover stays absent (fail-closed, no new value
   semantics in this rung).
5. **Gate reach (GoSemSafe + ledgers)**: flagship demos — a local-using panic-free program
   ACCEPTED + EMITTED (and go-built, proving rule 4 keeps emission valid); `x := 0; _ = 1 / x`
   SUPPORTED + DENOTABLE + REJECTED by `cmd_no_panic` on its `rt_div_zero` `CPan` (extending
   `panic_free_gate_div`'s denoted-panic class to name-carried values); a typed-width wrap demo
   if the T-tier ops cover it.  `SPEC_CONFORMANCE.md` rows for rules 1–5.

## Standing rules (inherited from the bridge arc's landing checklist, verbatim)

Ground every new projection in the existing authority and USE it the same tick; public statements
in PUBLIC vocabulary; a real result is `Theorem` + `Print Assumptions` + surface registration.  At
every landing: delete newly-subsumed material (hypothesis-strength test, ALL siblings), sweep
status/framing prose repo-wide, boundary-word grep as the LAST pre-commit step.  Work the
invariant (`Γ ≈ ρ`) on paper before coding the rung-4 threading.
