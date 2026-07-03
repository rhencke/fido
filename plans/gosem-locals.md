# GoSem locals — eval non-literals (`x := e`)

GOAL: `GoStmt` grows short variable declaration, the checker and the evaluator grow ONE
environment, and the panic-free gate's reach extends to variable-using programs judged at their
TRUE runtime behavior (the NAME-carried panic class).  BehaviorSafe GROWTH by fragment-widening;
this arc does NOT define the `BehaviorSafe` gate (naming is a correctness claim).

## Current state

Rungs 1–4 and 5a/5b are DONE (detail in the code and git history; the theorems are the
authority):

- Syntax + printing: `GsShortDecl`, `print_stmt_inj`/`print_program_inj` extended.
- ONE recognized-name table: `special_ident` (GoAst) + its name inverse `special_ident_name`;
  `classify` is its `SnType` projection.
- Scope-aware checking: sealed `ScopeS`/`BoundCat`/`scope_declare` + the state-threading
  `type_expr`, bridged to closed `ptype` by `type_expr_nil_ptype`; category projection `tcat`
  with `tcat_mark_insensitive` (categories never see used flags).
- The program gate: `supported_program` = package-main + the `body_okS` scope fold from
  `scope_empty` + `scope_all_used`.  `stmt_ok` stays the CLOSED scope-free fragment GoSem
  slice 1 is gated on; decl-free agreement is `body_okS_nil_declfree`.  Placements
  ground-truthed via `make go-verify`.
- Expression-level env evaluation: the sealed `_tc` engine family (Local, negtest-pinned per
  face) with `EId` arms; the env instance `denote_expr_env (G)(ρ)` over `tcat G`/`env_get ρ`;
  the closed coincidence `denote_expr_env_nil` (funext-free, via `reval_engines_ext`); env pins
  `env_eid_pins`/`env_float_pins`/`env_float_conv_class` in `gosem_core_surface`.

STATEMENT-level denotation of `x := e` is ABSENT: `denote_stmt (GsShortDecl _ _) = None`,
so decl programs are supported-but-undenoted (`shortdecl_supported_undenoted`,
`shortdecl_deadtail_supported_undenoted`).

## Next target — 5c: the env statement layer

`denote_stmt`/`denote_body` take `(G : ScopeS, ρ : Env)`; `denote_program` runs from
`(scope_empty, nil)`.  Invariants (argued once; do not re-litigate):

- ENVIRONMENT, never substitution: a declared variable is RUNTIME-categorized (Go compiles
  `x := 0; _ = 1/x` and panics at run time; `1/0` is a compile error) — substituting the
  literal re-constantizes use sites, at the checker AND at the evaluator.
- The `GsShortDecl` arm has EXACTLY the three `denote_expr_env` outcomes:
  - `None` → the whole program is ABSENT (option-threading, faithful-or-absent);
  - `Some (CPan p, _)` → the statement denotes the PANIC command; ρ does NOT extend;
  - `Some (CRet v, _)` → the ONLY case that extends ρ, continuing the body.
- CHECKER ADMISSION ≠ DENOTABILITY: `bind_category` is a supportedness authority; which
  admitted bindings VALUE is the evaluator's decision.
- The agreement invariant `Γ ≈ ρ` (binding value tags match checker categories; used flags are
  supportedness-only) is the lemma spine for the env soundness theorem
  (env-denotation ⊆ `supported_program`), quantified over DENOTED runs.
- A TERMINATOR's dead tail is checked by the suffix fold (`body_okS` + `scope_all_used` from
  the current scope), keeping env-denote ⊆ `supported_program` exactly.
- Locals widen NAME reach, not operation reach: a resolved variable feeds the EXISTING runtime
  value paths only; anything they don't cover stays absent (no new value semantics).
- The seam pins (`shortdecl_supported_undenoted`, `shortdecl_deadtail_supported_undenoted`)
  FLIP at 5c — swap them in the same commit.
- The LOCAL-FRONTIER suite is a MECHANICAL MAP (`forallb`) over the EXISTING
  `undenoted_frontier` ledger (never a second list); add a value-less `PtBool` member TO the
  ledger at this rung.  Every fixture quantifies over the LIST, never over "the gap".

Acceptance tests:

- `x := 1; _ = x` denotes (and the runtime bindings `x := len([]int{1})`, `y := x`).
- `x := 0; _ = 1 / x` denotes the runtime div panic (name-carried `rt_div_zero`).
- `x := 1 / len([]int{}); _ = x` denotes the RHS panic; ρ not extended.
- Unused/redeclared/forged programs stay rejected by GoSafe (gate untouched).

## Then — 6: gate reach

Flagship demos: a local-using panic-free program ACCEPTED + EMITTED + go-built;
`x := 0; _ = 1/x` supported + denotable + rejected by `cmd_no_panic`; `SPEC_CONFORMANCE.md`
rows for the remaining faithfulness rules; GoEmit demo gains a decl (golden bless).

## Standing rules

Ground every new projection in the existing authority and USE it the same tick; public
statements in PUBLIC vocabulary; a real result is `Theorem` + `Print Assumptions` + surface
registration.  At every landing: delete newly-subsumed material, sweep status prose repo-wide,
boundary-word grep last.  Work `Γ ≈ ρ` on paper before coding the threading.
