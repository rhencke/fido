# GoSem locals — eval non-literals (`x := e`)

GOAL: `GoStmt` grows short variable declaration, the checker and the evaluator grow ONE
environment, and the panic-free gate's reach extends to variable-using programs judged at
their TRUE runtime behavior. BehaviorSafe GROWTH by fragment-widening; this arc does NOT
define the `BehaviorSafe` gate.

## Current state

Rungs 1–4 and 5a/5b are DONE (the theorems are the authority): `GsShortDecl` +
print-injectivity; ONE recognized-name table (`special_ident` + inverse); the sealed
`ScopeS`/`scope_declare` checking with `type_expr` (bridged to closed `ptype`), category
projection `tcat` (mark-insensitive); the program gate `supported_program` (package-main +
`body_okS` fold from `scope_empty` + `scope_all_used`; `stmt_ok` stays the CLOSED fragment
GoSem slice 1 is gated on, agreement `body_okS_nil_declfree`); the sealed `_tc` engine
family with `EId` arms and the env instance `denote_expr_env (G)(ρ)` + closed coincidence
`denote_expr_env_nil` + env pins in `gosem_core_surface`.

STATEMENT-level denotation of `x := e` is ABSENT: `denote_stmt (GsShortDecl _ _) = None`,
so decl programs are supported-but-undenoted (`shortdecl_supported_undenoted`,
`shortdecl_deadtail_supported_undenoted`).

## Next target — 5c: the env statement layer

`denote_stmt`/`denote_body` take `(G : ScopeS, ρ : Env)`; `denote_program` runs from
`(scope_empty, nil)`. Invariants (argued once):

- ENVIRONMENT, never substitution: a declared variable is RUNTIME-categorized
  (`x := 0; _ = 1/x` compiles and panics at run time; `1/0` is a compile error).
- The `GsShortDecl` arm has EXACTLY the three `denote_expr_env` outcomes: `None` → whole
  program ABSENT; `Some (CPan p, _)` → the statement denotes the PANIC, ρ does NOT
  extend; `Some (CRet v, _)` → the ONLY ρ-extending case.
- CHECKER ADMISSION ≠ DENOTABILITY: `bind_category` is a supportedness authority; which
  admitted bindings VALUE is the evaluator's decision.
- `Γ ≈ ρ` (binding value tags match checker categories; used flags supportedness-only) is
  the lemma spine for env-denotation ⊆ `supported_program`, quantified over DENOTED runs.
- A TERMINATOR's dead tail is checked by the suffix fold from the current scope.
- Locals widen NAME reach, not operation reach: a resolved variable feeds EXISTING runtime
  value paths only.
- The seam pins (`shortdecl_*_supported_undenoted`) FLIP at 5c — same commit.
- The LOCAL-FRONTIER suite is a MECHANICAL `forallb` over the EXISTING `undenoted_frontier`
  ledger (add a value-less `PtBool` member at this rung); fixtures quantify over the LIST.

Decided implementation shape (2026-07-04, argued from the code):

- The rest-of-body's `Cmd` tree depends on the bound VALUE (the env evaluator FOLDS values:
  `y := x + 1` denotes differently per `x`), while denotability must be STATIC — so
  `denote_body_env : ScopeS -> list GoStmt -> option (Env -> Cmd unit)`: the outer option is
  the static decision, the inner function the value-dependent tree; the decl arm is
  `cbind ce (fun v => kf ((x, v) :: ρ))`.
- The static Someness predicate evaluates on `canon_env G` (each declared var bound to a
  canonical value of its checker tag); the SOMENESS-DETERMINISM lemma — for `Γ ≈ ρ`,
  `denote_expr_env G ρ e`'s Someness equals the canonical one — is the heavy proof and the
  spine of `Γ ≈ ρ` (engine None-ness is TAG-determined, never value-determined).
- The inner function's off-spec branch (a non-`Γ ≈ ρ` env, unreachable from
  `denote_program`'s `(scope_empty, nil)` start) is a fail-LOUD guard `CPan`, paired with
  an unreachability theorem — the `floats_checked_total` / closed-world pattern; never a
  silent `CRet`.
- Non-decl arms get env instances too (`denote_call_env` for args, blank-assign via
  `denote_expr_env`), each with a nil-coincidence lemma to the closed instance.

Acceptance: `x := 1; _ = x` denotes (+ runtime bindings `x := len([]int{1})`, `y := x`);
`x := 0; _ = 1/x` denotes the runtime div panic; `x := 1/len([]int{}); _ = x` denotes the
RHS panic without ρ extension; GoSafe rejections unchanged.

## Then — 6: gate reach

A local-using panic-free program ACCEPTED + EMITTED + go-built; `x := 0; _ = 1/x`
supported + denotable + rejected by `cmd_no_panic`; `SPEC_CONFORMANCE.md` rows; GoEmit
demo gains a decl (golden bless).

## Standing rules

Ground every new projection in the existing authority and USE it the same tick; public
statements in PUBLIC vocabulary; a real result is `Theorem` + `Print Assumptions` +
surface registration. At every landing: delete newly-subsumed material, sweep status
prose repo-wide, boundary-word grep last. Work `Γ ≈ ρ` on paper before coding.
