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
  - `PtBool`/`PtStr`/`PtAgg`/`PtMap ↦ Some` (themselves); `PtNil ↦ None` (`x := nil` is Go's
    "use of untyped nil" compile error).
- evaluator env `ρ : Ident ⇀ GoAny` — the world is closed, so the exact value IS known and carried;
  `EId x` resolves to `ρ x`; ops on the resolved value take the ALREADY-LANDED runtime tiers
  (GTInt R1–R8 / typed-runtime T1–T5).
- the agreement invariant `Γ ≈ ρ` (each binding's value tag matches its checker CATEGORY component;
  the used flag is supportedness-only, invisible to `ρ`) is the
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
   the gate could certify Go that does not build (fail-open — forbidden).  STRUCTURAL: the used flag
   lives IN `Γ` (see above) and uses are marked RECURSIVELY through subexpressions by the same
   traversal that types them; the no-unused rejection is the fold's final step, not a second pass.
   `_ = x` counts as a use (Go's own idiom for it).
5. declaring a CHECKER-RECOGNIZED name → reject through ONE shared authority
   `decl_ident_ok : string -> bool`, whose domain is EVERY string the checker recognizes by name —
   `nil` (ptype's EId case, GoTypes.v:544), `len`/`cap` and the conversion heads (GoTypes.v:590),
   the FULL `classify` scalar-keyword domain (14 names, GoAst.v:108: int/int8/…/uint64/bool/string/
   float64/float32), and the callee set `println`/`print`/`panic` — single-sourced NEXT TO the
   recognizers so a new recognized name cannot be added without extending the gate.  Never a second
   ad-hoc list.  Where Go PERMITS the shadowing (e.g. `len := 1`, `int := 1` are legal Go) this is
   a conservative NARROWING, named as such; each fixture's LEDGER placement (bad_programs vs
   valid_unsupported_programs — their contracts differ) is ground-truthed against the real
   toolchain via `make go-verify` at landing, never guessed.
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
1. **GoAst + GoPrint**: `GsShortDecl : Ident -> GExpr -> GoStmt`, printed `x := e` (gofmt-clean);
   `print_stmt_inj`/`print_program_inj` extended (discriminator care: an expr-statement call
   `x(1)` also starts with an identifier — the split is at `" := "` vs `"("` after the ident).
   Every GoStmt match repo-wide gains the arm WILDCARD-FREE: `stmt_ok` arm `false`, `denote_stmt`
   arm `None` (representation before admission — fail-closed).  Zero golden risk: nothing
   constructs it yet.
2. **GoTypes**: `ptype_env`/`svalue` Γ-parameterization + the `bind_category` authority (defined
   here, beside the categories it consumes — carrying the `int_const_repr` defaulting premise and
   the `PtNil` rejection) + `decl_ident_ok` (beside the recognizers it must cover); existing
   theorems lift at `[]`.
3. **GoSafe**: scope-threaded supportedness — `supported_program`'s `forallb` becomes ONE fold over
   `Γ : Ident ⇀ (PTy × bool)` (bind via `bind_category`, declare-gate via `decl_ident_ok`, uses
   marked recursively, final no-unused rejection in the same fold); rules 1–5b land with NAMED
   fixtures: `x := 9223372036854775808; _ = x` (bad — overflows every Go int) and a ~40-bit-const
   decl (valid-unsupported — fits 64-bit gc, outside the conservative range); `x := 1; _ = x;
   return` (good); `x := 1; return` (bad — declared and not used); `x := 1; x := 2; _ = x` (bad —
   no new variables); `_ := 1` (bad); `x := nil; _ = x` (bad — untyped nil); `len := 1` /
   `int := 1` / `nil := 1` (each with a `_ = <name>` use; rejected via `decl_ident_ok`; ledger per
   `make go-verify` ground truth).  Each rejection fixture ISOLATES its rule — append the `_ = x`
   use everywhere the unused rule is not the one under test, so exactly ONE rule rejects.
4. **GoSemDenote**: the evaluator takes `ρ`; `denote_stmt`/`denote_body` thread `Γ ≈ ρ`;
   `denote_stmt_sound`/`gosem_sound`/`denote_program_dec` re-proved over the invariant.  SCOPE:
   locals widen NAME reach, not operation reach — a resolved variable feeds the EXISTING runtime
   value paths only; any op those paths don't cover stays absent (fail-closed, no new value
   semantics in this rung).
5. **Gate reach (GoSemSafe + ledgers)**: flagship demos — a local-using panic-free program
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
