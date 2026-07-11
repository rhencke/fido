# GoCompile — the static compiler-admissibility layer

The layered stack (the user's framing): **GoAst** = this represents a syntactically valid program ·
**GoCompile** = this program would compile · **GoSem** = semantics atop a compilable program ·
**GoSafe/GoSemSafe** = safety atop the semantics.  Each layer is meaningful ONLY for programs the
layer below admits.  "The Go compiler may compile our program, but it must not be the FIRST
component to understand it" — GoCompile proves the front-end obligations.

Four claims that must NOT blur into one predicate:
1. GoAst: this syntax can be represented (syntactically valid).
2. GoCompile: this represented syntax WOULD COMPILE (statically admissible for the emitted subset).
3. GoSem: this compilable program has modeled runtime meaning.
4. GoSafe/GoSemSafe: this modeled behavior satisfies safety / panic-freedom / termination claims.

## Phase 1 — the rename/move — LANDED

`GoSafe.v` (the static checker: `ScopeS`/`type_expr`/`stmt_okS`/`body_okS`/scope-decl-use tracking +
constant/type-category checks through `GoTypes`) is RELOCATED to `GoCompile.v` — its correct
architectural home.  Repo-wide semantic rename, no compatibility aliases:
`supported_program`→`go_compile_check`, `SupportedProgram`→`GoCompile`, `ep_supported`→`ep_compile`,
`emit_supported`→`emit_compiled`, `demo_supported`→`demo_compiles`,
`good_programs_supported`→`good_programs_compile`, module/file `GoSafe`→`GoCompile`.  `GoSafe.v` is
now ABSENT (the name is RESERVED for real behavioral safety; behavior lives in `GoSemSafe.v`).
Spine: `GoAst → GoPrint → GoCompile → GoEmit`; behavior: `GoCompile → GoSem → GoSemSafe`.
`GoEmit` requires `GoCompile`; `GoSem`'s `gosem_sound` is `denotation ⊆ GoCompile`.  dune, Makefile,
Dockerfile, spine-gate, smart-ctor-gate, pre-commit, and every doc updated.

## Phase 2 — the proof-bearing declarative relation (NEXT — NOT a decorative alias)

Today `GoCompile p := go_compile_check p = true` — the executable checker AS the authority.  The
boss's stronger target (do NOT stop at the bool-alias): a DECLARATIVE static-admissibility relation
with the checker demoted to derived tooling.

  Inductive CompileExpr : ScopeS -> GExpr -> PTy -> ScopeS -> Prop := ...
  Inductive CompileStmt : ScopeS -> GoStmt -> ScopeS -> Prop := ...
  Inductive CompileBody : ScopeS -> list GoStmt -> ScopeS -> Prop := ...
  Record GoCompile (p : Program) : Prop := {
    gc_package_main; gc_body_compile : exists Gf, CompileBody scope_empty (prog_body p) Gf;
    gc_no_unused_locals; gc_names_resolved; gc_no_redeclare; gc_stmt_forms_valid;
    gc_type_categories_ok; gc_constants_ok; }.
  Theorem go_compile_check_sound : go_compile_check p = true -> GoCompile p.
  (* + go_compile_check_complete for the current emitted subset; if full completeness is too much,
     SHRINK the accepted subset rather than keep a weaker public proof shape — cut scope before
     weakening proof strength. *)

Then: public theorem surfaces mention the RECORD `GoCompile`, `go_compile_check` stays the executable
derived tooling only, `GoEmit`/`EmittableProgram.ep_compile` carry the record.

## What GoCompile covers NOW (current `Program` shape)

package name is `main` · statement forms legal for void `func main` · expr-statements are calls where
Go requires calls · `defer` payloads are calls · valid void-main return form · blank-assignment value
sink · short-decl binds a NEW valid non-blank non-recognized local · use-before-declare rejected ·
redeclaration rejected where the subset forbids · unused locals rejected · recognized/builtin names
cannot be rebound by locals · type/category via the single `GoTypes` authority · constants
representable in the target category · const errors (overflow / div-by-zero / shift / invalid
conversion category) rejected · map keys / duplicate keys / unsupported aggregate/map conversions are
explicit narrowed frontiers · any unsupported construct rejected or unrepresentable, never faked.

Do NOT add future Go-compiler features now (imports, multiple functions, top-level decls, arity,
labels/goto, channel directions, comparability, methods/interfaces) just to look complete — give them
a NAMED home in GoCompile when the AST grows.

## Rules

No behavioral claim in GoCompile — it is STATIC admissibility only (naming is a correctness claim,
Rule 6).  `GoSem` must not assign authoritative runtime meaning to programs GoCompile would reject
(except as an explicitly-fenced rejected frontier).  `BehaviorSafe` (future) = `GoCompile` +
`denotes` + safety — NEVER a synonym for `GoCompile`.  Zero axioms; every public surface gated;
golden byte-identical (this is a rename/relocation, no emission change).
