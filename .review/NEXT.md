# C6 — Names, types, scopes, facts, values and the scalar store

Baseline: f9b3ec581bfbb0bdcac9caae586bc1a23ac09d40
Review: contract

Goal:
C6 lands exact binding and use roles, the one program-indexed type algebra, the predeclared universe, static
slots, typed places, typed closed runtime values, the scalar-cell store and environment, and the
expression-fact/use boundary that declarations and variables need.

**C6 instantiates no `Machine.T` and defines no run relation.** C7 builds the first concrete machine for a
`Safe.Program` from C6's retained facts and store roots. C11 generalizes package initialization and starts to
imports and `init`.

66 closure rows and 22 latitude rows carry `milestone` `C6`; counts derive from the ledgers. `LAT-077` is
C6's only acceptance gate.

## 1. Module ownership and Dune order

Each root has exactly one owner. `Compilable.v` and `Safe.v` are not default owners.

| root | owner | status |
|---|---|---|
| ordinary-name refinement | `Names` | extended |
| source AST | `Syntax` | extended |
| source indexing, refined references | `Index` | extended |
| type algebra and type decisions | `Typing` | extended, program-indexed |
| retained static phase, diagnostics, public fact queries | `Compilable` | extended |
| runtime value, place, slot, store, environment | **`Runtime`** | **new module** |
| safety capability, migrated constant projection | `Safe` | narrowed |
| renderer | `Render` | extended |

Dune order becomes:

```text
Decimal Integer Float Complex FilePath ModulePath Version Collections Names Syntax Index Typing
Compilable Machine Runtime Safe Render Emit
```

`Runtime` sits after `Compilable` (it is indexed by `Compilable.Program`) and before `Safe`. `Machine` keeps
its position and stays uninstantiated.

## 2. Source declarations, in compilable order

```coq
Record OrdinaryIdentifier : Type := MakeOrdinary {
  ordinary_identifier : Names.Identifier;
  ordinary_not_blank  : Names.spelling ordinary_identifier <> "_"%string
}.

Inductive NameOrBlank : Type :=
| DeclaredName : OrdinaryIdentifier -> NameOrBlank
| BlankName    : NameOrBlank.

Inductive TypeExpr : Type :=
| NamedType : OrdinaryIdentifier -> TypeExpr.

Inductive Expr : Type :=
| Name                  : OrdinaryIdentifier -> Expr
| IntegerLiteral        : N -> Expr
| NegatedIntegerLiteral : N -> Expr
| StringLiteral         : string -> Expr
| FloatLiteral          : Float.Decimal -> Expr
| ComplexLiteral        : Complex.Decimal -> Expr
| Convert               : TypeExpr -> Expr -> Expr.

Record IdentifierList : Type := MakeIdentifierList {
  first_identifier : NameOrBlank;
  more_identifiers : list NameOrBlank
}.

Record ExpressionList : Type := MakeExpressionList {
  first_expression : Expr;
  more_expressions : list Expr
}.

Inductive ConstInitializer : Type :=
| ExplicitConstInitializer  : option TypeExpr -> ExpressionList -> ConstInitializer
| InheritedConstInitializer : ConstInitializer.

Record ConstSpec : Type := MakeConstSpec {
  const_names       : IdentifierList;
  const_initializer : ConstInitializer
}.

Inductive VarInitializer : Type :=
| VarTypeOnly : TypeExpr -> VarInitializer
| VarValues   : option TypeExpr -> ExpressionList -> VarInitializer.

Record VarSpec : Type := MakeVarSpec {
  var_names       : IdentifierList;
  var_initializer : VarInitializer
}.

Inductive TypeSpec : Type :=
| AliasSpec : NameOrBlank -> TypeExpr -> TypeSpec
| DefSpec   : NameOrBlank -> TypeExpr -> TypeSpec.

Inductive Declaration : Type :=
| ConstDecl : list ConstSpec -> Declaration
| VarDecl   : list VarSpec   -> Declaration
| TypeDecl  : list TypeSpec  -> Declaration.

Inductive Stmt : Type :=
| Println         : list Expr -> Stmt
| DeclarationStmt : Declaration -> Stmt
| ShortVarDecl    : IdentifierList -> ExpressionList -> Stmt.

Inductive Block : Type :=
| MakeBlock : list Stmt -> Block.

Inductive TopLevelDecl : Type :=
| TopDeclaration : Declaration -> TopLevelDecl
| Main           : Block -> TopLevelDecl.
```

No `with` group. `Syntax.File` carries `list TopLevelDecl`; no alias for the old `Decl` survives.
`Syntax.BoolLiteral` is deleted. A nested `Main` is unrepresentable.

**Canonical declaration spelling.** One spec renders ungrouped; zero or two-or-more specs render as a
parenthesized group; the empty group is exactly the empty list. The source model retains **no**
parenthesized-versus-ungrouped choice for a single spec, and no source-style flag is added.

## 3. Complete index additions

`Index.Kind` gains exactly:

```text
BlockKind  TopLevelDeclKind  MainKind  DeclarationKind'  ConstSpecKind  VarSpecKind
AliasSpecKind  DefSpecKind  DeclaredNameKind  BlankKind  NameExprKind
```

`DeclarationKind'` is the ordinary (const/var/type) declaration; the existing `DeclarationKind` is retired
with the old `Decl`. `Index.View` gains one constructor per new kind, each carrying its exact source value.

`Index.Role` gains exactly:

```text
TopLevelDeclaration n   BlockStatement n      DeclarationSpec n
ConstSpecName n         ConstSpecType         ConstSpecValue n
VarSpecName n           VarSpecType           VarSpecValue n
TypeSpecName            TypeSpecTarget
ShortDeclName n         ShortDeclValue n
MainBlock
```

Refined public references, each `NodeRefOf p k` except where noted:

```text
BlockRef  TopLevelDeclRef  MainRef  DeclarationRef  ConstSpecRef  VarSpecRef
AliasSpecRef  DefSpecRef  DeclaredNameRef  BlankRef  NameExprRef  TypeUseRef
```

Two further refinements carry a proof, not a Boolean test recovered later:

```coq
Definition BoundDefinedTypeRef (p : Syntax.Program) :=
  { r : DefSpecRef p | def_spec_name r <> BlankName }.
Definition VariableNameRef (p : Syntax.Program) :=
  { r : DeclaredNameRef p | declared_by_var_or_short r = true }.
```

Smart refinements `as_block`, `as_top_level_decl`, `as_main`, `as_declaration`, `as_const_spec`,
`as_var_spec`, `as_alias_spec`, `as_def_spec`, `as_declared_name`, `as_blank`, `as_name_expr` each map a
generic `Snapshot.NodeRef` to `option` of the refined type.

**Use references are not source nodes.** `ExprUseRef` is a separate inductive over source references:

```coq
Inductive ExprUseRef (p : Syntax.Program) : Type :=
| PrintlnArgUse      : StmtRef p -> nat -> ExprUseRef p
| ConversionOperandUse : ExprRef p -> ExprUseRef p
| ExplicitConstUse   : ConstSpecRef p -> nat -> ExprUseRef p
| InheritedConstUse  : InheritedConstUseRef p -> ExprUseRef p
| VarInitUse         : VarSpecRef p -> nat -> ExprUseRef p
| ShortVarInitUse    : StmtRef p -> nat -> ExprUseRef p.
```

`InheritedConstUseRef` is a semantic use-edge object, never a fabricated source node:

```coq
Record InheritedConstUseRef (p : Syntax.Program) : Type := MakeInheritedConstUse {
  ic_current        : ConstSpecRef p;
  ic_spec_index     : nat;                        (* the iota value for the current spec *)
  ic_position       : nat;                        (* position in the current identifier list *)
  ic_predecessor    : ConstSpecRef p;             (* nearest preceding EXPLICIT spec, same ConstDecl *)
  ic_pred_expr      : ExprRef p;                  (* predecessor expression at ic_position *)
  ic_pred_type      : option (TypeUseRef p);      (* predecessor optional type use *)
  ic_nearest_proof  : NearestExplicitPredecessor ic_current ic_predecessor
}.
```

The current use reuses the predecessor's **source expression and optional source type** under the current
spec's `iota`. It never reuses the predecessor's resolved value or typed result, copies the expression,
searches backward again, or reconstructs an equal predecessor.

## 4. One retained static phase; the old phase is absorbed

The current expression `Phase` and its constructible expression-fact records own the old fixed-resolver path.
C6 **replaces** that authority. It is generalized into the new root, not retained beside it.

The review named this root `C6.StaticPhase`. It is frozen here as **`Compilable.StaticPhase`**, deliberately:
a module named for a milestone would be wrong the moment C7 extends it, and `Compilable` already owns the
retained elaboration this phase joins. The name is the only difference; the topology below is the review's.

```coq
Module Type C6_PHASE.
  Parameter StaticPhase : forall {p : Syntax.Program}, Compilable.Input p -> Type.
  Parameter build_static_phase : forall {p} (i : Compilable.Input p), StaticPhase i.
  Parameter phase_diagnostics : forall {p} {i : Compilable.Input p},
    StaticPhase i -> list (Compilable.DiagnosticReason p).
End C6_PHASE.
```

`Compilable.Core` gains exactly one field, `core_static : StaticPhase (core_input core)`, and
`core_raw_diagnostics` is extended to include `phase_diagnostics core_static`. The old `phase` field and its
expression-fact records are deleted, their content generalized into `StaticPhase`.

One `StaticPhase` retains, by construction: package scope; local block and scope structure; the predeclared
outer scope; the exact package const/var dependency graph; the exact type-declaration graph; binding
results; type-use results; context-free expression results; use-edge results; blank-use results; slot
results; static initialization results; and all C6 diagnostics.

An accepted `Compilable.Program` exposes total facts from that exact object. A rejected `Compilable.Failure`
retains **the same object that produced its diagnostics** — never a copied list. No scope, graph,
environment or fact table is independently rebuilt anywhere.

Scope and identity-keyed tables use pinned standard finite maps and sets. Duplicate insertion **fails**; it
never overwrites.

## 5. Exact scope-start rules

| declaration | scope begins | visible in its own initializer / RHS |
|---|---|---|
| package `const`, `var`, `type`, `main` | the whole package block, all files | yes — forward and self reference are visible, and a cycle is a diagnostic |
| local `const` spec | end of the `ConstSpec` | no — an outer or predeclared name is selected |
| local `var` spec | end of the `VarSpec` | no — an outer or predeclared name is selected |
| local `type` spec | end of the `TypeSpec` | no for an alias; a `DefSpec` may refer to itself only through a form C6 does not admit, so a self-reference is a cycle diagnostic |
| short-variable new name | end of the `ShortVarDecl` statement | no |
| short redeclaration | keeps the existing slot; no new scope entry | n/a |
| predeclared object | the outer scope enclosing every package block | shadowed by any package or local declaration of the same spelling |
| blank | never enters any scope | n/a |

Package construction is two-stage: collect every package-level declared name across all files, rejecting
duplicates; then resolve package-level declarations against the complete package block. File order never
chooses package meaning. Local blocks are sequential. `main` participates in package uniqueness.
Package-scope `init` may not be introduced by a C6 const, type or var declaration.

## 6. Expression facts and use facts

Facts are abstract dependent families indexed by exact references, projected from the accepted capability.
No public constructible record pairs a reference with a target.

```coq
ExpressionFact : forall (cp : Compilable.Program), Index.ExprRef (Compilable.source cp) -> Type.
expression_fact : forall cp r, ExpressionFact cp r.
BindingFact  : forall cp, Index.NameExprRef (Compilable.source cp) -> Type.
binding_fact : forall cp r, BindingFact cp r.
TypeUseFact  : forall cp, Index.TypeUseRef (Compilable.source cp) -> Type.
type_use_fact : forall cp r, TypeUseFact cp r.
BlankUseFact : forall cp, Index.BlankRef (Compilable.source cp) -> Type.
blank_use_fact : forall cp r, BlankUseFact cp r.
SlotFact     : forall cp, Index.VariableNameRef (Compilable.source cp) -> Type.
slot_fact    : forall cp r, SlotFact cp r.
UseFact      : forall cp, Index.ExprUseRef (Compilable.source cp) -> Type.
use_fact     : forall cp r, UseFact cp r.
```

The complete context-free expression-fact cases:

```text
UntypedBoolFact     UntypedIntegerFact   UntypedFloatFact   UntypedComplexFact   UntypedStringFact
TypedConstantFact t          (t basic or defined)
NonconstantValueFact t       (an ordinary name bound to a variable, and any expression over one)
IotaFact                     (no context-free numeric value)
UntypedNilFact
NameConstantFact             (ordinary name bound to a constant)
NameVariableFact             (ordinary name bound to a variable)
ConversionConstantFact t
ConversionNonconstantFact t
```

The complete use-fact cases, one per `ExprUseRef` constructor: `PrintlnArgUse`, `ConversionOperandUse`,
`ExplicitConstUse`, `InheritedConstUse`, `VarInitUse`, `ShortVarInitUse`. Each owns defaulting, target type,
assignability, representability, arity position, and the current const-spec context where one applies. Every
use builder consumes the exact retained child fact and never re-reads the raw child.

The binding target universe distinguishes exactly: each of the eighteen predeclared type objects; `true`;
`false`; `iota`; `nil`; an exact declared constant; an exact declared variable; an exact alias declaration;
an exact defined-type declaration; the current `main` declaration. A value-role use cannot receive a type
object, and a type use cannot receive a variable or constant; wrong-kind resolution produces a structured
diagnostic from the retained binding object.

**`iota`** has no context-free numeric value. Its binding fact identifies the predeclared object; the
const-initializer use fact supplies the current declaration group and spec index, and that context
propagates through nested conversions without rereading ancestry or searching the syntax. A declaration
named `iota` resolves through the ordinary binding relation and gets no predeclared behaviour.

**`nil`** resolves through the ordinary predeclared binding. C6 has no nilable type, so an unshadowed `nil`
carries `UntypedNilFact` and **every** C6 use rejects it with `FIDO-E-NIL-NO-TYPE`. A declaration shadowing
`nil` binds normally.

## 7. Package const/var dependency authority

Package declarations and ordinary names are both representable at C6, so package constants and variables can
refer forward across files. Exact `go build` acceptance therefore needs dependency and cycle handling **in
C6**; it cannot wait for C11.

`StaticPhase` retains one package initialization-dependency object, distinct from the type-declaration graph
and never generalized into one abstraction with it. Its edges arise from the retained binding and use facts;
constant and variable dependencies are distinguished where their rules differ; the graph is built once. On
success it retains the exact acyclic result and canonical dependency facts; on failure an exact cycle
witness and diagnostics. C6 adds no runtime initialization order and no `Machine.step`. C11 consumes and
extends this same retained object; it builds no peer graph.

## 8. Type environment interface — owner `Typing`

```coq
Inductive SemanticType (p : Syntax.Program) : Type :=
| BoolType | IntegerType : Integer.Kind -> SemanticType p
| FloatType : Float.Kind -> SemanticType p | ComplexType : Complex.Kind -> SemanticType p
| StringType | DefinedType : Index.BoundDefinedTypeRef p -> SemanticType p.

Module Type TYPE_ENV.
  Parameter Env : Compilable.Program -> Type.
  Parameter alias_target   : forall cp, Env cp -> Index.AliasSpecRef (src cp) -> SemanticType (src cp).
  Parameter def_rhs        : forall cp, Env cp -> Index.BoundDefinedTypeRef (src cp) -> SemanticType (src cp).
  Parameter underlying     : forall cp, Env cp -> SemanticType (src cp) -> SemanticType (src cp).
  Parameter core_type      : forall cp, Env cp -> SemanticType (src cp) -> option (SemanticType (src cp)).
  Parameter identicalb     : forall cp, Env cp -> SemanticType (src cp) -> SemanticType (src cp) -> bool.
  Parameter assignableb    : forall cp, Env cp -> SemanticType (src cp) -> SemanticType (src cp) -> bool.
  Parameter convertibleb   : forall cp, Env cp -> SemanticType (src cp) -> SemanticType (src cp) -> bool.
  Parameter representableb : forall cp, Env cp -> SemanticType (src cp) -> Typing.Constant -> bool.
  Parameter zero_value     : forall cp (t : SemanticType (src cp)), Runtime.Value cp t.
End TYPE_ENV.
```

Each decision has one executable function and one reflection theorem, named in §11. A proof-only relation
beside a separate checker is forbidden. The signature is `TYPE_ENV`; the implementation is one sealed
`Module TypeEnv : TYPE_ENV`. No top-level Rocq assumption exists anywhere.

`Typing.TypedConstant` becomes `TypedConstant p : SemanticType p -> Type`. A typed constant of a defined
basic type retains that exact defined type while its value is represented through the exact underlying basic
type. `byte` and `rune` remain aliases of `uint8` and `int32`: source spelling preserved, no identity minted.

## 9. Runtime foundation — owner `Runtime` (new module)

```coq
Parameter Value       : forall (cp : Compilable.Program), Typing.SemanticType (src cp) -> Type.
Parameter Slot        : forall (cp : Compilable.Program), Typing.SemanticType (src cp) -> Type.
Parameter Place       : forall (cp : Compilable.Program), Typing.SemanticType (src cp) -> Type.
Parameter Store       : Compilable.Program -> Type.
Parameter Environment : Compilable.Program -> Type.

Parameter zero_value          : forall cp t, Value cp t.
Parameter materialize_constant : forall cp t, Typing.TypedConstant (src cp) t -> Value cp t.

Parameter empty_store : forall cp, Store cp.
Parameter allocate    : forall cp t, Store cp -> Value cp t -> Store cp * Place cp t.
Parameter load        : forall cp t, Store cp -> Place cp t -> option (Value cp t).
Parameter write       : forall cp t, Store cp -> Place cp t -> Value cp t -> Store cp.

Parameter empty_environment : forall cp, Environment cp.
Parameter bind_slot   : forall cp t, Environment cp -> Slot cp t -> Place cp t -> Environment cp.
Parameter lookup_slot : forall cp t, Environment cp -> Slot cp t -> option (Place cp t).
```

Declared inside `Module Type RUNTIME_ROOT` and supplied by one sealed `Module RuntimeRoot : RUNTIME_ROOT`.
`ObjectId` and the raw store representation are private to that implementation; only `allocate` mints an
identity, never derived from a source reference, name, client-supplied number, type tag or trace position.
A `Slot cp t` exists only for a nonblank variable declaration or a newly introduced short-declaration name.

`write` is part of the root: variables and short redeclarations are mutable, and deferring the only update
operation would force C7 to redesign the foundation immediately.

`Safe.eval_expr` cannot survive as a second fixed-resolver evaluator. Its replacement is frozen as

```coq
Parameter constant_value_at :
  forall (cp : Compilable.Program) (r : Index.ExprRef (src cp)), option { t & Value cp t }.
```

a projection over the accepted program, the exact expression reference and the retained C6 facts. It stays
**constant-only**; C7 owns runtime evaluation of variables and other nonconstant expressions. The current
pure constant-evaluation guarantee survives with its new indices; it is not deleted because its carrier
changed.

## 10. Diagnostics

Every row extends the existing snapshot-indexed `Compilable.DiagnosticReason`. Precedence is the listed
order: an earlier row suppresses a later one anchored at the same primary reference. All existing
diagnostics precede every C6 row.

| constructor | code | primary ref | related payload | value payload | erased form |
|---|---|---|---|---|---|
| `DuplicateDecl` | `FIDO-E-DUPLICATE-DECL` | `DeclaredNameRef` | earlier `DeclaredNameRef` | spelling | `(code, key, key)` |
| `MainConflict` | `FIDO-E-MAIN-CONFLICT` | `DeclaredNameRef` | `MainRef` | spelling | `(code, key, key)` |
| `InitMisuse` | `FIDO-E-INIT-MISUSE` | `DeclaredNameRef` | none | spelling | `(code, key)` |
| `FirstSpecInherited` | `FIDO-E-FIRST-SPEC-INHERITED` | `ConstSpecRef` | enclosing `DeclarationRef` | none | `(code, key, key)` |
| `DeclArity` | `FIDO-E-DECL-ARITY` | `ConstSpecRef` or `VarSpecRef` | none | names, values counts | `(code, key, nat, nat)` |
| `ShortDeclNoNew` | `FIDO-E-SHORT-DECL-NO-NEW` | `StmtRef` | none | none | `(code, key)` |
| `UnresolvedName` | `FIDO-E-UNRESOLVED-NAME` | `NameExprRef` or `TypeUseRef` | none | spelling | `(code, key)` |
| `WrongRole` | `FIDO-E-WRONG-ROLE` | `NameExprRef` or `TypeUseRef` | target declaration ref | expected, found role | `(code, key, key, role, role)` |
| `TypeCycle` | `FIDO-E-TYPE-CYCLE` | earliest `DefSpecRef` or `AliasSpecRef` in the cycle | every other ref in the cycle, source order | none | `(code, key, list key)` |
| `InitCycle` | `FIDO-E-INIT-CYCLE` | earliest `DeclaredNameRef` in the cycle | every other ref in the cycle, source order | none | `(code, key, list key)` |
| `NilNoType` | `FIDO-E-NIL-NO-TYPE` | `NameExprRef` | none | none | `(code, key)` |
| `IotaOutOfContext` | `FIDO-E-IOTA-CONTEXT` | `NameExprRef` | none | none | `(code, key)` |
| `ShortRedeclType` | `FIDO-E-SHORT-REDECL-TYPE` | `DeclaredNameRef` | original `DeclaredNameRef` | both types | `(code, key, key)` |
| `InitNotAssignable` | `FIDO-E-INIT-NOT-ASSIGNABLE` | `ExprRef` | target `TypeUseRef` when present | target type | `(code, key)` |
| `UnusedLocal` | `FIDO-E-UNUSED-LOCAL` | `DeclaredNameRef` | none | spelling | `(code, key)` |

Classification of the named hard cases: duplicate nonblank names **within one declaration list** and on a
**short-declaration left side** are both `DuplicateDecl` anchored at the later name; `iota` outside a const
initializer is `IotaOutOfContext`; unshadowed `nil` in any C6 use is `NilNoType`; constant and package
variable initialization cycles are both `InitCycle`, distinguished by their payload refs, not by a second
constructor; scope-timing failures surface as `UnresolvedName` at the use, because the declaration is simply
not yet in scope; a short declaration introducing no new nonblank name is `ShortDeclNoNew`; an inherited
const spec with no preceding explicit initializer is `FirstSpecInherited`.

## 11. Public theorem names and statements

Names are frozen here; none is chosen during proof implementation. Proof helpers are `Local`; every theorem
below is public because C7 and later milestones consume it.

```text
package_block_file_order_independent   package_block_duplicate_rejected
local_scope_starts_after_spec          local_shadows_package_and_predeclared
binding_total_on_accepted_names        blank_never_binds        blank_never_owns_slot
export_is_package_level_only           short_decl_requires_new_nonblank
short_redecl_keeps_slot                predeclared_resolves_exactly
byte_alias_uint8_no_identity           rune_alias_int32_no_identity
alias_preserves_identity               distinct_defs_distinct_identity
underlying_resolves_to_basic           type_cycle_rejected
identicalb_reflect  assignableb_reflect  convertibleb_reflect  representableb_reflect
expression_fact_context_free           use_fact_consumes_child_fact
inherited_const_predecessor_exact      inherited_const_iota_is_current
init_dependency_acyclic_on_accept      init_cycle_rejected
slot_unique_per_variable_name          zero_value_well_typed
materialize_constant_well_typed        empty_store_has_no_cell
load_after_allocate                    load_after_write
write_preserves_other_cells            allocate_preserves_existing_cells
allocate_fresh                         allocate_never_reuses
empty_environment_binds_nothing        bind_slot_preserves_others
lookup_slot_type_exact                 constants_types_blanks_allocate_nothing
render_ascii_valid                     render_direct_spelling
render_injective_where_relied_on       render_preserves_pre_c6_bytes
```

**Theorem migration rule.** Every existing public guarantee survives with the required program and reference
indices added. None is deleted or weakened because the old fixed resolver disappears; where a statement
mentioned `Compilable.predeclared_type`, it gains the retained phase instead.

## 12. Canonical rendering

Indentation is one tab per block depth. Statements and declarations are newline-separated. No trailing
whitespace and no blank line inside a group.

```text
render(TopDeclaration d)            = render_decl(d, depth 0)
render(Main b)                      = "func main() {" NL render_block(b, 1) "}" NL
render_block(MakeBlock ss, n)       = concat (render_stmt(s, n) for s in ss)
render_stmt(DeclarationStmt d, n)   = indent(n) render_decl(d, n)
render_stmt(Println args, n)        = indent(n) "println(" join(", ", args) ")" NL
render_stmt(ShortVarDecl ns es, n)  = indent(n) render_idlist(ns) " := " render_exprlist(es) NL
render_decl(ConstDecl [s], n)       = "const " render_const_spec(s) NL
render_decl(ConstDecl ss, n)        = "const (" NL (indent(n+1) render_const_spec(s) NL)* indent(n) ")" NL
render_const_spec(names, Explicit None es)      = render_idlist(names) " = " render_exprlist(es)
render_const_spec(names, Explicit (Some t) es)  = render_idlist(names) " " render_type(t) " = " render_exprlist(es)
render_const_spec(names, Inherited)             = render_idlist(names)
render_decl(VarDecl [s], n)         = "var " render_var_spec(s) NL
render_decl(VarDecl ss, n)          = "var (" NL (indent(n+1) render_var_spec(s) NL)* indent(n) ")" NL
render_var_spec(names, VarTypeOnly t)          = render_idlist(names) " " render_type(t)
render_var_spec(names, VarValues None es)      = render_idlist(names) " = " render_exprlist(es)
render_var_spec(names, VarValues (Some t) es)  = render_idlist(names) " " render_type(t) " = " render_exprlist(es)
render_decl(TypeDecl [s], n)        = "type " render_type_spec(s) NL
render_decl(TypeDecl ss, n)         = "type (" NL (indent(n+1) render_type_spec(s) NL)* indent(n) ")" NL
render_type_spec(AliasSpec nb t)    = render_nameorblank(nb) " = " render_type(t)
render_type_spec(DefSpec nb t)      = render_nameorblank(nb) " " render_type(t)
render_idlist(l)                    = join(", ", first :: more)
render_exprlist(l)                  = join(", ", first :: more)
render_nameorblank(DeclaredName i)  = Names.spelling i
render_nameorblank(BlankName)       = "_"
render_type(NamedType i)            = Names.spelling i
render_expr(Name i)                 = Names.spelling i
render_expr(Convert t e)            = render_type(t) "(" render_expr(e) ")"
```

An empty group renders as `const ()`, `var ()` or `type ()` followed by a newline. Literal rendering is
unchanged. **Every program accepted before C6 renders byte-identically after migration**, which
`render_preserves_pre_c6_bytes` states.

## 13. Deletions

`Syntax.BoolLiteral`; `Syntax.TypeName` (`Unqualified`) and the `type_expr_*` helpers; `Names.TypeName`,
`Names.SupportedType`, `Names.classify`, `Names.supported_of`, `Names.all_type_names` and every projection;
`Compilable.predeclared_type`, `predeclared_type_of_name` and its ten `Local Notation`s; the old expression
`Phase` and its constructible expression-fact records; `Safe.eval_expr` and the unindexed `Safe.Value`.
Current programs migrate first; the competing path is deleted in the same milestone. No wrapper survives.

## 14. Two reviews and their allowed files

**Semantic-root half** — allowed: `Names.v`, `Syntax.v`, `Index.v`, `Typing.v`, `Compilable.v`, `dune`.
Complete: corrected source constructors; complete `Index` kinds, roles, views and refined references; the
retained `StaticPhase` with scope, both graphs, and all fact families; reflected type decisions; migration
of the existing fragment to ordinary names; deletion of the sixteen-name resolver and the old phase. Then
**stop for the semantic-root implementation review**.

**Final half** — allowed additionally: `Runtime.v`, `Safe.v`, `Render.v`, `e2e/*`, goldens, generated Go,
`README.md`, `.review/scope.tsv` (`SR-008`), `ARCHITECTURE.md`, `ROADMAP.md`, `.review/NEXT.md`, acceptance
and ledger rows. Complete: typed values, slots, places, store, environment; zero values and materialization;
rendering; diagnostics; fixtures and `LAT-077`; generated artifacts and pinned-Go evidence.

No fixture, generated artifact or current-document update belongs to the semantic-root half unless a
semantic-root proof requires it.

## 15. Required fixtures

Package and local `const`/`type`/`var` accepted; a local variable used by `println`; unused local rejected
with `FIDO-E-UNUSED-LOCAL`; cross-file package declarations resolving independent of file order; duplicate
package names rejected; local shadowing of package and predeclared names; short declaration with no new
nonblank name rejected; blank declarations creating no binding or slot; `true`, `false`, the predeclared
type names, `byte` and `rune` resolving through ordinary binding; shadowing those names changing resolution;
alias preserving identity; two distinct defined declarations with equal underlying types having distinct
identity; every type-declaration cycle rejected; a package constant cycle and a package variable cycle each
rejected with `FIDO-E-INIT-CYCLE`; a first const spec with an inherited initializer rejected; an inherited
const spec taking the predecessor expression under its own `iota`; unshadowed `nil` rejected in every C6 use
context; `iota` outside a const initializer rejected; typed zero values for every admitted basic and defined
type; every currently accepted program rendering byte-identically after migration; generated C6 programs
passing the pinned Go build with their exact expected runtime observation.

## Preserve

`Syntax.Program` as the sole source authority and the AST as the one IR; the exact retained
`Compilable.Program`, `Failure` and whole-elaboration cores, and their sealing; `Machine.T` exactly as C5
froze it, uninstantiated; `Safe.Property = True` while the fragment has no unsafe behaviour; direct
rendering and the one `Emit.Mint.issue` authority; certified-module coverage, the whole-theory audit and
controls A-E; every sealed-capability, mint, transport and positive client control; working-tree and
staged-index separation; no-host-Python; `life.md`.

## Done

Every C6 row discharged or repriced under review; `LAT-077` discharged; no structural type, loop, closure,
user function, label, panic, concurrency, composite object, import, package-initialization **order** or
concrete machine appears; every deleted authority gone with no wrapper; `make prove`, `make check`,
`make audit-fresh`, `make regenerate`, `make regen-guard` pass; generated bytes change only where a newly
admitted construct is rendered, with goldens and differential evidence in the same commit; both reviews
pass; then Rob accepts C6.

## Stop

The program-indexed `SemanticType` migration cannot complete without weakening an existing theorem; a C6 row
needs a construct assigned to a later milestone; a decision cannot be given one executable function and a
reflection theorem; a fact family cannot be projected from the retained core without a free-standing
authority beside it; the package dependency graph cannot be built from retained facts without rereading
syntax; `LAT-077` needs a diagnostic the elaboration cannot produce from the retained object; a run relation,
evaluator or machine instantiation is needed for a C6 row; implementation needs a placeholder, compatibility
path, trusted shortcut, fuel, bound or premature future state.
