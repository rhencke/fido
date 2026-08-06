# C6 — ordinary names, one type algebra, static objects, and the permanent store

Review: contract

Goal:
C6 introduces ordinary names and shadowing. One ordinary identifier fills every name position; the retained
binding fact decides what each occurrence means. C6 lands the complete predeclared identity catalog, the
program-indexed type algebra, compiler-owned static variable identity, one expression-result authority, one
structural arity authority, and the permanent runtime store and environment. It defines **no run relation and
instantiates no `Machine.T`**; C7 builds the first machine.

## 1. Module order and ownership

```text
Decimal Integer Float Complex FilePath ModulePath Version Collections Names Syntax Index Typing
Compilable Machine Runtime Safe Render Emit
```

`Typing` imports `Index` and neither `Compilable` nor `Runtime`. `Runtime` sits after `Compilable`, because a
dynamic environment is keyed by a compiler-owned variable object.

`ARCHITECTURE.md` §1 states the ownership law once. This contract adds nothing to it and contradicts nothing
in it.

## 2. Support depends on binding, not on spelling

`main`, `any`, `error`, `uintptr` and `append` each denote a predeclared object **or** a user declaration that
shadows it. `T(x)` is a conversion or a call only after the head name resolves. A support decision that a
spelling ban would have to make before binding is therefore made after binding, against the exact object.

Constructor absence still owns every exclusion syntax alone can identify. Where legality depends on binding,
`Syntax` carries the ordinary source form and `Compilable` enforces the exact resolved capability boundary
before minting `Compilable.Program`. A resolved object whose semantic rule belongs to a later milestone
produces an exact unavailable-capability diagnostic naming the object, the required capability and the ledger
row that owns it — never an unresolved name, never a false wrong-role, never a broad unsupported catch-all.

The public acceptance claim is therefore the `SC-22` incremental subset theorem, not equivalence with pinned
`go build` over every `Syntax.Program`. `TypeIdentifier`, `OperandIdentifier`, `SR-010` and `SR-011` are
deleted.

## 3. Source topology

```coq
(* Names *)
Record OrdinaryIdentifier : Type := MakeOrdinary {
  ordinary_identifier : Identifier;
  ordinary_not_blank  : spelling ordinary_identifier <> "_"%string
}.

(* Collections *)
Record NonEmpty (A : Type) : Type := MakeNonEmpty { ne_first : A; ne_rest : list A }.

(* Syntax *)
Inductive BindingName : Type :=
| Named : Names.OrdinaryIdentifier -> BindingName
| Blank : BindingName.

Inductive UnaryOp : Type := UnaryMinus.

Inductive ApplicationHead : Type :=
| NamedHead : Names.OrdinaryIdentifier -> ApplicationHead.

Inductive TypeExpr : Type :=
| NamedType : Names.OrdinaryIdentifier -> TypeExpr.

Definition NonNegDecimal : Type := { d : Float.Decimal | (0 <= Float.coefficient d)%Z }.

Inductive Expr : Type :=
| Name           : Names.OrdinaryIdentifier -> Expr
| IntegerLiteral : N -> Expr
| FloatLiteral   : NonNegDecimal -> Expr
| StringLiteral  : string -> Expr
| Unary          : UnaryOp -> Expr -> Expr
| Application    : ApplicationHead -> list Expr -> Expr.

Inductive ConstInitializer : Type :=
| ExplicitConstInit  : option TypeExpr -> NonEmpty Expr -> ConstInitializer
| InheritedConstInit : ConstInitializer.
Record ConstSpec : Type := MakeConstSpec {
  const_names : NonEmpty BindingName; const_init : ConstInitializer }.

Inductive VarInitializer : Type :=
| VarTypeOnly : TypeExpr -> VarInitializer
| VarValues   : option TypeExpr -> NonEmpty Expr -> VarInitializer.
Record VarSpec : Type := MakeVarSpec {
  var_names : NonEmpty BindingName; var_init : VarInitializer }.

Inductive TypeSpec : Type :=
| AliasSpec : BindingName -> TypeExpr -> TypeSpec
| DefSpec   : BindingName -> TypeExpr -> TypeSpec.

Inductive Declaration : Type :=
| ConstDecl : list ConstSpec -> Declaration
| VarDecl   : list VarSpec   -> Declaration
| TypeDecl  : list TypeSpec  -> Declaration.

Inductive Stmt : Type :=
| ExprStmt        : Expr -> Stmt
| DeclarationStmt : Declaration -> Stmt
| ShortVarDecl    : NonEmpty BindingName -> NonEmpty Expr -> Stmt.

Inductive Block : Type := MakeBlock : list Stmt -> Block.

Inductive TopLevelDecl : Type :=
| TopDeclaration : Declaration -> TopLevelDecl
| Main           : Block -> TopLevelDecl.
```

`T(x)`, `complex(a, b)` and `println(a, b)` are the same `Application`. `ApplicationHead` is a distinct root
so C9 can add a callable-expression head and C10 a non-name type head without touching application semantics;
no placeholder constructor lands early. Because a head is not an `Expr`, a type name never needs an expression
result, and a bare type name in expression position is an ordinary wrong-role rejection.

Literals carry magnitude only. `IntegerLiteral` is a nonnegative `N`, `FloatLiteral` a `Float.Decimal` with
nonnegative coefficient, and every negative numeric source value is `Unary UnaryMinus`. The floating exponent
keeps its own sign inside the literal grammar. C6 owns the static unary-minus slice the existing fragment and
C6 variables need; C7 owns its execution and every other unary and binary operator. Unary plus, complement,
logical not, address, dereference, receive and all binary operators stay unrepresentable.

`Blank` creates no semantic object and no variable identity. `Block` is the reusable source block root, which
C6 reaches only through `Main`. Short declarations are function-local; the package-level form is
unrepresentable. A package block is a semantic scope built by the static phase, not a source construct.

## 4. Index topology

One kind and one view per source category, refined by view where the category has variants — one `TypeSpec`
occurrence refined to alias or definition, one `BindingName` occurrence refined to named or blank, one `Expr`
occurrence, one `ApplicationHead` occurrence. There is no peer node for call versus conversion, none for
`complex` versus `println`, and no wrapper occurrence duplicating the `Main` or declaration occurrence it
contains.

```text
FileKind  PackageClauseKind  MainKind  DeclarationKind  BlockKind  StatementKind
ConstSpecKind  VarSpecKind  TypeSpecKind  BindingNameKind
ExpressionKind  ApplicationHeadKind  TypeUseKind
```

Roles:

```text
FilePackage  FileTopLevel n  MainBlock  BlockStatement n  StatementDeclaration  DeclarationSpec n
BindingNameOccurrence n  ConstSpecType  ConstInitializerExpression n
VarSpecType  VarInitializerExpression n  TypeSpecTarget  TypeNameUse
ShortRightExpression n  StatementExpression  UnaryOperand
ApplicationHead  ApplicationArgument n
```

`Index` owns one sealed structural refinement used for **every** ordinary expression child:

```text
DirectExprUseRef  =  exact parent occurrence
                  +  exact child ExprRef
                  +  exact source role
                  +  proof the child occupies that role
```

A parent plus an unchecked natural is forbidden; the `n` in a role is an indexing label inside the proof, not
a public field. Frozen refinements: `NameUseRef`, `BindingSiteRef`, `ApplicationRef`, `ApplicationHeadRef`,
`ExpressionStatementRef`. A `NameUseRef` covers ordinary identifier occurrences in the expression-name,
type-name and named-application-head roles, and binding is one fact family over that one root.

An inherited const initializer has no current expression child, so it is a distinct causal use object.
`InheritedConstUseRef` retains the exact current const spec; the exact current binding-name occurrence; the
exact enclosing const declaration; the exact nearest preceding explicit const spec in that declaration; the
exact predecessor expression occurrence at the corresponding result position; the exact optional predecessor
type occurrence; the exact current structural `iota` index; and proofs of same-declaration, nearest-
predecessor and corresponding-position. No consumer searches backward, copies source, reconstructs an equal
predecessor, reuses the predecessor's resolved result, or reuses its arity plan.

`ExprUseRef` is exactly the sum of `DirectExprUseRef` and `InheritedConstUseRef`.

## 5. Predeclared identity and semantic objects

`Names.PredeclaredName` is the complete identity catalog over every pinned `PRE-*` spelling, owning exact
identity, spelling, equality and classification from a spelling — and no semantics. C6 installs every one of
them in the outer scope. Later milestones add capabilities to those exact identities; none creates a new
predeclared identity or a second lookup path. `Typing` owns the mapping from an admitted predeclared type
object to its `BasicType`; `Names` does not.

`Compilable` owns one sealed semantic object identity with exact origin:

```text
ObjectOrigin = Predeclared exact Names.PredeclaredName
             | Source      exact named BindingSiteRef
             | Main        exact MainRef
```

Blank creates no object. There is no binding-target constructor per predeclared type, constant, variable,
alias, definition or builtin.

Object **kind** — what the object is under Go's namespace rules — is separate from **admitted
capability**, what Fido currently implements. Capabilities are proof-carrying refinements of the exact
object, never a Boolean flag bag and never a callback registry:

```text
TypeTarget  ConstantTarget  VariableTarget  CallableTarget  ContextualTarget
```

An object may be known to be a type or a builtin while its semantic rule is assigned to a later milestone;
that is the unavailable-capability boundary of §2, not a wrong-role result.

`BindingFact cp use` retains the exact `NameUseRef` and the exact resolved object from the one binding phase.
Type use, value use and application-head use consume that same fact and require different capabilities. No
consumer reruns lookup.

One binder fact over an exact binding site classifies it as `Blank`, `Declares` an exact new object, or
`Reuses` an exact existing variable object (short declaration only). A same-block short redeclaration reuses
the exact object; an outer object is shadowed by a new one; at least one nonblank short left name must be new.

## 6. Static variable identity

A named var declaration or a new short binding creates one exact compiler-owned variable object carrying one
semantic type. **That object is the static slot.** `Compilable.VariableObject cp t` is a type-indexed
refinement and projection of the exact semantic object — never an independently minted id, record, registry
entry, or equality to a reconstructed object. `Runtime` mints no slot identity and uses this exact object as
its environment key. Constants, types, blank names and `main` have no variable object.

The object identity is minted during scope construction; the type index is added only once type and
initializer facts exist.

## 7. Typing

```coq
Inductive BasicType : Type :=
| BoolBasic | IntegerBasic : Integer.Kind -> BasicType
| FloatBasic : Float.Kind -> BasicType | ComplexBasic : Complex.Kind -> BasicType | StringBasic.

Inductive SemanticType (p : Syntax.Program) : Type :=
| BasicTypeOf : BasicType -> SemanticType p
| DefinedType : Index.BoundDefinedTypeRef p -> SemanticType p.

Module Type TYPE_ENV.
  Parameter Env : Syntax.Program -> Type.
  Parameter build : forall p, ResolvedEquations p -> Acyclic p -> Env p.
  Parameter alias_target   : forall {p}, Env p -> Index.AliasSpecRef p -> SemanticType p.
  Parameter definition_rhs : forall {p}, Env p -> Index.BoundDefinedTypeRef p -> SemanticType p.
  Parameter underlying     : forall {p}, Env p -> SemanticType p -> SemanticType p.
  Parameter identicalb     : forall {p}, Env p -> SemanticType p -> SemanticType p -> bool.
  Parameter assignableb    : forall {p}, Env p -> SemanticType p -> SemanticType p -> bool.
  Parameter convertibleb   : forall {p}, Env p -> SemanticType p -> SemanticType p -> bool.
  Parameter representableb : forall {p}, Env p -> SemanticType p -> Constant -> bool.
  Parameter TypedConstant  : forall {p}, Env p -> SemanticType p -> Type.
End TYPE_ENV.
```

`underlying` is the ordinary underlying-type operation, not a permanently basic-only one, so later structural
types extend the algebra rather than replace it; C6 additionally proves every C6-admitted type has a basic
underlying type. A defined type's identity is its exact nonblank declaration reference; an alias resolves to
its target and mints none. Each decision has one executable function and one reflection theorem.

`Env` is indexed by `Syntax.Program`, built once from exact resolved equations and exact acyclicity evidence
supplied by `Compilable`. `TypedConstant` is indexed by the exact environment, because a defined typed
constant's underlying type and representability depend on it; an independently rebuilt equal environment is
not provenance. `Typing` owns no name table, no scope lookup and no runtime value.

## 8. Static phase

Package expression facts may depend on forward constants and variables, so the dependency object is built
**before** the facts that consume it.

```text
exact Input
→ scope forest + binder classifications + semantic object identities
→ all name bindings + structural uses
→ type equations / type graph
→ exact TypeEnv or exact type-cycle object
→ package const/var dependency graph from retained bindings
→ exact acyclic order or exact dependency-cycle object
→ declaration and object semantic facts + typed variable-object refinements
→ bottom-up expression / use / application facts
→ arity and context plans + unused-local result
→ diagnostics
```

Each stage is indexed by the exact prior object, so a later stage cannot pair with a foreign equal
predecessor. Short-declaration new-versus-reused classification sits in scope construction because later
statements bind against its result. Local declarations are sequential; package declarations use the retained
acyclic order. The type graph and the package const/var dependency graph stay distinct — different nodes,
edges, cycle rules and later consumers. C11 consumes this same dependency object for runtime initialization
and adds no peer graph.

Scopes and both graphs are per package, keyed by the parent directory `Compilable` already retains. Each
package block is built from all files of that package before package-level resolution, rejecting duplicates
without overwrite. The same spelling in another package is unrelated, and no cross-package name resolves while
imports are absent.

**Exact scope starts:**

| declaration | scope begins |
|---|---|
| package `const`, `var`, `type`, `main` | the package block |
| local `const` spec | after the `ConstSpec` |
| local `var` spec | after the `VarSpec` |
| short-variable new binding | after the `ShortVarDecl` |
| **local `type` spec** | **at the identifier in the `TypeSpec`** |
| predeclared object | the outer universe block |
| blank | never |

A local alias or definition therefore sees its own name; with only named right-hand sides in C6, every
self-reference and every longer cycle is invalid and diagnosed. `init` is forbidden only for C6 package
declarations; a local declaration named `init` is ordinary.

The existing proof-carrying input, work forest, member index, outcome trace and sealed core are generalized
where they own these same causal facts. No second analyzer stands beside them. Accepted and rejected outcomes
retain the same exact phase object that produced their facts and diagnostics.

## 9. Expression results

Where a result came from is not what a result **is**. There is no `NameConstantFact`, `NameVariableFact`,
`ConversionConstantFact`, `ConversionNonconstantFact`, `ComplexFact` or `PrintlnFact`.

```text
ResultAtom   = UntypedConstant exact Constant
             | TypedConstant   exact SemanticType + exact Typing.TypedConstant
             | ValueResult     exact SemanticType

ExprResult   = FixedResults exact ordered list of ResultAtom
             | Contextual   exact contextual object
```

```text
integer / float / string literal → one constant result
true / false                     → one constant result through ordinary binding
variable name                    → one value result
unary minus                      → one result
T(x)                             → one result
complex(a, b)                    → one result
println(...)                     → zero results
iota                             → contextual until its exact const use supplies iota
nil                              → contextual until a legal target type exists
```

`ExpressionFact cp expr_ref` is the sole accepted context-free fact for that exact occurrence, and its
representation is sealed. Syntax-specific theorems are projections of it, never peer stores. C9 extends this
root for multi-result functions rather than replacing it.

`UseFact cp use_ref` consumes the exact use, the exact child `ExpressionFact`, the exact retained context and
the exact target facts. It owns context defaulting, target selection, assignability, representability, result
selection and `iota`/`nil` context. It never rereads the raw child and never reruns binding.

## 10. Application

The head's exact `BindingFact` classifies the application. Both cases share source structure and result
plumbing, not typing rules:

```text
ApplicationTarget = ConversionTarget exact TypeTarget
                  | CallableTarget   exact callable object
```

One closed executable application judgment with a reflection theorem decides acceptance. It stores no callback
in any object. Admitted rules:

- **conversion** — exactly one argument, one result, through the one `Typing` convertibility and
  representability authority, retaining constant-versus-nonconstant status and rerunning no resolution;
- **`complex`** — exactly two arguments; each a constant or value of an admitted float type, or an untyped
  numeric constant representable as one; the result is `complex128` when both are untyped or `float64`-typed
  and `complex64` when both are `float32`-typed; a mismatched pair is rejected. One result;
- **`println`** — a variadic list, each argument a constant or value of an admitted basic type (bool, any
  integer kind, float, complex, string) with untyped constants defaulted first. Zero results.

Every other predeclared callable identity resolves correctly and has no C6 application rule; it receives the
exact unavailable-capability diagnostic owned by its `PRE-*` row. The package `main` object is the same case
under a different row: `main()` is valid Go, C6 has no function objects, so the head resolves to the exact
`Main` object and the boundary is owned by `SPEC-060` and `SPEC-076` at C9.

`ApplicationFact` is a dependent view of the exact `ExpressionFact`, not a second table. It exposes the exact
source application, the exact head occurrence, binding, object and target, the exact ordered argument uses and
child facts, the exact argument arity plan, the exact result vector, and proof of the reflected judgment. C7
consumes this exact fact and neither reclassifies the target nor rebuilds argument order.

`StatementEligible` is a separate executable and reflected judgment. Result count alone does not decide it: at
C6 `println(...)` is eligible, `complex(...)` is not, and a conversion is not. Later function calls become
eligible because their results may be discarded, and receive expressions join this same relation at their
milestone.

## 11. Arity

One structural `ArityPlan` over an exact sequence of expression result vectors, with only the legal Go shapes:

```text
Pairwise     each right-hand expression supplies exactly one result
SingleMulti  one right-hand expression supplies the complete target sequence
```

Context plans retain that same exact `ArityPlan` and add their own rules — const initialization, var
initialization, short declaration, application arguments. Later assignment, return and call milestones extend
these context plans and add no second arity authority. Inherited const initialization builds a new
current-spec plan from the inherited source uses under the current `iota`; it never reuses the predecessor's
resolved plan.

## 12. Runtime

C6 creates the permanent store, not a disposable scalar one. C10 adds composite, map and channel object forms
behind these same roots and extends `Place` projections; it replaces nothing public.

```coq
Module Type RUNTIME_ROOT.
  Parameter Value : forall (cp : Compilable.Program), Typing.SemanticType (source cp) -> Type.
  Parameter Observation : forall (cp : Compilable.Program), Typing.SemanticType (source cp) -> Type.
  Parameter observe : forall {cp} {t}, Value cp t -> Observation cp t.
  Parameter Place : forall (cp : Compilable.Program), Typing.SemanticType (source cp) -> Type.
  Parameter Store : Compilable.Program -> Type.
  Parameter Environment : Compilable.Program -> Type.

  Parameter Live  : forall {cp} {t}, Store cp -> Place cp t -> Prop.
  Parameter Bound : forall {cp} {t}, Environment cp -> Compilable.VariableObject cp t -> Place cp t -> Prop.
  Parameter EnvironmentWF : forall {cp}, Store cp -> Environment cp -> Prop.

  Parameter zero_value : forall cp t, Value cp t.
  Parameter materialize_constant :
    forall cp t, Typing.TypedConstant (Compilable.type_environment cp) t -> Value cp t.

  Parameter empty_store : forall cp, Store cp.
  Parameter empty_environment : forall cp, Environment cp.
  Parameter load : forall {cp} {t} {m : Store cp} {q : Place cp t}, Live m q -> Value cp t.

  Parameter Allocation : forall {cp} {t} (before : Store cp), Value cp t -> Type.
  Parameter allocate   : forall {cp} {t} (m : Store cp) (v : Value cp t), Allocation m v.
  Parameter Write      : forall {cp} {t} {m : Store cp} {q : Place cp t}, Live m q -> Value cp t -> Type.
  Parameter write      : forall {cp} {t} {m : Store cp} {q : Place cp t} (ev : Live m q) (v : Value cp t),
    Write ev v.
  Parameter Bind : forall {cp} {t} {m : Store cp} {e : Environment cp} (wf : EnvironmentWF m e)
    (x : Compilable.VariableObject cp t) {q : Place cp t} (ev : Live m q), Type.
  Parameter bind : forall {cp} {t} {m : Store cp} {e : Environment cp} (wf : EnvironmentWF m e)
    (x : Compilable.VariableObject cp t) {q : Place cp t} (ev : Live m q), Bind wf x ev.
  Parameter lookup : forall {cp} {t} {m : Store cp} {e : Environment cp} (wf : EnvironmentWF m e)
    (x : Compilable.VariableObject cp t), option { q : Place cp t | Live m q /\ Bound e x q }.
End RUNTIME_ROOT.
```

Every operation result is **indexed by its exact inputs**, so the successor cannot be paired with a foreign
predecessor and no field-plus-equality claims an input it did not consume. Each projects the exact successor
and its preservation facts (§15). `load` takes liveness evidence rather than a bare place, so an earlier or
foreign store cannot satisfy it.

Store and environment stay separate because the store maps dynamic places to values while an environment maps
compiler-owned static variables to places, and future activations carry different environments over one
shared store. There is no merged `Memory`. Allocation, write and binding stay distinct operations and are not
a second transition relation.

`Value cp t` is intrinsically typed and every public observation stays indexed by the exact type, so C10 has
no untyped scalar observation to replace. `Runtime` owns zero values, typed-constant materialization, value
representation and store/place/environment operations — and no expression evaluator.

## 13. Safe and Render

`Safe` keeps only the safety property and the sealed certificate retaining the exact `Compilable.Program`.
`Safe.Property = True` remains honest for this fragment. Runtime value representation, value
well-formedness, typed-constant materialization and every expression, statement, declaration and file
evaluator leave `Safe`: constants and types to `Typing`, static expression results to `Compilable`, runtime
values and materialization to `Runtime`, dynamic evaluation to C7's machine.

`Render` stays a direct structural function over `Syntax.Program` and performs no resolution. Shared
renderers: integer, nonnegative float, string, unary minus, `NonEmpty` lists, declarations, blocks, one
application and one expression statement.

```text
render_expr(Unary UnaryMinus e)         = "-" render_expr(e)
render_expr(Application h args)         = render_head(h) "(" join(", ", map render_expr args) ")"
render_stmt(ExprStmt e, n)              = indent(n) render_expr(e) NL
```

Rendering never asks whether a head resolves to a type or a callable, because the source bytes are identical
either way. There is no special complex, conversion or `println` renderer. Render theorems depending on
`Safe.eval_expr` move or are deleted; semantic denotation belongs to `Typing`, `Compilable` or C7. **Every
previously accepted generated byte is preserved exactly**, including `println(x)`, `uint8(300)` and
`complex(re, im)`.

File level keeps the existing bytes: the header line, a blank line, the package clause, a blank line before
each top-level declaration, and the exact final newline. Within a declaration: one tab per block depth,
comma-space separators, no trailing whitespace, direct source spelling, and an inherited const spec rendering
names only. One spec renders ungrouped; zero or two-or-more render grouped, with the zero branches exactly
`const ()`, `var ()`, `type ()` each followed by a newline.

## 14. Diagnostics

Frozen as exact Rocq constructors, codes, primary and related anchors, payloads, erasure and precedence in the
implementation's first commit, before any proof is attempted. Anchors are exact refined references. Precedence
derives from one canonical source order within each package plus the existing preflight rule; every pre-C6
program keeps its exact existing diagnostics.

| code | rule | primary anchor | payload |
|---|---|---|---|
| `FIDO-E-DUPLICATE-DECL` | one identifier bound twice in a block, including a conflicting `main` | later `BindingSiteRef` | the exact earlier site |
| `FIDO-E-MISSING-MAIN` | a main package has no entry point | the package | — |
| `FIDO-E-INIT-MISUSE` | package-level `init` used for a C6 declaration | `BindingSiteRef` | — |
| `FIDO-E-UNRESOLVED-NAME` | no object in any enclosing scope | `NameUseRef` | the spelling |
| `FIDO-E-WRONG-ROLE` | the object exists with a different Go role | `NameUseRef` | exact object + required role |
| `FIDO-E-CAPABILITY-BOUNDARY` | the object's semantic rule belongs to a later milestone | `NameUseRef` | exact object + required capability + owning ledger row |
| `FIDO-E-TYPE-CYCLE` | a type-declaration cycle | one cycle member | the exact cycle evidence |
| `FIDO-E-INIT-CYCLE` | a package const/var dependency cycle | one cycle member | the exact cycle evidence |
| `FIDO-E-FIRST-SPEC-INHERITED` | the first const spec omits its expression list | `ConstSpecRef` | — |
| `FIDO-E-ARITY` | no legal `ArityPlan` shape fits the site | the exact plan site | the exact result vectors and target count |
| `FIDO-E-SHORT-DECL-NO-NEW` | no nonblank left name is new | `ShortVarDecl` occurrence | — |
| `FIDO-E-SHORT-REDECL-TYPE` | a reused variable object gets a different type | the left `BindingSiteRef` | both exact types |
| `FIDO-E-NIL-NO-TYPE` | `nil` has no legal target type | `ExprRef` | — |
| `FIDO-E-IOTA-CONTEXT` | `iota` outside a const initializer | `ExprRef` | — |
| `FIDO-E-INIT-NOT-ASSIGNABLE` | an initializer is not assignable or representable | `ExprUseRef` | source and target types |
| `FIDO-E-UNUSED-LOCAL` | a local variable object is never read | its `BindingSiteRef` | — |
| `FIDO-E-BAD-ARGUMENT` | an argument fails the target's application rule | the exact argument occurrence | the target's precise reason |
| `FIDO-E-BAD-OPERAND` | an operand fails the operator's rule | the exact operand occurrence | the operator's precise reason |
| `FIDO-E-NOT-STATEMENT` | the expression is not statement-eligible | `ExpressionStatementRef` | why it is ineligible |

There is no generic code-plus-payload bag and no broad unsupported catch-all.
`FIDO-E-CAPABILITY-BOUNDARY` retains the exact object, the exact required capability and the exact governing
ledger row, and is distinct from both unresolved-name and wrong-role. Arity is one authority: conversion
argument counts, call argument counts, const/var initializer counts and short-declaration counts all fail
through `FIDO-E-ARITY`. Unused locals cover function-local variable objects only; package variables are
exempt.

## 15. Public interfaces and theorems

Every public fact is an abstract dependent family or a projection from the retained capability. No
client-constructible peer record may pair a reference with a target.

| query | index |
|---|---|
| `object_fact` | `ObjectRef` |
| `binder_fact` | `BindingSiteRef` |
| `binding_fact` | `NameUseRef` |
| `type_use_fact` | `NameUseRef` in a type role |
| `expression_fact` | `ExprRef` |
| `use_fact` | `ExprUseRef` |
| `application_view` | `ApplicationRef` |
| `arity_plan` | an exact plan site |
| `variable_object` | `BindingSiteRef` of a var name or new short binding |
| `package_dependency_fact` | an exact package |

Full theorem statements — binders, indices, premises and relation direction — are frozen in the same
commit for: complete predeclared outer-scope identity and ordinary shadowing; per-package scope construction
and
file-order independence; duplicate rejection without overwrite; the const/var scope-start law and the separate
local-type scope-start law beginning at the identifier; binding totality and uniqueness on accepted programs;
object kind and capability refinements; alias non-identity and exact defined-type identity; the type
environment and each reflected decision; type-cycle and dependency-cycle reflection; direct-use structural
provenance; inherited-const predecessor and current-`iota` provenance; expression-result and use-fact
totality; application target classification and result-vector exactness; statement eligibility; structural
arity matching and context-plan exactness; short binding classification and exact variable reuse; store
allocation, freshness, liveness, load and write with its frame law; environment binding, lookup and
well-formedness preservation; direct rendering and pre-C6 byte preservation.

A public theorem exposes an accepted guarantee or is required by a named later consumer. Obsolete carrier
names do not survive as aliases; for every existing theorem whose carrier changes, the implementation names
its exact replacement or states why the guarantee is subsumed. Proof helpers stay local.

## 16. Review boundaries

C6 is one milestone with two implementation reviews. A file allowlist cannot bound either, because
program-indexing `SemanticType` necessarily reaches `Safe`, `Render`, the witnesses and every downstream
theorem naming the old type.

**Semantic-root review** stops only when the whole repository is green and all of these hold: the corrected
source and index topology exist; the complete predeclared identity and binding root exist; scopes, both graphs
and the exact type environment exist; the static phase runs in the §8 order; object, expression, use,
application, arity, binder and variable facts project from the retained core; the permanent `Runtime`
value/store/place/environment roots exist; the pre-C6 fragment is mechanically migrated through every module
required for coherence; the fixed sixteen-name resolver, the old expression phase, the special source forms,
the `Safe` value and evaluator path and every compatibility wrapper are deleted; all existing generated bytes
and runtime goldens are unchanged; and `make check` plus forced-fresh verification pass. No C6 feature fixture
and no C7 runtime semantics land before this review.

**Final review** then completes C6 declaration and name behaviour, the diagnostics of §14, canonical
rendering, C6 fixtures and `LAT-077`, generated artifacts and pinned-Go evidence, and current document and
ledger truth.

## 17. Fixtures

Package and local `const`/`type`/`var` accepted; a local variable read by `println`; unused local rejected;
cross-file package declarations resolving independent of file order; two packages using the same spelling
without collision; duplicate package names rejected; local shadowing of package and predeclared names; a
shadowed `println` and a shadowed `complex` each producing the exact wrong-role diagnostic; an unshadowed
`len`, an unshadowed `var x uintptr` and a recursive `main()` each producing the exact capability-boundary
diagnostic naming its own owning row; short
declaration with no new nonblank name rejected; short redeclaration reusing its variable object; blank
declarations creating no object; `true`, `false`, the predeclared type names, `byte` and `rune` resolving
through ordinary binding; alias preserving identity; two defined declarations with equal underlying types
having distinct identity; a local type spec referring to its own name rejected as a cycle; a package constant
cycle and a package variable cycle each rejected; a package expression depending on a forward constant
accepted; a first const spec with an inherited initializer rejected; an inherited spec taking the predecessor
expression under its own `iota`; unshadowed `nil` rejected in every C6 use; `iota` outside a const initializer
rejected; unary minus on a constant and on a variable accepted, and on a string rejected; `complex(...)` as an
expression statement rejected; typed zero values for every admitted basic and defined type; every currently
accepted program rendering byte-identically after migration; generated C6 programs passing the pinned Go build
with their exact expected runtime observation.

## Preserve

`Syntax.Program` as the sole source authority and the AST as the one IR; the retained `Compilable.Program`,
`Failure` and whole-elaboration cores and their sealing; `Machine.T` uninstantiated; direct rendering and the
one `Emit.Mint.issue` authority; certified-module coverage, the whole-theory audit and controls A-E; every
sealed-capability, mint, transport and positive client control; working-tree and staged-index separation;
no-host-Python; `life.md`.

## Stop

The program-indexed `SemanticType` migration cannot complete without weakening an accepted guarantee; a C6 row
needs a construct assigned to a later milestone; a decision cannot be given one function and one reflection
theorem; a fact family cannot be projected from the retained core without a free-standing authority beside it;
the dependency object cannot be built from retained bindings before the facts that consume it; a place could
be paired with a foreign store or an environment with a foreign variable object; an unavailable capability
cannot be reported with its exact object and owning ledger row; `LAT-077` needs a diagnostic the phase cannot
produce; a run relation, evaluator or machine instantiation is needed for a C6 row; implementation needs a
placeholder, compatibility path, trusted shortcut, fuel, bound or premature future state.
