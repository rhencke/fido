# C6 — Names, types, scopes, facts, values and the scalar memory root

Review: contract

Goal:
C6 lands exact binding and use roles, the one program-indexed type algebra, the admitted predeclared subset,
static slots, typed values, typed places, and one causal scalar memory root. It defines **no run relation and
no concrete `Machine.T`**; C7 builds the first machine. 66 closure rows and 22 latitude rows carry
`milestone` `C6`; `LAT-077` is the only acceptance gate.

## 1. Module ownership and Dune order

```text
Decimal Integer Float Complex FilePath ModulePath Version Collections Names Syntax Index Typing
Compilable Machine Runtime Safe Render Emit
```

`Typing` imports `Index` and **neither `Compilable` nor `Runtime`**. `Runtime` sits after `Compilable` and
before `Safe`. Owners: `Names` ordinary/type/operand identifier refinements; `Syntax` the AST; `Index`
occurrences and refined references; `Typing` the type algebra, its source-indexed environment and every type
decision; `Compilable` the retained static phase, diagnostics and public fact queries; `Runtime` values,
slots, places and memory; `Safe` the safety capability only; `Render` direct rendering.

## 2. Source boundary

```coq
Record OrdinaryIdentifier : Type := MakeOrdinary {
  ordinary_identifier : Names.Identifier;
  ordinary_not_blank  : Names.spelling ordinary_identifier <> "_"%string
}.

(* One authority for "spellings C6 cannot resolve to a type it implements". *)
Definition unimplemented_type_names : list string := ["any"; "comparable"; "error"; "uintptr"].

Record TypeIdentifier : Type := MakeTypeIdentifier {
  type_identifier : OrdinaryIdentifier;
  type_identifier_supported :
    ~ In (Names.spelling (ordinary_identifier type_identifier)) unimplemented_type_names
}.

Record OperandIdentifier : Type := MakeOperandIdentifier {
  operand_identifier : OrdinaryIdentifier;
  operand_identifier_supported :
    ~ In (Names.spelling (ordinary_identifier operand_identifier)) unimplemented_type_names;
  operand_identifier_not_main :
    Names.spelling (ordinary_identifier operand_identifier) <> "main"%string
}.

Inductive NameOrBlank : Type :=
| DeclaredName : OrdinaryIdentifier -> NameOrBlank
| BlankName    : NameOrBlank.

Inductive TypeExpr : Type :=
| NamedType : TypeIdentifier -> TypeExpr.

Inductive Expr : Type :=
| Name                  : OperandIdentifier -> Expr
| IntegerLiteral        : N -> Expr
| NegatedIntegerLiteral : N -> Expr
| StringLiteral         : string -> Expr
| FloatLiteral          : Float.Decimal -> Expr
| Apply                 : Application -> Expr
with Application : Type :=
| MakeApplication : Expr -> list Expr -> Application.

Record IdentifierList : Type := MakeIdentifierList {
  first_identifier : NameOrBlank; more_identifiers : list NameOrBlank }.
Record ExpressionList : Type := MakeExpressionList {
  first_expression : Expr; more_expressions : list Expr }.

Inductive ConstInitializer : Type :=
| ExplicitConstInitializer  : option TypeExpr -> ExpressionList -> ConstInitializer
| InheritedConstInitializer : ConstInitializer.
Record ConstSpec : Type := MakeConstSpec {
  const_names : IdentifierList; const_initializer : ConstInitializer }.

Inductive VarInitializer : Type :=
| VarTypeOnly : TypeExpr -> VarInitializer
| VarValues   : option TypeExpr -> ExpressionList -> VarInitializer.
Record VarSpec : Type := MakeVarSpec {
  var_names : IdentifierList; var_initializer : VarInitializer }.

Inductive TypeSpec : Type :=
| AliasSpec : NameOrBlank -> TypeExpr -> TypeSpec
| DefSpec   : NameOrBlank -> TypeExpr -> TypeSpec.

Inductive Declaration : Type :=
| ConstDecl : list ConstSpec -> Declaration
| VarDecl   : list VarSpec   -> Declaration
| TypeDecl  : list TypeSpec  -> Declaration.

Inductive Stmt : Type :=
| ExpressionStatement : Application -> Stmt
| DeclarationStmt     : Declaration -> Stmt
| ShortVarDecl        : IdentifierList -> ExpressionList -> Stmt.

Inductive Block : Type := MakeBlock : list Stmt -> Block.

Inductive TopLevelDecl : Type :=
| TopDeclaration : Declaration -> TopLevelDecl
| Main           : Block -> TopLevelDecl.
```

### One application root

`complex(a, b)`, `println(a, b)` and `T(x)` are **one source shape** — `head(argument, …)` — and differ
only after the exact head occurrence resolves. `Application` is therefore the basic source object. The
dedicated `ComplexLiteral`, `Println` and `Convert` constructors are **deleted**, with no alias or wrapper.
`Complex.Decimal` survives as a semantic constant and value representation; it is not a source constructor.

Source construction does not decide whether a head is a type or a callable. Static resolution of that exact
head occurrence decides the application kind, and no reconstructed equal application, head or argument may
substitute for the retained occurrence.

`ExpressionStatement` carries an exact `Application`, so a non-application expression statement is
unrepresentable rather than rejected. Statement eligibility is a *fact*, not a spelling: an application is a
valid expression statement only when its retained target is **callable**, never merely because its spelling
has parentheses. A conversion used as a statement is rejected with an exact diagnostic. Future
receive-expression statements join the same eligibility relation rather than replacing it.

`OperandIdentifier` excludes `main`, `any`, `comparable`, `error` and `uintptr`, because with one application
root a conversion head **is** an operand: admitting those spellings would make valid Go representable and
then rejected, violating exact admissibility. That also makes `main()` unrepresentable, which is a valid Go
call — the widened price is `SR-010`. `TypeIdentifier` excludes the four unimplemented type names for the
declaration positions that still take a type. Both are temporary source boundaries priced in
`.review/scope.tsv`. A user declaration may still bind any of those spellings; only these source forms are
restricted, which deliberately gives up their shadowed uses until the full roots land. No special function
type for `main` is added to dodge the boundary.

`Block` is the **`main` function body only**. A package block is a semantic scope built by the static phase,
not a source construct. Short variable declarations are function-local only; the package-level form is
unrepresentable.

## 3. Index — one node per source occurrence

```text
FileKind  PackageClauseKind  MainKind  DeclarationKind  BlockKind  StatementKind
ConstSpecKind  VarSpecKind  AliasSpecKind  DefSpecKind  DeclaredNameKind  BlankKind
ExpressionKind  ApplicationKind  TypeUseKind
```

`DeclarationKind` is reused for ordinary const/var/type declarations once the old `Decl` is deleted; there is
no `DeclarationKind'`. There is no `TopLevelDeclKind` — a `Main` or ordinary declaration **is** the top-level
occurrence, and `TopLevelDeclRef` is a refined sum of `MainRef` and top-level `DeclarationRef`. There is no
`NameExprKind` — a name expression is an `ExpressionKind` and `NameExprRef` refines `ExprRef` by its exact
view. `TypeUseKind` replaces `TypeNameKind` with no compatibility alias. `Index.View` gains one constructor
per kind.

Roles:

```text
FilePackage  FileTopLevel n  MainBlock  BlockStatement n  StatementDeclaration  DeclarationSpec n
ConstSpecName n  ConstSpecType  ConstSpecValue n  VarSpecName n  VarSpecType  VarSpecValue n
TypeSpecName  TypeSpecTarget  ShortDeclName n  ShortDeclValue n
ApplicationHead  ApplicationArgument n  ExpressionStatementApplication
```

There is **one** node kind and view per application occurrence — no second node for "call", "conversion",
`complex` or `println` over the same source. The **roles** `PrintlnArgument`, `ConversionTarget` and
`ConversionOperand`, and the references `PrintlnCalleeUseRef` and `ComplexLiteralCalleeUseRef`, are all
**deleted**: each was a special name for an application child. (The surviving `ConversionTarget` in §7 is an
`ApplicationTarget` constructor, a different thing in a different namespace.) The `n` in a role is an
indexing label only; every public use reference is an intrinsic validated child reference, never a parent
plus an unchecked natural.

Refined application references, each retaining the exact parent, exact child, exact role, and proof the child
occupies that role:

```text
ApplicationRef  ApplicationHeadRef  ApplicationArgumentRef  ExpressionStatementApplicationRef
```

**Short declarations.** `ShortLhsRef p` refines a name-or-blank occurrence inside a `ShortVarDecl`. The
static phase classifies every nonblank one as exactly `NewShortBinding` or `ExistingSameBlockSlot`. An
outer-block binding is **not** a redeclaration — the short declaration creates a new binding in the current
block. A same-block existing variable keeps its exact slot. Blank creates neither. The earlier
`VariableNameRef` refinement over `declared_by_var_or_short = true` is **deleted**: it wrongly treated every
short left name as a declaration.

**Use edges carry structural validity.** `ExprUseRef` is abstract, minted only from an exact child `ExprRef`,
its validated parent and its exact role, so an invalid parent/role/position combination is unrepresentable. A
constructor taking a generic `StmtRef` and a free `nat` is forbidden. Public projections expose the retained
parent, role and child.

`InheritedConstUseRef` is abstract and retains: the exact current `ConstSpecRef`; the exact current identifier
occurrence (not a free position); the exact enclosing `ConstDecl`; the exact nearest preceding explicit
`ConstSpecRef` in that same declaration; the exact predecessor expression child at the corresponding
position; the exact optional predecessor type child; the current spec's structural index used as `iota`; and
proofs of the nearest-predecessor and same-position relations. The static phase builds it once; no consumer
searches backward, recomputes the predecessor, copies the expression, or reuses its resolved value.

## 4. Scopes and graphs are per package

A program may hold several command packages in different directories, so the package identity is the
parent-directory key `Compilable` already retains. `Compilable.StaticPhase` holds a `PackageMap` of
package-static objects; each owns its package block, the declarations from exactly that package's files, its
function-body scope, its type graph and environment, its const/var dependency object, and its bindings,
facts, slots and diagnostics. The same spelling may appear in different packages without collision, and no
cross-package name resolves while imports are absent.

Construction, independently per package: collect that package's names from all its files; reject duplicates
without overwrite; resolve its declarations against the complete package block.

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

A local alias or definition therefore **sees its own name**. With only named right-hand sides in C6, every
self-reference and every longer alias/definition cycle is invalid and diagnosed. `init` is forbidden only for
C6 package const/var/type declarations; a local declaration named `init` is ordinary.

The type-declaration graph and the const/var dependency object are **separate**, both per package. The
dependency object's edges come from retained bindings and use facts, never from rereading syntax; it
distinguishes constant and variable rules and retains exact acyclic evidence or exact cycle evidence. C11
consumes this same object for imports, `init` and runtime order, and builds no peer.

## 5. Typing — algebra and source-indexed environment

```coq
Inductive BasicType : Type :=
| BoolBasic | IntegerBasic : Integer.Kind -> BasicType
| FloatBasic : Float.Kind -> BasicType | ComplexBasic : Complex.Kind -> BasicType | StringBasic.

Inductive SemanticType (p : Syntax.Program) : Type :=
| BasicTypeOf : BasicType -> SemanticType p
| DefinedType : Index.BoundDefinedTypeRef p -> SemanticType p.

Module Type TYPE_ENV.
  Parameter Env : Syntax.Program -> Type.
  Parameter build : forall p, ResolvedTargets p -> Acyclic p -> Env p.
  Parameter alias_target    : forall {p}, Env p -> Index.AliasSpecRef p -> SemanticType p.
  Parameter definition_rhs  : forall {p}, Env p -> Index.BoundDefinedTypeRef p -> SemanticType p.
  Parameter underlying_basic : forall {p}, Env p -> SemanticType p -> BasicType.
  Parameter identicalb   : forall {p}, Env p -> SemanticType p -> SemanticType p -> bool.
  Parameter assignableb  : forall {p}, Env p -> SemanticType p -> SemanticType p -> bool.
  Parameter convertibleb : forall {p}, Env p -> SemanticType p -> SemanticType p -> bool.
  Parameter representableb : forall {p}, Env p -> SemanticType p -> Constant -> bool.
  Parameter TypedConstant : forall {p}, Env p -> SemanticType p -> Type.
End TYPE_ENV.
```

`Env` is indexed by `Syntax.Program`, never by `Compilable.Program`, because `Typing` precedes `Compilable`.
`underlying_basic` is **total** — every admitted C6 type has one basic underlying type, so there is no
optional `core_type` and no `core_type` name at all. `zero_value` is **not** here: `Typing` decides types,
`Runtime` owns values.

`TypedConstant` is indexed by the exact environment, because a defined typed constant's representability
depends on it and cannot be validated from `p` and `t` alone. A defined typed constant retains its exact
defined identity together with an intrinsically valid value of the exact underlying basic type. Aliases
resolve to their target and mint no identity. Every conversion, defaulting, exact-value and denotation
function takes the same environment; no standalone `TypedConstant p t` survives. `Compilable.Program`
projects `type_environment cp` from its retained phase, and `Runtime` materialization consumes
`TypedConstant (type_environment cp) t`.

Each Boolean decision has one relation and one reflection theorem (§9). No proof-only relation sits beside an
unrelated checker.

## 6. `STATIC_PHASE` — a dependent causal chain

The old expression `Phase` and its constructible fact records are **absorbed and deleted** in the same
semantic-root implementation. `Compilable.Core` retains exactly one `core_static`; accepted and rejected
results retain that same object and diagnostics are projections of it.

```coq
Module Type STATIC_PHASE.
  Parameter Scopes    : forall {p}, Input p -> Type.
  Parameter TypeBind  : forall {p} {i : Input p}, Scopes i -> Type.
  Parameter TypeGraph : forall {p} {i : Input p} {s : Scopes i}, TypeBind s -> Type.
  Parameter TypeEnvOf : forall {p} {i} {s} {tb : TypeBind s}, TypeGraph tb -> option (Typing.Env p).
  Parameter Facts     : forall {p} {i} {s} {tb} (tg : TypeGraph tb), Type.
  Parameter Slots     : forall {p} {i} {s} {tb} {tg}, Facts tg -> Type.
  Parameter InitGraph : forall {p} {i} {s} {tb} {tg} {f}, Slots f -> Type.
  Parameter StaticPhase : forall {p}, Input p -> Type.
  Parameter build_static_phase : forall {p} (i : Input p), StaticPhase i.
  Parameter phase_scopes : forall {p} {i} (ph : StaticPhase i), Scopes i.
  Parameter phase_typebind : forall {p} {i} (ph : StaticPhase i), TypeBind (phase_scopes ph).
  Parameter phase_typegraph : forall {p} {i} (ph : StaticPhase i), TypeGraph (phase_typebind ph).
  Parameter phase_facts : forall {p} {i} (ph : StaticPhase i), Facts (phase_typegraph ph).
  Parameter phase_slots : forall {p} {i} (ph : StaticPhase i), Slots (phase_facts ph).
  Parameter phase_initgraph : forall {p} {i} (ph : StaticPhase i), InitGraph (phase_slots ph).
  Parameter phase_diagnostics : forall {p} {i}, StaticPhase i -> list (DiagnosticReason p).
End STATIC_PHASE.
```

Each stage is **indexed by the exact prior object**, so a later stage cannot be paired with a foreign equal
predecessor. The order is: exact `Input` → per-package scopes and duplicate outcomes → binding results for
type uses and the two special callee uses → per-package type graphs → `Typing.Env` or exact cycle failure →
expression and use facts → slot and short-LHS classifications → per-package const/var dependency objects →
diagnostics.

## 7. Fact families

Each family is queried from the accepted capability and its representation is sealed. No client can pair an
arbitrary reference with an arbitrary target.

| family | index | production query |
|---|---|---|
| `BindingFact` | `NameExprRef` | `binding_fact cp r` |
| `TypeUseFact` | `TypeUseRef` | `type_use_fact cp r` |
| `ExpressionFact` | `ExprRef` | `expression_fact cp r` |
| `UseFact` | `ExprUseRef` | `use_fact cp r` |
| `BlankUseFact` | `BlankRef` | `blank_use_fact cp r` |
| `SlotFact` | `DeclaredNameRef` of a var spec | `slot_fact cp r` |
| `ShortLhsFact` | `ShortLhsRef` | `short_lhs_fact cp r` |
| `ApplicationFact` | `ApplicationRef` | `application_fact cp r` |

Public observations: binding target; binding package and scope; resolved source type; semantic type;
constant status and exact constant; nonconstant value type; use target type; defaulting and representability
result; short-LHS new-or-existing classification; slot type and exact declaring source reference. Every
observation has a theorem tying it to the retained phase.

**One application fact, no per-builtin stores.** There is no `CallFact`, `ConversionFact`, `ComplexFact` or
`PrintlnFact`; builtin-specific theorems are consequences of `ApplicationFact`, not peer authorities. Its
projections expose, without making it constructible: the exact retained head occurrence; the exact head
binding/type result; the exact `ApplicationTarget`; the exact ordered argument occurrences; each argument's
retained context-free fact; each argument-use fact; the **exact ordered result-type vector**; proof that the
target's application rule accepts those arguments; and the exact context where result arity is consumed.

```text
ApplicationTarget = ConversionTarget <exact type object>
                  | CallableTarget   <exact callable object>
```

Both refine the **exact retained binding result** — no string tag, numeric callable id, registry lookup or
independently assembled target. A `CallableTarget` is proof-carrying. At C6 its members are `complex` and
`println`; declared functions, methods and further builtins extend the same path at their own milestones. A
predeclared builtin may be callable **without** having an ordinary first-class Go function type.

Result vectors are exact ordered lists, never a Boolean has-value flag: `complex(…)` one result,
`println(…)` **zero**, `T(x)` one. Value contexts consume the vector and enforce their own arity. An
expression statement does **not** require zero results — Go permits discarding them — it requires that the
target be callable. Short declarations and const/var initializers consume the same vector authority and grow
no peer arity logic.

The static application relation is one executable decision with a reflection theorem, closed over the target:

- **conversion** — exactly one argument in C6; consumes the retained argument fact; uses the one
  `Typing.Env`; applies the one convertibility and representability authority; one result type; retains
  constant-versus-nonconstant status; reruns no name resolution, type resolution or constant evaluation.
- **`complex`** — exactly two arguments. Each must be a constant or value of an admitted float type, or an
  untyped numeric constant representable as one; the result is `complex128` when both are untyped or
  `float64`-typed, and `complex64` when both are `float32`-typed; a mismatched pair is rejected. One result.
  No output effect. No dedicated source or renderer path.
- **`println`** — a variadic ordered list; each argument must be a constant or value of an admitted basic
  type — bool, any integer kind, float, complex or string — with untyped constants defaulted first.
  **Zero** results. No C6 runtime step and no output event; C7's machine gives it output behaviour. No
  dedicated source or renderer path.

Binding target universe: the eighteen admitted predeclared type objects; `true`; `false`; `iota`; `nil`; the
callable entries for `complex` and `println`; exact package and local constants and variables; exact alias
and defined-type declarations; and the exact package `main` binding, present for role diagnostics though C6
operand syntax cannot name it. **This is the C6 subset, not the whole predeclared universe** — every other
predeclared function arrives at its own milestone. Head resolution uses the ordinary scope relation only;
there is no builtin spelling check beside it, and `complex` or `println` may be shadowed exactly like any
other predeclared object.

## 8. `Runtime` — one causal memory root

A place minted in one history must not pair with a foreign or earlier store, and a private numeric id does
not repair that: equal counters in sibling histories are not the same allocation. One `Memory cp` owns the
store, the environment and their invariant.

```coq
Module Type RUNTIME_ROOT.
  Parameter Value : forall (cp : Compilable.Program), Typing.SemanticType (source cp) -> Type.
  Parameter ValueView : forall {cp} {t}, Value cp t -> ScalarObservation.
  Parameter Slot  : forall (cp : Compilable.Program), Typing.SemanticType (source cp) -> Type.
  Parameter Place : forall (cp : Compilable.Program), Typing.SemanticType (source cp) -> Type.
  Parameter Memory : Compilable.Program -> Type.
  Parameter Live  : forall {cp} {t}, Memory cp -> Place cp t -> Prop.
  Parameter Bound : forall {cp} {t}, Memory cp -> Slot cp t -> Place cp t -> Prop.

  Parameter zero_value : forall cp t, Value cp t.
  Parameter materialize_constant :
    forall cp t, Typing.TypedConstant (Compilable.type_environment cp) t -> Value cp t.
  Parameter slot_of_fact :
    forall cp (r : Index.DeclaredNameRef (source cp)) (f : Compilable.SlotFact cp r),
      Slot cp (Compilable.slot_type f).

  Parameter empty_memory : forall cp, Memory cp.
  Record Allocation (cp : Compilable.Program) (t : Typing.SemanticType (source cp)) : Type :=
    MakeAllocation {
      alloc_before : Memory cp; alloc_value : Value cp t;
      alloc_after  : Memory cp; alloc_place : Place cp t;
      alloc_live   : Live alloc_after alloc_place;
      alloc_extends : forall t' (q : Place cp t'), Live alloc_before q -> Live alloc_after q }.
  Parameter allocate : forall {cp} {t} (m : Memory cp) (v : Value cp t),
    { a : Allocation cp t | alloc_before a = m /\ alloc_value a = v }.
  Parameter load  : forall {cp} {t} {m : Memory cp} {q : Place cp t}, Live m q -> Value cp t.
  Parameter write : forall {cp} {t} {m : Memory cp} {q : Place cp t}, Live m q -> Value cp t ->
    { m' : Memory cp | (forall t' r, Live m r -> Live m' r) /\ WriteAgrees m' q }.
  Parameter empty_environment_of : forall cp, Memory cp.
  Parameter bind_slot : forall {cp} {t} {m : Memory cp} {q : Place cp t}, Live m q -> Slot cp t ->
    { m' : Memory cp | Bound m' (…) q /\ forall t' s r, Bound m s r -> Bound m' s r }.
  Parameter lookup_slot : forall {cp} {t} (m : Memory cp) (s : Slot cp t),
    option { q : Place cp t | Live m q /\ Bound m s q }.
End RUNTIME_ROOT.
```

`load` and `write` take **liveness evidence**, not a bare place, so a foreign or earlier memory cannot
satisfy them. `bind_slot` cannot create a dangling entry. `lookup_slot` returns liveness for that exact
memory. `Slot` is projected from the exact `SlotFact`; clients never mint source-slot identities. `ValueView`
exposes the scalar observation C7 needs — an abstract value with no observation API is not a foundation.
Constants, types, blank names, short redeclarations and `main` create no slot; a new short binding creates
one; a same-block redeclaration reuses the exact existing slot. `Runtime` alone owns zero values and constant
materialization; `Safe` keeps only the safety capability.

## 9. Diagnostics and theorems

Both are frozen as exact Rocq surfaces in the implementation's first commit **before any proof is attempted**,
extending `Compilable.DiagnosticReason`, `DiagnosticCode`, `erase_diagnostic`, `diagnostic_primary` and
`diagnostic_related`. Anchors use exact sum references introduced only where a real shared rule exists:
`BindingSiteRef` (a declared name or a short LHS), `NameUseRef` (a name expression or a type use),
`AritySiteRef` (a const spec, var spec or short declaration), `AssignmentTargetRef`, `LocalVariableRef` (a
local var name or a new short binding), and `BindingTarget`.

Codes: `FIDO-E-DUPLICATE-DECL`, `FIDO-E-MAIN-CONFLICT`, `FIDO-E-INIT-MISUSE`,
`FIDO-E-FIRST-SPEC-INHERITED`, `FIDO-E-DECL-ARITY`, `FIDO-E-SHORT-DECL-NO-NEW`,
`FIDO-E-SHORT-REDECL-TYPE`, `FIDO-E-UNRESOLVED-NAME`, `FIDO-E-WRONG-ROLE`, `FIDO-E-TYPE-CYCLE`,
`FIDO-E-INIT-CYCLE`, `FIDO-E-NIL-NO-TYPE`, `FIDO-E-IOTA-CONTEXT`, `FIDO-E-INIT-NOT-ASSIGNABLE`,
`FIDO-E-UNUSED-LOCAL`.

Application diagnostics are **generic**, flowing through one authority rather than per-builtin paths. A head
that resolves to nothing is the ordinary `FIDO-E-UNRESOLVED-NAME`; the rest are:
`FIDO-E-NOT-APPLICABLE` (head resolves to neither a type nor a callable, anchored at the head, payload the
`BindingTarget`); `FIDO-E-CONVERSION-ARITY` (anchored at the application, payload expected and found counts);
`FIDO-E-CALL-ARITY` (same shape, for a callable target); `FIDO-E-BAD-ARGUMENT` (anchored at the exact
argument occupying the failing position, payload the target's precise reason); `FIDO-E-RESULT-ARITY`
(anchored at the consuming use, payload the exact result vector and the arity the context required);
`FIDO-E-CONVERSION-AS-STATEMENT` (anchored at the expression statement's application). A builtin contributes
a precise payload for its own rejected argument rule; it never contributes a separate diagnostic authority.

A wrong-role target may be predeclared and carry no declaration reference, so its payload is a
`BindingTarget`. A short redeclaration anchors at a `ShortLhsRef`. Arity applies to short declarations too.
An inferred or short-declaration assignment target may have no `TypeUseRef`. Unused locals cover local var
names and new short bindings only; package variables are exempt. Precedence derives from **one canonical
source order within each package** plus the existing preflight rule; migrated conversion and defaulting
diagnostics share that one order with the new declaration diagnostics, so no blanket "legacy first" rule
applies. Every pre-C6 program keeps its exact existing diagnostics.

Theorem statements are frozen the same way and in the same commit — full binders, indices, premises and
relation direction — covering: per-package scope construction and file-order independence; duplicate
rejection without overwrite; the const/var scope-start law; **the separate local-type scope-start law, which
begins at the identifier**; short-LHS classification and slot continuity; blank nonbinding; binding, type and
use totality on accepted programs; alias and defined-type identity; type-cycle and init-cycle reflection;
each type-decision reflection; inherited-const predecessor and current-`iota` provenance; typed value and
materialization laws; memory allocation, liveness, load, write, binding, freshness and preservation; direct
rendering and pre-C6 byte preservation. The false name `local_scope_starts_after_spec` does not survive.

A public theorem must expose an accepted guarantee directly or be required by a named later consumer.
**There is no blanket survival rule for existing theorem names**: accepted guarantees are preserved, obsolete
carrier names are not, and for every existing theorem whose carrier changes the implementation names its
exact replacement or states why the guarantee is subsumed. No compatibility aliases.

## 10. Rendering

`Render` stays a direct structural function over `Syntax.Program`. It never consults binding facts or
reconstructs a phase.

There is **one** application rendering equation, and no dedicated conversion, `complex` or `println` path:

```text
render_expr(Apply (MakeApplication h args)) = render_expr(h) "(" join(", ", map render_expr args) ")"
render_stmt(ExpressionStatement a, n)       = indent(n) render_expr(Apply a) NL
```

Rendering never reruns resolution to decide whether an application is a conversion or a call, because the
source spelling is identical either way. That is precisely why one root is correct — the old split invented
three renderers for one set of bytes. Current accepted programs therefore render **byte-identically**:
`println(x)`, `uint8(300)` and `complex(re, im)` all come out of this one equation.

File level keeps the existing bytes exactly: the header line, a blank line, the package clause, a blank line
before each top-level declaration, and the exact final newline. Within a declaration: one tab per block
depth, comma-space separators, no trailing whitespace, direct source spelling, and an inherited const spec
rendering names only.

One spec renders ungrouped. Zero or two-or-more render grouped, with the zero branches exactly
`const ()`, `var ()`, `type ()` each followed by a newline.

## 11. Two implementation reviews, bounded by result

File allowlists cannot work: program-indexing `SemanticType` necessarily changes `Safe`, `Render`, the
witnesses and every downstream theorem mentioning the old type.

**Semantic-root review** stops when: the corrected source and `Index` topology exist; per-package scopes and
exact use edges exist; the permanent static-phase chain exists; the type environment and reflected decisions
exist; facts project from the retained core; the causal `Runtime` memory root exists; the pre-C6 fragment is
mechanically migrated through every module needed for a green tree; the fixed resolver, old phase, unindexed
value and pure evaluator are deleted; no compatibility wrapper remains; all existing generated bytes and
runtime goldens remain exact; and `make check` plus forced-fresh verification pass. That migration may touch
every module mechanically required for coherence. It may **not** add C6 feature fixtures or begin C7.

**Final review** then completes declaration and name behaviour, structured diagnostics, canonical rendering,
C6 fixtures and `LAT-077`, generated artifacts and pinned-Go evidence, and current documentation and ledger
truth.

## 12. The C6/C7 application boundary

C6 owns application **source structure**, exact identities and roles, ordinary head binding, type-versus-
callable classification, static argument acceptance, exact result-type vectors, application and use facts,
static diagnostics, and canonical rendering. C6 defines no run relation and performs no application.

C7 owns evaluation order, argument evaluation, conversion execution, callable execution, `println` output
actions, runtime faults, and the first concrete `Machine.T`. It **consumes** the exact C6 `ApplicationFact`
and the exact source occurrences: it does not rediscover the target, rebuild argument order, or introduce a
second call or conversion semantics.

## 13. `LAT-077` — the exact unused-local rule

Package variables are exempt. Only function-local regular variables and new short bindings are checked. A
right-hand operand use counts as a read. An existing slot appearing only on a short-declaration left side
does **not** count as a read. Blank never binds. The gate is discharged from the retained exact use facts,
never by a syntax rescan.

## 14. Deletions — no alias, wrapper or compatibility constructor

Source: `Syntax.BoolLiteral`; `Syntax.ComplexLiteral`; `Syntax.Convert`; `Stmt.Println`; `Syntax.TypeName`
(`Unqualified`) and the `type_expr_*` helpers over `Names.SupportedType`. Names: `Names.TypeName`,
`Names.SupportedType`, `Names.classify`, `Names.supported_of`, `Names.all_type_names` and every projection.
Resolver: `Compilable.predeclared_type`, `predeclared_type_of_name` and its ten `Local Notation`s. Phase: the
old expression `Phase` and its constructible expression-fact records. Runtime: `Safe.eval_expr` and the
unindexed `Safe.Value`. Index: the `PrintlnArgument`, `ConversionTarget` and `ConversionOperand` roles, the
`PrintlnCalleeUseRef` and `ComplexLiteralCalleeUseRef` references, `DeclarationKind'`, `TopLevelDeclKind`,
`NameExprKind`, `TypeNameKind` and the `VariableNameRef` refinement.

`Complex.Decimal` is **kept** as a semantic constant and value representation; only its role as a source
constructor is deleted. Current programs migrate to the ordinary-name and application forms first; the
competing paths are deleted in the same milestone. Git owns the old topology.

## 15. Fixtures

Package and local `const`/`type`/`var` accepted; a local variable read by `println`; unused local rejected;
cross-file package declarations resolving independent of file order; two packages using the same spelling
without collision; duplicate package names rejected; local shadowing of package and predeclared names;
shadowed `println` and shadowed `complex` each producing the wrong-role diagnostic; short declaration with no
new nonblank name rejected; short redeclaration reusing its slot; blank declarations creating no binding or
slot; `true`, `false`, the predeclared type names, `byte` and `rune` resolving through ordinary binding;
alias preserving identity; two defined declarations with equal underlying types having distinct identity; a
local type spec referring to its own name rejected as a cycle; package constant and package variable cycles
each rejected; a first const spec with an inherited initializer rejected; an inherited spec taking the
predecessor expression under its own `iota`; unshadowed `nil` rejected in every C6 use; `iota` outside a
const initializer rejected; typed zero values for every admitted basic and defined type; every currently
accepted program rendering byte-identically after migration; generated C6 programs passing the pinned Go
build with their exact expected runtime observation.

## Preserve

`Syntax.Program` as the sole source authority and the AST as the one IR; the retained `Compilable.Program`,
`Failure` and whole-elaboration cores and their sealing; `Machine.T` uninstantiated; `Safe.Property = True`
while the fragment has no unsafe behaviour; direct rendering and the one `Emit.Mint.issue` authority;
certified-module coverage, the whole-theory audit and controls A-E; every sealed-capability, mint, transport
and positive client control; working-tree and staged-index separation; no-host-Python; `life.md`.

## Stop

The program-indexed `SemanticType` migration cannot complete without weakening an accepted guarantee; a C6
row needs a construct assigned to a later milestone; a decision cannot be given one function and one
reflection theorem; a fact family cannot be projected from the retained core without a free-standing
authority beside it; the per-package dependency object cannot be built from retained facts without rereading
syntax; a place could be paired with a foreign memory; `LAT-077` needs a diagnostic the phase cannot produce;
a run relation, evaluator or machine instantiation is needed for a C6 row; implementation needs a
placeholder, compatibility path, trusted shortcut, fuel, bound or premature future state.
