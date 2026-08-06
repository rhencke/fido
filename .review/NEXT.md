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

Record TypeIdentifier : Type := MakeTypeIdentifier {
  type_identifier : OrdinaryIdentifier;
  type_identifier_supported :
    ~ In (Names.spelling (ordinary_identifier type_identifier))
         ["any"; "comparable"; "error"; "uintptr"]
}.

Record OperandIdentifier : Type := MakeOperandIdentifier {
  operand_identifier : OrdinaryIdentifier;
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
| ComplexLiteral        : Complex.Decimal -> Expr
| Convert               : TypeExpr -> Expr -> Expr.

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
| Println         : list Expr -> Stmt
| DeclarationStmt : Declaration -> Stmt
| ShortVarDecl    : IdentifierList -> ExpressionList -> Stmt.

Inductive Block : Type := MakeBlock : list Stmt -> Block.

Inductive TopLevelDecl : Type :=
| TopDeclaration : Declaration -> TopLevelDecl
| Main           : Block -> TopLevelDecl.
```

`TypeIdentifier` and `OperandIdentifier` exist because C6 implements neither `any`/`comparable`/`error`/
`uintptr` nor function values. A raw identifier there would make **valid Go representable and then rejected**,
which violates exact admissibility. These are temporary source boundaries priced in `.review/scope.tsv`
`SR-010` and `SR-011`. A user declaration may still bind those spellings; only the C6 type-use and operand
source forms are restricted, which deliberately gives up their shadowed uses until the full roots land. No
special function type for `main` is added to dodge the boundary.

`Block` is the **`main` function body only**. A package block is a semantic scope built by the static phase,
not a source construct. Short variable declarations are function-local only; the package-level form is
unrepresentable.

**Fixed callee spellings.** `Stmt.Println` renders `println(...)` and `ComplexLiteral` renders
`complex(re, im)`. Because C6 introduces shadowing, the static phase establishes two semantic use edges,
`PrintlnCalleeUseRef` and `ComplexLiteralCalleeUseRef`, each resolving through the same scope relation as
every other name. An accepted program using either form proves the use resolves to the corresponding
predeclared object; a shadowing constant, variable, alias or defined type yields the exact wrong-role
diagnostic. These names are not hardwired outside the binding phase, `Render` never reruns resolution, no
generic call expression appears, and declarations named `println` or `complex` remain legal. C7 owns call and
output behaviour and closes `PRE-31` and `PRE-42`.

## 3. Index — one node per source occurrence

```text
FileKind  PackageClauseKind  MainKind  DeclarationKind  BlockKind  StatementKind
ConstSpecKind  VarSpecKind  AliasSpecKind  DefSpecKind  DeclaredNameKind  BlankKind
ExpressionKind  TypeUseKind
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
TypeSpecName  TypeSpecTarget  ShortDeclName n  ShortDeclValue n  PrintlnArgument n
ConversionTarget  ConversionOperand
```

No source child exists for the fixed `println` or `complex` spellings; their callee uses are semantic edges
from the enclosing source reference.

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
| `PrintlnCalleeFact` | `PrintlnCalleeUseRef` | `println_callee_fact cp r` |
| `ComplexLiteralCalleeFact` | `ComplexLiteralCalleeUseRef` | `complex_callee_fact cp r` |

Public observations: binding target; binding package and scope; resolved source type; semantic type;
constant status and exact constant; nonconstant value type; use target type; defaulting and representability
result; short-LHS new-or-existing classification; slot type and exact declaring source reference; and each
special callee's exact predeclared target. Every observation has a theorem tying it to the retained phase.

Binding target universe: the eighteen admitted predeclared type objects; `true`; `false`; `iota`; `nil`; the
binding-only entries for `complex` and `println`; exact package and local constants and variables; exact
alias and defined-type declarations; and the exact package `main` binding, present for role diagnostics even
though C6 operand syntax cannot name it as a value. **This is the C6 subset, not the whole predeclared
universe** — every other predeclared function arrives at its own milestone.

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
reconstructs a phase; the static phase separately proves the fixed `println` and `complex` forms resolve to
their predeclared objects.

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

## 12. `LAT-077` — the exact unused-local rule

Package variables are exempt. Only function-local regular variables and new short bindings are checked. A
right-hand operand use counts as a read. An existing slot appearing only on a short-declaration left side
does **not** count as a read. Blank never binds. The gate is discharged from the retained exact use facts,
never by a syntax rescan.

## 13. Fixtures

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
