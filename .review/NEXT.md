# C6 — Names, types, scopes, facts, values and the scalar store

Baseline: 6b2b083c5cb0e1bb767d72622c745f2e80179090
Review: contract

Goal:
C6 lands exact binding and use roles, the one type algebra, the predeclared universe, static slots, dynamic
places, typed closed runtime values, the first scalar-cell store slice, and the expression-fact/use boundary
that declarations and variables need.

**C6 instantiates no `Machine.T`.** It builds the static facts, typed values, slots, places, store and exact
closed-command **start facts** that the runtime consumes. C7 is the first concrete machine for a
`Safe.Program`: it consumes C6's retained facts and store roots, gives the existing expression/`println`
fragment one run relation, and adds the C7 expression, output, order and fatal-panic slice. C11 generalizes
starts and initialization to imports and package dependency order.

`Safe.Property` stays `True` while the represented fragment has no unsafe behaviour, and the current pure
constant-evaluation claim is preserved — its value carrier migrates, but C6 does not delete the only current
evaluator.

## Rows and gates

66 closure rows and 22 latitude rows carry `milestone` `C6`; counts are derived from the ledgers, never
written by hand. `LAT-077` is C6's only acceptance gate. `LAT-019` and `LAT-X004` are C7. Label scopes are
C8. `GRAM-104`'s unqualified `OperandName` branch is C6; `GRAM-105`'s qualified branch is C11. `GRAM-050`
(`TypeLit`) is sum-production evidence and authorises no C6 constructor.

## Contract slices

- **SC-02** predeclared constants, constant declarations, `iota`, C6 constant initializers, defaulting and
  representability for admitted forms;
- **SC-03** package and local scopes, declarations, binding facts, static slots, blank uses, uniqueness,
  package-only export classification, predeclared shadowing;
- **SC-04** one type algebra over basic, alias and defined types, with no structural or generic case;
- **SC-05** context-free facts and exact C6 use edges, including ordinary name expressions;
- **SC-08** typed scalar cells, typed places, allocation identity and typed lookup only;
- **SC-14** C6 zero values and exact closed-command **start facts** only. The first concrete machine start is
  C7's;
- **SC-21** minimal exact public roots and disposable internals;
- **SC-22** `LAT-077` only.

## 1. Source constructor topology

`Names.Identifier` admits the spelling `_`, so it cannot be the ordinary-name type. There is exactly one
ordinary-name authority and exactly one blank constructor:

```coq
Record OrdinaryIdentifier : Type := MakeOrdinary {
  ordinary_identifier : Names.Identifier;
  ordinary_not_blank  : Names.spelling ordinary_identifier <> "_"%string
}.

Record IdentifierList : Type := MakeIdentifierList {
  first_identifier : NameOrBlank;
  more_identifiers : list NameOrBlank
}.

Record ExpressionList : Type := MakeExpressionList {
  first_expression : Expr;
  more_expressions : list Expr
}.
```

These are source-grammar carriers, not a generic collection framework. A spec's identifier list and an
explicit expression list are never empty; an empty parenthesized group is an empty `list ConstSpec`,
`list VarSpec` or `list TypeSpec`.

```coq
Inductive TypeExpr : Type :=
| NamedType : OrdinaryIdentifier -> TypeExpr.

Inductive NameOrBlank : Type :=
| DeclaredName : OrdinaryIdentifier -> NameOrBlank
| BlankName    : NameOrBlank.

Inductive Expr : Type :=
| Name                  : OrdinaryIdentifier -> Expr
| IntegerLiteral        : N -> Expr
| NegatedIntegerLiteral : N -> Expr
| StringLiteral         : string -> Expr
| FloatLiteral          : Float.Decimal -> Expr
| ComplexLiteral        : Complex.Decimal -> Expr
| Convert               : TypeExpr -> Expr -> Expr.

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

No `with` group is needed: `Stmt` reaches `Declaration` but not `Block`, so every type above is a plain
inductive in dependency order. `VarInitializer` gives "no type and no values" no constructor. A nested
`Main` is **unrepresentable**, not rejected after construction. `Syntax.File` carries `list TopLevelDecl`
and no compatibility alias for the old `Decl` survives. `BoolLiteral` is deleted; `true` and `false` are
ordinary resolved names.

An `InheritedConstInitializer` in the **first** spec of a group is representable source and is rejected with
an exact diagnostic; it is never silently read as an empty expression list.

## 2. Exact references and roles

`Index.Kind` gains structural kinds so no reference stands for two semantically different objects. The
refined public references are at least:

```text
BlockRef            ConstSpecRef        VarSpecRef          AliasSpecRef
DefinedTypeSpecRef  BoundDefinedTypeRef DeclaredNameRef     VariableNameRef
BlankRef            NameExprRef         TypeUseRef          ExprUseRef
```

`BoundDefinedTypeRef` names **only** a nonblank defined-type declaration — a blank definition creates no
type identity — and `DefinedType` is defined over it, never over a reference that could also name an alias.

`Index.Role` gains exact C6 roles; the contract enumerates them rather than using one generic spec-child
role, because const inheritance, variable initialization, a type right-hand side, a declaration name and a
short declaration obey different rules:

```text
TopLevelDeclaration n     BlockStatement n        DeclarationSpec n
ConstSpecName n           ConstSpecType           ConstSpecValue n
VarSpecName n             VarSpecType             VarSpecValue n
TypeSpecName              TypeSpecTarget
ShortDeclName n           ShortDeclValue n
```

A reference remains indexed by the exact `Syntax.Program` and exact source occurrence. No spelling, list
position, rebuilt equal syntax or independently rediscovered predecessor is identity.

## 3. Inherited const use is an intrinsic causal object

`LAT-067` is not closed by representing an omitted expression list as `[]`. Each inherited constant use
retains, by construction:

- the exact current `ConstSpecRef`;
- the current spec index that determines `iota`;
- the exact value position within the current identifier list;
- the exact predecessor explicit expression reference, from the nearest preceding non-inherited spec of the
  same declaration group;
- the proof that this is the required predecessor.

The inherited use consumes the predecessor's retained **context-free expression fact** while applying the
**current** const-spec context and current `iota`. It does not copy the prior expression, reuse the prior
resolved value, search backward again, or reconstruct an equal predecessor. This is frozen as an exact
`InheritedConstUseRef` constructor of `ExprUseRef`, not left to implementation.

## 4. One retained static phase

C6 **extends the existing retained whole-elaboration object**. It creates no free-standing scope, type,
binding or slot authority beside `Compilable.Core`. One C6 static phase joins the causal chain, taking the
exact prior index/elaboration object as input and retaining by construction:

package blocks built across all files; local block and scope structure; the predeclared outer scope; the
exact type-declaration graph and its resolution result; binding targets for every admitted name use;
type-use facts; context-free expression facts; exact expression-use facts; blank-use facts; static slot
facts; C6 diagnostics.

Both the accepted `Compilable.Program` and the rejected `Compilable.Failure` retain that exact phase through
their existing core. A rejection retains the phase, not a copied diagnostic list.

Scope construction is two-stage and file-order-independent: collect every package-level declaration name
across all files of the package, rejecting duplicates; then resolve package-level declarations against the
complete package block. Local blocks are sequential — a declaration enters scope exactly where the Go rule
says, a later local declaration is not visible earlier, and local names may shadow package and predeclared
names where Go permits. `main` participates in package uniqueness though its constructor is special.
Package-scope `init` may not be introduced by a C6 const, type or var declaration. Blank names introduce no
binding.

Scope and identity-keyed tables use the pinned standard finite maps and sets. Duplicate insertion **fails**;
it never overwrites. No project-authored map storage and no list scan is a semantic authority.

## 5. Facts are indexed projections, not constructible records

A public record pairing a reference with a target can be forged. Facts are abstract dependent families
indexed by exact references, with total queries projected from the accepted capability:

```coq
BindingFact  : forall (cp : Compilable.Program), Index.NameExprRef (Compilable.source cp) -> Type.
binding_fact : forall cp (r : Index.NameExprRef (Compilable.source cp)), BindingFact cp r.
```

Type-use, expression-use, blank-use and slot facts take the same topology. Public total queries live on
`Compilable.Program` and rerun no scope construction, type resolution or expression analysis.

The binding target universe distinguishes each admitted predeclared type object; `true`; `false`; `iota`;
`nil`; an exact declared constant; an exact declared variable; an exact alias declaration; an exact
defined-type declaration; and the current `main` declaration where a package-name conflict is checked. A
value-role use cannot silently receive a type object, and a type use cannot silently receive a variable or
constant; wrong-kind resolution produces a structured diagnostic **from the retained binding object**.

A slot fact exists only for a nonblank variable declaration or a newly introduced nonblank short-declaration
name. Constants, aliases, defined types, blanks and predeclared objects have no slot constructor.

`ExprUseRef` constructors are frozen and include at least: println argument; conversion operand; explicit
const initializer; inherited const initializer; variable initializer; short-variable initializer. Every use
builder consumes the retained child `ExpressionFact` and never re-reads the raw child.

## 6. One type algebra with one environment

```coq
Inductive SemanticType (p : Syntax.Program) : Type :=
| BoolType    : SemanticType p
| IntegerType : Integer.Kind -> SemanticType p
| FloatType   : Float.Kind   -> SemanticType p
| ComplexType : Complex.Kind -> SemanticType p
| StringType  : SemanticType p
| DefinedType : Index.BoundDefinedTypeRef p -> SemanticType p.
```

A type value carrying only a declaration reference **cannot compute its own underlying type**, so every type
operation consumes the one retained C6 environment; public accepted-program queries consume the exact
`Compilable.Program` that retains it. The environment retains exact facts for alias target, defined-type
right-hand side, underlying type, core type for the C6 slice, identity, assignability, convertibility,
representability and zero value. An alias has no semantic-type constructor; it resolves to its target.

Every decision the compiler consumes has **one executable decision function and a reflection theorem**. A
proof-only relation beside a separate checker is forbidden.

The type-declaration graph is built once and retained: on success it carries acyclicity and exact
resolution; on failure an exact cycle witness and a diagnostic anchored in the declarations forming the
cycle. Package type declarations may refer forward across files; local ones obey sequential scope. With no
structural type constructor in C6, every declaration cycle is invalid.

All current typed-constant and conversion surfaces migrate to the program-indexed algebra. A typed constant
of a defined basic type retains that exact defined type while its value is represented through the exact
underlying basic type. `byte` and `rune` remain aliases of `uint8` and `int32`: they preserve source
spelling and mint no identity.

**No top-level Rocq `Parameter`.** Abstract public components live in a `Module Type` supplied by one
concrete sealed module, as the capability boundaries already do. The whole-theory assumption audit stays
empty.

## 7. Typed values, places and store

```coq
Value : forall (cp : Compilable.Program), Typing.SemanticType (Compilable.source cp) -> Type.
Place : forall (cp : Compilable.Program), Typing.SemanticType (Compilable.source cp) -> Type.
Store : Compilable.Program -> Type.

allocate : forall cp t, Store cp -> Value cp t -> Store cp * Place cp t.
load     : forall cp t, Store cp -> Place cp t -> option (Value cp t).
```

Basic constructors carry their intrinsic evidence — an integer value carries representability — and a
defined-type value carries a value of its exact underlying type without losing the defined identity. A
packed dynamic object exists only at the private map boundary and is not a second runtime-type authority.

`ObjectId` and the raw store representation are private inside the sealed implementation. Only allocation
mints an identity, and an identity is never derived from a source reference, a name, a client-supplied
natural number, a type tag or a trace position. Environment lookup is typed by the exact slot, not
`DeclaredNameRef -> option (Place p)`.

Frozen and proved: load-after-allocate; allocation freshness; no identity reuse; preservation of every
previously allocated cell; loaded value/type coherence; constants, aliases, defined-type declarations and
blanks allocate nothing; a variable slot maps only to a place of its exact static type. The full
reachable-state lookup theorem belongs with C7's machine; C6 proves the store and environment invariants
that theorem consumes.

The unindexed `Safe.Value` path migrates to this one typed authority. No peer value type is added.

## 8. Diagnostics

C6 extends the existing snapshot-indexed `DiagnosticReason`; no second diagnostic system appears. For every
class below the contract fixes the constructor, the stable code, the exact primary anchor, related anchors,
payload, erased form, and precedence relative to the others:

| code | class | primary anchor |
|---|---|---|
| `FIDO-E-UNRESOLVED-NAME` | name resolves to nothing in any enclosing scope | the name use |
| `FIDO-E-WRONG-ROLE` | object used in the wrong role | the name use |
| `FIDO-E-DUPLICATE-DECL` | duplicate declaration in one block | the later declared name |
| `FIDO-E-INIT-MISUSE` | package-scope `init` introduced by a C6 declaration | the declared name |
| `FIDO-E-FIRST-SPEC-INHERITED` | first const spec has an inherited initializer | that spec's name use |
| `FIDO-E-DECL-ARITY` | declaration name/value arity mismatch | the spec |
| `FIDO-E-TYPE-CYCLE` | type-declaration cycle | the declarations forming the cycle |
| `FIDO-E-INIT-NOT-ASSIGNABLE` | initializer not assignable or representable | the initializer expression |
| `FIDO-E-SHORT-DECL-NO-NEW` | short declaration with no new nonblank name | the short declaration |
| `FIDO-E-SHORT-REDECL-TYPE` | short redeclaration with a mismatched type | the redeclared name |
| `FIDO-E-UNUSED-LOCAL` | unused function-local variable | the declared name |
| `FIDO-E-MAIN-CONFLICT` | package `main` conflicts with another declaration | the conflicting declaration |

## 9. Rendering

The renderer stays direct over the one AST: no token layer, no parser, no raw-text escape. The contract
fixes canonical output for package and local const/var/type declaration groups; empty groups; explicit and
inherited const specs; type aliases and definitions; blocks and indentation; short declarations; ordinary
names and blanks; the migrated `main` body; and conversions through ordinary resolved type names.

Required theorems: exact ASCII/UTF-8 validity; direct source spelling; injectivity where the existing
renderer relies on it; and **byte-identical rendering of every program accepted before C6**.

## 10. Public theorem surface

These are public because C7 and later milestones consume them; only proof helpers are `Local`.

Package block construction independent of file order; duplicate rejection with no overwrite; local scope
start and sequential visibility; exact shadowing of package and predeclared names; total binding for every
accepted ordinary name use; blank never binds and never owns a slot; package-only export classification;
short-declaration same-block and new-name rules; exact predeclared resolution including `byte`, `rune`,
`true`, `false`, `iota` and `nil`; alias identity preservation; distinct defined declarations have distinct
identity; exact underlying/basic resolution; every C6 type cycle rejected; reflected identity, assignability,
convertibility and representability decisions; expression fact/use separation; exact inherited-const
predecessor and current-`iota` facts; one static slot per accepted variable name; typed zero values; store
freshness, no reuse, frame preservation and load coherence.

## 11. Deletions — no wrappers, aliases or compatibility constructors

`Syntax.BoolLiteral`; `Names.TypeName`, `Names.SupportedType`, `Names.classify`, `Names.supported_of`,
`Names.all_type_names` and every projection over them; `Syntax.TypeName` (`Unqualified`) and the
`type_expr_*` helpers built on `Names.SupportedType`; `Compilable.predeclared_type`,
`predeclared_type_of_name` and the ten `Local Notation`s fixing it. Current programs migrate through the
ordinary-name path first; the competing path is then deleted in the same milestone.

## 12. Two implementation reviews

**Semantic-root review** — stop when all are complete: corrected source constructors; exact `Index` kinds,
roles and refined references; the retained package/local scope object; the retained type environment and
cycle result; abstract dependent binding, type, expression, use, blank and slot facts; reflected decisions
and universal invariants; migration of the existing fragment to ordinary names; deletion of the closed
sixteen-name resolver and every competing name/type authority. **Do not start values, store or rendering
until this review passes.**

**Final review** — typed values; typed places and the scalar store; zero values; declaration rendering;
exact diagnostics; fixtures and `LAT-077`; generated artifacts and pinned-Go evidence; the current
documentation updates below.

No concrete `Machine.T` appears in C6.

## Documents the C6 implementation must update

`README.md` current capability; `.review/scope.tsv` row `SR-008`; `ARCHITECTURE.md`; `ROADMAP.md`;
`.review/NEXT.md`; and the affected acceptance and ledger rows. None of these is edited during contract
review, because the code has not changed yet.

## Required fixtures

Package and local `const`/`type`/`var` declarations accepted; a local variable used by the existing
`println` path; an unused local rejected with `FIDO-E-UNUSED-LOCAL`; cross-file package declarations
resolving independent of file order; duplicate package names rejected; local shadowing of package and
predeclared names where Go permits; a short declaration with no new nonblank name rejected; blank
declarations creating no binding and no slot; `true`, `false`, the predeclared type names, `byte` and `rune`
resolving through ordinary binding facts; shadowing those names changing resolution exactly; an alias
preserving identity; two distinct defined declarations with equal underlying types having distinct identity;
every C6 type-declaration cycle rejected; a first const spec with an inherited initializer rejected; typed
zero values for every admitted basic and defined type; **every currently accepted program rendering
byte-identically after migration**; and generated C6 programs passing the pinned Go build with their exact
expected runtime observation. The `LAT-019` shift-precision fixtures are C7's.

## Preserve

`Syntax.Program` as the sole source authority and the AST as the one IR; the exact retained
`Compilable.Program`, `Failure` and whole-elaboration cores, and their sealing; `Machine.T` exactly as C5
froze it, uninstantiated; direct rendering and the one `Emit.Mint.issue` authority; certified-module
coverage, the whole-theory audit and controls A-E; every sealed-capability, mint, transport and positive
client control; working-tree and staged-index separation; no-host-Python; `life.md`.

## Done

Every C6 closure and latitude row discharged or explicitly repriced under review; `LAT-077` discharged with
its exact diagnostic and fixture; no structural type, loop, closure, user function, label, panic,
concurrency, composite object, import, package initialization **or concrete machine** appears; every deleted
authority gone with no wrapper; `make prove`, `make check`, `make audit-fresh`, `make regenerate`,
`make regen-guard` pass; generated bytes change only where a newly admitted construct is actually rendered,
with goldens updated in the same commit and the differential evidence to justify them; both implementation
reviews pass; then Rob accepts C6.

## Stop

The program-indexed `SemanticType` migration cannot complete without weakening an existing theorem; a C6 row
needs a construct assigned to a later milestone; a decision cannot be given one executable function and a
reflection theorem; an abstract fact family cannot be projected from the retained core without a free-standing
authority beside it; `LAT-077` needs a diagnostic the elaboration cannot produce from the retained object; a
run relation, evaluator or machine instantiation would be needed to discharge a C6 row; implementation needs
a placeholder, compatibility path, trusted shortcut, fuel, bound or premature future state.
