# C6 — the static semantic foundation

Review: contract

Goal:
Ordinary names and shadowing. One identifier fills every name position and the retained binding fact decides
what each occurrence means. C6 lands the complete predeclared identity catalog, one type algebra and
environment, exact constants, expression/use/application facts, one result-consumption root, compiler-owned
static variable identity, both dependency objects, and a **three-way** decision that never calls unmodelled
Go a rejection.

**C6 is entirely static.** It defines no run relation, adds no `Runtime` module, and mints no value, place,
store, environment or `Machine.T`. C7 introduces all of those together as one vertical, per `ARCH-11`.

## 1. Module order and ownership

```text
Decimal Integer Float Complex FilePath ModulePath Version Collections Names Syntax Index Typing
Compilable Machine Safe Render Emit
```

`ARCHITECTURE.md` §1 states the ownership law once; this contract adds nothing to it. The two facts that bind
here: `Typing` imports `Index` and **never** `Compilable`, so no `Typing` signature may mention an
`ObjectRef`; and `Runtime` does not appear in this order at all.

## 2. Three public outcomes

One analysis computes two orthogonal sets. A **diagnostic** asserts the source is invalid Go. A **boundary**
asserts only that Fido does not yet model an exact capability of an exact object.

```coq
Parameter Elaboration : Syntax.Program -> Type.
Parameter elaborate   : forall p, Elaboration p.
Parameter diagnostics : forall {p}, Elaboration p -> list (DiagnosticReason p).
Parameter boundaries  : forall {p}, Elaboration p -> list (ScopeBoundary p).

Inductive Decision (p : Syntax.Program) : Type :=
| Compiled     : Program p -> Decision p
| Rejected     : Failure p -> Decision p
| OutsideScope : Outside p -> Decision p.

Parameter compile : forall p, Decision p.
```

`Program p`, `Failure p` and `Outside p` are sealed and each retains the exact `Elaboration p` that produced
it. Precedence is fixed: any diagnostic gives `Rejected`; no diagnostic with any boundary gives
`OutsideScope`; both empty gives `Compiled`. **A boundary is never converted to a diagnostic to keep a binary
result type.** Only `Compiled` carries a `Program`, so only `Compiled` reaches `Safe.Program` or an image.

A boundary names an object and a capability — never a ledger row, a code, a string or a payload bag:

```coq
Inductive Capability : Type :=
| TypeCap | ConstantCap | VariableCap | CallableCap | ContextualCap.

Record ScopeBoundary (p : Syntax.Program) : Type := MakeBoundary {
  boundary_use      : Index.NameUseRef p;
  boundary_object   : ObjectRef p;
  boundary_bound    : Binds boundary_use boundary_object;
  boundary_required : Capability;
  boundary_absent   : ~ Admits boundary_object boundary_required
}.
```

`.review/closure.csv` maps each object to the milestone that owes its capability. That mapping is project
scheduling data and lives nowhere inside a certified type.

Frozen statements:

```text
compile_compiled_iff        compile p = Compiled _  <->  diagnostics = [] /\ boundaries = []
compile_rejected_iff        compile p = Rejected _  <->  diagnostics <> []
compile_outside_scope_iff   compile p = OutsideScope _  <->  diagnostics = [] /\ boundaries <> []
rejected_has_witness        every Rejected carries at least one exact definite-invalidity witness
outside_scope_is_not_rejection   OutsideScope yields no Program and no proof of Go invalidity
compiled_has_no_boundary    every accepted capability lies inside the current semantic scope
```

The declarative `Admissible` judgment stays **exact** over the no-boundary domain, in both directions.

## 3. Source topology

```coq
(* Names *)
Record OrdinaryIdentifier : Type := MakeOrdinary {
  ordinary_identifier : Identifier;
  ordinary_not_blank  : spelling ordinary_identifier <> "_"%string }.

(* Collections *)
Record NonEmpty (A : Type) : Type := MakeNonEmpty { ne_first : A; ne_rest : list A }.

(* Syntax *)
Inductive BindingName : Type :=
| Named : Names.OrdinaryIdentifier -> BindingName
| Blank : BindingName.

Inductive UnaryOp : Type := UnaryMinus.

Definition NonNegDecimal : Type := { d : Float.Decimal | (0 <= Float.coefficient d)%Z }.

Inductive Literal : Type :=
| IntegerLiteral : N -> Literal
| FloatLiteral   : NonNegDecimal -> Literal
| StringLiteral  : string -> Literal.

Inductive TypeExpr : Type :=
| NamedType : Names.OrdinaryIdentifier -> TypeExpr.

Inductive Expr : Type :=
| Name        : Names.OrdinaryIdentifier -> Expr
| LiteralExpr : Literal -> Expr
| Unary       : UnaryOp -> Expr -> Expr
| Application : Expr -> list Expr -> Expr.

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

An application head is **one real child expression occurrence** under the `ApplicationHead` role — a name
used as a head is the same source object as a name anywhere else. There is no `ApplicationHead` source
category, kind or reference. C9 adds callable expression heads without touching this constructor; a future
explicit non-name type head is a real Go grammar distinction and may add its own constructor then,
projecting into this same application machinery.

Literals carry magnitude only; every negative numeric source value is `Unary UnaryMinus`. The floating
exponent keeps its sign inside the literal. C6 owns the static unary-minus slice; C7 owns its execution and
every other operator. `Blank` creates no object and no variable identity. `Block` is the reusable block root,
reached only through `Main` at C6; no general function-declaration scaffold lands early. Short declarations
are function-local; the package-level form is unrepresentable. A package block is a semantic scope, not a
source construct.

## 4. Index and use topology

One kind and view per source category, refined by view where a category has variants. No peer node for call
versus conversion, for `complex` versus `println`, for a name expression versus the same expression
occurrence, for an application head versus its exact child expression, or for a top-level wrapper versus the
declaration it contains.

```text
kinds  FileKind PackageClauseKind MainKind DeclarationKind BlockKind StatementKind
       ConstSpecKind VarSpecKind TypeSpecKind BindingNameKind ExpressionKind TypeUseKind

roles  FilePackage  FileTopLevel n  MainBlock  BlockStatement n  StatementDeclaration
       DeclarationSpec n  BindingNameOccurrence n  ConstSpecType  ConstInitializerExpression n
       VarSpecType  VarInitializerExpression n  TypeSpecTarget  TypeNameUse
       ShortRightExpression n  StatementExpression  UnaryOperand
       ApplicationHead  ApplicationArgument n
```

One sealed structural root covers **every** ordinary expression child — application head, application
argument, unary operand, statement expression, explicit const initializer, var initializer, short-declaration
right side:

```text
DirectExprUseRef = exact parent occurrence + exact child ExprRef + exact source role
                 + proof the child occupies that role
```

No public reference is a parent plus an unchecked natural. An inherited const initializer has no current
expression child, so it stays a distinct causal object: `InheritedConstUseRef` retains the exact current const
spec, current binding-name occurrence, enclosing const declaration, nearest preceding explicit const spec,
predecessor expression occurrence at the corresponding result position, optional predecessor type occurrence,
current structural `iota` index, and proofs of same-declaration, nearest-predecessor and corresponding
position. No consumer searches backward, copies source, reconstructs an equal predecessor, or reuses the
predecessor's resolved result or plan.

```text
ExprUseRef = DirectExprUseRef | InheritedConstUseRef
```

Frozen refinements: `NameUseRef`, `BindingSiteRef`, `ApplicationRef`, `ExpressionStatementRef`.

## 5. Semantic objects

```coq
Inductive ObjectOrigin (p : Syntax.Program) : Type :=
| Predeclared : Names.PredeclaredName -> ObjectOrigin p
| Source      : Index.BindingSiteRef p -> ObjectOrigin p
| Main        : Index.MainRef p -> ObjectOrigin p.
```

`ObjectRef p` is sealed over that origin. Identity is never a string, integer, map index or reconstructed
equality. Blank has no object.

`Names.PredeclaredName` is the complete catalog over every pinned `PRE-*` spelling, owning exact identity,
spelling, equality and classification from a spelling — and no semantics. C6 installs every one in the outer
scope, which is what makes shadowing correct. `Typing` owns the map from an admitted predeclared type object
to its `BasicType`; `Names` does not.

**Kind** is what Go says the object is. **Capability** is what Fido currently implements. Capabilities are
proof-carrying refinements of the exact object, never a boolean list, a callback registry, one constructor per
spelling, or an independently rebuilt target record. An object may be known to be a type or a builtin while
its rule belongs to a later milestone; that is a `ScopeBoundary`, not a wrong-role diagnostic.

`BindingFact cp use` retains the exact `NameUseRef` and the exact resolved object from the one binding phase.
Type use, value use and head use consume that same fact and require different capabilities; no consumer reruns
lookup. One binder fact over an exact binding site classifies it `Blank`, `Declares` an exact new object, or
`Reuses` an exact existing variable object (short declaration only). A same-block short redeclaration reuses
the exact object; an outer object is shadowed by a new one; at least one nonblank short left name must be new.

**Static variable identity.** A named var declaration or new short binding creates one exact compiler-owned
variable object carrying one semantic type, and **that object is the static slot**.
`Compilable.VariableObject cp t` is a type-indexed refinement and projection of the exact semantic object —
never an independent id, registry entry, or equality to a reconstructed object. Constants, types, blank names
and `main` have none. C7's dynamic environment maps these exact objects to dynamic places.

## 6. Typing

`Typing` mentions no `Compilable` type. It owns type forms, semantic types, exact constants, the environment's
input and output, and reflected decisions — and no scope lookup, source traversal or object identity.

```coq
Inductive TypeForm (p : Syntax.Program) : Type :=
| BasicForm : BasicType -> TypeForm p.
(* later milestones add function, aggregate, interface, generic and channel forms *)

Inductive SemanticType (p : Syntax.Program) : Type :=
| FormType    : TypeForm p -> SemanticType p
| DefinedType : Index.BoundDefinedTypeRef p -> SemanticType p.

Inductive TypeTarget (p : Syntax.Program) : Type :=
| PredeclaredTarget : BasicType -> TypeTarget p
| AliasTarget       : Index.AliasSpecRef p -> TypeTarget p
| DefinedTarget     : Index.BoundDefinedTypeRef p -> TypeTarget p.

Module Type TYPE_ENV.
  Parameter ResolvedTypeEquations : Syntax.Program -> Type.
  Parameter TypeGraphEvidence : forall {p}, ResolvedTypeEquations p -> Type.
  Parameter Env : Syntax.Program -> Type.
  Parameter build : forall {p} (eqs : ResolvedTypeEquations p), TypeGraphEvidence eqs -> Env p.

  Parameter denote     : forall {p}, Env p -> TypeTarget p -> SemanticType p.
  Parameter underlying : forall {p}, Env p -> SemanticType p -> TypeForm p.
  Parameter identicalb     : forall {p}, Env p -> SemanticType p -> SemanticType p -> bool.
  Parameter assignableb    : forall {p}, Env p -> SemanticType p -> SemanticType p -> bool.
  Parameter convertibleb   : forall {p}, Env p -> SemanticType p -> SemanticType p -> bool.
  Parameter representableb : forall {p}, Env p -> SemanticType p -> Constant -> bool.
  Parameter TypedConstant  : forall {p}, Env p -> SemanticType p -> Type.
End TYPE_ENV.
```

`underlying` returns a **`TypeForm`**, so a defined type is never an underlying result. C6 proves every
admitted form is basic; later milestones extend `TypeForm` and do not replace `underlying`. A defined type's
identity is its exact nonblank declaration reference; an alias mints none and resolves to its target.
`TypedConstant` is indexed by the exact `Env` that establishes a defined type's underlying form — an equal
rebuilt environment is not provenance. Each decision has one function, one relation and one reflection
theorem. `Compilable` builds the exact `ResolvedTypeEquations` from retained bindings and owns the fact that
an exact object has an exact `TypeTarget`; `Typing` owns what that target means.

## 7. Static phase

An initializer determines the type of `var x = e` and `x := e`, so typed variable facts cannot precede
expression facts. Declaration elaboration is therefore interleaved, in package dependency order and local
source order.

```text
exact Input
→ scope forest + binder classifications + object identities
→ all name bindings + structural uses
→ type equations / type graph
→ exact TypeEnv or exact type-cycle object
→ package const/var dependency graph from retained bindings
→ exact acyclic order or exact dependency-cycle object
→ declaration elaboration, in package dependency order and local source order:
    → bottom-up initializer expression facts
    → exact use facts
    → exact result-consumption plan
    → constant / variable semantic fact
    → typed variable-object refinement where applicable
→ remaining bottom-up expression and application facts
→ unused-local result
→ diagnostics + scope boundaries
```

Each stage is indexed by the exact prior object, so a later stage cannot pair with a foreign equal
predecessor. Short-declaration new-versus-reused classification sits in scope construction because later
statements bind against its result. The type graph and the package const/var dependency graph stay
distinct — different nodes, edges, cycle rules and later consumers; C11 consumes the same dependency object
and adds no peer graph.

Scopes and both graphs are per package, keyed by the parent directory `Compilable` already retains, built from
all files of that package before package-level resolution, rejecting duplicates without overwrite. The same
spelling in another package is unrelated, and no cross-package name resolves while imports are absent.

| declaration | scope begins |
|---|---|
| package `const`, `var`, `type`, `main` | the package block |
| local `const` spec | after the `ConstSpec` |
| local `var` spec | after the `VarSpec` |
| short-variable new binding | after the `ShortVarDecl` |
| **local `type` spec** | **at the identifier in the `TypeSpec`** |
| predeclared object | the outer universe block |
| blank | never |

A local alias or definition sees its own name; with only named right-hand sides, every self-reference and
longer cycle is invalid and diagnosed. `init` is forbidden only for C6 package declarations.

The existing proof-carrying input, work forest, member index, outcome trace and sealed core are generalized
where they own these same causal facts. No second analyzer and no post-hoc fact table stands beside them.

## 8. Expression results

A result is not classified by the syntax that produced it. There is no `NameConstantFact`,
`NameVariableFact`, `ConversionConstantFact`, `ConversionNonconstantFact`, `ComplexFact` or `PrintlnFact`.

```text
ResultAtom  = UntypedConstant exact Constant
            | TypedConstant   exact SemanticType + exact Typing.TypedConstant
            | ValueResult     exact SemanticType

ExprMeaning = FixedResults    exact ordered list of ResultAtom
            | ObjectReference exact ObjectRef
            | Contextual      exact contextual object
```

`ObjectReference` lets a head name retain its exact object without pretending a type object is a standalone
value.

```text
literal                          → one constant result
true / false                     → one constant result through ordinary binding
variable name                    → one value result
type or callable name, head role → exact object reference
unary minus                      → one result
T(x)                             → one result
complex(a, b)                    → one result
println(...)                     → zero results
iota                             → contextual until its exact const use supplies iota
nil                              → contextual until a legal target type exists
```

`ExpressionFact cp expr_ref` is the sole context-free fact for that exact occurrence and its representation is
sealed; syntax-specific theorems are projections, never peer stores. `UseFact cp use_ref` consumes the exact
use, the exact child fact, the exact retained context and the exact target facts, and owns defaulting, target
selection, assignability, representability, result selection and `iota`/`nil` context. It never rereads the
raw child and never reruns binding. C9 extends the result vector for multi-results.

## 9. Application

The head's exact `BindingFact` classifies the application. Both cases share source structure and result
plumbing, not typing rules:

```text
ApplicationTarget = ConversionTarget exact TypeCapability
                  | CallableTarget   exact CallableCapability
```

One closed executable judgment with a reflection theorem decides acceptance; no object stores a callback.
Admitted rules:

- **conversion** — exactly one argument, one result, through the one `Typing` convertibility and
  representability authority, retaining constant-versus-nonconstant status and rerunning no resolution;
- **`complex`** — exactly two arguments, each an untyped numeric constant or a value of an admitted float
  type:

  | arguments | result |
  |---|---|
  | both untyped numeric constants | **untyped complex constant** |
  | one untyped, one typed `float32` | the untyped one converts to `float32`; `complex64` |
  | one untyped, one typed `float64` | the untyped one converts to `float64`; `complex128` |
  | both typed `float32` | `complex64` |
  | both typed `float64` | `complex128` |
  | both typed, differing float types | rejected |

- **`println`** — a variadic list, each argument an untyped constant or a value of an admitted basic type
  (bool, any integer kind, float, complex, string), untyped constants defaulted first. Zero results. C6 owns
  static acceptance only; C7 owns evaluation and output.

Every other predeclared callable resolves correctly, has no C6 application rule, and produces a
`ScopeBoundary` — never a rejection. The package `main` object is the same case: `main()` is valid Go, C6
has no function objects, so the head resolves to the exact `Main` object and the boundary names its missing
`CallableCap`.

`ApplicationFact` is a dependent view of the exact `ExpressionFact`, not a peer table. It exposes the exact
application and head occurrence, the exact head use, binding, object and target, the exact ordered argument
uses and child facts, the exact argument result-consumption plan, the exact result vector, and proof of the
reflected judgment. C7 consumes it and neither reclassifies the target nor rebuilds argument order.

`StatementEligible` is a separate executable and reflected judgment; result count alone does not decide it. At
C6 `println(...)` is eligible, `complex(...)` is not, a conversion is not, and any non-application expression
statement is rejected by the exact Go statement rule. Later calls become eligible because their results may be
discarded; receive expressions join the same relation at their milestone.

## 10. Result consumption

One structural root over an exact sequence of expression result vectors, with only the legal Go shapes:

```text
Pairwise     each right-hand expression supplies exactly one result
SingleMulti  one right-hand expression supplies the complete target sequence
```

Context plans retain that same exact root and add their own rules — const initialization, var
initialization, short declaration, application arguments. Later assignment and return milestones extend
these context plans and add no second arity, defaulting or assignability authority. Inherited const
initialization builds a new current-spec plan from the inherited source uses under the current `iota`; it
never reuses the predecessor's resolved plan.

## 11. Safe and Render

`Safe` keeps only `Property = True`, the safety property, and the sealed certificate retaining the exact
compiled capability. `Safe.Value`, value well-formedness, typed-constant materialization and every expression,
statement, declaration and file evaluator are deleted: constants and types to `Typing`, static expression
results to `Compilable`, and runtime values and evaluation to C7.

`Render` is structural and performs no binding or type lookup. Rendering must be **precedence- and
token-safe**: `"-" ++ render e` is not a correct unary renderer, because a nested unary emits `--x` and
retokenizes.

```coq
Inductive Prec : Type := PrimaryPrec | UnaryPrec.

prec (Name _)          = PrimaryPrec
prec (LiteralExpr _)   = PrimaryPrec
prec (Application _ _) = PrimaryPrec
prec (Unary _ _)       = UnaryPrec
```

`render_at r e` parenthesizes exactly when `prec e` binds looser than `r`, and never otherwise:

```text
render (Unary UnaryMinus e)  = "-" ++ render_at PrimaryPrec e
render (Application h args)  = render_at PrimaryPrec h ++ "(" ++ join(", ", map render args) ++ ")"
render_stmt (ExprStmt e, n)  = indent(n) ++ render e ++ NL
```

Arguments sit at the top of the expression grammar and take no parentheses. Frozen outputs: `-1`; `-(-x)`;
`-T(x)` — minimal parentheses, since a call binds tighter than unary; `f(x)`; `f(-x)`; `(-f)(x)` if a unary
ever heads an application. One literal renderer, one unary renderer, one application renderer and one
expression-statement renderer replace the special complex, conversion and `println` paths. **Every pre-C6
generated byte is preserved exactly**, including `println(x)`, `uint8(300)` and `complex(re, im)`.

File level keeps the existing bytes: the header line, a blank line, the package clause, a blank line before
each top-level declaration, and the exact final newline. Within a declaration: one tab per block depth,
comma-space separators, no trailing whitespace, direct source spelling, and an inherited const spec rendering
names only. One spec renders ungrouped; zero or two-or-more render grouped, with the zero branches exactly
`const ()`, `var ()`, `type ()` each followed by a newline.

## 12. Diagnostics

Frozen here, not selected during implementation. Every constructor takes exact refined references; erasure
drops payloads and keeps the code; precedence is one canonical source order per package plus the existing
preflight rule. Every pre-C6 program keeps its exact existing diagnostics. A boundary is **not** a diagnostic
and has its own public projection (§2).

```coq
Inductive DiagnosticReason (p : Syntax.Program) : Type :=
| DuplicateBinding   : Index.BindingSiteRef p -> Index.BindingSiteRef p -> DiagnosticReason p
| MissingMain        : Index.PackageRef p -> DiagnosticReason p
| InitMisuse         : Index.BindingSiteRef p -> DiagnosticReason p
| UnresolvedName     : Index.NameUseRef p -> DiagnosticReason p
| WrongRole          : Index.NameUseRef p -> ObjectKind -> Capability -> DiagnosticReason p
| TypeCycle          : Index.TypeSpecRef p -> CycleEvidence p -> DiagnosticReason p
| DependencyCycle    : Index.BindingSiteRef p -> CycleEvidence p -> DiagnosticReason p
| FirstSpecInherited : Index.ConstSpecRef p -> DiagnosticReason p
| ResultMismatch     : PlanSiteRef p -> list nat -> nat -> DiagnosticReason p
| ShortDeclNoNew     : Index.StatementRef p -> DiagnosticReason p
| ShortRedeclType    : Index.BindingSiteRef p -> SemanticType p -> SemanticType p -> DiagnosticReason p
| NilNoTarget        : Index.ExprRef p -> DiagnosticReason p
| IotaNoContext      : Index.ExprRef p -> DiagnosticReason p
| NotAssignable      : Index.ExprUseRef p -> SemanticType p -> SemanticType p -> DiagnosticReason p
| UnusedLocal        : Index.BindingSiteRef p -> DiagnosticReason p
| BadArgument        : Index.DirectExprUseRef p -> ArgumentReason p -> DiagnosticReason p
| BadOperand         : Index.DirectExprUseRef p -> OperandReason p -> DiagnosticReason p
| NotStatement       : Index.ExpressionStatementRef p -> IneligibleReason p -> DiagnosticReason p.
```

Codes: `FIDO-E-DUPLICATE-DECL`, `FIDO-E-MISSING-MAIN`, `FIDO-E-INIT-MISUSE`, `FIDO-E-UNRESOLVED-NAME`,
`FIDO-E-WRONG-ROLE`, `FIDO-E-TYPE-CYCLE`, `FIDO-E-INIT-CYCLE`, `FIDO-E-FIRST-SPEC-INHERITED`,
`FIDO-E-RESULT-MISMATCH`, `FIDO-E-SHORT-DECL-NO-NEW`, `FIDO-E-SHORT-REDECL-TYPE`, `FIDO-E-NIL-NO-TYPE`,
`FIDO-E-IOTA-CONTEXT`, `FIDO-E-INIT-NOT-ASSIGNABLE`, `FIDO-E-UNUSED-LOCAL`, `FIDO-E-BAD-ARGUMENT`,
`FIDO-E-BAD-OPERAND`, `FIDO-E-NOT-STATEMENT`.

`DuplicateBinding` covers a conflicting `main` and duplicate nonblank names in one short declaration; missing
`main` stays distinct. `ResultMismatch` is the one arity authority — conversion and call argument counts,
const and var initializer counts, and short-declaration counts all fail through it. `WrongRole` fires only
when the object's Go kind cannot fill the source role; when the kind fits but Fido has no rule, the outcome is
a boundary. Unused locals cover function-local variable objects only.

## 13. Public interfaces and theorems

Every public fact is an abstract dependent family or a projection from the retained capability; no
client-constructible record pairs a reference with a target.

| query | index |
|---|---|
| `object_fact` | `ObjectRef` |
| `binder_fact` | `BindingSiteRef` |
| `binding_fact` | `NameUseRef` |
| `type_use_fact` | `NameUseRef` in a type role |
| `expression_fact` | `ExprRef` |
| `use_fact` | `ExprUseRef` |
| `application_view` | `ApplicationRef` |
| `result_plan` | an exact plan site |
| `variable_object` | `BindingSiteRef` of a var name or new short binding |
| `package_dependency_fact` | an exact package |
| `scope_boundaries` | the exact elaboration |

Full statements — binders, indices, premises and direction — are frozen in the same commit for: the six
outcome theorems of §2; complete predeclared outer-scope identity and ordinary shadowing; per-package scope
construction and file-order independence; duplicate rejection without overwrite; the const/var scope-start law
and the separate local-type law beginning at the identifier; binding totality and uniqueness on accepted
programs; object kind and capability refinements; alias non-identity and exact defined-type identity;
`underlying` returning a form and every reflected decision; type-cycle and dependency-cycle reflection;
direct-use structural provenance; inherited-const predecessor and current-`iota` provenance; expression-result
and use-fact totality; application target classification and result-vector exactness; statement eligibility;
structural result matching and context-plan exactness; short binding classification and exact variable reuse;
static variable identity; precedence-safe rendering and pre-C6 byte preservation.

A public theorem exposes an accepted guarantee or is required by a named later consumer. Obsolete carrier
names do not survive as aliases; for every existing theorem whose carrier changes, the implementation names
its exact replacement or states why the guarantee is subsumed. Proof helpers stay local.

## 14. Review boundaries

**Semantic-root review** stops only when the whole repository is green and: the source and index roots exist;
the exact three-way outcome exists; the complete predeclared identity and object/binding roots exist; the type
form, environment and reflected decisions exist; the static phase runs in the §7 order; expression, use,
application and result-plan facts project from the retained core; compiler-owned variable identity exists; the
fixed sixteen-name resolver, the old expression phase, the special source forms, `Safe.Value` and
`Safe.eval_expr` are deleted; **no `Runtime` module, value, place, store, environment or machine has landed**;
and every existing program renders byte-identically.

**Final C6 review** then completes declarations and shadowing, the diagnostics and boundaries of §2 and §12,
C6 rendering, C6 fixtures, `LAT-077`, generated-artifact evidence, and current document and ledger truth.

C7 is forbidden until Rob accepts C6.

## Done

Package and local `const`/`type`/`var` accepted; a local variable read by `println`; unused local rejected;
cross-file package declarations independent of file order; two packages sharing a spelling without collision;
duplicate package names rejected; local shadowing of package and predeclared names; a shadowed `println` and a
shadowed `complex` each giving the exact wrong-role diagnostic; an unshadowed `len`, a `var x uintptr` and a
recursive `main()` each giving `OutsideScope` with its exact object and capability and **no** diagnostic;
short declaration with no new nonblank name rejected; short redeclaration reusing its variable object; blank
declarations creating no object; `true`, `false`, `byte` and `rune` resolving through ordinary binding; alias
preserving identity; two defined declarations with equal underlying forms having distinct identity; a local
type spec naming itself rejected as a cycle; package constant and variable cycles rejected; a package
expression depending on a forward constant accepted; a first const spec with an inherited initializer
rejected; an inherited spec taking the predecessor expression under its own `iota`; unshadowed `nil` and
out-of-context `iota` rejected; `complex` of two untyped constants yielding an untyped complex constant;
unary minus on a constant and a variable accepted and on a string rejected; `-(-x)` rendering with its
parentheses; `complex(...)` as an expression statement rejected; every currently accepted program rendering
byte-identically after migration; generated C6 programs passing the pinned Go build with their exact expected
observation.

## Preserve

`Syntax.Program` as the sole source authority and the AST as the one IR; the retained `Compilable` cores and
their sealing; `Machine.T` uninstantiated; direct rendering and the one `Emit.Mint.issue` authority;
certified-module coverage, the whole-theory audit and controls A-E; every sealed-capability, mint, transport
and positive client control; working-tree and staged-index separation; no-host-Python; `life.md`.

## Stop

The program-indexed `SemanticType` migration cannot complete without weakening an accepted guarantee; a C6 row
needs a construct assigned to a later milestone; a decision cannot be given one function and one reflection
theorem; a fact family cannot be projected from the retained core without a free-standing authority beside it;
the dependency object cannot be built before the facts that consume it, or declaration elaboration cannot be
interleaved as §7 requires; a boundary cannot be reported with its exact object and capability without naming
a ledger row inside a certified type; `Typing` cannot be closed without mentioning a `Compilable` type;
`LAT-077` needs a diagnostic the phase cannot produce; a run relation, value, store, environment or machine is
needed for a C6 row; implementation needs a placeholder, compatibility path, trusted shortcut, fuel, bound or
premature future state.
