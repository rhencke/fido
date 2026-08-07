# C6 — the static semantic foundation

Review: contract

Goal:
Ordinary names and shadowing, with meaning decided by binding. C6 lands the complete predeclared identity
catalog, one type algebra and environment, exact constants, expression/use/application facts, one
result-consumption root, compiler-owned static variable identity, both dependency objects, and a **three-way**
decision that never calls unmodelled Go a rejection.

**C6 is entirely static.** No `Runtime` module, no value, place, store, environment or `Machine.T`. C7
introduces all of them together as one vertical, per `ARCH-11`.

## 1. Module order and ownership

```text
Decimal Integer Float Complex FilePath ModulePath Version Collections Names Syntax Index Typing
Compilable Machine Safe Render Emit
```

`ARCHITECTURE.md` §1 states the ownership law once. Two consequences bind here: `Typing` imports `Index` and
never `Compilable`, so no `Typing` signature mentions an `ObjectRef`; and `Runtime` is absent from this order.
`Float` owns decimal representation, so the nonnegative refinement `Float.NonNegativeDecimal` lives there and
`Syntax` never inspects `Float.coefficient`.

## 2. Core-indexed three-way outcome

The accepted C4 topology already indexes the decision by the exact retained core. C6 **extends** it; it does
not replace it with an unindexed payload plus a theorem.

```coq
Module Type ELABORATION.
  Parameter Core : Syntax.Program -> Type.
  Parameter core_diagnostics : forall {p}, Core p -> list (DiagnosticReason p).
  Parameter core_boundaries  : forall {p} (core : Core p), list (ScopeBoundary core).

  Inductive Decision {p} (core : Core p) : Type :=
  | AcceptedDecision (Hd : core_diagnostics core = nil) (Hb : core_boundaries core = nil)
  | RejectedDecision (Hd : core_diagnostics core <> nil)
  | OutsideDecision  (Hd : core_diagnostics core = nil) (Hb : core_boundaries core <> nil).

  Parameter Elaboration : Syntax.Program -> Type.
  Parameter elaboration_core : forall {p}, Elaboration p -> Core p.
  Parameter decision : forall {p} (a : Elaboration p), Decision (elaboration_core a).
  Parameter elaborate : forall p : Syntax.Program, Elaboration p.
End ELABORATION.
```

Emptiness and nonemptiness are stated over the **canonical projections of the exact core**, which is how C4
already carries `AcceptedDecision`/`RejectedDecision`; a `Collections.NonEmpty` payload would restate a fact
the index already forces. Every branch is about the same retained `Core`.

`Program` stays the opaque capability accepted at C4 — `Program : Type`, not `Program p`.

```coq
Module Type CAPABILITY.
  Parameter Program : Type.
  Parameter source   : Program -> Syntax.Program.
  Parameter core     : forall cp : Program, Core (source cp).
  Parameter accepted : forall cp : Program, core_diagnostics (core cp) = nil.
  Parameter in_scope : forall cp : Program, core_boundaries (core cp) = nil.

  Parameter Failure : Syntax.Program -> Type.
  Parameter failure_core : forall {p}, Failure p -> Core p.
  Parameter rejected : forall {p} (fail : Failure p), core_diagnostics (failure_core fail) <> nil.

  Parameter Outside : Syntax.Program -> Type.
  Parameter outside_core : forall {p}, Outside p -> Core p.
  Parameter outside_clean : forall {p} (o : Outside p), core_diagnostics (outside_core o) = nil.
  Parameter outside_blocked : forall {p} (o : Outside p), core_boundaries (outside_core o) <> nil.

  Inductive Outcome (p : Syntax.Program) : Type :=
  | Compiled     (cp : Program) (Hcp : source cp = p)
  | Rejected     (fail : Failure p)
  | OutsideScope (out : Outside p).

  Parameter compile : forall p : Syntax.Program, Outcome p.
End CAPABILITY.
```

Only the internal mint constructs `Program`, `Failure` or `Outside`. `Compiled` alone reaches `Safe.Program`
and `Emit.Image`.

## 3. Object kind, requirement, and the sealed boundary

**Kind** is what Go says an object is, independent of what Fido implements.

```coq
Inductive ObjectKind : Type :=
| TypeObject | ConstantObject | VariableObject | FunctionObject | BuiltinObject | NilObject.

Inductive ObjectOrigin (p : Syntax.Program) : Type :=
| Predeclared : Names.PredeclaredName -> ObjectOrigin p
| SourceBound : Index.BindingSiteRef p -> ObjectOrigin p
| MainObject  : Index.MainRef p -> ObjectOrigin p.

Parameter ObjectRef  : forall {p}, Core p -> Type.
Parameter object_origin : forall {p} {core : Core p}, ObjectRef core -> ObjectOrigin p.
Parameter object_kind   : forall {p} {core : Core p}, ObjectRef core -> ObjectKind.
```

`iota` is a `ConstantObject` with an exact contextual rule; `nil` is `NilObject`; `main` is a
`FunctionObject`; predeclared builtins are `BuiltinObject`. `WrongRole` means the **kind** cannot satisfy the
source role — never that Fido has not implemented the object. There is no flat `Capability` enumeration and
no `ContextualCap`.

A **requirement** is an exact semantic obligation at an exact site. It is closed; later milestones add
constructors when a genuinely new obligation arrives, never handlers.

```coq
Inductive SemanticRequirement {p} (core : Core p) : Type :=
| TypeMeaningReq
    (u : Index.NameUseRef p) (b : BindingFact core u) (i : TypeIdentity p)
| ValueMeaningReq
    (u : Index.NameUseRef p) (b : BindingFact core u)
| ApplicationReq
    (a : Index.ApplicationRef p)
    (hf : ExpressionFact core (Index.application_head a))
    (tgt : ApplicationTarget hf)
    (args : ArgumentFacts core a)
    (demand : ResultDemand)
| StatementReq
    (s : Index.ExpressionStatementRef p)
    (ef : ExpressionFact core (Index.statement_expression s))
| UnaryReq
    (n : Index.UnaryRef p) (op : Syntax.UnaryOp)
    (of_ : ExpressionFact core (Index.unary_operand n)).
```

`ApplicationReq` carries the exact **profile** — the head target plus the exact ordered argument facts —
so one `len` object supports strings at C7, arrays/slices/maps at C10 and channels at C14 without changing
identity or asserting invalidity. `make(slice)` and `make(channel)` are two distinct unmet requirements over
one object.

`ScopeBoundary` is a sealed dependent family indexed by the exact core and the exact unmet requirement. It has
no public constructor, so no client can pair an independently proved binding with an independently proved
negative.

```coq
Parameter RequirementSatisfied : forall {p} {core : Core p}, SemanticRequirement core -> Prop.
Parameter ScopeBoundary : forall {p} (core : Core p), Type.
Parameter boundary_requirement :
  forall {p} {core : Core p}, ScopeBoundary core -> SemanticRequirement core.
Parameter boundary_missing :
  forall {p} {core : Core p} (b : ScopeBoundary core),
  ~ RequirementSatisfied (boundary_requirement b).

Inductive BoundaryView {p} (core : Core p) : Type :=
| MissingTypeMeaning      (u : Index.NameUseRef p) (o : ObjectRef core)
| MissingValueMeaning     (u : Index.NameUseRef p) (o : ObjectRef core)
| MissingApplicationRule  (a : Index.ApplicationRef p) (tgt : ErasedTarget) (prof : ErasedProfile)
| MissingStatementRule    (s : Index.ExpressionStatementRef p)
| MissingUnaryRule        (n : Index.UnaryRef p) (op : Syntax.UnaryOp) (form : ErasedForm).

Parameter boundary_view : forall {p} {core : Core p}, ScopeBoundary core -> BoundaryView core.
Parameter erase_boundary : forall {p} {core : Core p}, ScopeBoundary core -> ErasedBoundary.
```

`ErasedBoundary` is the boundary's own stable erased view, separate from `ErasedDiagnostic`. No certified
value contains a roadmap or ledger-row identifier; `.review/closure.csv` maps an object to the milestone
that owes its rule, on its own side.

## 4. Honest analysis after a boundary

An unsupported type or callable can prevent a later fact from existing. Every semantic site therefore has one
closed outcome, and a dependent site records that it was blocked without inventing a second root.

```coq
Inductive SiteOutcome {p} (core : Core p) (A : Type) : Type :=
| Supported       (a : A)
| DefiniteFailure (d : DiagnosticReason p) (root : RootDiagnostic core d)
| OutsideSite     (b : ScopeBoundary core)
| Blocked         (q : Index.Snapshot.NodeRef p) (h : NotSupportedAt core q).
```

```text
type U uintptr   root boundary: the exact uintptr type requirement
type T U         Blocked by the exact U site; no duplicate boundary
var x T          Blocked by the exact T site; no fake semantic type
```

Independent branches are still traversed and every independently establishable diagnostic is retained. No
placeholder type, fake fact or "unknown" result is ever minted. `core_diagnostics` contains **root**
diagnostics only and `core_boundaries` **root** boundaries only; both are deterministically ordered by the one
source and preflight order, duplicate-free by exact requirement identity, and projections of the retained
core — never rebuilt from the final branch. `Compiled` makes every accepted fact query total because both
lists are empty; `Failure` and `Outside` retain the exact partial analysis and expose no total
accepted-program API.

## 5. Source topology

```coq
(* Names *)
Record OrdinaryIdentifier : Type := MakeOrdinary {
  ordinary_identifier : Identifier;
  ordinary_not_blank  : spelling ordinary_identifier <> "_"%string }.

(* Collections *)
Record NonEmpty (A : Type) : Type := MakeNonEmpty { ne_first : A; ne_rest : list A }.

(* Float *)
Record NonNegativeDecimal : Type := MakeNonNegDecimal {
  nnd_decimal  : Decimal;
  nnd_nonneg   : (0 <= coefficient nnd_decimal)%Z }.

(* Syntax *)
Inductive BindingName : Type :=
| Named : Names.OrdinaryIdentifier -> BindingName
| Blank : BindingName.

Inductive UnaryOp : Type := UnaryMinus.

Inductive Literal : Type :=
| IntegerLiteral : N -> Literal
| FloatLiteral   : Float.NonNegativeDecimal -> Literal
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

An application head is one real child expression occurrence under the `ApplicationHead` role. There is no
`ApplicationHead` source category, kind or reference. Literals carry magnitude; every negative numeric source
value is `Unary UnaryMinus`. `Blank` creates no object. `Block` is reached only through `Main` at C6; no
general function-declaration scaffold lands early. Short declarations are function-local. A package block is a
semantic scope, not a source construct.

## 6. Index and use topology

One kind and view per source category, refined by view where a category has variants. No peer node for call
versus conversion, `complex` versus `println`, a name expression versus the same expression occurrence, an
application head versus its exact child expression, or a top-level wrapper versus the declaration it contains.

```text
kinds  FileKind PackageClauseKind MainKind DeclarationKind BlockKind StatementKind
       ConstSpecKind VarSpecKind TypeSpecKind BindingNameKind ExpressionKind TypeUseKind

roles  FilePackage  FileTopLevel n  MainBlock  BlockStatement n  StatementDeclaration
       DeclarationSpec n  BindingNameOccurrence n  ConstSpecType  ConstInitializerExpression n
       VarSpecType  VarInitializerExpression n  TypeSpecTarget  TypeNameUse
       ShortRightExpression n  StatementExpression  UnaryOperand
       ApplicationHead  ApplicationArgument n
```

```coq
Parameter DirectExprUseRef : Syntax.Program -> Type.
Parameter direct_parent : forall {p}, DirectExprUseRef p -> Index.Snapshot.NodeRef p.
Parameter direct_child  : forall {p}, DirectExprUseRef p -> Index.ExprRef p.
Parameter direct_role   : forall {p}, DirectExprUseRef p -> Index.Role p.
Parameter direct_occupies :
  forall {p} (u : DirectExprUseRef p),
  Index.OccupiesRole (direct_parent u) (direct_child u) (direct_role u).

Parameter InheritedConstUseRef : Syntax.Program -> Type.

Inductive ExprUseRef (p : Syntax.Program) : Type :=
| DirectUse    : DirectExprUseRef p -> ExprUseRef p
| InheritedUse : InheritedConstUseRef p -> ExprUseRef p.
```

`DirectExprUseRef` covers every ordinary expression child — application head, application argument, unary
operand, statement expression, explicit const initializer, var initializer, short-declaration right side. No
public reference is a parent plus an unchecked natural. `InheritedConstUseRef` stays distinct because the
current spec has no expression child; it retains the exact current const spec, current binding-name
occurrence, enclosing const declaration, nearest preceding explicit const spec, predecessor expression
occurrence at the corresponding result position, optional predecessor type occurrence, current structural
`iota` index, and proofs of same-declaration, nearest-predecessor and corresponding position. No consumer
searches backward, copies source, reconstructs an equal predecessor, or reuses the predecessor's resolved
result or plan.

## 7. Typing

`Typing` mentions no `Compilable` type. Raw type identity is separate from admitted semantic type, so no
client can build a semantic type for a cyclic, rejected or blocked definition.

```coq
Inductive TypeIdentity (p : Syntax.Program) : Type :=
| PredeclaredIdentity : BasicType -> TypeIdentity p
| DefinedIdentity     : Index.BoundDefinedTypeRef p -> TypeIdentity p.

Module Type TYPE_ENV.
  Parameter ResolvedTypeEquations : Syntax.Program -> Type.
  Parameter TypeGraphEvidence : forall {p}, ResolvedTypeEquations p -> Type.
  Parameter Env : forall {p} (eqs : ResolvedTypeEquations p), TypeGraphEvidence eqs -> Type.

  Parameter TypeForm : forall {p} {eqs : ResolvedTypeEquations p} {ev}, Env eqs ev -> Type.
  Parameter BasicForm : forall {p} {eqs} {ev} (env : Env eqs ev), BasicType -> TypeForm env.

  Parameter SemanticType : forall {p} {eqs : ResolvedTypeEquations p} {ev}, Env eqs ev -> Type.
  Parameter Resolved : forall {p} {eqs} {ev}, Env eqs ev -> TypeIdentity p -> Prop.
  Parameter semantic_of_identity :
    forall {p} {eqs} {ev} (env : Env eqs ev) (i : TypeIdentity p), Resolved env i -> SemanticType env.
  Parameter semantic_identity :
    forall {p} {eqs} {ev} {env : Env eqs ev}, SemanticType env -> TypeIdentity p.

  Parameter underlying : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> TypeForm env.
  Parameter identicalb   : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> SemanticType env -> bool.
  Parameter assignableb  : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> SemanticType env -> bool.
  Parameter convertibleb : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> SemanticType env -> bool.
  Parameter representableb : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> Constant -> bool.
  Parameter TypedConstant : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> Type.
End TYPE_ENV.
```

`Env` is indexed by the exact equations and the exact successful graph evidence, so an equal rebuilt
environment is not provenance. `underlying` returns a `TypeForm`, never a defined type. C6 proves every
admitted form is basic; later milestones extend `TypeForm` and do not replace `underlying`. An alias mints no
`TypeIdentity` and resolves to the target semantic type. `TypedConstant` is indexed by that same exact
environment and semantic type. The exact `Compilable` core retains the exact equations, graph evidence and
environment; a boundary-bearing or cyclic type requirement produces a `SiteOutcome`, never an invalid
environment.

## 8. Static phase

An initializer determines the type of `var x = e` and `x := e`, so declaration elaboration is interleaved, in
package dependency order and local source order.

```text
exact Input
→ scope forest + binder classifications + object identities
→ all name bindings + structural uses
→ resolved type equations
→ exact TypeEnv (equations + graph evidence) or exact type-cycle outcome
→ package const/var dependency graph from retained bindings
→ exact acyclic order or exact dependency-cycle outcome
→ declaration elaboration, in package dependency order and local source order:
    → bottom-up initializer expression facts
    → exact use facts
    → exact result-consumption plan
    → constant / variable semantic fact
    → typed static-variable refinement where applicable
→ remaining bottom-up expression and application facts
→ unused-local result
→ root diagnostics + root boundaries
```

Each stage is indexed by the exact prior object. Short-declaration new-versus-reused classification sits in
scope construction because later statements bind against its result. The type graph and the package const/var
dependency graph stay distinct; C11 consumes the same dependency object and adds no peer graph. Scopes and
both graphs are per package, keyed by the parent directory the core already retains, built from all files of
that package before package-level resolution, rejecting duplicates without overwrite.

| declaration | scope begins |
|---|---|
| package `const`, `var`, `type`, `main` | the package block |
| local `const` spec | after the `ConstSpec` |
| local `var` spec | after the `VarSpec` |
| short-variable new binding | after the `ShortVarDecl` |
| **local `type` spec** | **at the identifier in the `TypeSpec`** |
| predeclared object | the outer universe block |
| blank | never |

The existing proof-carrying input, work forest, member index, outcome trace and sealed core are generalized
where they own these same causal facts. No second analyzer stands beside them.

## 9. Facts

```coq
Parameter BindingFact : forall {p} (core : Core p), Index.NameUseRef p -> Type.
Parameter bound_object : forall {p} {core} {u}, BindingFact core u -> ObjectRef core.

Inductive BinderClass {p} (core : Core p) : Type :=
| BinderBlank
| BinderDeclares (o : ObjectRef core)
| BinderReuses   (v : StaticVariable core).
Parameter BinderFact : forall {p} (core : Core p), Index.BindingSiteRef p -> Type.
Parameter binder_class : forall {p} {core} {s}, BinderFact core s -> BinderClass core.

Inductive ResultAtom {p} (core : Core p) : Type :=
| UntypedConstant (c : Typing.Constant)
| TypedConstantAtom (t : SemanticTypeOf core) (tc : TypedConstantOf core t)
| ValueResult (t : SemanticTypeOf core).

Inductive ResultForm {p} (core : Core p) : Type :=
| FixedResults      (v : list (ResultAtom core))
| ContextualResult  (r : ContextualRule core)
| NoStandaloneResult.

Parameter ExpressionFact : forall {p} (core : Core p), Index.ExprRef p -> Type.
Parameter referenced_object : forall {p} {core} {r}, ExpressionFact core r -> option (ObjectRef core).
Parameter result_form : forall {p} {core} {r}, ExpressionFact core r -> ResultForm core.

Parameter UseFact : forall {p} (core : Core p), ExprUseRef p -> Type.
Parameter ResultPlan : forall {p} (core : Core p), PlanSiteRef p -> Type.
Parameter StaticVariable : forall {p}, Core p -> Type.
Parameter static_variable_object : forall {p} {core}, StaticVariable core -> ObjectRef core.
Parameter static_variable_type : forall {p} {core} (v : StaticVariable core), SemanticTypeOf core.
```

`referenced_object` and `result_form` are **independent** projections, so a name retains both its exact object
and its exact results. No public constructor permits an arbitrary pairing.

```text
literal        referenced_object = None                       result_form = one constant
true / false   referenced_object = exact predeclared constant  result_form = one constant
variable name  referenced_object = exact variable object       result_form = one value
type name      referenced_object = exact type object           result_form = NoStandaloneResult
println name   referenced_object = exact builtin object        result_form = NoStandaloneResult
iota           referenced_object = exact iota object           result_form = Contextual iota rule
nil            referenced_object = exact nil object            result_form = Contextual nil rule
```

A named var declaration or new short binding creates one exact `StaticVariable` — **that object is the
static slot**. It is a refinement and projection of the exact semantic object, never an independent id or
registry entry. Constants, types, blank names and `main` create none. C7's dynamic environment maps these
exact objects to dynamic places.

## 10. Application

Classification consumes the exact head **`ExpressionFact`**, not the head binding fact, so C9's
function-valued heads extend this sum rather than replacing it.

```coq
Inductive ApplicationTarget {p} {core : Core p} {h : Index.ExprRef p}
                            (f : ExpressionFact core h) : Type :=
| ConversionTarget     (t : SemanticTypeOf core) (Ht : HeadDenotesType f t)
| ObjectCallableTarget (o : ObjectRef core) (Ho : HeadDenotesCallableObject f o).
(* C9 adds ValueCallableTarget: an exact one-result function value carried by the same head fact *)

Parameter ApplicationFact : forall {p} (core : Core p), Index.ApplicationRef p -> Type.
Parameter application_head_fact :
  forall {p} {core} {a} (af : ApplicationFact core a), ExpressionFact core (Index.application_head a).
Parameter application_target :
  forall {p} {core} {a} (af : ApplicationFact core a), ApplicationTarget (application_head_fact af).
Parameter application_results :
  forall {p} {core} {a}, ApplicationFact core a -> list (ResultAtom core).
```

`ApplicationFact` is a dependent projection of the exact application `ExpressionFact`, not a peer table. C7
consumes it and neither reclassifies the target nor rebuilds argument order.

Admitted C6 rules, all over **exact underlying forms**, so a defined type named over an admitted form is not
rejected for being named:

- **conversion** — exactly one argument, one result, through the one `Typing` convertibility and
  representability authority, retaining constant-versus-nonconstant status and rerunning no resolution;
- **`complex`** — exactly two arguments whose underlying forms are floating:

  | arguments | result |
  |---|---|
  | both untyped numeric constants, each valid for the real/imaginary operand rule | **untyped complex constant** |
  | one untyped, one typed with underlying `float32` | the untyped one converts through the one `Typing` authority; `complex64` |
  | one untyped, one typed with underlying `float64` | likewise; `complex128` |
  | both typed with underlying `float32` | `complex64` |
  | both typed with underlying `float64` | `complex128` |
  | both typed, differing underlying float forms | rejected |

- **`println`** — a variadic list, each argument an untyped constant or a value whose **underlying form** is
  an admitted basic form (bool, any integer kind, float, complex, string), untyped constants defaulted first.
  Empty result vector. C7 alone owns evaluation and output.

There is no separate complex or println fact store. Every other predeclared callable resolves correctly and
produces an `ApplicationReq` boundary for the exact missing profile. `main()` is the same case: valid Go, no
C6 function objects, so the head resolves to the exact `MainObject` and its `ApplicationReq` is unmet.

`StatementEligible` is a separate executable and reflected judgment; result count alone does not decide it.

## 11. Result consumption

```coq
Inductive ResultPlanShape : Type := Pairwise | SingleMulti.
```

Context plans retain that same exact root and add their own rules — const initialization, var
initialization, short declaration, application arguments. Later assignment and return milestones extend
these context plans and add no second arity, defaulting or assignability authority. Inherited const
initialization builds a new current-spec plan from the inherited source uses under the current `iota`; it
never reuses the predecessor's resolved plan.

## 12. Safe and Render

`Safe` keeps `Property`, the sealed certificate retaining the exact compiled capability, and nothing else.
`Safe.Value`, `value_type`, `ValueWellFormed`, `value_well_formedb`, `ValueDenotesConstant`,
`typed_constant_to_value`, `resolved_constant_value`, `eval_expr`, `eval_stmt`, `eval_decl` and `eval_file`
are deleted; §14 records where each guarantee goes.

`Render` is structural and performs no binding or type lookup. Rendering is **precedence- and token-safe**:
`"-" ++ render e` is wrong because a nested unary emits `--x` and retokenizes.

```coq
Inductive Prec : Type := PrimaryPrec | UnaryPrec.

Definition prec (e : Syntax.Expr) : Prec :=
  match e with
  | Syntax.Unary _ _ => UnaryPrec
  | _ => PrimaryPrec
  end.

Parameter render_at : Prec -> Syntax.Expr -> string.
```

`render_at r e` parenthesizes exactly when `prec e` binds looser than `r`, and never otherwise.

```text
render (Unary UnaryMinus e)  = "-" ++ render_at PrimaryPrec e
render (Application h args)  = render_at PrimaryPrec h ++ "(" ++ join(", ", map render args) ++ ")"
render_stmt (ExprStmt e, n)  = indent(n) ++ render e ++ NL
```

Frozen outputs: `-1`; `-(-x)`; `-T(x)`, minimal parentheses since a call binds tighter than unary; `f(x)`;
`f(-x)`; `(-f)(x)` if a unary ever heads an application. Arguments sit at the top of the expression grammar
and take no parentheses. One literal, one unary, one application and one expression-statement renderer replace
the special complex, conversion and `println` paths. **Every pre-C6 generated byte is preserved exactly.**

File level keeps the existing bytes: the header line, a blank line, the package clause, a blank line before
each top-level declaration, and the exact final newline. Within a declaration: one tab per block depth,
comma-space separators, no trailing whitespace, direct source spelling, and an inherited const spec rendering
names only. One spec renders ungrouped; zero or two-or-more render grouped, with the zero branches exactly
`const ()`, `var ()`, `type ()` each followed by a newline.

## 13. The complete diagnostic surface

`DiagnosticCode` is an inductive of constructors, not strings, and is extended — not replaced. Every
retained current diagnostic keeps its code and user-visible result.

| constructor | code | primary anchor | related | erased payload | status |
|---|---|---|---|---|---|
| `InvalidConversion (primary : Index.ApplicationRef p) (head : Index.ExprRef p) (operand : Index.ExprRef p) (outer : list (Index.ApplicationRef p)) (target : TypeIdentity p) (operand_status : ConstantInfo)` | `CodeInvalidConversion` | the innermost failing application | outer applications | target identity + source target | **carrier changed**: anchors an `Application`, not a deleted `Convert`; `Index.TypeNameRef` becomes the head `ExprRef` |
| `DefaultNotRepresentable (primary : Index.ExprRef p) (exact_constant : Constant) (default_target : TypeIdentity p)` | `CodeDefaultNotRepresentable` | the expression | — | constant + target | retained; `SemanticType` becomes `TypeIdentity` |
| `MainRedeclared (later : Index.DeclRef p) (earlier : Index.DeclRef p)` | `CodeMainRedeclared` | later declaration | earlier declaration | — | **retained unchanged** |
| `MissingMainEntry (package_primary : PackageRef p)` | `CodeMissingMainEntry` | the package | — | — | retained unchanged |
| `BuildOutputIsDirectory (package_primary : PackageRef p) (output_name : string)` | `CodeBuildOutputIsDirectory` | the package | — | output name | retained unchanged |
| `DuplicateBinding (later : Index.BindingSiteRef p) (earlier : Index.BindingSiteRef p)` | `CodeDuplicateBinding` | later site | earlier site | — | new |
| `InitMisuse (site : Index.BindingSiteRef p)` | `CodeInitMisuse` | the site | — | — | new |
| `UnresolvedName (u : Index.NameUseRef p)` | `CodeUnresolvedName` | the use | — | spelling | new |
| `WrongRole (u : Index.NameUseRef p) (role : Index.UseRole) (actual : ObjectKind)` | `CodeWrongRole` | the use | the object's binding site when it has one | role + kind | new |
| `NotApplicable (a : Index.ApplicationRef p) (actual : ObjectKind)` | `CodeNotApplicable` | the application head | — | kind | new |
| `TypeCycle (site : Index.TypeSpecRef p) (cycle : CycleEvidence p)` | `CodeTypeCycle` | one cycle member | the other members | — | new |
| `DependencyCycle (site : Index.BindingSiteRef p) (cycle : CycleEvidence p)` | `CodeDependencyCycle` | one cycle member | the other members | — | new |
| `FirstSpecInherited (s : Index.ConstSpecRef p)` | `CodeFirstSpecInherited` | the const spec | — | — | new |
| `ResultMismatch (site : PlanSiteRef p) (expected : ResultPlanShape) (targets : nat) (observed : list ErasedResultVector)` | `CodeResultMismatch` | the plan site | each right-hand expression | shape + target count + observed vectors | new |
| `ShortDeclNoNew (s : Index.StatementRef p)` | `CodeShortDeclNoNew` | the short declaration | — | — | new |
| `ShortRedeclType (site : Index.BindingSiteRef p) (existing : TypeIdentity p) (found : TypeIdentity p)` | `CodeShortRedeclType` | the left name | the earlier declaration | both identities | new |
| `NilNoTarget (r : Index.ExprRef p)` | `CodeNilNoTarget` | the expression | — | — | new |
| `IotaNoContext (r : Index.ExprRef p)` | `CodeIotaNoContext` | the expression | — | — | new |
| `NotAssignable (u : ExprUseRef p) (from : TypeIdentity p) (to : TypeIdentity p)` | `CodeNotAssignable` | the use | the target's type occurrence | both identities | new |
| `UnusedLocal (site : Index.BindingSiteRef p)` | `CodeUnusedLocal` | the binding site | — | — | new |
| `BadArgument (u : DirectExprUseRef p) (why : ArgumentReason)` | `CodeBadArgument` | the exact argument | the application | reason | new |
| `BadOperand (u : DirectExprUseRef p) (why : OperandReason)` | `CodeBadOperand` | the exact operand | the operator occurrence | reason | new |
| `NotStatement (s : Index.ExpressionStatementRef p) (why : IneligibleReason)` | `CodeNotStatement` | the statement | — | reason | new |

Precedence: a failed preflight still takes precedence over a package's semantic errors; otherwise one
canonical source order within each package. `WrongRole` carries the exact use role and the exact actual
`ObjectKind` and never a support flag. `MainRedeclared` is **not** folded into `DuplicateBinding` — its code
and payload are accepted user-visible results. Unavailable semantics are boundaries, never diagnostics.

## 14. Migration of accepted guarantees

| current guarantee | disposition |
|---|---|
| `compile_complete : forall p, Admissible p -> exists cp Hcp, compile p = Compiled cp Hcp` | retained, premise strengthened: `Admissible p -> core_boundaries (elaboration_core (elaborate p)) = nil -> …` |
| `compile_rejected_of_inadmissible : forall p, ~ Admissible p -> exists fail, compile p = Rejected fail` | retained unchanged |
| `compile_ok_valid : forall p cp Hcp, compile p = Compiled cp Hcp -> source cp = p /\ Admissible (source cp)` | retained unchanged |
| `compile_rejected_not_admissible` | retained unchanged |
| `compile_program_typed` | retained; `Typing.Program predeclared_type p` becomes the binding-phase judgment |
| `compile_ok_of_source_spec_valid_b` | retained, gaining the no-boundary premise |
| `elaboration_accepted_iff_admissible : core_diagnostics … = nil <-> Admissible p` | retained; the accepted branch additionally requires `core_boundaries … = nil` |
| `elaboration_rejected_iff_inadmissible` | retained unchanged |
| `program_of_admissible`, `capability_of_admissible`, `capability_source`, `capability_is_compile_outcome` | retained, each gaining the no-boundary premise |
| `Safe.eval_expr` and its ten lemmas (`eval_expr_resolved`, `eval_expr_resolved_type`, `eval_expr_resolved_value`, `eval_projects_stored_float_runtime`, `eval_projects_stored_complex_runtime`, `eval_expr_denotes`, `eval_zero_sign_agnostic`, `eval_string_value`, `eval_string_resolved_type`, and the value helpers) | **deleted from `Safe` at C6; re-proved at C7** over `Runtime.Value` and the one machine. `SPEC-140` and the C7 rows own them. |
| `Safe.Value`, `value_type`, `ValueWellFormed`, `value_well_formedb`, `ValueDenotesConstant`, `typed_constant_to_value`, `resolved_constant_value` | deleted from `Safe`; C7 `Runtime` |
| `Render.const_info_denotes` | **retained at C6** — spelling denotes constant status, no runtime value |
| `Render.const_info_denotes_functional` | retained at C6 unchanged |
| `Render.resolved_expr_denotes` | **split**: the constant/spelling half is retained at C6; the value half (`eval_expr`, `ValueWellFormed`, `ValueDenotesConstant`) is deferred to C7 and re-proved there |
| `Render.resolved_string_denotes`, `boundary_max`, `boundary_min` | deferred to C7 with the value half |

No obsolete name survives as an alias, and no guarantee is dropped without a row here naming where it goes.

## 15. Public theorem types

```coq
Theorem decision_accepted_iff : forall p (a : Elaboration p),
  (exists Hd Hb, decision a = AcceptedDecision Hd Hb)
  <-> core_diagnostics (elaboration_core a) = nil /\ core_boundaries (elaboration_core a) = nil.

Theorem decision_rejected_iff : forall p (a : Elaboration p),
  (exists Hd, decision a = RejectedDecision Hd) <-> core_diagnostics (elaboration_core a) <> nil.

Theorem decision_outside_iff : forall p (a : Elaboration p),
  (exists Hd Hb, decision a = OutsideDecision Hd Hb)
  <-> core_diagnostics (elaboration_core a) = nil /\ core_boundaries (elaboration_core a) <> nil.

Theorem compiled_retains_core : forall p cp Hcp,
  compile p = Compiled cp Hcp -> core cp = elaboration_core (elaborate p).
Theorem rejected_retains_core : forall p fail,
  compile p = Rejected fail -> failure_core fail = elaboration_core (elaborate p).
Theorem outside_retains_core : forall p out,
  compile p = OutsideScope out -> outside_core out = elaboration_core (elaborate p).

Theorem outcome_branches_disjoint : forall p,
  ~ (core_diagnostics (elaboration_core (elaborate p)) <> nil
     /\ core_boundaries (elaboration_core (elaborate p)) <> nil
     /\ exists out, compile p = OutsideScope out).

Theorem boundaries_canonical : forall p (core : Core p) b1 b2,
  In b1 (core_boundaries core) -> In b2 (core_boundaries core) ->
  boundary_requirement b1 = boundary_requirement b2 -> b1 = b2.
Theorem boundaries_are_roots : forall p (core : Core p) b,
  In b (core_boundaries core) -> RootBoundary core b.
Theorem blocked_adds_no_boundary : forall p (core : Core p) q h A (o : SiteOutcome core A),
  o = Blocked q h -> forall b, In b (core_boundaries core) -> boundary_site b <> q.

Theorem predeclared_complete : forall (n : Names.PredeclaredName) p (core : Core p),
  exists o : ObjectRef core, object_origin o = Predeclared n /\ InUniverseScope core o.
Theorem predeclared_shadowed : forall p (core : Core p) (u : Index.NameUseRef p)
    (b : BinderFact core (enclosing_binding_site u)) o,
  binder_class b = BinderDeclares o -> ShadowsAt core u o.

Theorem binding_total : forall p cp (u : Index.NameUseRef (source cp)),
  exists! bf : BindingFact (core cp) u, True.
Theorem object_kind_correct : forall p (core : Core p) (o : ObjectRef core),
  object_kind o = go_kind_of_origin (object_origin o).

Theorem env_provenance : forall p (core : Core p),
  Typing.Env (core_equations core) (core_graph_evidence core) = core_env core.
Theorem alias_no_identity : forall p (core : Core p) (a : Index.AliasSpecRef p) i,
  AliasResolves core a i -> ~ exists r, i = DefinedIdentity r /\ AliasMints core a r.
Theorem defined_identity_exact : forall p (core : Core p) r1 r2,
  Typing.identicalb (core_env core) (defined_semantic core r1) (defined_semantic core r2) = true <-> r1 = r2.

Theorem underlying_reflect : forall p (core : Core p) t f,
  Typing.underlying (core_env core) t = f <-> UnderlyingRel (core_env core) t f.
Theorem identical_reflect : forall p (core : Core p) t u,
  Typing.identicalb (core_env core) t u = true <-> Identical (core_env core) t u.
Theorem assignable_reflect : forall p (core : Core p) t u,
  Typing.assignableb (core_env core) t u = true <-> Assignable (core_env core) t u.
Theorem convertible_reflect : forall p (core : Core p) t u,
  Typing.convertibleb (core_env core) t u = true <-> Convertible (core_env core) t u.
Theorem representable_reflect : forall p (core : Core p) t c,
  Typing.representableb (core_env core) t c = true <-> Representable (core_env core) t c.

Theorem direct_use_provenance : forall p (u : DirectExprUseRef p),
  Index.OccupiesRole (direct_parent u) (direct_child u) (direct_role u).
Theorem inherited_const_provenance : forall p (u : InheritedConstUseRef p),
  NearestPrecedingExplicit p (inherited_current u) (inherited_predecessor u)
  /\ CorrespondingPosition p (inherited_current u) (inherited_predecessor u) (inherited_position u)
  /\ inherited_iota u = structural_iota_index (inherited_current u).

Theorem expression_object_result_coherent : forall p cp r (f : ExpressionFact (core cp) r),
  (referenced_object f = None -> result_form f <> NoStandaloneResult)
  /\ (forall o, referenced_object f = Some o ->
        object_kind o = TypeObject \/ object_kind o = BuiltinObject -> result_form f = NoStandaloneResult).

Theorem application_target_from_head : forall p cp a (af : ApplicationFact (core cp) a),
  TargetDeterminedBy (application_target af) (application_head_fact af).
Theorem application_results_exact : forall p cp a (af : ApplicationFact (core cp) a),
  application_results af = target_result_vector (application_target af) (application_args af).

Theorem result_plan_exact : forall p cp s (rp : ResultPlan (core cp) s),
  PlanPairs rp = pair_targets_with_results (plan_targets rp) (plan_result_vectors rp).
Theorem short_binding_classified : forall p cp s (bf : BinderFact (core cp) s),
  ShortLeftName s -> binder_class bf = BinderBlank
                  \/ (exists o, binder_class bf = BinderDeclares o)
                  \/ (exists v, binder_class bf = BinderReuses v /\ SameBlockExisting s v).
Theorem static_variable_identity : forall p cp (v1 v2 : StaticVariable (core cp)),
  static_variable_object v1 = static_variable_object v2 -> v1 = v2.

Theorem unused_local_sound : forall p cp s,
  In (UnusedLocal s) (core_diagnostics (core cp)) -> ~ exists u, ReadsVariableAt (core cp) u s.
Theorem unused_local_complete : forall p (core : Core p) s,
  LocalVariableSite core s -> (~ exists u, ReadsVariableAt core u s) ->
  In (UnusedLocal s) (core_diagnostics core).

Theorem render_precedence_safe : forall e,
  RetokenizesAs (render_expr e) e.
Theorem render_bytes_preserved : forall p (Hpre : PreC6Program p),
  render_program (migrate p) = legacy_render_program p.
```

Every public fact is an abstract dependent family or a projection from the retained core; no
client-constructible record pairs a reference with a target. Proof helpers stay local; obsolete carrier names
do not survive as aliases.

## 16. Review boundaries

**Semantic-root review** stops only when the whole repository is green and: the source and index roots exist;
internal decisions remain indexed by the exact retained core; `Compiled`/`Rejected`/`OutsideScope` exist
intrinsically; exact object kind, binding, requirement and sealed boundary roots exist; the type
identity/environment topology exists; facts carry object and result information coherently; application
classification consumes the exact head expression fact; result plans and compiler-owned static variable
identity exist; the old fixed resolver, the old expression phase, the special source forms, `Safe.Value` and
`Safe.eval_expr` are deleted; **no `Runtime` module or machine has landed**; and every existing program
renders byte-identically.

**Final C6 review** then completes declarations and shadowing, diagnostics and boundary erasure, C6 rendering,
C6 fixtures, `LAT-077`, generated-artifact evidence, and current document and ledger truth.

C7 is forbidden until Rob accepts C6.

## Done

Package and local `const`/`type`/`var` accepted; a local variable read by `println`; unused local rejected;
cross-file package declarations independent of file order; two packages sharing a spelling without collision;
duplicate package names rejected; local shadowing of package and predeclared names.

Exact shadowing cases, decided by ordinary binding and nothing else:

```text
type complex int; complex(x)     conversion, accepted
var complex int;  complex(x)     NotApplicable — definite invalidity
type println int; println(x)     conversion, and NotStatement in statement position
var println int;  println(x)     NotApplicable — definite invalidity
```

An unshadowed `len(s)`, a `var x uintptr` and a recursive `main()` each give `OutsideScope` with the exact
unmet requirement and **no** diagnostic; `type U uintptr; type T U; var x T` gives exactly one root boundary
and two `Blocked` sites. Short declaration with no new nonblank name rejected; short redeclaration reusing its
static variable; blank declarations creating no object; `true`, `false`, `byte` and `rune` resolving through
ordinary binding; alias preserving identity; two defined declarations with equal underlying forms having
distinct identity; a local type spec naming itself rejected as a cycle; package constant and variable cycles
rejected; a package expression depending on a forward constant accepted; a first const spec with an inherited
initializer rejected; an inherited spec taking the predecessor expression under its own `iota`; unshadowed
`nil` and out-of-context `iota` rejected; `complex` of two untyped constants yielding an untyped complex
constant, and of two values of a defined type whose underlying form is `float32` yielding `complex64`; a
`println` argument of a defined type whose underlying form is `string` accepted; unary minus on a constant and
a variable accepted and on a string rejected; `-(-x)` rendering with its parentheses; every currently accepted
program rendering byte-identically after migration; generated C6 programs passing the pinned Go build with
their exact expected observation.

## Preserve

`Syntax.Program` as the sole source authority and the AST as the one IR; `Program` as the opaque C4
capability, with `Failure` and `Outside` retaining the exact core; the retained work forest, member index,
outcome trace and sealed core; `Machine.T` uninstantiated; direct rendering and the one `Emit.Mint.issue`
authority; certified-module coverage, the whole-theory audit and controls A-E; every sealed-capability, mint,
transport and positive client control; working-tree and staged-index separation; no-host-Python; `life.md`.

## Stop

The migration cannot complete without weakening an accepted guarantee that §14 does not relocate; a C6 row
needs a construct assigned to a later milestone; a decision cannot be given one function and one reflection
theorem; a fact family cannot be projected from the retained core without a free-standing authority beside it;
`ScopeBoundary` cannot be sealed and still expose the exact requirement its consumers need; a blocked site
cannot be recorded without minting a second root; the dependency object cannot be built before the facts that
consume it, or declaration elaboration cannot be interleaved as §8 requires; `Typing` cannot be closed
without mentioning a `Compilable` type; an invalid defined declaration can still construct a `SemanticType`;
`LAT-077` needs a diagnostic the phase cannot produce; a run relation, value, store, environment or machine is
needed for a C6 row; implementation needs a placeholder, compatibility path, trusted shortcut, fuel, bound or
premature future state.
