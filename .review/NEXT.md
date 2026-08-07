# C6 — the static semantic foundation

Review: contract

Goal:
Ordinary names acquire meaning only through binding. C6 lands the complete predeclared identity catalog, one
type environment, exact constants, expression/use/application facts, one result-consumption root,
compiler-owned static variable identity, both dependency objects, and a three-way decision that never calls
unmodelled Go a rejection.

**C6 is entirely static.** No `Runtime` module, no value, place, store, environment or `Machine.T`. C7
introduces all of them together as one vertical, per `ARCH-11`.

## 1. Module order and ownership

```text
Decimal Integer Float Complex FilePath ModulePath Version Collections Names Syntax Index Typing
Compilable Machine Safe Render Emit
```

`ARCHITECTURE.md` §1 states the ownership law once. Two consequences bind here: `Typing` sees only `Names`,
`Syntax` and `Index`, so no `Typing` signature mentions a `Compilable` type; and `Runtime` is absent.
`Float` owns decimal representation, so `Float.NonNegativeDecimal` lives there and `Syntax` never inspects
`Float.coefficient`.

## 2. The phase owns static meaning; the core owns the report

The existing implementation already retains one exact expression `Phase` inside one exact `Core`. That phase
is generalized into the permanent static-analysis object. No second analyzer is added beside it.

The **phase** owns scopes, semantic objects, binding, type inputs and environments, expression/use/
application/result-plan facts, static variable identities, both dependency objects, root diagnostics and root
boundaries. The **core** additionally owns build plan, layout, package facts and the canonical report. Static
identity is never indexed by those unrelated core fields.

```coq
Parameter Phase : forall {p : Syntax.Program}, Input p -> Type.
Parameter phase : forall {p} (core : Core p), Phase (core_input core).

Parameter ObjectRef     : forall {p} {i : Input p}, Phase i -> Type.
Parameter ScopeBoundary : forall {p} {i : Input p}, Phase i -> Type.

Parameter core_diagnostics : forall {p}, Core p -> list (DiagnosticReason p).
Parameter core_boundaries  : forall {p} (core : Core p), list (ScopeBoundary (phase core)).
```

This removes the self-reference in which `ScopeBoundary core` was defined through facts over the same `core`
whose boundary list it inhabits.

`Decision` stays indexed by the exact `Core`, extending the accepted C4 shape to three branches:

```coq
Inductive Decision {p} (core : Core p) : Type :=
| AcceptedDecision (Hd : core_diagnostics core = nil) (Hb : core_boundaries core = nil)
| RejectedDecision (Hd : core_diagnostics core <> nil)
| OutsideDecision  (Hd : core_diagnostics core = nil) (Hb : core_boundaries core <> nil).
```

Precedence: any diagnostic gives `Rejected`; no diagnostic with any boundary gives `OutsideScope`; both empty
gives `Compiled`. A boundary is never converted to a diagnostic.

`Program` stays the opaque C4 capability.

```coq
Parameter Program : Type.
Parameter source   : Program -> Syntax.Program.
Parameter core     : forall cp : Program, Core (source cp).
Parameter accepted : forall cp : Program, core_diagnostics (core cp) = nil.
Parameter in_scope : forall cp : Program, core_boundaries (core cp) = nil.

Parameter Failure : Syntax.Program -> Type.
Parameter failure_core : forall {p}, Failure p -> Core p.
Parameter rejected : forall {p} (f : Failure p), core_diagnostics (failure_core f) <> nil.

Parameter Outside : Syntax.Program -> Type.
Parameter outside_core : forall {p}, Outside p -> Core p.
Parameter outside_clean : forall {p} (o : Outside p), core_diagnostics (outside_core o) = nil.
Parameter outside_blocked : forall {p} (o : Outside p), core_boundaries (outside_core o) <> nil.

Inductive Outcome (p : Syntax.Program) : Type :=
| Compiled     (cp : Program) (Hcp : source cp = p)
| Rejected     (fail : Failure p)
| OutsideScope (out : Outside p).

Parameter compile : forall p : Syntax.Program, Outcome p.
```

Only the internal mint constructs `Program`, `Failure` or `Outside`; only `Compiled` reaches `Safe.Program`
or `Emit.Image`.

## 3. Requirements, boundaries, and the internal partial analysis

**Kind** is what Go says an object is, independent of what Fido implements.

```coq
Inductive ObjectKind : Type :=
| TypeObject | ConstantObject | VariableObject | FunctionObject | BuiltinObject | NilObject.

Inductive ObjectOrigin (p : Syntax.Program) : Type :=
| Predeclared : Names.PredeclaredName -> ObjectOrigin p
| SourceBound : Index.BindingSiteRef p -> ObjectOrigin p
| MainObject  : Index.MainRef p -> ObjectOrigin p.

Parameter object_origin : forall {p} {i} {ph : Phase i}, ObjectRef ph -> ObjectOrigin p.
Parameter object_kind   : forall {p} {i} {ph : Phase i}, ObjectRef ph -> ObjectKind.
```

`iota` is a `ConstantObject` with an exact contextual rule; `nil` is `NilObject`; `main` is a
`FunctionObject`; predeclared builtins are `BuiltinObject`. `WrongRole` means the **kind** cannot fill the
source role — never that Fido has not implemented the object.

A requirement is an exact semantic obligation at an exact site, indexed by the phase. A type-meaning
requirement carries the bound object and does **not** presuppose an admitted type meaning; the absence of one
is exactly what may be unmet.

```coq
Inductive SemanticRequirement {p} {i : Input p} (ph : Phase i) : Type :=
| TypeMeaningReq
    (u : Index.NameUseRef p) (b : PhaseBindingFact ph u) (o : ObjectRef ph)
| ValueMeaningReq
    (u : Index.NameUseRef p) (b : PhaseBindingFact ph u) (o : ObjectRef ph)
| ApplicationReq
    (a : Index.ApplicationRef p)
    (hf : PhaseExprFact ph (Index.application_head a))
    (cand : TargetCandidate hf)
    (args : PhaseArgFacts ph a)
    (prof : ArgumentProfile ph a)
| StatementReq
    (s : Index.ExpressionStatementRef p) (ef : PhaseExprFact ph (Index.statement_expression s))
| UnaryReq
    (n : Index.UnaryRef p) (op : Syntax.UnaryOp) (of_ : PhaseExprFact ph (Index.unary_operand n)).
```

`ApplicationReq` carries no result demand: intrinsic application support and use-context result consumption
are different facts, and §7 owns the latter. The argument profile is what lets one `len` object support
strings at C7, aggregates at C10 and channels at C14 — `make(slice)` and `make(channel)` are two
requirements over one identity.

One executable decision, and only its negative branch mints a boundary:

```coq
Parameter RequirementSatisfied :
  forall {p} {i : Input p} {ph : Phase i}, SemanticRequirement ph -> Prop.
Parameter requirement_dec :
  forall {p} {i : Input p} {ph : Phase i} (r : SemanticRequirement ph),
    { RequirementSatisfied r } + { ~ RequirementSatisfied r }.

Parameter boundary_requirement :
  forall {p} {i} {ph : Phase i}, ScopeBoundary ph -> SemanticRequirement ph.
Parameter boundary_missing :
  forall {p} {i} {ph : Phase i} (b : ScopeBoundary ph),
    ~ RequirementSatisfied (boundary_requirement b).
```

`ScopeBoundary` is sealed: no public constructor, so no client pairs an independently proved binding with an
independently proved negative. Canonicality uses a **proof-free** key, never equality of proof-rich dependent
requirements:

```coq
Inductive RequirementKind : Type :=
| KTypeMeaning | KValueMeaning | KApplication | KStatement | KUnary.

Record BoundaryKey : Type := MakeBoundaryKey {
  bk_site    : Index.Key;
  bk_kind    : RequirementKind;
  bk_object  : option ErasedObjectOrigin;
  bk_profile : option ErasedProfile }.

Parameter boundary_key : forall {p} {i} {ph : Phase i}, ScopeBoundary ph -> BoundaryKey.
```

The public boundary view preserves the exact anchor and resolved object without exposing proof constructors:

```coq
Inductive BoundaryView : Type :=
| MissingTypeMeaning     (site : Index.Key) (obj : ErasedObjectOrigin)
| MissingValueMeaning    (site : Index.Key) (obj : ErasedObjectOrigin)
| MissingApplicationRule (site : Index.Key) (tgt : ErasedTarget) (prof : ErasedProfile)
| MissingStatementRule   (site : Index.Key) (form : ErasedForm)
| MissingUnaryRule       (site : Index.Key) (op : Syntax.UnaryOp) (form : ErasedForm).

Parameter boundary_view : forall {p} {i} {ph : Phase i}, ScopeBoundary ph -> BoundaryView.
```

No certified value contains a roadmap or ledger-row identifier. `.review/closure.csv` maps a stable
`BoundaryView` to the milestone that owes its rule, outside the certified model.

**Partial analysis is internal and sealed.** Each internal site result retains the exact site, the exact
predecessor phase object, and either its exact supported fact, its exact root diagnostic, its exact root
boundary, or — when blocked — the exact dependency edge and the exact predecessor result that blocked it.
A blocked site adds no diagnostic and no boundary and mints no placeholder type, object, fact or plan. There
is no public constructor for a partial site result; the public surface is exactly the total accepted queries
of §9, the canonical diagnostics of a `Failure` and the canonical boundaries of an `Outside`.

## 4. Source topology

```coq
(* Names *)
Record OrdinaryIdentifier : Type := MakeOrdinary {
  ordinary_identifier : Identifier;
  ordinary_not_blank  : spelling ordinary_identifier <> "_"%string }.

(* Collections *)
Record NonEmpty (A : Type) : Type := MakeNonEmpty { ne_first : A; ne_rest : list A }.

(* Float *)
Record NonNegativeDecimal : Type := MakeNonNegDecimal {
  nnd_decimal : Decimal;
  nnd_nonneg  : (0 <= coefficient nnd_decimal)%Z }.

(* Syntax *)
Inductive BindingName : Type := Named (n : Names.OrdinaryIdentifier) | Blank.
Inductive UnaryOp : Type := UnaryMinus.

Inductive Literal : Type :=
| IntegerLiteral : N -> Literal
| FloatLiteral   : Float.NonNegativeDecimal -> Literal
| StringLiteral  : string -> Literal.

Inductive TypeExpr : Type := NamedType (n : Names.OrdinaryIdentifier).

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

An application head is one real child expression occurrence under the `ApplicationHead` role; there is no
`ApplicationHead` source category, kind or reference. Literals carry magnitude; every negative numeric source
value is `Unary UnaryMinus`. `Blank` creates no object. `Block` is reached only through `Main` at C6. Short
declarations are function-local. A package block is a semantic scope, not a source construct.

## 5. Index and use topology

One kind and view per source category. No peer node for call versus conversion, `complex` versus `println`, a
name expression versus the same occurrence, an application head versus its exact child, or a top-level wrapper
versus the declaration it contains.

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
Parameter direct_occupies : forall {p} (u : DirectExprUseRef p),
  Index.OccupiesRole (direct_parent u) (direct_child u) (direct_role u).

Parameter InheritedConstUseRef : Syntax.Program -> Type.

Inductive ExprUseRef (p : Syntax.Program) : Type :=
| DirectUse    : DirectExprUseRef p -> ExprUseRef p
| InheritedUse : InheritedConstUseRef p -> ExprUseRef p.
```

`DirectExprUseRef` covers every ordinary expression child — head, argument, unary operand, statement
expression, const initializer, var initializer, short right side. No public reference is a parent plus an
unchecked natural. `InheritedConstUseRef` stays distinct because the current spec has no expression child; it
retains the exact current spec, current binding-name occurrence, enclosing declaration, nearest preceding
explicit spec, predecessor expression at the corresponding position, optional predecessor type, current
structural `iota`, and proofs of same-declaration, nearest-predecessor and corresponding position.

## 6. Typing

`Typing` sees only `Names`, `Syntax` and `Index`. `Compilable` constructs the exact inputs from retained
bindings; `Typing` gives them meaning. An unsupported predeclared type object stays an exact `Compilable`
object and raises a type-meaning boundary **before** any `TypeTarget` is minted.

```coq
Inductive TypeTarget (p : Syntax.Program) : Type :=
| PredeclaredTarget : BasicType -> TypeTarget p
| AliasTarget       : Index.AliasSpecRef p -> TypeTarget p
| DefinedTarget     : Index.BoundDefinedTypeRef p -> TypeTarget p.

Parameter ResolvedTypeEquations : Syntax.Program -> Type.
Parameter GraphOutcome : forall {p}, ResolvedTypeEquations p -> Type.
Parameter TypeGraphEvidence : forall {p}, ResolvedTypeEquations p -> Type.
Parameter TypeCycle : forall {p}, ResolvedTypeEquations p -> Type.
Parameter resolve_graph : forall {p} (eqs : ResolvedTypeEquations p), GraphOutcome eqs.
Parameter graph_acyclic : forall {p} {eqs : ResolvedTypeEquations p},
  GraphOutcome eqs -> option (TypeGraphEvidence eqs).
Parameter graph_cycle : forall {p} {eqs : ResolvedTypeEquations p},
  GraphOutcome eqs -> option (TypeCycle eqs).

Parameter Env : forall {p} (eqs : ResolvedTypeEquations p), TypeGraphEvidence eqs -> Type.
Parameter build_env : forall {p} (eqs : ResolvedTypeEquations p) (ev : TypeGraphEvidence eqs),
  Env eqs ev.

Parameter TypeForm     : forall {p} {eqs} {ev}, Env eqs ev -> Type.
Parameter SemanticType : forall {p} {eqs} {ev}, Env eqs ev -> Type.
Parameter basic_form   : forall {p} {eqs} {ev} (env : Env eqs ev), BasicType -> TypeForm env.
Parameter form_type    : forall {p} {eqs} {ev} {env : Env eqs ev}, TypeForm env -> SemanticType env.

Parameter Resolves : forall {p} {eqs} {ev}, Env eqs ev -> TypeTarget p -> SemanticType env -> Prop.
Parameter denote : forall {p} {eqs} {ev} (env : Env eqs ev) (t : TypeTarget p),
  { s : SemanticType env | Resolves env t s }.

Parameter underlying     : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> TypeForm env.
Parameter identicalb     : forall {p} {eqs} {ev} (env : Env eqs ev),
  SemanticType env -> SemanticType env -> bool.
Parameter assignableb    : forall {p} {eqs} {ev} (env : Env eqs ev),
  SemanticType env -> SemanticType env -> bool.
Parameter convertibleb   : forall {p} {eqs} {ev} (env : Env eqs ev),
  SemanticType env -> SemanticType env -> bool.
Parameter representableb : forall {p} {eqs} {ev} (env : Env eqs ev),
  SemanticType env -> Constant -> bool.
Parameter TypedConstant  : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> Type.

Parameter TypeView : Type.
Parameter type_view : forall {p} {eqs} {ev} {env : Env eqs ev}, SemanticType env -> TypeView.
```

A defined semantic type exists only through `denote` on an exact `DefinedTarget` resolved in the exact
environment, so a cyclic, rejected or blocked declaration cannot produce one. An alias returns its target's
semantic type and mints no identity. `underlying` returns a `TypeForm`, never a defined semantic type. C6's
`TypeForm` has only the admitted basic forms; later milestones extend it. `TypeView` is the derived
proof-free representation diagnostics use, and is not a second semantic authority. There is no universal
`TypeIdentity`.

## 7. Static phase order, facts, and result consumption

An initializer determines the type of `var x = e` and `x := e`, so declaration elaboration is interleaved, in
package dependency order and local source order. **Scope construction depends only on the early binding
disposition**, never on the later typed static variable.

```text
exact Input
→ scope forest + early binder disposition + object identities
→ all name bindings + structural uses
→ resolved type equations → graph outcome → exact Env or exact type cycle
→ package const/var dependency graph from retained bindings → exact order or exact cycle
→ declaration elaboration, in package dependency order and local source order:
    → bottom-up initializer expression facts
    → exact use facts
    → exact result plan
    → constant / variable semantic fact
    → exact typed static-variable refinement where applicable
→ remaining bottom-up expression and application facts
→ unused-local result
→ root diagnostics + root boundaries
```

```coq
Inductive BinderDisposition {p} {i} (ph : Phase i) : Type :=
| DispBlank
| DispDeclares (o : ObjectRef ph)
| DispReuses   (o : ObjectRef ph) (Hsame : SameBlockVariable ph o).
```

`DispReuses` names the exact existing **object**, not a typed static variable, so scopes are built before any
type decision. After initializer facts, type decisions and result plans exist, the exact typed
`StaticVariable` is minted and the accepted short-LHS fact projects blank, a new exact static variable, or an
existing exact static variable.

| declaration | scope begins |
|---|---|
| package `const`, `var`, `type`, `main` | the package block |
| local `const` spec | after the `ConstSpec` |
| local `var` spec | after the `VarSpec` |
| short-variable new binding | after the `ShortVarDecl` |
| **local `type` spec** | **at the identifier in the `TypeSpec`** |
| predeclared object | the outer universe block |
| blank | never |

Scopes and both graphs are per package, keyed by the parent directory the input already retains, built from
all files of that package before package-level resolution and rejecting duplicates without overwrite. The type
graph and the package const/var dependency graph stay distinct; C11 consumes the same dependency object and
adds no peer graph.

**Result form.** A result is not classified by the syntax that produced it. `referenced_object` and
`result_form` are independent projections, so a name retains both its exact object and its exact results.

```coq
Inductive ResultAtom {p} {i} (ph : Phase i) : Type :=
| UntypedConstant   (c : Typing.Constant)
| TypedConstantAtom (s : PhaseSemanticType ph) (tc : PhaseTypedConstant ph s)
| ValueResult       (s : PhaseSemanticType ph).

Inductive ResultForm {p} {i} (ph : Phase i) : Type :=
| FixedResults     (v : list (ResultAtom ph))
| ContextualResult (r : ContextualRule ph)
| NoStandaloneResult.
```

```text
literal        referenced_object = None                       result_form = one constant
true / false   referenced_object = exact predeclared constant  result_form = one constant
variable name  referenced_object = exact variable object       result_form = one value
type name      referenced_object = exact type object           result_form = NoStandaloneResult
println name   referenced_object = exact builtin object        result_form = NoStandaloneResult
iota           referenced_object = exact iota object           result_form = Contextual iota rule
nil            referenced_object = exact nil object            result_form = Contextual nil rule
```

**Result consumption** is one abstract `ResultPlan` indexed by the exact plan site — not a two-case label.
It retains the exact target occurrences, the exact right-hand expression uses, each exact result vector, the
exact legal pairing, blank consumption, target types, defaulting, assignability, representability, and the
short-declaration new-or-reused classification where applicable. Its construction relation distinguishes
several expressions each supplying one result from one expression supplying the complete sequence. Later
assignments and returns extend the same relation under their own context rules and add no peer arity logic.
Inherited const initialization builds a new current-spec plan from the inherited **source uses** under the
current `iota`; it never reuses the predecessor's resolved plan.

## 8. Application

```coq
Parameter HeadCallable :
  forall {p} {i} {ph : Phase i} {h : Index.ExprRef p}, PhaseExprFact ph h -> Type.

Inductive ApplicationTarget {p} {i} {ph : Phase i} {h : Index.ExprRef p}
                            (f : PhaseExprFact ph h) : Type :=
| ConversionTarget (s : PhaseSemanticType ph) (Hs : HeadDenotesType f s)
| CallableTarget   (c : HeadCallable f).
```

`HeadCallable` is an abstract refinement of the exact head expression fact. At C6 predeclared callable objects
inhabit it; at C9 an expression producing a function value inhabits the **same** relation. **C9 adds no
constructor to `ApplicationTarget`.**

`ApplicationFact` is a dependent view of the exact application `ExpressionFact`, not a peer table, and exposes
the exact application occurrence, head occurrence and head fact, target, ordered argument uses, exact child
expression facts, exact argument-use facts, exact result vector, and the reflected acceptance proof.

Admitted C6 rules:

- **conversion** — exactly one argument, one result, through the one `Typing` convertibility and
  representability authority, retaining constant-versus-nonconstant status and rerunning no resolution;
- **`complex`** — exactly two arguments:

  | arguments | result |
  |---|---|
  | two untyped numeric constants valid for the real/imaginary rule | one untyped complex constant |
  | one untyped, one typed floating | the untyped operand converts to the **exact type** of the typed one |
  | two typed operands with **identical semantic types** whose underlying form is `float32` | `complex64` |
  | two typed operands with **identical semantic types** whose underlying form is `float64` | `complex128` |
  | two typed operands whose semantic types are not identical | rejected |

  Two distinct defined types are **not** accepted merely because their underlying forms match; identity is
  decided by `identicalb`, and the defined-type rule follows the pinned Go rule through exact identity plus
  underlying form.

- **`println`** — a variadic list, each argument an untyped constant or a value whose underlying form is an
  admitted basic form, untyped constants defaulted first. Zero results, no C6 runtime effect.

Every other predeclared callable resolves correctly and raises an `ApplicationReq` boundary for the exact
missing profile. `main()` is the same case: valid Go, no C6 function objects, so the head resolves to the
exact `MainObject` and its requirement is unmet.

`StatementEligible` is a separate executable and reflected judgment over the exact expression fact; result
count alone does not decide it. Result-use demand is not part of intrinsic application support — result
plans and statement eligibility consume the exact result vector separately.

## 9. Accepted public queries

Partial facts stay internal to the exact phase. Every public fact is **total** over an accepted
`Compilable.Program`, following the existing accepted-facts pattern. `Failure` and `Outside` retain the same
core and phase but expose none of this.

```coq
Parameter Object : Program -> Type.

Parameter BindingFact : forall cp : Program, Index.NameUseRef (source cp) -> Type.
Parameter binding_fact : forall cp u, BindingFact cp u.

Parameter BinderFact : forall cp : Program, Index.BindingSiteRef (source cp) -> Type.
Parameter binder_fact : forall cp s, BinderFact cp s.

Parameter ExpressionFact : forall cp : Program, Index.ExprRef (source cp) -> Type.
Parameter expression_fact : forall cp r, ExpressionFact cp r.

Parameter UseFact : forall cp : Program, ExprUseRef (source cp) -> Type.
Parameter use_fact : forall cp u, UseFact cp u.

Parameter ApplicationFact : forall cp : Program, Index.ApplicationRef (source cp) -> Type.
Parameter application_fact : forall cp a, ApplicationFact cp a.

Parameter ResultPlan : forall cp : Program, Index.PlanSiteRef (source cp) -> Type.
Parameter result_plan : forall cp s, ResultPlan cp s.

Parameter StaticVariable : Program -> Type.
Parameter static_variable_object : forall {cp}, StaticVariable cp -> Object cp.
Parameter static_variable_type : forall {cp} (v : StaticVariable cp), AcceptedSemanticType cp.

Parameter referenced_object : forall {cp} {r}, ExpressionFact cp r -> option (Object cp).
Parameter result_form : forall {cp} {r}, ExpressionFact cp r -> AcceptedResultForm cp.
Parameter object_kind_of : forall {cp}, Object cp -> ObjectKind.
Parameter accepted_env : forall cp : Program, AcceptedEnv cp.
Parameter package_dependency_fact : forall cp (k : Index.PackageRef (source cp)), DependencyFact cp k.
```

A named var declaration or new short binding creates one exact `StaticVariable` — **that object is the
static slot**, a refinement and projection of the exact semantic object, never an independent id or registry
entry. Constants, types, blank names and `main` create none. C7 maps it to a dynamic place.

## 10. Safe and Render

`Safe` keeps `Property`, the sealed certificate retaining the exact compiled capability, and nothing else.
`Safe.Value`, `value_type`, `ValueWellFormed`, `value_well_formedb`, `ValueDenotesConstant`,
`typed_constant_to_value`, `resolved_constant_value`, `eval_expr`, `eval_stmt`, `eval_decl` and `eval_file`
are deleted; §12 records where each guarantee goes.

`Render` is structural and performs no binding or type lookup. `"-" ++ render e` is wrong: a nested unary
emits `--x` and retokenizes.

```coq
Inductive Prec : Type := PrimaryPrec | UnaryPrec.
Definition prec (e : Syntax.Expr) : Prec :=
  match e with Syntax.Unary _ _ => UnaryPrec | _ => PrimaryPrec end.
Parameter render_at : Prec -> Syntax.Expr -> string.
```

`render_at r e` parenthesizes exactly when `prec e` binds looser than `r`, never otherwise.

```text
render (Unary UnaryMinus e) = "-" ++ render_at PrimaryPrec e
render (Application h args) = render_at PrimaryPrec h ++ "(" ++ join(", ", map render args) ++ ")"
render_stmt (ExprStmt e, n) = indent(n) ++ render e ++ NL
```

Frozen outputs: `-1`; `-(-x)`; `-T(x)` with minimal parentheses since a call binds tighter than unary;
`f(x)`; `f(-x)`; `(-f)(x)`. One literal, one unary, one application and one expression-statement renderer
replace the special complex, conversion and `println` paths. **Every pre-C6 generated byte is preserved
exactly.** File level keeps the existing bytes: the header line, a blank line, the package clause, a blank
line before each top-level declaration, and the exact final newline; within a declaration one tab per block
depth, comma-space separators, no trailing whitespace, direct source spelling, an inherited const spec
rendering names only, one spec ungrouped, and zero or two-or-more grouped with the zero branches exactly
`const ()`, `var ()`, `type ()`.

## 11. Diagnostics

`DiagnosticCode` is an inductive of constructors, extended not replaced. Every accepted current constructor
keeps its public meaning, carrier, code and anchors.

| constructor | code | status |
|---|---|---|
| `InvalidConversion (primary : Index.ApplicationRef p) (head : Index.ExprRef p) (operand : Index.ExprRef p) (outer : list (Index.ApplicationRef p)) (target : TypeView) (operand_status : ConstantInfo)` | `CodeInvalidConversion` | carrier changed: anchors an `Application`, not the deleted `Convert`; `TypeNameRef` becomes the head `ExprRef`; `SemanticType` becomes the proof-free `TypeView` |
| `DefaultNotRepresentable (primary : Index.ExprRef p) (exact_constant : Constant) (default_target : TypeView)` | `CodeDefaultNotRepresentable` | retained; payload becomes `TypeView` |
| `MainRedeclared (later : Index.DeclRef p) (earlier : Index.DeclRef p)` | `CodeMainRedeclared` | retained unchanged |
| `MissingMainEntry (pkg : PackageRef p)` | `CodeMissingMainEntry` | retained unchanged |
| `BuildOutputIsDirectory (pkg : PackageRef p) (output_name : string)` | `CodeBuildOutputIsDirectory` | retained unchanged |
| `DuplicateBinding (later : Index.BindingSiteRef p) (earlier : Index.BindingSiteRef p)` | `CodeDuplicateBinding` | new |
| `InitMisuse (site : Index.BindingSiteRef p)` | `CodeInitMisuse` | new |
| `UnresolvedName (u : Index.NameUseRef p)` | `CodeUnresolvedName` | new |
| `WrongRole (u : Index.NameUseRef p) (required : Index.UseRole) (actual : ObjectKind)` | `CodeWrongRole` | new; carries Go kind and required role, never implementation support |
| `NotApplicable (a : Index.ApplicationRef p) (actual : ObjectKind)` | `CodeNotApplicable` | new |
| `TypeCycleDiag (eqs : ResolvedTypeEquations p) (c : Typing.TypeCycle eqs)` | `CodeTypeCycle` | new; evidence indexed by the exact type equations |
| `DependencyCycleDiag (g : DependencyGraph p) (c : DependencyCycle g)` | `CodeDependencyCycle` | new; evidence indexed by the exact dependency graph |
| `FirstSpecInherited (s : Index.ConstSpecRef p)` | `CodeFirstSpecInherited` | new |
| `ResultMismatch (site : Index.PlanSiteRef p) (targets : nat) (observed : list ErasedResultVector)` | `CodeResultMismatch` | new |
| `ShortDeclNoNew (s : Index.StatementRef p)` | `CodeShortDeclNoNew` | new |
| `ShortRedeclType (site : Index.BindingSiteRef p) (existing : TypeView) (found : TypeView)` | `CodeShortRedeclType` | new |
| `NilNoTarget (r : Index.ExprRef p)` | `CodeNilNoTarget` | new |
| `IotaNoContext (r : Index.ExprRef p)` | `CodeIotaNoContext` | new |
| `NotAssignable (u : ExprUseRef p) (target : AssignmentTargetAnchor p) (from : TypeView) (to : TypeView)` | `CodeNotAssignable` | new; `AssignmentTargetAnchor` is a sum over an explicit `TypeUseRef` and an inferred or short-declaration target that has none |
| `UnusedLocal (site : Index.BindingSiteRef p)` | `CodeUnusedLocal` | new |
| `BadArgument (u : DirectExprUseRef p) (why : ArgumentReason)` | `CodeBadArgument` | new |
| `BadOperand (u : DirectExprUseRef p) (why : OperandReason)` | `CodeBadOperand` | new |
| `NotStatement (s : Index.ExpressionStatementRef p) (why : IneligibleReason)` | `CodeNotStatement` | new |

A failed preflight still precedes a package's semantic errors; otherwise one canonical source order per
package. Unavailable semantics are boundaries, never diagnostics. Boundary erasure is separate from
diagnostic erasure.

## 12. Migration of accepted guarantees

`OutsideScope` makes two current statements **false as written**: an invalid program may depend on an
unavailable semantic root, so C6 cannot always establish its downstream invalidity, and it is honestly
`OutsideScope` rather than `Rejected`. Both gain the no-boundary premise.

```coq
Definition InScope (p : Syntax.Program) : Prop :=
  core_boundaries (elaboration_core (elaborate p)) = nil.
```

| current guarantee | disposition |
|---|---|
| `compile_complete` | **restated**: `Admissible p -> InScope p -> exists cp Hcp, compile p = Compiled cp Hcp` |
| `compile_rejected_of_inadmissible` | **restated, not retained**: `InScope p -> ~ Admissible p -> exists fail, compile p = Rejected fail`. The unpremised form is false. |
| `elaboration_accepted_iff_admissible` | **restated**: `InScope p -> (core_diagnostics (elaboration_core (elaborate p)) = nil <-> Admissible p)` |
| `elaboration_rejected_iff_inadmissible` | **restated, not retained**: same `InScope` premise; the unpremised converse is false |
| `compile_ok_valid` | retained unchanged |
| `compile_rejected_not_admissible` | retained unchanged — rejection soundness needs no premise |
| `compile_program_typed` | retained; the fixed resolver becomes the binding phase |
| `compile_ok_of_source_spec_valid_b` | restated with the `InScope` premise |
| `program_of_admissible`, `capability_of_admissible`, `capability_source`, `capability_is_compile_outcome` | restated with the `InScope` premise |
| `Safe.eval_expr` and its lemmas `eval_expr_resolved`, `eval_expr_resolved_type`, `eval_expr_resolved_value`, `eval_projects_stored_float_runtime`, `eval_projects_stored_complex_runtime`, `eval_expr_denotes`, `eval_zero_sign_agnostic`, `eval_string_value`, `eval_string_resolved_type` | deleted from `Safe` at C6; re-proved at C7 over `Runtime.Value`. `SPEC-X034`, `SPEC-X035` and `SPEC-X036` own them. |
| `Safe.Value`, `value_type`, `ValueWellFormed`, `value_well_formedb`, `ValueDenotesConstant`, `typed_constant_to_value`, `resolved_constant_value` | deleted from `Safe`; C7 `Runtime` |
| `Render.const_info_denotes`, `Render.const_info_denotes_functional` | retained at C6 — spelling denotes constant status, no runtime value |
| `Render.resolved_expr_denotes` | **split**: the constant/spelling half retained at C6; the value half deferred to C7 with `SPEC-X034` |
| `Render.resolved_string_denotes`, `boundary_max`, `boundary_min` | deferred to C7 with the value half |

No obsolete name survives as an alias, and no guarantee is dropped without a row naming where it goes.

## 13. Public theorems

```coq
Theorem decision_accepted_iff : forall p (a : Elaboration p),
  (exists Hd Hb, decision a = AcceptedDecision Hd Hb)
  <-> core_diagnostics (elaboration_core a) = nil /\ core_boundaries (elaboration_core a) = nil.

Theorem decision_rejected_iff : forall p (a : Elaboration p),
  (exists Hd, decision a = RejectedDecision Hd) <-> core_diagnostics (elaboration_core a) <> nil.

Theorem decision_outside_iff : forall p (a : Elaboration p),
  (exists Hd Hb, decision a = OutsideDecision Hd Hb)
  <-> core_diagnostics (elaboration_core a) = nil /\ core_boundaries (elaboration_core a) <> nil.

Theorem compiled_retains_core : forall p cp (Hcp : source cp = p),
  compile p = Compiled cp Hcp ->
  eq_rect (source cp) Core (core cp) p Hcp = elaboration_core (elaborate p).

Theorem rejected_retains_core : forall p (fail : Failure p),
  compile p = Rejected fail -> failure_core fail = elaboration_core (elaborate p).

Theorem outside_retains_core : forall p (out : Outside p),
  compile p = OutsideScope out -> outside_core out = elaboration_core (elaborate p).

Theorem compiled_admissible : forall p cp (Hcp : source cp = p),
  compile p = Compiled cp Hcp -> Admissible (source cp) /\ InScope (source cp).

Theorem rejected_not_admissible : forall p (fail : Failure p),
  compile p = Rejected fail -> ~ Admissible p.

Theorem in_scope_accepted_iff : forall p, InScope p ->
  (core_diagnostics (elaboration_core (elaborate p)) = nil <-> Admissible p).

Theorem in_scope_inadmissible_rejected : forall p, InScope p -> ~ Admissible p ->
  exists fail, compile p = Rejected fail.

Theorem in_scope_admissible_compiled : forall p, Admissible p -> InScope p ->
  exists cp Hcp, compile p = Compiled cp Hcp.

Theorem outside_claims_nothing : forall p (out : Outside p),
  compile p = OutsideScope out ->
  core_diagnostics (outside_core out) = nil /\ core_boundaries (outside_core out) <> nil.

Theorem requirement_dec_reflects :
  forall p (i : Input p) (ph : Phase i) (r : SemanticRequirement ph),
  (exists h, requirement_dec r = left h) <-> RequirementSatisfied r.

Theorem boundary_root_sound : forall p (core : Core p) (b : ScopeBoundary (phase core)),
  In b (core_boundaries core) -> ~ RequirementSatisfied (boundary_requirement b).

Theorem boundary_root_complete :
  forall p (core : Core p) (r : SemanticRequirement (phase core)),
  RequirementRaisedBy (phase core) r -> ~ RequirementSatisfied r ->
  RootRequirement (phase core) r ->
  exists b, In b (core_boundaries core) /\ boundary_requirement b = r.

Theorem boundary_keys_nodup : forall p (core : Core p),
  NoDup (map boundary_key (core_boundaries core)).

Theorem boundary_order_canonical : forall p (core : Core p),
  Sorted boundary_key_lt (map boundary_key (core_boundaries core)).

Theorem blocked_adds_no_boundary :
  forall p (core : Core p) (r : SemanticRequirement (phase core)),
  ~ RootRequirement (phase core) r ->
  forall b, In b (core_boundaries core) -> boundary_requirement b <> r.

Theorem predeclared_complete : forall p (i : Input p) (ph : Phase i) (n : Names.PredeclaredName),
  exists o : ObjectRef ph, object_origin o = Predeclared n /\ InUniverseScope ph o.

Theorem predeclared_shadowed :
  forall p (i : Input p) (ph : Phase i) (s : Index.BindingSiteRef p) (o : ObjectRef ph),
  binder_disposition ph s = DispDeclares o -> forall u, ResolvesAt ph u s -> BoundTo ph u o.

Theorem binding_fact_total : forall cp u, BindingFact cp u.
Theorem expression_fact_total : forall cp r, ExpressionFact cp r.
Theorem result_plan_total : forall cp s, ResultPlan cp s.

Theorem env_provenance : forall cp,
  accepted_env cp = build_env (core_equations cp) (core_graph_evidence cp).

Theorem denote_resolves : forall p eqs ev (env : Env eqs ev) (t : TypeTarget p),
  Resolves env t (proj1_sig (denote env t)).

Theorem alias_no_identity : forall p eqs ev (env : Env eqs ev) (a : Index.AliasSpecRef p),
  proj1_sig (denote env (AliasTarget a)) = proj1_sig (denote env (alias_target_of a)).

Theorem defined_identity_exact : forall p eqs ev (env : Env eqs ev) r1 r2,
  identicalb env (proj1_sig (denote env (DefinedTarget r1)))
                 (proj1_sig (denote env (DefinedTarget r2))) = true <-> r1 = r2.

Theorem underlying_reflect : forall p eqs ev (env : Env eqs ev) s f,
  underlying env s = f <-> UnderlyingRel env s f.
Theorem identical_reflect : forall p eqs ev (env : Env eqs ev) s t,
  identicalb env s t = true <-> Identical env s t.
Theorem assignable_reflect : forall p eqs ev (env : Env eqs ev) s t,
  assignableb env s t = true <-> Assignable env s t.
Theorem convertible_reflect : forall p eqs ev (env : Env eqs ev) s t,
  convertibleb env s t = true <-> Convertible env s t.
Theorem representable_reflect : forall p eqs ev (env : Env eqs ev) s c,
  representableb env s c = true <-> Representable env s c.

Theorem direct_use_provenance : forall p (u : DirectExprUseRef p),
  Index.OccupiesRole (direct_parent u) (direct_child u) (direct_role u).

Theorem inherited_const_provenance : forall p (u : InheritedConstUseRef p),
  NearestPrecedingExplicit (inherited_current u) (inherited_predecessor u)
  /\ CorrespondingPosition (inherited_current u) (inherited_predecessor u) (inherited_position u)
  /\ inherited_iota u = structural_iota_index (inherited_current u).

Theorem expression_object_result_coherent : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o ->
  (object_kind_of o = TypeObject \/ object_kind_of o = BuiltinObject) ->
  result_form f = NoStandaloneResult cp.

Theorem application_target_from_head : forall cp a,
  ApplicationTargetOf (application_fact cp a) (application_head_fact cp a).

Theorem application_results_exact : forall cp a,
  application_results (application_fact cp a)
  = target_result_vector (application_target cp a) (application_args cp a).

Theorem result_plan_pairs_exact : forall cp s,
  PlanPairing (result_plan cp s) (plan_targets cp s) (plan_result_vectors cp s).

Theorem short_binding_classified : forall cp s,
  ShortLeftName s ->
  short_lhs_class cp s = ShortBlank
  \/ (exists v, short_lhs_class cp s = ShortNew v)
  \/ (exists v, short_lhs_class cp s = ShortExisting v).

Theorem static_variable_identity : forall cp (v1 v2 : StaticVariable cp),
  static_variable_object v1 = static_variable_object v2 -> v1 = v2.

Theorem dependency_graph_sound : forall cp k,
  DependencyEdgesFromBindings (package_dependency_fact cp k).

Theorem dependency_cycle_reflect : forall p (g : DependencyGraph p),
  acyclicb g = true <-> ~ exists c : DependencyCycle g, True.

Theorem unused_local_sound : forall cp s,
  In (UnusedLocal s) (core_diagnostics (core cp)) -> ~ ReadsVariableAt cp s.
Theorem unused_local_complete : forall p (core : Core p) s,
  LocalVariableSite (phase core) s -> ~ PhaseReadsVariableAt (phase core) s ->
  In (UnusedLocal s) (core_diagnostics core).

Theorem render_precedence_safe : forall e, RetokenizesAs (render_expr e) e.
Theorem render_bytes_preserved : forall p, PreC6Program p ->
  render_program (migrate p) = legacy_render_program p.
```

Every declaration above uses only types introduced earlier in this contract. Proof helpers stay local;
obsolete carrier names do not survive as aliases.

## 14. Review boundaries

**Semantic-root review** stops only when the repository is green and contains: the corrected source and index
roots; the generalized exact phase; phase-indexed objects, facts and requirements; the core-indexed three-way
decision; sealed requirement boundaries with their proof-free key; the module-order-safe type environment with
its actual `build_env`; total accepted-program fact queries; the stable application and result-plan roots;
compiler-owned static variable identity; the old fixed resolver and old expression phase deleted; `Safe.Value`
and `Safe.eval_expr` deleted; no `Runtime` module or machine; and prior generated bytes unchanged.

**Final C6 review** then completes declaration and shadowing behaviour, diagnostics and boundaries, direct
rendering, C6 fixtures, `LAT-077`, generated-artifact evidence, and current document and ledger truth.

C7 is forbidden until Rob accepts C6.

## Done

Package and local `const`/`type`/`var` accepted; a local variable read by `println`; unused local rejected;
cross-file package declarations independent of file order; two packages sharing a spelling without collision;
duplicate package names rejected; local shadowing of package and predeclared names.

```text
type complex int; complex(x)     conversion, accepted
var complex int;  complex(x)     NotApplicable — definite invalidity
type println int; println(x)     conversion, and NotStatement in statement position
var println int;  println(x)     NotApplicable — definite invalidity
```

An unshadowed `len(s)`, a `var x uintptr` and a recursive `main()` each give `OutsideScope` with the exact
unmet requirement and no diagnostic; `type U uintptr; type T U; var x T` gives exactly one root boundary and
two blocked sites. Two defined types with identical underlying `float32` but distinct identity are
**rejected** by `complex`; one defined `float32`-based type used twice is accepted and yields `complex64`.
Short declaration with no new nonblank name rejected; short redeclaration reusing its static variable; blank
declarations creating no object; `true`, `false`, `byte` and `rune` resolving through ordinary binding; alias
preserving identity; a local type spec naming itself rejected as a cycle; package constant and variable cycles
rejected; a package expression depending on a forward constant accepted; a first const spec with an inherited
initializer rejected; an inherited spec taking the predecessor expression under its own `iota`; unshadowed
`nil` and out-of-context `iota` rejected; a `println` argument of a defined type whose underlying form is
`string` accepted; unary minus on a constant and a variable accepted and on a string rejected; `-(-x)`
rendering with its parentheses; every currently accepted program rendering byte-identically after migration;
generated C6 programs passing the pinned Go build with their exact expected observation.

## Preserve

`Syntax.Program` as the sole source authority and the AST as the one IR; `Program` as the opaque C4
capability, with `Failure` and `Outside` retaining the exact core; the retained input, work forest, member
index, outcome trace and sealed core; `Machine.T` uninstantiated; direct rendering and the one
`Emit.Mint.issue` authority; certified-module coverage, the whole-theory audit and controls A-E; every
sealed-capability, mint, transport and positive client control; working-tree and staged-index separation;
no-host-Python; `life.md`.

## Stop

A static identity cannot be indexed by the exact phase without reaching a core field; the boundary key cannot
be made proof-free; a blocked site cannot be recorded without minting a root; `requirement_dec` needs a second
Boolean checker beside it; an accepted fact query cannot be made total over `Program`; the `InScope` premise
cannot be discharged where an accepted guarantee needs it; `Typing` cannot be closed without a `Compilable`
type; `build_env` cannot be given an exact cycle-or-evidence predecessor; `ApplicationTarget` would need a C9
constructor; `complex` cannot decide identity without a second type authority; a theorem in §13 cannot be
stated over the names defined here; `LAT-077` needs a diagnostic the phase cannot produce; a run relation,
value, store, environment or machine is needed for a C6 row; implementation needs a placeholder, compatibility
path, trusted shortcut, fuel, bound or premature future state.
