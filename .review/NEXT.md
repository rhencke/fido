# C6 — the static semantic foundation

Review: contract

Goal:
Ordinary names acquire meaning only through binding. C6 lands the complete predeclared identity catalog, one
type environment, exact constants, expression/use/application facts, one result-consumption root,
compiler-owned static variable identity, both dependency objects, and a three-way decision that never calls
unmodelled Go a rejection.

**C6 is entirely static.** No `Runtime` module, no value, place, store, environment or `Machine.T`. C7
introduces all of them as one vertical, per `ARCH-11`.

## 1. Module order and ownership

```text
Decimal Integer Float Complex FilePath ModulePath Version Collections Names Syntax Index Typing
Compilable Machine Safe Render Emit
```

`ARCHITECTURE.md` §1 states the ownership law once. `Typing` sees only `Names`, `Syntax` and `Index`.
`Float` owns decimal representation, so `Float.NonNegativeDecimal` lives there.

## 2. Source

```coq
(* Names *)
Record OrdinaryIdentifier : Type := MakeOrdinary {
  ordinary_identifier : Identifier;
  ordinary_not_blank  : spelling ordinary_identifier <> "_"%string }.
Parameter PredeclaredName : Type.
Parameter predeclared_spelling : PredeclaredName -> string.
Parameter predeclared_eqb : PredeclaredName -> PredeclaredName -> bool.
Parameter classify_spelling : string -> option PredeclaredName.

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

An application head is one child expression occurrence under the `ApplicationHead` role. Literals carry
magnitude; every negative numeric value is `Unary UnaryMinus`. Short declarations are function-local; a
package block is a semantic scope, not a source construct.

**`Main`'s disposition is decided now.** `Main` is **not** permanent. C9 introduces the one general
function-declaration root and, in the same milestone, deletes `Main`, migrating every source value to that
root. No compatibility constructor survives and `func main()` never has two representations. C6 adds no
general function scaffold in advance.

## 3. Index

One kind and view per source category; no peer node for call versus conversion, `complex` versus `println`, a
name expression versus the same occurrence, a head versus its child, or a wrapper versus the declaration it
contains.

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
Inductive UseRole : Type := TypeNameRole | ValueNameRole | HeadNameRole.

Parameter DirectExprUseRef : Syntax.Program -> Type.
Parameter direct_parent : forall {p}, DirectExprUseRef p -> Index.Snapshot.NodeRef p.
Parameter direct_child  : forall {p}, DirectExprUseRef p -> Index.ExprRef p.
Parameter direct_role   : forall {p}, DirectExprUseRef p -> Index.Role p.
Parameter direct_occupies : forall {p} (u : DirectExprUseRef p),
  Index.OccupiesRole (direct_parent u) (direct_child u) (direct_role u).

Parameter InheritedConstUseRef : Syntax.Program -> Type.
Parameter inherited_current     : forall {p}, InheritedConstUseRef p -> Index.ConstSpecRef p.
Parameter inherited_predecessor : forall {p}, InheritedConstUseRef p -> Index.ConstSpecRef p.
Parameter inherited_position    : forall {p}, InheritedConstUseRef p -> nat.
Parameter inherited_iota        : forall {p}, InheritedConstUseRef p -> nat.
Parameter NearestPrecedingExplicit : forall {p}, Index.ConstSpecRef p -> Index.ConstSpecRef p -> Prop.
Parameter CorrespondingPosition : forall {p},
  Index.ConstSpecRef p -> Index.ConstSpecRef p -> nat -> Prop.

Inductive ExprUseRef (p : Syntax.Program) : Type :=
| DirectUse    : DirectExprUseRef p -> ExprUseRef p
| InheritedUse : InheritedConstUseRef p -> ExprUseRef p.
```

## 4. Typing

```coq
Inductive BasicType : Type :=
| BoolBasic | IntegerBasic (k : Integer.Kind) | FloatBasic (k : Float.Kind)
| ComplexBasic (k : Complex.Kind) | StringBasic.

Parameter RawTypeTarget : Syntax.Program -> Type.
Parameter PredeclaredRaw : forall {p}, BasicType -> RawTypeTarget p.
Parameter AliasRaw   : forall {p}, Index.AliasSpecRef p -> RawTypeTarget p.
Parameter DefinedRaw : forall {p}, Index.BoundDefinedTypeRef p -> RawTypeTarget p.

Parameter ResolvedTypeEquations : Syntax.Program -> Type.
Parameter TypeGraphEvidence : forall {p}, ResolvedTypeEquations p -> Type.
Parameter TypeCycle : forall {p}, ResolvedTypeEquations p -> Type.

Inductive GraphOutcome {p} (eqs : ResolvedTypeEquations p) : Type :=
| GraphAcyclic : TypeGraphEvidence eqs -> GraphOutcome eqs
| GraphCyclic  : TypeCycle eqs -> GraphOutcome eqs.

Parameter resolve_graph : forall {p} (eqs : ResolvedTypeEquations p), GraphOutcome eqs.

Parameter Env : forall {p} (eqs : ResolvedTypeEquations p), TypeGraphEvidence eqs -> Type.
Parameter build_env : forall {p} (eqs : ResolvedTypeEquations p) (ev : TypeGraphEvidence eqs), Env eqs ev.

Parameter TypeForm : forall {p} {eqs} {ev}, Env eqs ev -> Type.
Parameter SemanticType : forall {p} {eqs} {ev}, Env eqs ev -> Type.
Parameter basic_form : forall {p} {eqs} {ev} (env : Env eqs ev), BasicType -> TypeForm env.
Parameter form_type  : forall {p} {eqs} {ev} {env : Env eqs ev}, TypeForm env -> SemanticType env.

Parameter ResolvedTypeTarget :
  forall {p} {eqs} {ev}, Env eqs ev -> RawTypeTarget p -> Type.
Parameter denote :
  forall {p} {eqs} {ev} {env : Env eqs ev} {t : RawTypeTarget p},
  ResolvedTypeTarget env t -> SemanticType env.

Parameter underlying : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> TypeForm env.
Parameter identicalb   : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> SemanticType env -> bool.
Parameter assignableb  : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> SemanticType env -> bool.
Parameter convertibleb : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> SemanticType env -> bool.
Parameter representableb : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> Constant -> bool.
Parameter Underlying  : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> TypeForm env -> Prop.
Parameter Identical   : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> SemanticType env -> Prop.
Parameter Assignable  : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> SemanticType env -> Prop.
Parameter Convertible : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> SemanticType env -> Prop.
Parameter Representable : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> Constant -> Prop.

Parameter TypedConstant : forall {p} {eqs} {ev} (env : Env eqs ev), SemanticType env -> Type.
Parameter convert_constant : forall {p} {eqs} {ev} (env : Env eqs ev) (s : SemanticType env) (c : Constant),
  Representable env s c -> TypedConstant env s.
Parameter default_type : forall {p} {eqs} {ev} (env : Env eqs ev), Constant -> SemanticType env.

Parameter TypeView : Type.
Parameter type_view : forall {p} {eqs} {ev} {env : Env eqs ev}, SemanticType env -> TypeView.
```

`build_env` accepts only `GraphAcyclic` evidence, so a cyclic graph cannot produce an environment. `denote`
requires exact successful-resolution evidence, so a cyclic, rejected or blocked declaration mints no semantic
type. An alias resolves to its target's semantic type and mints no identity. `underlying` returns a
`TypeForm`. C6's `TypeForm` has only the basic forms.

## 5. The phase owns static meaning; the core owns the report

The existing exact expression `Phase` inside the exact `Core` is generalized into the permanent
static-analysis object. No peer analyzer is added.

```coq
Module Type STATIC_ANALYSIS.
  Parameter Scopes    : forall {p}, Input p -> Type.
  Parameter Objects   : forall {p} {i : Input p}, Scopes i -> Type.
  Parameter Bindings  : forall {p} {i} {s : Scopes i}, Objects s -> Type.
  Parameter Equations : forall {p} {i} {s} {o : Objects s}, Bindings o -> Type.
  Parameter TypeResolution : forall {p} {i} {s} {o} {b : Bindings o}, Equations b -> Type.
  Parameter Dependencies : forall {p} {i} {s} {o} {b} {te : Equations b}, TypeResolution te -> Type.
  Parameter Facts   : forall {p} {i} {s} {o} {b} {te} {tr : TypeResolution te}, Dependencies tr -> Type.
  Parameter Reports : forall {p} {i} {s} {o} {b} {te} {tr} {d : Dependencies tr}, Facts d -> Type.

  Parameter Phase : forall {p}, Input p -> Type.
  Parameter phase_scopes    : forall {p} {i} (ph : Phase i), Scopes i.
  Parameter phase_objects   : forall {p} {i} (ph : Phase i), Objects (phase_scopes ph).
  Parameter phase_bindings  : forall {p} {i} (ph : Phase i), Bindings (phase_objects ph).
  Parameter phase_equations : forall {p} {i} (ph : Phase i), Equations (phase_bindings ph).
  Parameter phase_types     : forall {p} {i} (ph : Phase i), TypeResolution (phase_equations ph).
  Parameter phase_deps      : forall {p} {i} (ph : Phase i), Dependencies (phase_types ph).
  Parameter phase_facts     : forall {p} {i} (ph : Phase i), Facts (phase_deps ph).
  Parameter phase_reports   : forall {p} {i} (ph : Phase i), Reports (phase_facts ph).
  Parameter build_phase : forall {p} (i : Input p), Phase i.
End STATIC_ANALYSIS.
```

Every stage is indexed by the exact prior object; there is no equality-to-recomputation field. Internal
partial site results are private and retain the exact site, the exact predecessor object, and one of: the
exact supported fact, the exact root diagnostic, the exact root boundary, or the exact dependency edge plus
the exact predecessor result that blocked it. A blocked site mints no placeholder fact, diagnostic or
boundary. The existing work forest, member index, outcome trace and suffix provenance are generalized, not
duplicated.

Scope construction depends only on the early binder disposition, never on the later typed static variable.
Declaration elaboration is interleaved in package dependency order and local source order, because an
initializer determines the type of `var x = e` and `x := e`.

| declaration | scope begins |
|---|---|
| package `const`, `var`, `type`, `main` | the package block |
| local `const` spec | after the `ConstSpec` |
| local `var` spec | after the `VarSpec` |
| short-variable new binding | after the `ShortVarDecl` |
| **local `type` spec** | **at the identifier in the `TypeSpec`** |
| predeclared object | the outer universe block |
| blank | never |

## 6. Objects, requirements, boundaries

```coq
Inductive ObjectKind : Type :=
| TypeObject | ConstantObject | VariableObject | FunctionObject | BuiltinObject | NilObject.

Inductive ObjectOrigin (p : Syntax.Program) : Type :=
| Predeclared : Names.PredeclaredName -> ObjectOrigin p
| SourceBound : Index.BindingSiteRef p -> ObjectOrigin p
| MainObject  : Index.MainRef p -> ObjectOrigin p.

Parameter ObjectRef : forall {p} {i : Input p}, Phase i -> Type.
Parameter object_origin : forall {p} {i} {ph : Phase i}, ObjectRef ph -> ObjectOrigin p.
Parameter object_kind   : forall {p} {i} {ph : Phase i}, ObjectRef ph -> ObjectKind.

Parameter PhaseBindingFact :
  forall {p} {i : Input p} (ph : Phase i), Index.NameUseRef p -> Type.
Parameter bound_object :
  forall {p} {i} {ph : Phase i} {u}, PhaseBindingFact ph u -> ObjectRef ph.

Parameter PhaseApplicationSite :
  forall {p} {i : Input p} (ph : Phase i), Index.ApplicationRef p -> Type.
Parameter PhaseStatementSite :
  forall {p} {i : Input p} (ph : Phase i), Index.ExpressionStatementRef p -> Type.
Parameter PhaseUnarySite :
  forall {p} {i : Input p} (ph : Phase i), Index.UnaryRef p -> Type.

Inductive SemanticRequirement {p} {i : Input p} (ph : Phase i) : Type :=
| TypeMeaningReq  (u : Index.NameUseRef p) (b : PhaseBindingFact ph u)
| ValueMeaningReq (u : Index.NameUseRef p) (b : PhaseBindingFact ph u)
| ApplicationReq  (a : Index.ApplicationRef p) (site : PhaseApplicationSite ph a)
| StatementReq    (s : Index.ExpressionStatementRef p) (site : PhaseStatementSite ph s)
| UnaryReq        (n : Index.UnaryRef p) (site : PhaseUnarySite ph n).

Parameter RequirementSatisfied :
  forall {p} {i : Input p} {ph : Phase i}, SemanticRequirement ph -> Prop.
Parameter requirement_dec :
  forall {p} {i : Input p} {ph : Phase i} (r : SemanticRequirement ph),
  { RequirementSatisfied r } + { ~ RequirementSatisfied r }.
Parameter RootRequirement :
  forall {p} {i : Input p} (ph : Phase i), SemanticRequirement ph -> Prop.

Parameter ScopeBoundary :
  forall {p} {i : Input p} (ph : Phase i), SemanticRequirement ph -> Type.
Parameter boundary_missing :
  forall {p} {i} {ph : Phase i} {r : SemanticRequirement ph},
  ScopeBoundary ph r -> ~ RequirementSatisfied r.

Parameter PackedBoundary : forall {p} {i : Input p}, Phase i -> Type.
Parameter boundary_requirement :
  forall {p} {i} {ph : Phase i}, PackedBoundary ph -> SemanticRequirement ph.
Parameter boundary_evidence :
  forall {p} {i} {ph : Phase i} (b : PackedBoundary ph),
  ScopeBoundary ph (boundary_requirement b).

Parameter RequirementKey : Type.
Parameter requirement_key :
  forall {p} {i} {ph : Phase i}, SemanticRequirement ph -> RequirementKey.
Parameter boundary_key :
  forall {p} {i} {ph : Phase i}, PackedBoundary ph -> RequirementKey.
Parameter key_lt : RequirementKey -> RequirementKey -> Prop.

Inductive BoundaryView : Type :=
| MissingTypeMeaning     (site : Index.Key) (obj : ErasedObjectOrigin)
| MissingValueMeaning    (site : Index.Key) (obj : ErasedObjectOrigin)
| MissingApplicationRule (site : Index.Key) (tgt : ErasedTarget) (prof : ErasedProfile)
| MissingStatementRule   (site : Index.Key) (form : ErasedForm)
| MissingUnaryRule       (site : Index.Key) (op : Syntax.UnaryOp) (form : ErasedForm).
Parameter boundary_view : forall {p} {i} {ph : Phase i}, PackedBoundary ph -> BoundaryView.
```

No requirement constructor accepts an object or profile independent of the fact that established it: the
object is `bound_object b` and the target and profile are projections of `site`. `ScopeBoundary` is indexed by
the exact requirement, its constructor is private, and only the negative branch of `requirement_dec` mints
one. Canonicality is stated over proof-free `RequirementKey`, never over equality of proof-rich requirements.
No certified value contains a roadmap or ledger identifier; `.review/closure.csv` maps a `BoundaryView` to the
milestone that owes its rule.

## 7. Outcome

```coq
Parameter phase : forall {p} (core : Core p), Phase (core_input core).
Parameter core_diagnostics : forall {p}, Core p -> list (DiagnosticReason p).
Parameter core_boundaries  : forall {p} (core : Core p), list (PackedBoundary (phase core)).

Inductive Decision {p} (core : Core p) : Type :=
| AcceptedDecision (Hd : core_diagnostics core = nil) (Hb : core_boundaries core = nil)
| RejectedDecision (Hd : core_diagnostics core <> nil)
| OutsideDecision  (Hd : core_diagnostics core = nil) (Hb : core_boundaries core <> nil).

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
Definition InScope (p : Syntax.Program) : Prop :=
  core_boundaries (elaboration_core (elaborate p)) = nil.
```

Only the internal mint constructs `Program`, `Failure` or `Outside`; only `Compiled` reaches `Safe.Program`
or `Emit.Image`.

## 8. Accepted public facts

Partial facts stay internal to the phase. Every public query is total over an accepted `Program`.

```coq
Parameter Object : Program -> Type.
Parameter object_origin_of : forall {cp}, Object cp -> ObjectOrigin (source cp).
Parameter object_kind_of   : forall {cp}, Object cp -> ObjectKind.

Parameter bound_object_at : forall (cp : Program) (u : Index.NameUseRef (source cp)), Object cp.
Parameter use_role_at : forall (cp : Program) (u : Index.NameUseRef (source cp)), UseRole.

Parameter StaticVariable : forall (cp : Program), Object cp -> Type.

Inductive BinderDisposition (cp : Program) : Type :=
| DispBlank
| DispDeclares (o : Object cp)
| DispReuses   (o : Object cp) (v : StaticVariable cp o).
Parameter binder_disposition :
  forall (cp : Program) (s : Index.BindingSiteRef (source cp)), BinderDisposition cp.

Parameter AcceptedEnv : Program -> Type.
Parameter accepted_env : forall cp : Program, AcceptedEnv cp.
Parameter AcceptedType : forall (cp : Program), Type.
Parameter type_at : forall (cp : Program) (u : Index.NameUseRef (source cp)), option (AcceptedType cp).
Parameter accepted_type_view : forall {cp}, AcceptedType cp -> Typing.TypeView.
Parameter static_variable_type : forall {cp} {o} (v : StaticVariable cp o), AcceptedType cp.

Inductive ResultAtom (cp : Program) : Type :=
| UntypedConstant   (c : Typing.Constant)
| TypedConstantAtom (t : AcceptedType cp) (k : AcceptedTypedConstant cp t)
| ValueResult       (t : AcceptedType cp).

Inductive ContextualResult : Type := IotaResult | NilResult.

Inductive ResultForm (cp : Program) : Type :=
| FixedResults      (v : list (ResultAtom cp))
| ContextualForm    (c : ContextualResult)
| NoStandaloneResult.

Parameter ExpressionFact : forall (cp : Program), Index.ExprRef (source cp) -> Type.
Parameter expression_fact : forall cp r, ExpressionFact cp r.
Parameter referenced_object : forall {cp} {r}, ExpressionFact cp r -> option (Object cp).
Parameter result_form : forall {cp} {r}, ExpressionFact cp r -> ResultForm cp.

Parameter UseFact : forall (cp : Program), ExprUseRef (source cp) -> Type.
Parameter use_fact : forall cp u, UseFact cp u.
Parameter use_target_type : forall {cp} {u}, UseFact cp u -> option (AcceptedType cp).
Parameter use_defaulted : forall {cp} {u}, UseFact cp u -> option (AcceptedType cp).
Parameter use_selected : forall {cp} {u}, UseFact cp u -> list (ResultAtom cp).
Parameter use_assignable : forall {cp} {u} (f : UseFact cp u) (t : AcceptedType cp),
  use_target_type f = Some t -> AcceptedAssignable cp (use_selected f) t.

Parameter HeadCallable : forall {cp} {r}, ExpressionFact cp r -> Type.
Inductive AppTarget {cp} {r} (f : ExpressionFact cp r) : Type :=
| ConversionTarget (t : AcceptedType cp) (Ht : HeadDenotesType f t)
| CallableTarget   (c : HeadCallable f).

Parameter ApplicationFact : forall (cp : Program), Index.ApplicationRef (source cp) -> Type.
Parameter application_fact : forall cp a, ApplicationFact cp a.
Parameter app_head_fact : forall {cp} {a} (af : ApplicationFact cp a),
  ExpressionFact cp (Index.application_head a).
Parameter app_target : forall {cp} {a} (af : ApplicationFact cp a), AppTarget (app_head_fact af).
Parameter app_arg_uses : forall {cp} {a}, ApplicationFact cp a -> list (DirectExprUseRef (source cp)).
Parameter app_profile : forall {cp} {a}, ApplicationFact cp a -> ArgumentProfile cp.
Parameter app_results : forall {cp} {a}, ApplicationFact cp a -> list (ResultAtom cp).
Parameter StatementEligible : forall (cp : Program), Index.ExpressionStatementRef (source cp) -> Prop.
Parameter statement_eligible_dec : forall cp s,
  { StatementEligible cp s } + { ~ StatementEligible cp s }.

Parameter ResultPlan : forall (cp : Program), Index.PlanSiteRef (source cp) -> Type.
Parameter result_plan : forall cp s, ResultPlan cp s.
Parameter plan_targets : forall {cp} {s}, ResultPlan cp s -> list (Index.BindingSiteRef (source cp)).
Parameter plan_sources : forall {cp} {s}, ResultPlan cp s -> list (DirectExprUseRef (source cp)).
Parameter plan_vectors : forall {cp} {s}, ResultPlan cp s -> list (list (ResultAtom cp)).
Parameter plan_pairing : forall {cp} {s} (rp : ResultPlan cp s),
  list (Index.BindingSiteRef (source cp) * ResultAtom cp).
Parameter plan_blank_consumed : forall {cp} {s}, ResultPlan cp s -> list (ResultAtom cp).
Parameter plan_target_types : forall {cp} {s}, ResultPlan cp s -> list (option (AcceptedType cp)).
Parameter plan_short_class : forall {cp} {s},
  ResultPlan cp s -> list (BinderDisposition cp).

Parameter DependencyFact : forall (cp : Program), Index.PackageRef (source cp) -> Type.
Parameter dependency_fact : forall cp k, DependencyFact cp k.
Parameter dependency_order : forall {cp} {k},
  DependencyFact cp k -> list (Index.BindingSiteRef (source cp)).
```

`StaticVariable cp o` is **indexed by the exact object**, so variable identity is intrinsic to the topology
and needs no extensional theorem. A same-block short redeclaration returns the exact existing object.
`ContextualResult` has exactly the two C6 cases; there is no open contextual bucket.

## 9. Application rules

`HeadCallable` is the one lasting refinement of the exact head expression fact. At C6 predeclared callable
objects inhabit it; at C9 an expression producing a function value inhabits the **same** refinement. **C9 adds
no `AppTarget` constructor.**

- **conversion** — one argument, one result, through `convertibleb`/`representableb`, retaining
  constant-versus-nonconstant status and rerunning no resolution.
- **`complex`** — two arguments:

  | arguments | result |
  |---|---|
  | two untyped numeric constants valid for the real/imaginary rule | one untyped complex constant |
  | one untyped, one typed floating | the untyped operand converts to the **exact type** of the typed one |
  | two typed operands with `identicalb env s t = true`, underlying `float32` | `complex64` |
  | two typed operands with `identicalb env s t = true`, underlying `float64` | `complex128` |
  | two typed operands with `identicalb env s t = false` | rejected |

  Two distinct defined types are **rejected** even when their underlying forms match.

- **`println`** — a variadic list, each argument an untyped constant or a value whose underlying form is an
  admitted basic form, untyped constants defaulted first. Zero results, no C6 runtime effect.

Every other predeclared callable resolves and raises an `ApplicationReq` boundary for the exact missing
profile. `main()` is the same case. Result-use demand is not part of intrinsic application support; result
plans and statement eligibility consume the result vector separately.

## 10. Safe and Render

`Safe` retains `Property`, `Program`, `compiled`, `certify`, `certify_retains`, `source`, `core`,
`certify_source`, `certify_retains_capability` and `certify_retains_core` **unchanged**. §12 dispositions
every other current `Safe` declaration.

`Render` is structural and performs no binding or type lookup. Rendering is precedence- and token-safe, stated
by structural lexical predicates over source constructors and emitted bytes. **There is no parser,
tokenizer or round-trip authority, and no public legacy renderer.**

```coq
Inductive Prec : Type := PrimaryPrec | UnaryPrec.
Definition prec (e : Syntax.Expr) : Prec :=
  match e with Syntax.Unary _ _ => UnaryPrec | _ => PrimaryPrec end.
Parameter render_at : Prec -> Syntax.Expr -> string.
Parameter render_expr : Syntax.Expr -> string.

Parameter NoAdjacentMinus : string -> Prop.
Parameter AsciiOnly : string -> Prop.
Parameter NoTrailingBlank : string -> Prop.
Parameter Parenthesized : string -> Prop.
```

```text
render (Unary UnaryMinus e) = "-" ++ render_at PrimaryPrec e
render (Application h args) = render_at PrimaryPrec h ++ "(" ++ join(", ", map render args) ++ ")"
render_stmt (ExprStmt e, n) = indent(n) ++ render e ++ NL
```

Frozen outputs: `-1`; `-(-x)`; `-T(x)`; `f(x)`; `f(-x)`; `(-f)(x)`. File level keeps the existing bytes: the
header line, a blank line, the package clause, a blank line before each top-level declaration, and the exact
final newline; within a declaration one tab per block depth, comma-space separators, no trailing whitespace,
direct source spelling, an inherited const spec rendering names only, one spec ungrouped, and zero or
two-or-more grouped with the zero branches exactly `const ()`, `var ()`, `type ()`.

## 11. Diagnostics

`DiagnosticCode` is an inductive of constructors, extended not replaced.

| constructor | code | status |
|---|---|---|
| `InvalidConversion (primary : Index.ApplicationRef p) (head : Index.ExprRef p) (operand : Index.ExprRef p) (outer : list (Index.ApplicationRef p)) (target : Typing.TypeView) (operand_status : ConstantInfo)` | `CodeInvalidConversion` | restated: anchors an `Application`; the `TypeNameRef` becomes the head `ExprRef`; `SemanticType` becomes `TypeView` |
| `DefaultNotRepresentable (primary : Index.ExprRef p) (exact_constant : Constant) (default_target : Typing.TypeView)` | `CodeDefaultNotRepresentable` | restated: payload becomes `TypeView` |
| `MainRedeclared (later : Index.MainRef p) (earlier : Index.MainRef p)` | `CodeMainRedeclared` | restated: `Index.DeclRef` is deleted, so the anchor becomes the exact `MainRef`; code and meaning unchanged |
| `MissingMainEntry (pkg : PackageRef p)` | `CodeMissingMainEntry` | retained unchanged |
| `BuildOutputIsDirectory (pkg : PackageRef p) (output_name : string)` | `CodeBuildOutputIsDirectory` | retained unchanged |
| `DuplicateBinding (later : Index.BindingSiteRef p) (earlier : Index.BindingSiteRef p)` | `CodeDuplicateBinding` | new |
| `InitMisuse (site : Index.BindingSiteRef p)` | `CodeInitMisuse` | new |
| `UnresolvedName (u : Index.NameUseRef p)` | `CodeUnresolvedName` | new |
| `WrongRole (u : Index.NameUseRef p) (required : UseRole) (actual : ObjectKind)` | `CodeWrongRole` | new |
| `NotApplicable (a : Index.ApplicationRef p) (head : HeadView)` | `CodeNotApplicable` | new; `HeadView` describes an object kind now and a noncallable value expression later |
| `TypeCycleDiag (eqs : Typing.ResolvedTypeEquations p) (c : Typing.TypeCycle eqs)` | `CodeTypeCycle` | new; evidence indexed by its own graph |
| `DependencyCycleDiag (g : DependencyGraph p) (c : DependencyCycle g)` | `CodeDependencyCycle` | new; evidence indexed by its own graph |
| `FirstSpecInherited (s : Index.ConstSpecRef p)` | `CodeFirstSpecInherited` | new |
| `ResultMismatch (site : Index.PlanSiteRef p) (targets : nat) (observed : list ErasedResultVector)` | `CodeResultMismatch` | new |
| `ShortDeclNoNew (s : Index.StatementRef p)` | `CodeShortDeclNoNew` | new |
| `ShortRedeclType (site : Index.BindingSiteRef p) (existing : Typing.TypeView) (found : Typing.TypeView)` | `CodeShortRedeclType` | new |
| `NilNoTarget (r : Index.ExprRef p)` | `CodeNilNoTarget` | new |
| `IotaNoContext (r : Index.ExprRef p)` | `CodeIotaNoContext` | new |
| `NotAssignable (u : ExprUseRef p) (target : AssignmentTargetAnchor p) (from : Typing.TypeView) (to : Typing.TypeView)` | `CodeNotAssignable` | new; the anchor is a sum over an explicit `TypeUseRef` and an inferred or short-declaration target that has none |
| `UnusedLocal (site : Index.BindingSiteRef p)` | `CodeUnusedLocal` | new |
| `BadArgument (u : DirectExprUseRef p) (why : ArgumentReason)` | `CodeBadArgument` | new |
| `BadOperand (u : DirectExprUseRef p) (why : OperandReason)` | `CodeBadOperand` | new |
| `NotStatement (s : Index.ExpressionStatementRef p) (why : IneligibleReason)` | `CodeNotStatement` | new |

A failed preflight precedes a package's semantic errors; otherwise one canonical source order per package.
Boundaries have their own erased view and `key_lt` ordering and never enter `DiagnosticReason`.

## 12. Migration inventory

Every current `Safe` and affected `Render` declaration, dispositioned exactly.

| declaration | disposition |
|---|---|
| `Safe.Property`, `Safe.Program`, `compiled`, `certify`, `certify_retains`, `source`, `core`, `certify_source`, `certify_retains_capability`, `certify_retains_core` | retained unchanged |
| `Safe.Value`, `value_type`, `ValueWellFormed`, `value_well_formedb`, `typed_constant_to_value`, `resolved_constant_value` | moved to C7 `Runtime` |
| `value_well_formedb_iff`, `typed_constant_to_value_type`, `typed_constant_to_value_well_formed`, `typed_constant_to_value_denotes`, `resolved_constant_value_float`, `resolved_constant_value_complex` | moved to C7 `Runtime` |
| `ValueDenotesConstant`, `value_denotes_constant_runtime`, `value_denotes_complex_runtime`, `float_nonconstant_no_denotes`, `complex_nonconstant_no_denotes` | moved to C7 `Runtime` |
| `Safe.eval_expr`, `eval_expr_resolved`, `eval_expr_resolved_type`, `eval_expr_resolved_value`, `eval_projects_stored_float_runtime`, `eval_projects_stored_complex_runtime`, `eval_expr_denotes`, `eval_zero_sign_agnostic`, `eval_string_value`, `eval_string_resolved_type` | moved to C7 `Machine`; `SPEC-X034` owns them |
| `Safe.eval_stmt`, `eval_decl`, `eval_file` | deleted; subsumed by the C7 machine's run relation |
| `Typing.resolve_constant_info`, `convert_constant`, `ConstantRepresentable` | moved to the §4 `Typing` interface, now environment-indexed |
| `Render.const_info_denotes` | restated with the `Application` carrier; retained at C6 |
| `Render.const_info_denotes_functional` | retained unchanged |
| `Render.resolved_expr_denotes` | restated at C6 as the constant/spelling half only; the value half moves to C7 with `eval_expr` |
| `Render.resolved_string_denotes`, `boundary_max`, `boundary_min` | moved to C7 with the value half |
| `Render` type-expression spelling and injectivity | restated over `Syntax.TypeExpr` with the one ordinary identifier |
| `Render` expression, argument, statement and declaration rendering | restated over the new source roots |
| `Render` ASCII and newline-safety | retained unchanged |
| `Render` integer, string, float and complex decoding and faithfulness | retained unchanged; the complex decoder now reads an `Application` |
| `Compilable.predeclared_type`, `predeclared_type_of_name` | deleted; subsumed by the phase binding relation |
| `Names.TypeName`, `SupportedType`, `classify`, `supported_of`, `all_type_names` | deleted; subsumed by `PredeclaredName` |
| `compile_complete` | restated: `Admissible p -> InScope p -> exists cp Hcp, compile p = Compiled cp Hcp` |
| `compile_rejected_of_inadmissible` | restated: `InScope p -> ~ Admissible p -> exists fail, compile p = Rejected fail` |
| `elaboration_accepted_iff_admissible` | restated with the `InScope` premise |
| `elaboration_rejected_iff_inadmissible` | restated with the `InScope` premise |
| `compile_ok_valid`, `compile_rejected_not_admissible` | retained unchanged |
| `compile_program_typed`, `compile_ok_of_source_spec_valid_b` | restated over the phase judgment with the `InScope` premise |
| `program_of_admissible`, `capability_of_admissible`, `capability_source`, `capability_is_compile_outcome` | restated with the `InScope` premise |

No compatibility alias survives.

## 13. Theorems

The §13 statements are written in the **post-`Arguments`** spelling, which is what the implementation
declares:

```coq
Arguments MakeNonEmpty {A} _ _.
Arguments Predeclared {p} _.  Arguments SourceBound {p} _.  Arguments MainObject {p} _.
Arguments DirectUse {p} _.  Arguments InheritedUse {p} _.
Arguments GraphAcyclic {p eqs} _.  Arguments GraphCyclic {p eqs} _.
Arguments TypeMeaningReq {p i ph} _ _.  Arguments ValueMeaningReq {p i ph} _ _.
Arguments ApplicationReq {p i ph} _ _.  Arguments StatementReq {p i ph} _ _.
Arguments UnaryReq {p i ph} _ _.
Arguments AcceptedDecision {p core} _ _.
Arguments RejectedDecision {p core} _.  Arguments OutsideDecision {p core} _ _.
Arguments Compiled {p} _ _.  Arguments Rejected {p} _.  Arguments OutsideScope {p} _.
Arguments DispBlank {cp}.  Arguments DispDeclares {cp} _.  Arguments DispReuses {cp} _ _.
Arguments UntypedConstant {cp} _.  Arguments TypedConstantAtom {cp} _ _.
Arguments ValueResult {cp} _.
Arguments FixedResults {cp} _.  Arguments ContextualForm {cp} _.  Arguments NoStandaloneResult {cp}.
Arguments ConversionTarget {cp r f} _ _.  Arguments CallableTarget {cp r f} _.
Arguments UnusedLocal {p} _.
```

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

Theorem in_scope_accepted_iff : forall p, InScope p ->
  (core_diagnostics (elaboration_core (elaborate p)) = nil <-> Admissible p).
Theorem in_scope_inadmissible_rejected : forall p, InScope p -> ~ Admissible p ->
  exists fail, compile p = Rejected fail.
Theorem in_scope_admissible_compiled : forall p, Admissible p -> InScope p ->
  exists cp Hcp, compile p = Compiled cp Hcp.
Theorem rejected_not_admissible : forall p (fail : Failure p),
  compile p = Rejected fail -> ~ Admissible p.

Theorem requirement_dec_reflects : forall p (i : Input p) (ph : Phase i) (r : SemanticRequirement ph),
  (exists h, requirement_dec r = left h) <-> RequirementSatisfied r.

Theorem boundary_key_sound : forall p (i : Input p) (ph : Phase i) (b : PackedBoundary ph),
  boundary_key b = requirement_key (boundary_requirement b).
Theorem root_boundary_complete : forall p (core : Core p) (r : SemanticRequirement (phase core)),
  RootRequirement (phase core) r -> ~ RequirementSatisfied r ->
  exists b, In b (core_boundaries core) /\ boundary_key b = requirement_key r.
Theorem boundary_keys_nodup : forall p (core : Core p),
  NoDup (map boundary_key (core_boundaries core)).
Theorem boundary_order_canonical : forall p (core : Core p),
  Sorted key_lt (map boundary_key (core_boundaries core)).
Theorem listed_boundary_is_root : forall p (core : Core p) b,
  In b (core_boundaries core) -> RootRequirement (phase core) (boundary_requirement b).

Theorem predeclared_complete : forall p (i : Input p) (ph : Phase i) (n : Names.PredeclaredName),
  exists o : ObjectRef ph, object_origin o = Predeclared n.
Theorem predeclared_shadowed : forall cp (u : Index.NameUseRef (source cp)) s o,
  binder_disposition cp s = DispDeclares o -> InnermostDeclaring cp u s ->
  bound_object_at cp u = o.

Theorem denote_underlying_basic : forall cp (t : AcceptedType cp),
  exists b : Typing.BasicType, AcceptedUnderlying cp t b.
Theorem alias_no_identity : forall p eqs ev (env : Typing.Env eqs ev) a
    (r : Typing.ResolvedTypeTarget env (Typing.AliasRaw a))
    (r' : Typing.ResolvedTypeTarget env (alias_raw_target a)),
  Typing.denote r = Typing.denote r'.
Theorem defined_identity_exact : forall p eqs ev (env : Typing.Env eqs ev) d1 d2
    (r1 : Typing.ResolvedTypeTarget env (Typing.DefinedRaw d1))
    (r2 : Typing.ResolvedTypeTarget env (Typing.DefinedRaw d2)),
  Typing.identicalb env (Typing.denote r1) (Typing.denote r2) = true <-> d1 = d2.

Theorem underlying_reflect : forall p eqs ev (env : Typing.Env eqs ev) s f,
  Typing.underlying env s = f <-> Typing.Underlying env s f.
Theorem identical_reflect : forall p eqs ev (env : Typing.Env eqs ev) s t,
  Typing.identicalb env s t = true <-> Typing.Identical env s t.
Theorem assignable_reflect : forall p eqs ev (env : Typing.Env eqs ev) s t,
  Typing.assignableb env s t = true <-> Typing.Assignable env s t.
Theorem convertible_reflect : forall p eqs ev (env : Typing.Env eqs ev) s t,
  Typing.convertibleb env s t = true <-> Typing.Convertible env s t.
Theorem representable_reflect : forall p eqs ev (env : Typing.Env eqs ev) s c,
  Typing.representableb env s c = true <-> Typing.Representable env s c.

Theorem direct_use_provenance : forall p (u : DirectExprUseRef p),
  Index.OccupiesRole (direct_parent u) (direct_child u) (direct_role u).
Theorem inherited_const_provenance : forall p (u : InheritedConstUseRef p),
  NearestPrecedingExplicit (inherited_current u) (inherited_predecessor u)
  /\ CorrespondingPosition (inherited_current u) (inherited_predecessor u) (inherited_position u).

Theorem type_object_has_no_result : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o ->
  (object_kind_of o = TypeObject \/ object_kind_of o = BuiltinObject) ->
  result_form f = NoStandaloneResult cp.
Theorem variable_name_has_one_value : forall cp r (f : ExpressionFact cp r) o,
  referenced_object f = Some o -> object_kind_of o = VariableObject ->
  exists t, result_form f = FixedResults cp (ValueResult cp t :: nil).

Theorem application_results_exact : forall cp a,
  app_results (application_fact cp a)
  = target_results (app_target (application_fact cp a)) (app_profile (application_fact cp a)).
Theorem complex_needs_identical_types : forall cp a s t,
  ComplexApplication cp a -> TypedOperandTypes cp a s t ->
  AcceptedIdentical cp s t.
Theorem statement_eligible_reflect : forall cp s,
  (exists h, statement_eligible_dec cp s = left h) <-> StatementEligible cp s.

Theorem plan_pairs_every_target : forall cp s,
  map fst (plan_pairing (result_plan cp s)) = plan_targets (result_plan cp s).
Theorem plan_consumes_every_result : forall cp s,
  map snd (plan_pairing (result_plan cp s)) ++ plan_blank_consumed (result_plan cp s)
  = List.concat (plan_vectors (result_plan cp s)).

Theorem short_decl_has_new_name : forall cp s,
  ShortDeclSite cp s ->
  exists b, In b (short_left_sites cp s) /\ exists o, binder_disposition cp b = DispDeclares o.
Theorem short_reuse_is_same_block : forall cp b o v,
  binder_disposition cp b = DispReuses o v -> SameBlockEarlier cp b o.

Theorem dependency_order_acyclic : forall cp k,
  Acyclic (dependency_graph cp k) (dependency_order (dependency_fact cp k)).
Theorem dependency_cycle_reflect : forall p (g : DependencyGraph p),
  acyclicb g = true <-> Acyclic g (order_of g).

Theorem unused_local_iff : forall p (core : Core p) site,
  In (UnusedLocal site) (core_diagnostics core)
  <-> LocalVariableSite (phase core) site /\ ~ PhaseReadsVariableAt (phase core) site.

Theorem unary_never_merges : forall e,
  NoAdjacentMinus (render_expr (Syntax.Unary Syntax.UnaryMinus e)).
Theorem parens_exactly_when_needed : forall r e,
  Parenthesized (render_at r e) <-> PrecLooser (prec e) r.
Theorem render_ascii : forall e, AsciiOnly (render_expr e).
Theorem render_no_trailing_blank : forall f, NoTrailingBlank (render_file f).
```

Every declaration uses only names introduced earlier in this contract. Proof helpers stay `Local`; obsolete
carrier names do not survive as aliases.

Prior-byte preservation is **migration evidence**, discharged by the existing goldens and the
generated-artifact byte-compare at the semantic-root review, not by a retained public legacy renderer.

## 14. Review boundaries

**Semantic-root review** stops only when the repository is green and contains: the corrected source and index
roots; the generalized exact phase as a predecessor-indexed chain; phase-indexed objects, facts and
requirements; the core-indexed three-way decision; requirement-indexed sealed boundaries with proof-free keys;
the `GraphOutcome` sum and `build_env`; resolution-evidence-gated `denote`; total accepted-program queries;
`HeadCallable`; object-indexed `StaticVariable`; the old fixed resolver and old expression phase deleted;
`Safe.Value` and `Safe.eval_expr` deleted; no `Runtime` module or machine; prior generated bytes unchanged.

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
two blocked sites. Two defined types with identical underlying `float32` but distinct identity are rejected by
`complex`; one such type used twice yields `complex64`. Short declaration with no new nonblank name rejected;
short redeclaration returning the exact existing object; blank declarations creating no object; `true`,
`false`, `byte` and `rune` resolving through ordinary binding; alias preserving identity; a local type spec
naming itself rejected as a cycle; package constant and variable cycles rejected; a package expression
depending on a forward constant accepted; a first const spec with an inherited initializer rejected; an
inherited spec taking the predecessor expression under its own `iota`; unshadowed `nil` and out-of-context
`iota` rejected; a `println` argument of a defined type whose underlying form is `string` accepted; unary
minus on a constant and a variable accepted and on a string rejected; `-(-x)` rendering with its parentheses;
every currently accepted program rendering byte-identically after migration; generated C6 programs passing the
pinned Go build with their exact expected observation.

## Preserve

`Syntax.Program` as the sole source authority and the AST as the one IR; `Program` as the opaque C4
capability, with `Failure` and `Outside` retaining the exact core; the retained input, work forest, member
index, outcome trace and sealed core; `Machine.T` uninstantiated; direct rendering and the one
`Emit.Mint.issue` authority; certified-module coverage, the whole-theory audit and controls A-E; every
sealed-capability, mint, transport and positive client control; working-tree and staged-index separation;
no-host-Python; `life.md`.

## Stop

A static identity cannot be indexed by the exact phase without reaching a core field; a requirement
constructor cannot be built from site objects alone; the boundary key cannot be made proof-free; a blocked
site cannot be recorded without minting a root; an accepted query cannot be made total over `Program`; the
`InScope` premise cannot be discharged where an accepted guarantee needs it; `Typing` cannot be closed without
a `Compilable` type; `denote` cannot be gated on resolution evidence; `AppTarget` would need a C9 constructor;
`complex` cannot decide identity without a second type authority; a §13 theorem cannot be stated over the
names defined here; rendering cannot be proved safe without a tokenizer; `LAT-077` needs a diagnostic the
phase cannot produce; a run relation, value, store, environment or machine is needed for a C6 row;
implementation needs a placeholder, compatibility path, trusted shortcut, fuel, bound or premature future
state.
