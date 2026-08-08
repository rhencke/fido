
(* ── §1 Role-indexed phase facts ───────────────────────────────────────────── *)
Parameter PhaseBindingFact : forall {p} {i : Input p} (ph : Phase i), NameUseRef p -> Type.
Parameter PhaseExpressionFact : forall {p} {i : Input p} (ph : Phase i), ExprRef p -> Type.
Parameter PhaseHeadUseFact : forall {p} {i : Input p} (ph : Phase i), ExprUseRef p -> Type.
Parameter PhaseStatementUseFact : forall {p} {i : Input p} (ph : Phase i), ExprUseRef p -> Type.
Parameter PhaseResultUseFact : forall {p} {i : Input p} (ph : Phase i), ExprUseRef p -> Type.
Parameter PhaseApplicationFact : forall {p} {i : Input p} (ph : Phase i), ApplicationRef p -> Type.
Parameter PhaseStatementFact : forall {p} {i : Input p} (ph : Phase i),
  ExpressionStatementRef p -> Type.
Parameter PhaseUnaryFact : forall {p} {i : Input p} (ph : Phase i), UnaryRef p -> Type.
Parameter PhaseConsumptionFact : forall {p} {i : Input p} (ph : Phase i),
  ConsumptionSiteRef p -> Type.
Parameter PhaseStaticVariableFact : forall {p} {i : Input p} (ph : Phase i),
  VariableSiteRef p -> Type.

Definition refinement_fact {p} {i : Input p} (ph : Phase i) (u : ExprUseRef p)
  (k : UseRefinement) : Type :=
  match k with
  | HeadRefinement      => PhaseHeadUseFact ph u
  | StatementRefinement => PhaseStatementUseFact ph u
  | ResultRefinement    => PhaseResultUseFact ph u
  end.

Definition PhaseUseFact {p} {i : Input p} (ph : Phase i) (u : ExprUseRef p) : Type :=
  refinement_fact ph u (use_refinement u).

Definition SiteFact {p} {i : Input p} (ph : Phase i) (s : Site p) : Type :=
  match s with
  | SBinding _ u     => PhaseBindingFact ph u
  | SExpression _ r  => PhaseExpressionFact ph r
  | SUse _ u         => PhaseUseFact ph u
  | SApplication _ a => PhaseApplicationFact ph a
  | SStatement _ t   => PhaseStatementFact ph t
  | SUnary _ n       => PhaseUnaryFact ph n
  | SConsumption _ c => PhaseConsumptionFact ph c
  | SVariable _ v    => PhaseStaticVariableFact ph v
  end.

(* ── §4 Private site outcomes: every branch is about this exact site ───────── *)
Inductive SiteOutcome {p} {i : Input p} (ph : Phase i) : Site p -> Type :=
| Supported : forall s, SiteFact ph s -> SiteOutcome ph s
| DefiniteFailure : forall s, SiteFailure ph s -> SiteOutcome ph s
| Outside : forall s, SiteRequirement ph s -> SiteOutcome ph s
| Blocked : forall s pred, SiteDependency ph pred s -> SiteOutcome ph pred -> SiteOutcome ph s.

Definition IsSupported {p} {i : Input p} {ph : Phase i} {s} (o : SiteOutcome ph s) : Prop :=
  match o with Supported _ _ _ => True | _ => False end.

Definition supported_fact {p} {i : Input p} {ph : Phase i} {s} (o : SiteOutcome ph s)
  : IsSupported o -> SiteFact ph s :=
  match o in SiteOutcome _ s0 return IsSupported o -> SiteFact ph s0 with
  | Supported _ _ f => fun _ => f
  | DefiniteFailure _ _ _ => fun h => match h return SiteFact ph _ with end
  | Outside _ _ _ => fun h => match h return SiteFact ph _ with end
  | Blocked _ _ _ _ _ => fun h => match h return SiteFact ph _ with end
  end.

Definition IsRootOutside {p} {i : Input p} {ph : Phase i} {s} (o : SiteOutcome ph s) : Prop :=
  match o with Outside _ _ _ => True | _ => False end.

Definition root_requirement {p} {i : Input p} {ph : Phase i} {s} (o : SiteOutcome ph s)
  : IsRootOutside o -> SiteRequirement ph s :=
  match o in SiteOutcome _ s0 return IsRootOutside o -> SiteRequirement ph s0 with
  | Outside _ _ r => fun _ => r
  | Supported _ _ _ => fun h => match h return SiteRequirement ph _ with end
  | DefiniteFailure _ _ _ => fun h => match h return SiteRequirement ph _ with end
  | Blocked _ _ _ _ _ => fun h => match h return SiteRequirement ph _ with end
  end.

(* One outcome per site.  No client constructs these values. *)
Parameter phase_outcome : forall {p} {i : Input p} (ph : Phase i) (s : Site p), SiteOutcome ph s.

Definition RootRequirement {p} {i : Input p} (ph : Phase i) (s : Site p)
  (r : SiteRequirement ph s) : Prop :=
  exists h : IsRootOutside (phase_outcome ph s), root_requirement (phase_outcome ph s) h = r.

(* ── §11 Package dependency: static order, distinct from runtime initialization ── *)
Inductive InitUnit (p : SyntaxProgram) : Type :=
| ConstUnit : ConstSpecRef p -> InitUnit p
| VarUnit   : BindingSiteRef p -> InitUnit p
| BlankUnit : BlankRef p -> InitUnit p.

Parameter DependencyGraph : forall {p} {i : Input p}, Phase i -> PackageRef p -> Type.
Parameter DependencyEdge : forall {p} {i : Input p} {ph : Phase i} {k}
  (g : DependencyGraph ph k), InitUnit p -> InitUnit p -> Prop.
Parameter EdgesFromBindings : forall {p} {i : Input p} {ph : Phase i} {k}
  (g : DependencyGraph ph k), Prop.
Parameter SourceOrderConstrained : forall {p} {i : Input p} {ph : Phase i} {k}
  (g : DependencyGraph ph k), Prop.
Parameter DependencyCycle : forall {p} {i : Input p} {ph : Phase i} {k},
  DependencyGraph ph k -> Type.
Parameter AcyclicOrder : forall {p} {i : Input p} {ph : Phase i} {k},
  DependencyGraph ph k -> Type.
Parameter order_units : forall {p} {i : Input p} {ph : Phase i} {k} {g : DependencyGraph ph k},
  AcyclicOrder g -> list (InitUnit p).

Inductive DependencyOutcome {p} {i : Input p} {ph : Phase i} {k}
  (g : DependencyGraph ph k) : Type :=
| DependencyOrdered : AcyclicOrder g -> DependencyOutcome g
| DependencyCyclic  : DependencyCycle g -> DependencyOutcome g.

Parameter phase_dependency_graph : forall {p} {i : Input p} (ph : Phase i) (k : PackageRef p),
  DependencyGraph ph k.
Parameter phase_dependency_outcome : forall {p} {i : Input p} (ph : Phase i) (k : PackageRef p),
  DependencyOutcome (phase_dependency_graph ph k).

(* Constants stay compile-time facts; only variable and blank work projects into the C7 store. *)
Definition RuntimeInitUnit {p} (u : InitUnit p) : bool :=
  match u with ConstUnit _ _ => false | VarUnit _ _ => true | BlankUnit _ _ => true end.

Definition runtime_initialization {p} {i : Input p} {ph : Phase i} {k}
  {g : DependencyGraph ph k} (o : AcyclicOrder g) : list (InitUnit p) :=
  List.filter RuntimeInitUnit (order_units o).
