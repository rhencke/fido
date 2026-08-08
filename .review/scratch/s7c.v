
(* ── §10 Site failures retain their exact causes ───────────────────────────── *)
(* The source witnesses a diagnostic must consume.  These are facts about the source and its bindings, not
   claims that Go rejects the program: two binders sharing a spelling in one scope IS the duplication, and a
   package-level declaration spelled `init` IS the reservation. *)
Definition ShortHasNoNewName {p} {i : Input p} (ph : Phase i) (d : ShortDeclRef p) : Prop :=
  forall (n : BindingNameRef p) (sp : string),
    short_lhs_decl n = Some d -> short_lhs_spelling n = sp ->
    match binder_fact ph n with
    | BFShortNew _ _ _ _ _ _ _ _ => False
    | _ => True
    end.

Definition NoReadOf {p} {i : Input p} (ph : Phase i) (v : VariableSiteRef p) : Prop :=
  forall (u : NameUseRef p) (bf : BindingFact ph u),
    bound_object ph u bf
      <> source_object ph (establisher_site (variable_site_establisher v)).

(* A duplicate declaration is a failure at the declaration site, not at some unrelated name use; an argument
   failure retains the exact argument use, not a free index; a consumption failure retains the exact
   occurrence, not a free position. *)
(* No environment index: a failed or cyclic core must be able to report why no environment exists.  The
   three cases that genuinely resolved a type carry the exact readiness they used. *)
Inductive SiteFailure {p} {i : Input p} (ph : Phase i) : Site p -> Type :=
(* Unresolved consumes the complete decision: resolve_name returned None for this exact use. *)
| FUnresolvedName : forall (u : NameUseRef p),
    resolve_name ph u = None -> SiteFailure ph (SBinding p u)
(* A name bound to an object that cannot carry the role its use demands. *)
| FWrongRole : forall (u : NameUseRef p) (bf : BindingFact ph u),
    ~ HasValueCapability (bound_object ph u bf) ->
    ~ HasTypeCapability (bound_object ph u bf) ->
    SiteFailure ph (SBinding p u)
| FDuplicateDeclaration : forall earlier later : ObjectEstablisher p,
    DuplicateEstablishers earlier later -> SiteFailure ph (SDeclaration p later)
| FPackageInitReserved : forall b : ObjectEstablisher p,
    PackageInitReserved (establisher_context b) (establisher_spelling b) ->
    SiteFailure ph (SDeclaration p b)
| FNotAStatement : forall t : ExpressionStatementRef p, StatementReason ->
    SiteFailure ph (SStatement p t)
| FResultCountWrong : forall c : ConsumptionSiteRef p, nat -> nat ->
    SiteFailure ph (SConsumption p c)
| FNotAssignableAt : forall (c : ConsumptionSiteRef p)  (u : ExprUseRef p)
    (a : ResultAtomAt ph),
    ResultUseFactAt ph u a -> SemanticType p -> SiteFailure ph (SConsumption p c)
| FNotRepresentableAt : forall (c : ConsumptionSiteRef p)  (u : ExprUseRef p)
    (a : ResultAtomAt ph),
    ResultUseFactAt ph u a -> SemanticType p -> SiteFailure ph (SConsumption p c)
| FConstInitNotConstant : forall (c : ConsumptionSiteRef p)  (u : ExprUseRef p)
    (a : ResultAtomAt ph),
    ResultUseFactAt ph u a -> ConstInitReason -> SiteFailure ph (SConsumption p c)
| FNoNewVariable : forall d : ShortDeclRef p,
    ShortHasNoNewName ph d -> SiteFailure ph (SConsumption p (ShortSite p d))
(* A short reuse whose right-hand side does not fit the reused variable's exact type. *)
| FShortReuseMismatch : forall (d : ShortDeclRef p)  (o : ObjectRef ph)
    (sv : StaticVariable ph o) (u : ExprUseRef p) (a : ResultAtomAt ph),
    ResultUseFactAt ph u a -> ~ AtomFits ph a (static_type sv) ->
    SiteFailure ph (SConsumption p (ShortSite p d))
| FContext : forall r : ExprRef p, ContextReason -> SiteFailure ph (SExpression p r)
| FDefaultNotRepresentable : forall r : ExprRef p,
    UntypedConstantKind -> TypeView -> SiteFailure ph (SExpression p r)
| FUnusedLocal : forall (est : ObjectEstablisher p) (v : VariableSiteRef p),
    StaticVariable ph (source_object ph (establisher_site est)) ->
    NoReadOf ph v -> SiteFailure ph (SDeclaration p est)
| FInitializationCycle : forall k : PackageRef p, InitCycle ph k -> SiteFailure ph (SDependency p k).

(* ── The fact a supported site carries ─────────────────────────────────────── *)
Parameter DeclarationFact : forall {p} {i : Input p} (ph : Phase i), ObjectEstablisher p -> Type.
(* A supported dependency site is exactly a valid initialization order for that package. *)
Definition DependencyFact {p} {i : Input p} (ph : Phase i) (k : PackageRef p) : Type :=
  InitOrder ph k.

(* No global readiness index: each case names only the predecessor it actually needs.  A binding fact needs
   no type environment at all; the cases that resolve types retain the exact readiness they used. *)
(* §6 No global readiness wrapper: every fact carries only the exact type evidence it needs.  An
   independent `println(1)` has facts even when `type U uintptr` is outside scope. *)
Definition SiteFact {p} {i : Input p} (ph : Phase i) (s : Site p) : Type :=
  match s with
  | SBinding _ u     => BindingFact ph u
  | SDeclaration _ b => DeclarationFact ph b
  | SDependency _ k  => DependencyFact ph k
  | SExpression _ r  => { form : ResultFormAt ph & ExprFact ph r form }
  | SUse _ u         => match use_refinement u with
                        | ResultRefinement =>
                            { a : ResultAtomAt ph & ResultUseFactAt ph u a }
                        | _ => { form : ResultFormAt ph &
                                 ExprFact ph (expression_of_use u) form }
                        end
  | SStatement _ t   => StmtFact ph t
  | SConsumption _ c => ConsumptionFact ph c
  end.

(* ── §10 One outcome per site ──────────────────────────────────────────────── *)
(* The topology below is the specification of a module-private type.  `Compilable.Report` exports
   `phase_outcome` and the projections; it does not export these constructors, because they are freely
   applicable and a client holding them could fabricate an outcome claiming a site failed. *)
Inductive SiteOutcome {p} {i : Input p} (ph : Phase i) : Site p -> Type :=
| Supported       : forall s : Site p, SiteFact ph s -> SiteOutcome ph s
| DefiniteFailure : forall s, SiteFailure ph s -> SiteOutcome ph s
| Outside         : forall s, SiteRequirement ph s -> SiteOutcome ph s
(* Blocked retains the exact predecessor site and the exact dependency edge, and nothing more: the
   predecessor's outcome is `phase_outcome ph pred`, which is unique, so no equal-looking substitute can be
   supplied alongside it. *)
| Blocked         : forall s pred, SiteDependency ph pred s -> SiteOutcome ph s.

Definition IsSupported {p} {i : Input p} {ph : Phase i} {s}
  (o : SiteOutcome ph s) : Prop :=
  match o with Supported _ _ _ => True | _ => False end.

Definition supported_fact {p} {i : Input p} {ph : Phase i} {s}
  (o : SiteOutcome ph s) : IsSupported o -> SiteFact ph s :=
  match o in SiteOutcome _ s0 return IsSupported o -> SiteFact ph s0 with
  | Supported _ _ f => fun _ => f
  | DefiniteFailure _ _ _ => fun h => match h return SiteFact ph _ with end
  | Outside _ _ _ => fun h => match h return SiteFact ph _ with end
  | Blocked _ _ _ _ => fun h => match h return SiteFact ph _ with end
  end.

Definition IsDefiniteFailure {p} {i : Input p} {ph : Phase i} {s}
  (o : SiteOutcome ph s) : Prop :=
  match o with DefiniteFailure _ _ _ => True | _ => False end.

Definition IsRootOutside {p} {i : Input p} {ph : Phase i} {s}
  (o : SiteOutcome ph s) : Prop :=
  match o with Outside _ _ _ => True | _ => False end.

Definition root_requirement {p} {i : Input p} {ph : Phase i} {s}
  (o : SiteOutcome ph s) : IsRootOutside o -> SiteRequirement ph s :=
  match o in SiteOutcome _ s0 return IsRootOutside o -> SiteRequirement ph s0 with
  | Outside _ _ r => fun _ => r
  | Supported _ _ _ => fun h => match h return SiteRequirement ph _ with end
  | DefiniteFailure _ _ _ => fun h => match h return SiteRequirement ph _ with end
  | Blocked _ _ _ _ => fun h => match h return SiteRequirement ph _ with end
  end.

(* Every site has an outcome for an arbitrary core, with no global environment in sight. *)
Parameter phase_outcome : forall {p} {i : Input p} (ph : Phase i) (s : Site p), SiteOutcome ph s.

