
(* ── §17 Theorem surface ───────────────────────────────────────────────────── *)

(* §17.1 Names/index/source *)
Theorem all_predeclared_nodup : NoDup all_predeclared.
Proof. Admitted.
Theorem all_predeclared_complete : forall n : PredeclaredName, In n all_predeclared.
Proof. Admitted.
Theorem predeclared_spelling_injective : forall a b : PredeclaredName,
  predeclared_spelling a = predeclared_spelling b -> a = b.
Proof. Admitted.
Theorem classify_spelling_roundtrip : forall n : PredeclaredName,
  classify_spelling (predeclared_spelling n) = Some n.
Proof. Admitted.
Theorem classify_spelling_sound : forall (s : string) (n : PredeclaredName),
  classify_spelling s = Some n -> predeclared_spelling n = s.
Proof. Admitted.
Theorem predeclared_eqb_spec : forall a b : PredeclaredName,
  predeclared_eqb a b = true <-> a = b.
Proof. Admitted.
Theorem ordinary_excludes_blank_only : forall x : OrdinaryIdentifier,
  spelling (ordinary_identifier x) <> "_"%string.
Proof. Admitted.

(* §17.2 Binding *)
Theorem resolve_name_reflects :
  forall {p} {i : Input p} (ph : Phase i) (u : NameUseRef p) (o : ObjectRef ph),
  resolve_name ph u = Some o <-> Resolves ph u o.
Proof. Admitted.
Theorem resolution_is_same_spelling :
  forall {p} {i : Input p} (ph : Phase i) (u : NameUseRef p) (o : ObjectRef ph),
  Resolves ph u o -> object_spelling o = name_use_spelling u.
Proof. Admitted.
Theorem resolution_is_unique :
  forall {p} {i : Input p} (ph : Phase i) (u : NameUseRef p) (o1 o2 : ObjectRef ph),
  Resolves ph u o1 -> Resolves ph u o2 -> o1 = o2.
Proof. Admitted.
Theorem source_binding_shadows_predeclared :
  forall {p} {i : Input p} (ph : Phase i) (u : NameUseRef p) (sc : ScopeId p)
    (m : ScopeBindings ph sc) (b : ObjectEstablisher p) (n : PredeclaredName),
  Encloses sc (name_use_scope u) ->
  scope_build ph sc = ScopeReady ph sc m ->
  scope_lookup m (name_use_spelling u) = Some b -> VisibleAt b u ->
  ~ Resolves ph u (predeclared_object ph n).
Proof. Admitted.
Theorem duplicate_scope_fails :
  forall {p} {i : Input p} (ph : Phase i) (sc : ScopeId p) (e l : ObjectEstablisher p),
  DuplicateEstablishers e l -> establisher_scope l = sc ->
  forall m : ScopeBindings ph sc, scope_build ph sc <> ScopeReady ph sc m.
Proof. Admitted.

(* §17.3 Type resolution *)
Theorem byte_is_uint8 : AliasPredeclared PByte TUint8.
Proof. Admitted.
Theorem rune_is_int32 : AliasPredeclared PRune TInt32.
Proof. Admitted.
Theorem every_basic_type_has_a_name : forall t : PredeclaredBasicType,
  exists n, AdmittedPredeclaredType n t.
Proof. Admitted.
Theorem default_types_exact :
  default_basic UCBool = TBool /\ default_basic UCInteger = TInt /\
  default_basic UCFloat = TFloat64 /\ default_basic UCComplex = TComplex128 /\
  default_basic UCString = TString.
Proof. Admitted.
Theorem identicalb_reflect : forall {p} (s t : SemanticType p),
  identicalb s t = true <-> Identical s t.
Proof. Admitted.
Theorem assignableb_reflect : forall {p} (s t : SemanticType p),
  assignableb s t = true <-> Assignable s t.
Proof. Admitted.
Theorem value_convertibleb_reflect :
  forall {p} {i : Input p} {ph : Phase i}  (s t : SemanticType p),
  value_convertibleb ph s t = true <-> ValueConvertible ph s t.
Proof. Admitted.
Theorem representableb_reflect :
  forall {p} {i : Input p} {ph : Phase i}  (s : SemanticType p) (c : Constant),
  representableb ph s c = true <-> Representable ph s c.
Proof. Admitted.

(* §17.4 Objects *)
Theorem source_object_origin_is_its_site :
  forall {p} {i : Input p} (ph : Phase i) (s : ObjectSiteRef p),
  object_origin (source_object ph s) = SourceSite p s.
Proof. Admitted.
Theorem object_origin_injective :
  forall {p} {i : Input p} {ph : Phase i} (o1 o2 : ObjectRef ph),
  object_origin o1 = object_origin o2 -> o1 = o2.
Proof. Admitted.

(* §17.5 Reports *)
Theorem view_lt_irrefl : forall a : RequirementView, ~ view_lt a a.
Proof. Admitted.
Theorem view_lt_transitive : forall a b c : RequirementView,
  view_lt a b -> view_lt b c -> view_lt a c.
Proof. Admitted.
Theorem view_lt_total : forall a b : RequirementView, view_lt a b \/ a = b \/ view_lt b a.
Proof. Admitted.

Definition StrictlyIncreasingBy {A : Type} (lt : A -> A -> Prop) : list A -> Prop :=
  fix go l := match l with
  | [] => True
  | a :: rest => match rest with [] => True | b :: _ => lt a b /\ go rest end
  end.

Theorem boundary_order_canonical : forall {p} (c : Core p),
  StrictlyIncreasingBy view_lt (List.map (fun b => boundary_view b) (core_boundaries c)).
Proof. Admitted.
Theorem boundary_views_nodup : forall {p} (c : Core p),
  NoDup (List.map (fun b => boundary_view b) (core_boundaries c)).
Proof. Admitted.
Theorem root_boundary_complete : forall {p} (c : Core p) (s : Site p),
  IsRootOutside (phase_outcome (phase c) s) ->
  exists b, List.In b (core_boundaries c) /\ boundary_site (phase c) b = s.
Proof. Admitted.

(* §17.6 Outcome *)
Definition elaborated (p : SyntaxProgram) : Core p := elaboration_core (elaborate p).
Definition IsCompiled {p} (o : Outcome p) : Prop :=
  match o with Compiled _ _ _ => True | _ => False end.
Definition IsRejected {p} (o : Outcome p) : Prop :=
  match o with Rejected _ _ => True | _ => False end.
Definition IsOutsideScope {p} (o : Outcome p) : Prop :=
  match o with OutsideScope _ _ => True | _ => False end.

Theorem compiled_iff : forall p : SyntaxProgram,
  IsCompiled (compile p) <->
  core_diagnostics (elaborated p) = [] /\ core_boundaries (elaborated p) = [].
Proof. Admitted.
Theorem rejected_iff : forall p : SyntaxProgram,
  IsRejected (compile p) <-> core_diagnostics (elaborated p) <> [].
Proof. Admitted.
Theorem outside_scope_iff : forall p : SyntaxProgram,
  IsOutsideScope (compile p) <->
  core_diagnostics (elaborated p) = [] /\ core_boundaries (elaborated p) <> [].
Proof. Admitted.

Theorem compiled_retains_core : forall (p : SyntaxProgram) (cp : Program) (e : source cp = p),
  compile p = Compiled p cp e ->
  eq_rect (source cp) Core (core cp) p e = elaborated p.
Proof. Admitted.
Theorem rejected_retains_core : forall (p : SyntaxProgram) (f : Failure p),
  compile p = Rejected p f -> failure_core f = elaborated p.
Proof. Admitted.
Theorem outside_retains_core : forall (p : SyntaxProgram) (o : Outside_ p),
  compile p = OutsideScope p o -> outside_core o = elaborated p.
Proof. Admitted.

Theorem compile_sound : forall (p : SyntaxProgram) (cp : Program) (e : source cp = p),
  compile p = Compiled p cp e -> Admissible p.
Proof. Admitted.
Theorem compile_complete_in_scope : forall p : SyntaxProgram,
  Admissible p -> InScope p -> exists (cp : Program) (e : source cp = p), compile p = Compiled p cp e.
Proof. Admitted.
Theorem rejected_not_admissible : forall (p : SyntaxProgram) (f : Failure p),
  compile p = Rejected p f -> ~ Admissible p.
Proof. Admitted.

(* §17.7 Empty reports force every site supported — this is how `accepted_supported` is derived. *)
Theorem empty_report_implies_all_supported : forall {p} (c : Core p) (s : Site p),
  core_diagnostics c = [] -> core_boundaries c = [] ->
  IsSupported (phase_outcome (phase c) s).
Proof. Admitted.

(* §17.8 Dependencies *)
Theorem init_units_nodup : forall {p} (k : PackageRef p), NoDup (package_init_units k).
Proof. Admitted.
Theorem runtime_projection_excludes_constants :
  forall {p} {i : Input p} {ph : Phase i} {k : PackageRef p} (o : InitOrder ph k),
  List.Forall (fun u => RuntimeInitUnit u = true) (runtime_initialization o).
Proof. Admitted.


(* §14 Blocked causality *)
Theorem dependency_decreases_stage :
  forall {p} {i : Input p} (ph : Phase i) (pred s : Site p),
  SiteDependency ph pred s -> (site_stage ph pred < site_stage ph s)%nat.
Proof. Admitted.

(* §16 Additional theorem obligations *)
Theorem node_blocked_cause_not_supported :
  forall {p} {i : Input p} (ph : Phase i)
    (acyc : AcyclicEquations (phase_equations ph)) (n m : TypeNode p)
    (e : TypeEdge (phase_equations ph) n m),
  node_outcome ph acyc n = NodeBlocked ph n m e ->
  ~ NodeIsSupported (node_outcome ph acyc m).
Proof. Admitted.

Theorem type_ready_iff_all_supported :
  forall {p} {i : Input p} (ph : Phase i)
    (acyc : AcyclicEquations (phase_equations ph)),
  (forall n, NodeIsSupported (node_outcome ph acyc n)) ->
  TypeReady ph.
Proof. Admitted.

Theorem static_variable_identity :
  forall {p} {i : Input p} (ph : Phase i) (o : ObjectRef ph) (sv : StaticVariable ph o),
  object_origin o = SourceSite p (establisher_site (static_est ph o sv)).
Proof. Admitted.
