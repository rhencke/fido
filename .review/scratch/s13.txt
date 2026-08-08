
(* ── Theorems ──────────────────────────────────────────────────────────────── *)
Section Theorems.

(* §2.1 the source-name root. *)
Theorem ordinary_excludes_blank_only : forall x : OrdinaryIdentifier,
  spelling (ordinary_identifier x) <> "_"%string.
Proof. Admitted.
Theorem predeclared_spellings_are_source_names : forall n : PredeclaredName,
  predeclared_spelling n <> "_"%string ->
  exists x : OrdinaryIdentifier, spelling (ordinary_identifier x) = predeclared_spelling n.
Proof. Admitted.
Theorem blank_is_not_an_ordinary_name : forall x : OrdinaryIdentifier,
  Named x <> Blank.
Proof. Admitted.

(* Names: the pinned catalog is complete, exact and injective. *)
Theorem all_predeclared_nodup : NoDup all_predeclared.
Proof. Admitted.
Theorem all_predeclared_complete : forall n, In n all_predeclared.
Proof. Admitted.
Theorem predeclared_spelling_injective : forall a b,
  predeclared_spelling a = predeclared_spelling b -> a = b.
Proof. Admitted.
Theorem classify_spelling_roundtrip : forall n, classify_spelling (predeclared_spelling n) = Some n.
Proof. Admitted.
Theorem predeclared_eqb_spec : forall a b, predeclared_eqb a b = true <-> a = b.
Proof. Admitted.

(* §3.1 the refinement has no fallback: it is an elimination of the child-role witness. *)
Theorem head_role_is_head_refinement :
  refinement_of_child_role ECApplicationHead = HeadRefinement.
Proof. Admitted.
Theorem statement_role_is_statement_refinement :
  refinement_of_child_role ECStatement = StatementRefinement.
Proof. Admitted.
Theorem argument_role_is_result_refinement :
  refinement_of_child_role ECApplicationArg = ResultRefinement.
Proof. Admitted.
Theorem inherited_use_is_result : forall p (u : InheritedConstUseRef p),
  use_refinement (InheritedUse p u) = ResultRefinement.
Proof. Admitted.

(* §5 the closed type bridge. *)
Theorem byte_is_uint8 : AliasPredeclared PByte TUint8.
Proof. Admitted.
Theorem rune_is_int32 : AliasPredeclared PRune TInt32.
Proof. Admitted.
Theorem aliases_mint_no_identity : forall n t, AliasPredeclared n t ->
  ~ AdmittedPredeclaredType n t.
Proof. Admitted.
Theorem no_type_meaning_names : forall n,
  In n [PAny; PComparable; PError; PUintptr] -> predeclared_type_role n = NoTypeMeaning.
Proof. Admitted.
Theorem sixteen_named_basic_types : forall t : PredeclaredBasicType,
  exists n, AdmittedPredeclaredType n t.
Proof. Admitted.
Theorem default_types_exact :
  default_basic UCBool = TBool /\ default_basic UCInteger = TInt /\
  default_basic UCFloat = TFloat64 /\ default_basic UCComplex = TComplex128 /\
  default_basic UCString = TString.
Proof. Admitted.

(* §3.2 environment provenance is intrinsic; the alias/definition mapping is frozen. *)
Theorem cyclic_phase_has_no_environment : forall p (eqs : ResolvedTypeEquations p) c,
  ~ IsTypeReady (PhaseCyclic eqs c).
Proof. Admitted.
Theorem ready_is_acyclic : forall p (eqs : ResolvedTypeEquations p) (r : TypeReady eqs),
  AcyclicEquations eqs.
Proof. Admitted.
Theorem predeclared_target_terminal : forall p (eqs : ResolvedTypeEquations p) n m x,
  equation_target eqs n = RawPredeclared p x -> ~ TypeEdge eqs n m.
Proof. Admitted.
Theorem resolution_is_functional : forall p (eqs : ResolvedTypeEquations p) n r1 r2,
  AcyclicEquations eqs -> ResolvesTo eqs n r1 -> ResolvesTo eqs n r2 -> r1 = r2.
Proof. Admitted.
Theorem defined_resolves_to_itself : forall p (eqs : ResolvedTypeEquations p) d,
  ResolvesTo eqs (DefinedNode p d) (ResolvedDefined p d).
Proof. Admitted.
Theorem alias_resolves_through_target : forall p (eqs : ResolvedTypeEquations p) a n res,
  equation_target eqs (AliasNode p a) = RawAlias p n -> ResolvesTo eqs (AliasNode p n) res ->
  ResolvesTo eqs (AliasNode p a) res.
Proof. Admitted.
Theorem defined_underlying_follows_resolution :
  forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) d h t,
  ResolvesTo eqs (DefinedNode p d) (ResolvedBasic p t) ->
  defined_underlying env d h = predeclared_basic_form t.
Proof. Admitted.
Theorem alias_resolves_to_exact_type :
  forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) a t,
  ResolvesTo eqs (AliasNode p a) (ResolvedBasic p t) ->
  AliasResolvesTo env a (PredeclaredType env t).
Proof. Admitted.

(* §Keep assignability is identity; conversion splits constant from value. *)
Theorem assignable_is_identity : forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) s t,
  Assignable env s t <-> Identical env s t.
Proof. Admitted.
Theorem defined_not_assignable_to_predeclared :
  forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) d h t,
  ~ Assignable env (DefinedType env d h) (PredeclaredType env t).
Proof. Admitted.
Theorem distinct_predeclared_not_assignable :
  forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) t u,
  t <> u -> ~ Assignable env (PredeclaredType env t) (PredeclaredType env u).
Proof. Admitted.
Theorem no_value_scalar_to_complex :
  forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) s t bs bt,
  Underlying env s (BasicForm env bs) -> Underlying env t (BasicForm env bt) ->
  ScalarNumericBasic bs -> ComplexBasicForm bt -> ~ ValueConvertible env s t.
Proof. Admitted.
Theorem no_value_complex_to_scalar :
  forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) s t bs bt,
  Underlying env s (BasicForm env bs) -> Underlying env t (BasicForm env bt) ->
  ComplexBasicForm bs -> ScalarNumericBasic bt -> ~ ValueConvertible env s t.
Proof. Admitted.
Theorem identicalb_reflect : forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) s t,
  identicalb env s t = true <-> Identical env s t.
Proof. Admitted.
Theorem assignableb_reflect : forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) s t,
  assignableb env s t = true <-> Assignable env s t.
Proof. Admitted.
Theorem value_convertibleb_reflect : forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) s t,
  value_convertibleb env s t = true <-> ValueConvertible env s t.
Proof. Admitted.
Theorem representableb_reflect : forall p eqs (r : TypeReady eqs) (env : @Env p eqs r) s c,
  representableb env s c = true <-> Representable env s c.
Proof. Admitted.
