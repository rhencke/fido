(* Analysis — the sole fact and issue authority: per-occurrence outcomes, the issue table, and the preflight. *)

From Stdlib Require Import List Bool String Ascii ZArith NArith Lia Eqdep_dec.
From Fido Require Import Names Integer Float Complex Syntax Index Index.Model Index.Refs Index.Edges FilePath Compilable.TypeResolution Compilable.Bindings.
Import ListNotations.

Module TR := Compilable.TypeResolution.
Module BN := Compilable.Bindings.

(* small list utilities used by the §24.4 redeclaration laws: NoDup passes through map-inverse and filter *)
Lemma nodup_map_inv {A B} (f : A -> B) (l : list A) : NoDup (map f l) -> NoDup l.
Proof.
  induction l as [|a t IH]; intro H; [ constructor | ].
  cbn in H. inversion H as [|? ? Hna H']; subst. constructor; [ intro Hin; apply Hna, in_map, Hin | exact (IH H') ].
Qed.
Lemma nodup_filter {A} (f : A -> bool) (l : list A) : NoDup l -> NoDup (filter f l).
Proof.
  induction l as [|a t IH]; intro H; cbn; [ constructor | ].
  inversion H as [|? ? Hna H']; subst.
  destruct (f a); [ constructor; [ intro Hin; apply filter_In in Hin; exact (Hna (proj1 Hin)) | exact (IH H') ] | exact (IH H') ].
Qed.
(* a duplicate-free key projection is injective on members: equal keys force the equal element *)
Lemma nodup_map_inj {A B} (f : A -> B) (l : list A) (H : NoDup (map f l)) :
  forall a b, In a l -> In b l -> f a = f b -> a = b.
Proof.
  induction l as [|x t IH]; intros a b Ha Hb Hab; [ inversion Ha | ].
  cbn in H. inversion H as [|? ? Hnx H']; subst.
  destruct Ha as [<-|Ha]; destruct Hb as [<-|Hb]; [ reflexivity | | | exact (IH H' a b Ha Hb Hab) ].
  - exfalso. apply Hnx. rewrite Hab. exact (in_map f t b Hb).
  - exfalso. apply Hnx. rewrite <- Hab. exact (in_map f t a Ha).
Qed.

(* every file's node enumeration is duplicate-free: its ordinal positions are the distinct seq 0..count *)
Lemma file_nodes_nodup {p} {idx : Index.ProgramIndex p} (fr : Index.FileRef idx) : NoDup (Index.file_nodes fr).
Proof. apply (nodup_map_inv Index.nr_pos). rewrite Index.file_nodes_pos. apply seq_NoDup. Qed.
(* every node of a file is in that file's enumeration: the ordinals cover exactly seq 0..count, once each *)
Lemma file_nodes_complete {p} {idx : Index.ProgramIndex p} (fr : Index.FileRef idx) (r : Index.NodeRef idx) :
  Index.nr_file r = fr -> In r (Index.file_nodes fr).
Proof.
  intro Hf. assert (Hin : In (Index.nr_pos r) (map Index.nr_pos (Index.file_nodes fr))).
  { rewrite Index.file_nodes_pos. apply in_seq. split; [ lia | ].
    rewrite <- Hf. pose proof (Index.nr_pos_lt r). lia. }
  apply in_map_iff in Hin. destruct Hin as [r' [Hpos Hin']].
  assert (Hre : r' = r)
    by (apply Index.noderef_positional; [ rewrite (Index.file_nodes_file fr r' Hin'), Hf; reflexivity | exact Hpos ]).
  subst r'; exact Hin'.
Qed.
(* the exact expression child of an expr statement stays in that statement's file: children never cross files *)
Lemma ee_child_file {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx)
  (Hv : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr) :
  Index.nr_file (Index.Edges.ee_child (Index.Edges.exprstmt_expr (Index.Refs.mkExprStmtRef r Hv))) = Index.nr_file r.
Proof.
  symmetry.
  exact (proj2 (Index.node_parent_inv _ _
    (Index.Child.ca_node_parent (Index.Edges.ee_at (Index.Edges.exprstmt_expr (Index.Refs.mkExprStmtRef r Hv)))))).
Qed.

(* the Analysis applicability/fact kind of an occurrence; the displayed Family is a total projection of site+kind *)
Inductive FactKind : Type := ValueKind | ApplicationKind | StatementKind | TypeUseKind.

(* a value-producing literal, unary or application node: the exact subject of a default overflow *)
Definition is_value_default_node {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) : bool :=
  match Index.node_view site with
  | Index.Model.VLiteral _ | Index.Model.VUnary _ | Index.Model.VApplication => true
  | _ => false
  end.
(* a var/type-spec declaration node: the exact subject of a deferred value-declaration meaning *)
Definition is_value_decl_node {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) : bool :=
  match Index.node_view site with Index.Model.VVarSpec _ | Index.Model.VTypeSpec _ => true | _ => false end.
Lemma is_value_default_lit {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) (l : Syntax.Literal) :
  Index.node_view site = Index.Model.VLiteral l -> is_value_default_node site = true.
Proof. intro H. unfold is_value_default_node. rewrite H. reflexivity. Qed.
Lemma is_value_default_unary {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) (u : Syntax.UnaryOp) :
  Index.node_view site = Index.Model.VUnary u -> is_value_default_node site = true.
Proof. intro H. unfold is_value_default_node. rewrite H. reflexivity. Qed.
Lemma is_value_default_app {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) :
  Index.node_view site = Index.Model.VApplication -> is_value_default_node site = true.
Proof. intro H. unfold is_value_default_node. rewrite H. reflexivity. Qed.
(* an application occurrence is a live expression node, so its use path is available *)
Lemma is_expr_node_app {p} {idx : Index.ProgramIndex p} {site : Index.NodeRef idx} :
  Index.node_view site = Index.Model.VApplication -> Index.Edges.is_expr_node site = true.
Proof. intro H. unfold Index.Edges.is_expr_node. rewrite H. reflexivity. Qed.
Lemma is_value_decl_var {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) (v : Index.Model.VarShape) :
  Index.node_view site = Index.Model.VVarSpec v -> is_value_decl_node site = true.
Proof. intro H. unfold is_value_decl_node. rewrite H. reflexivity. Qed.
Lemma is_value_decl_type {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) (t : Index.Model.TypeSpecShape) :
  Index.node_view site = Index.Model.VTypeSpec t -> is_value_decl_node site = true.
Proof. intro H. unfold is_value_decl_node. rewrite H. reflexivity. Qed.

(* the exact cause of an invalidity, owned by phase bp, site and fact kind: site A / kind X never inhabits B / Y *)
Inductive Cause {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) (site : Index.NodeRef idx) : FactKind -> Type :=
| InvalidIdentity : forall (n : Names.OrdinaryIdentifier)
    (r : BN.ResolutionRef (BN.use_env bp site) n) (pn : Names.PredeclaredName),
    BN.resolution_object_view r = Some (BN.PredeclaredObject pn) -> Cause bp site ValueKind
| UnresolvedNameV : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n),
    BN.resolution_object_view r = None -> BN.resolution_redecl_root r = None -> Cause bp site ValueKind
| TypeAsValue : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n) (o : BN.ObjectRef idx),
    BN.resolution_object_view r = Some o -> Cause bp site ValueKind
| ComplexMismatch : Index.node_view site = Index.Model.VApplication ->
    Index.NodeRef idx -> Index.NodeRef idx -> Cause bp site ValueKind
| ConversionOverflow : Index.node_view site = Index.Model.VApplication ->
    TR.TypeForm -> Index.NodeRef idx -> Cause bp site ValueKind
| ConversionNotRepresentable : Index.node_view site = Index.Model.VApplication ->
    TR.TypeForm -> Index.NodeRef idx -> Cause bp site ValueKind
| NoValueUsed : Index.node_view site = Index.Model.VApplication -> Cause bp site ValueKind
| UnaryMismatch : Index.node_view site = Index.Model.VUnary Syntax.UnaryMinus -> Cause bp site ValueKind
| DefaultOverflow : is_value_default_node site = true -> TR.Constant -> Cause bp site ValueKind
| ConstMissingInit : forall (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF),
    BN.ConstSpecJudgmentRef bp cs -> site = Index.Refs.sp_node cs -> Cause bp site ValueKind
| ResultCountMismatch : forall (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF),
    site = Index.Refs.sp_node cs -> nat -> nat -> Cause bp site ValueKind
| NotCallable : forall (ar : Index.Refs.AppRef idx), site = Index.Refs.app_node ar ->
    forall (n : Names.OrdinaryIdentifier)
      (r : BN.ResolutionRef (BN.use_env bp (Index.Edges.ah_child (Index.Edges.app_head ar))) n) (o : BN.ObjectRef idx),
    BN.resolution_object_view r = Some o -> Cause bp site ApplicationKind
| NotCallableExpr : Index.node_view site = Index.Model.VApplication -> Cause bp site ApplicationKind
| ConversionArity : Index.node_view site = Index.Model.VApplication ->
    Names.PredeclaredName -> nat -> Cause bp site ApplicationKind
| ComplexArity : Index.node_view site = Index.Model.VApplication -> nat -> Cause bp site ApplicationKind
| MainArity : forall (ar : Index.Refs.AppRef idx), site = Index.Refs.app_node ar ->
    forall (n : Names.OrdinaryIdentifier)
      (r : BN.ResolutionRef (BN.use_env bp (Index.Edges.ah_child (Index.Edges.app_head ar))) n) (f : BN.FunctionDeclRef idx),
    BN.resolution_object_view r = Some (BN.SourceObject (BN.DOFunc f)) ->
    list (Index.NodeRef idx) -> nat -> Cause bp site ApplicationKind
(* §330 iota/nil resolved as an application head: the invalid identity moves to the application row, a diagnostic *)
| InvalidApplicationIdentity : forall (ar : Index.Refs.AppRef idx), site = Index.Refs.app_node ar ->
    forall (n : Names.OrdinaryIdentifier)
      (r : BN.ResolutionRef (BN.use_env bp (Index.Edges.ah_child (Index.Edges.app_head ar))) n) (pn : Names.PredeclaredName),
    BN.resolution_object_view r = Some (BN.PredeclaredObject pn) -> Cause bp site ApplicationKind
(* §332 an unresolved application head: the head-name unresolved issue moves to the application row, a diagnostic *)
| UnresolvedApplicationHead : forall (ar : Index.Refs.AppRef idx), site = Index.Refs.app_node ar ->
    forall (n : Names.OrdinaryIdentifier)
      (r : BN.ResolutionRef (BN.use_env bp (Index.Edges.ah_child (Index.Edges.app_head ar))) n),
    BN.resolution_object_view r = None -> BN.resolution_redecl_root r = None -> Cause bp site ApplicationKind
| UnresolvedNameT : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n),
    BN.resolution_object_view r = None -> BN.resolution_redecl_root r = None -> Cause bp site TypeUseKind
| NotAType : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n) (o : BN.ObjectRef idx),
    BN.resolution_object_view r = Some o -> Cause bp site TypeUseKind
| IllegalStatement : Index.node_view site = Index.Model.VStmt Index.Model.SSExpr -> Cause bp site StatementKind
| ShortDuplicate : forall (st : Index.Refs.ShortStmtRef idx) (se : BN.ShortEventRef bp st)
    (dd : BN.ShortDuplicateDecision se) (n : Names.OrdinaryIdentifier),
    dd = BN.short_duplicate_decision se -> BN.short_dup_decision_name dd = Some n ->
    site = Index.Refs.sh_node st -> Cause bp site StatementKind
| ShortCountMismatch : forall (st : Index.Refs.ShortStmtRef idx),
    site = Index.Refs.sh_node st -> Index.Refs.sh_names st <> Index.Refs.sh_values st -> Cause bp site StatementKind
| ShortReusesNonVariable : forall (st : Index.Refs.ShortStmtRef idx)
    (i : nat) (row : BN.ShortDecisionRowRef (BN.short_event bp st) i) (m : nat),
    BN.row_decision row = BN.ShortExistingNonVariableData m ->
    site = Index.Refs.sh_node st -> Cause bp site StatementKind
| ShortNoNewName : forall (st : Index.Refs.ShortStmtRef idx),
    existsb BN.is_new_row (BN.se_rows (BN.short_event bp st)) = false ->
    site = Index.Refs.sh_node st -> Cause bp site StatementKind.
Arguments InvalidIdentity {p idx s bd bp site n} _ _ _.
Arguments UnresolvedNameV {p idx s bd bp site n} _ _ _.
Arguments TypeAsValue {p idx s bd bp site n} _ _ _.
Arguments ComplexMismatch {p idx s bd bp site} _ _ _. Arguments ConversionOverflow {p idx s bd bp site} _ _ _.
Arguments ConversionNotRepresentable {p idx s bd bp site} _ _ _. Arguments NoValueUsed {p idx s bd bp site} _.
Arguments UnaryMismatch {p idx s bd bp site} _. Arguments DefaultOverflow {p idx s bd bp site} _ _.
Arguments ConstMissingInit {p idx s bd bp site cs} _ _. Arguments ResultCountMismatch {p idx s bd bp site} cs _ _ _.
Arguments NotCallable {p idx s bd bp site} _ _ _ _ _ _. Arguments NotCallableExpr {p idx s bd bp site} _.
Arguments ConversionArity {p idx s bd bp site} _ _ _. Arguments ComplexArity {p idx s bd bp site} _ _.
Arguments MainArity {p idx s bd bp site} _ _ _ _ _ _ _ _.
Arguments InvalidApplicationIdentity {p idx s bd bp site} _ _ _ _ _ _.
Arguments UnresolvedApplicationHead {p idx s bd bp site} _ _ _ _ _ _.
Arguments UnresolvedNameT {p idx s bd bp site n} _ _ _. Arguments NotAType {p idx s bd bp site n} _ _ _.
Arguments IllegalStatement {p idx s bd bp site} _. Arguments ShortDuplicate {p idx s bd bp site st se} _ _ _ _ _.
Arguments ShortCountMismatch {p idx s bd bp site} st _ _.
Arguments ShortReusesNonVariable {p idx s bd bp site} st i row m _ _.
Arguments ShortNoNewName {p idx s bd bp site} st _ _.

(* §8.6 the exact positive short-declaration verdict: local structural legality, prior to declared-and-used *)
Record ShortStructurallyValid {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) (st : Index.Refs.ShortStmtRef idx) : Prop := mkShortValid {
  ssv_no_dup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp st)) = None ;
  ssv_count : Index.Refs.sh_names st = Index.Refs.sh_values st ;
  ssv_no_blocker : BN.short_blocker_decision (BN.short_event bp st) = BN.ShortNoBlocker ;
  ssv_has_new : existsb BN.is_new_row (BN.se_rows (BN.short_event bp st)) = true ;
  ssv_no_mixed : existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp st)) = false ;
}.
Arguments mkShortValid {p idx s bd bp st} _ _ _ _ _.

(* one outward link of a use path: a unary operand, an application argument i, or an application head *)
Inductive Link {p} {idx : Index.ProgramIndex p} : Type :=
| LUnary : Index.Refs.UnaryRef idx -> Link
| LArg   : Index.Refs.AppRef idx -> nat -> Link
| LHead  : Index.Refs.AppRef idx -> Link.
Arguments Link {p} idx.

(* the exact ordered link sequence of a path, from the subject's own link outward to the root *)
Fixpoint path_links {p} {idx : Index.ProgramIndex p} {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r)
  : list (Link idx) :=
  match path with
  | Index.Edges.EUPUnary u _ sub => LUnary u :: path_links sub
  | Index.Edges.EUPArg a i _ sub => LArg a i :: path_links sub
  | Index.Edges.EUPHead a _ sub => LHead a :: path_links sub
  | _ => []
  end.

(* initializer ancestry: the path bottoms at the exact const value edge through any finite mixed link chain *)
Inductive ConstRootOf {p} {idx : Index.ProgramIndex p}
  : forall {r : Index.NodeRef idx}, Index.Edges.ExprUsePath r ->
    forall (sp : Index.Refs.SpecRef idx Index.Model.ConstSpecF) (j : nat), Index.Edges.SpecValueEdge sp j -> Prop :=
| CRConst : forall sp j (e : Index.Edges.SpecValueEdge sp j), ConstRootOf (Index.Edges.EUPConst sp j e) sp j e
| CRUnary : forall (u : Index.Refs.UnaryRef idx) (e : Index.Edges.UnaryOperandEdge u)
    (sub : Index.Edges.ExprUsePath (Index.Refs.un_node u)) sp j se,
    ConstRootOf sub sp j se -> ConstRootOf (Index.Edges.EUPUnary u e sub) sp j se
| CRArg : forall (a : Index.Refs.AppRef idx) (i : nat) (e : Index.Edges.ApplicationArgEdge a i)
    (sub : Index.Edges.ExprUsePath (Index.Refs.app_node a)) sp j se,
    ConstRootOf sub sp j se -> ConstRootOf (Index.Edges.EUPArg a i e sub) sp j se
| CRHead : forall (a : Index.Refs.AppRef idx) (e : Index.Edges.ApplicationHeadEdge a)
    (sub : Index.Edges.ExprUsePath (Index.Refs.app_node a)) sp j se,
    ConstRootOf sub sp j se -> ConstRootOf (Index.Edges.EUPHead a e sub) sp j se.

(* the computed initializer root of a path: exactly the const value edge it bottoms at, None outside every ConstSpec *)
Fixpoint path_const_root {p} {idx : Index.ProgramIndex p} {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r)
  : option { sp : Index.Refs.SpecRef idx Index.Model.ConstSpecF & { j : nat & Index.Edges.SpecValueEdge sp j } } :=
  match path with
  | Index.Edges.EUPConst sp j e => Some (existT _ sp (existT _ j e))
  | Index.Edges.EUPUnary _ _ sub => path_const_root sub
  | Index.Edges.EUPArg _ _ _ sub => path_const_root sub
  | Index.Edges.EUPHead _ _ sub => path_const_root sub
  | _ => None
  end.

(* the computed root is the exact ancestry witness: every Some is a ConstRootOf, at any depth of mixed links *)
Lemma path_const_root_sound {p} {idx : Index.ProgramIndex p} {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r) :
  match path_const_root path with
  | Some (existT _ sp (existT _ j e)) => ConstRootOf path sp j e
  | None => True
  end.
Proof.
  induction path as [s e | sp j e | sp j e Ht | sp j e Ht | st j e | u e sub IH | a i e sub IH | a e sub IH]; cbn [path_const_root];
    try exact I; try (constructor; fail).
  - destruct (path_const_root sub) as [[sp' [j' e']]|]; [ apply CRUnary; exact IH | exact I ].
  - destruct (path_const_root sub) as [[sp' [j' e']]|]; [ apply CRArg; exact IH | exact I ].
  - destruct (path_const_root sub) as [[sp' [j' e']]|]; [ apply CRHead; exact IH | exact I ].
Qed.

(* the exact-witness form of soundness: a computed root is the ancestry of the path it was read from *)
Lemma path_const_root_at {p} {idx : Index.ProgramIndex p} {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r)
  sp j (e : Index.Edges.SpecValueEdge sp j) :
  path_const_root path = Some (existT _ sp (existT _ j e)) -> ConstRootOf path sp j e.
Proof. intro H. pose proof (path_const_root_sound path) as Hs. rewrite H in Hs. exact Hs. Qed.

(* completeness: initializer ancestry is never lost by the computed root, through every link constructor *)
Lemma path_const_root_complete {p} {idx : Index.ProgramIndex p} {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r)
  sp j (e : Index.Edges.SpecValueEdge sp j) :
  ConstRootOf path sp j e -> path_const_root path = Some (existT _ sp (existT _ j e)).
Proof.
  intro H. induction H; cbn [path_const_root]; [ reflexivity | exact IHConstRootOf | exact IHConstRootOf | exact IHConstRootOf ].
Qed.

(* outside discrimination: a path whose terminal is not a const value edge manufactures no initializer witness *)
Lemma path_const_root_outside {p} {idx : Index.ProgramIndex p} {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r) :
  path_const_root path = None -> forall sp j (e : Index.Edges.SpecValueEdge sp j), ~ ConstRootOf path sp j e.
Proof. intros Hn sp j e Hc. rewrite (path_const_root_complete path sp j e Hc) in Hn. discriminate Hn. Qed.

(* an explicit declaration target at the exact top of a path: a typed const value or an explicit-type var value *)
Inductive ExplicitRoot {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) : Type :=
| ERConst : forall (sp : Index.Refs.SpecRef idx Index.Model.ConstSpecF) (j : nat) (e : Index.Edges.SpecValueEdge sp j),
    site = Index.Edges.sv_child e -> Index.Refs.shape_has_type Index.Model.ConstSpecF (Index.Refs.sp_shape sp) = true ->
    ExplicitRoot site
| ERVar : forall (sp : Index.Refs.SpecRef idx Index.Model.VarSpecF) (j : nat) (e : Index.Edges.SpecValueEdge sp j),
    site = Index.Edges.sv_child e -> Index.Refs.shape_has_type Index.Model.VarSpecF (Index.Refs.sp_shape sp) = true ->
    ExplicitRoot site.
Arguments ERConst {p idx site} sp j e _ _.
Arguments ERVar {p idx site} sp j e _ _.

Inductive Requirement {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) (site : Index.NodeRef idx) : FactKind -> Type :=
(* the residual value-meaning requirement of a DOBinder source use; a DOShort use is instead a lawful nonconstant *)
| ReqValueMeaning : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n) (org : BN.DeclOrigin idx),
    BN.resolution_object_view r = Some (BN.SourceObject org) -> Requirement bp site ValueKind
| ReqComplexType : Index.node_view site = Index.Model.VApplication -> Requirement bp site ValueKind
| ReqMainUse : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n) (f : BN.FunctionDeclRef idx),
    BN.resolution_object_view r = Some (BN.SourceObject (BN.DOFunc f)) -> Requirement bp site ValueKind
| ReqConstDecl : forall (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF),
    BN.ConstSpecJudgmentRef bp cs -> site = Index.Refs.sp_node cs -> Requirement bp site ValueKind
| ReqDeclMeaningV : is_value_decl_node site = true -> Requirement bp site ValueKind
| ReqApplication : forall (ar : Index.Refs.AppRef idx), site = Index.Refs.app_node ar ->
    forall (n : Names.OrdinaryIdentifier)
      (r : BN.ResolutionRef (BN.use_env bp (Index.Edges.ah_child (Index.Edges.app_head ar))) n) (pn : Names.PredeclaredName),
    BN.resolution_object_view r = Some (BN.PredeclaredObject pn) ->
    list (Index.NodeRef idx) -> Requirement bp site ApplicationKind
| ReqTypeMeaning : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n) (o : BN.ObjectRef idx),
    BN.resolution_object_view r = Some o -> Requirement bp site TypeUseKind
| ReqShortRedeclarationTypes : forall (st : Index.Refs.ShortStmtRef idx),
    site = Index.Refs.sh_node st -> Requirement bp site StatementKind
| ReqShortRhsMeaning : forall (st : Index.Refs.ShortStmtRef idx) (j : nat) (edge : Index.Edges.ShortRhsEdge st j),
    site = Index.Refs.sh_node st -> Requirement bp site StatementKind
| ReqShortUsage : forall (st : Index.Refs.ShortStmtRef idx),
    site = Index.Refs.sh_node st -> Requirement bp site StatementKind
(* §262 iota rooted at a const initializer value: the exact path, its const value edge and the ancestry proof *)
| RInitializerIdentity : forall (n : Names.OrdinaryIdentifier)
    (r0 : BN.ResolutionRef (BN.use_env bp site) n) (pn : Names.PredeclaredName),
    BN.resolution_object_view r0 = Some (BN.PredeclaredObject pn) ->
    forall (path : Index.Edges.ExprUsePath site) (sp : Index.Refs.SpecRef idx Index.Model.ConstSpecF) (j : nat)
      (e : Index.Edges.SpecValueEdge sp j), ConstRootOf path sp j e -> Requirement bp site ValueKind
(* §264 nil as the direct value child of an explicit-type var: the exact var value edge at the top of the path *)
| RTypedTargetIdentity : forall (n : Names.OrdinaryIdentifier)
    (r0 : BN.ResolutionRef (BN.use_env bp site) n) (pn : Names.PredeclaredName),
    BN.resolution_object_view r0 = Some (BN.PredeclaredObject pn) ->
    forall (sp : Index.Refs.SpecRef idx Index.Model.VarSpecF) (j : nat) (e : Index.Edges.SpecValueEdge sp j),
      site = Index.Edges.sv_child e -> Index.Refs.shape_has_type Index.Model.VarSpecF (Index.Refs.sp_shape sp) = true ->
      Requirement bp site ValueKind
(* §250 an untyped constant at a no-type const value edge keeps its exact constant: the declaration makes no default *)
| RConstNoDefault : forall (sp : Index.Refs.SpecRef idx Index.Model.ConstSpecF) (j : nat) (e : Index.Edges.SpecValueEdge sp j),
    site = Index.Edges.sv_child e -> Index.Refs.shape_has_type Index.Model.ConstSpecF (Index.Refs.sp_shape sp) = false ->
    TR.Constant -> Requirement bp site ValueKind
(* §250 an untyped constant under an explicit declaration target: the exact root owns the (unmodelled) conversion *)
| RTypedTargetConstant : ExplicitRoot site -> TR.Constant -> Requirement bp site ValueKind
(* a represented, semantically valid conversion family whose rule is absent: an exact boundary, never an invalidity *)
| RConversionUnmet : Index.node_view site = Index.Model.VApplication ->
    TR.TypeForm -> Index.NodeRef idx -> Requirement bp site ValueKind
(* §271 a type-spec binder application head: the source-type/conversion applicability is unmodelled, a boundary *)
| ReqSourceTypeApp : forall (ar : Index.Refs.AppRef idx), site = Index.Refs.app_node ar ->
    forall (h : Names.OrdinaryIdentifier) (r0 : BN.ResolutionRef (BN.use_env bp (Index.Edges.ah_child (Index.Edges.app_head ar))) h) (b : BN.BinderRef idx),
    BN.resolution_object_view r0 = Some (BN.SourceObject (BN.DOBinder b)) ->
    Index.node_role (BN.binder_node b) = Index.Model.RSpecName Index.Model.TypeSpecF -> Requirement bp site ApplicationKind
(* §271 a var-spec binder head: source-value callability is unmodelled, a boundary; never infer its type *)
| ReqSourceValueApp : forall (ar : Index.Refs.AppRef idx), site = Index.Refs.app_node ar ->
    forall (h : Names.OrdinaryIdentifier) (r0 : BN.ResolutionRef (BN.use_env bp (Index.Edges.ah_child (Index.Edges.app_head ar))) h) (b : BN.BinderRef idx),
    BN.resolution_object_view r0 = Some (BN.SourceObject (BN.DOBinder b)) ->
    Index.node_role (BN.binder_node b) = Index.Model.RSpecName Index.Model.VarSpecF -> Requirement bp site ApplicationKind
(* §271 a short-origin application head: the short-declared function-value callability is unmodelled, a boundary *)
| ReqShortOriginApp : forall (ar : Index.Refs.AppRef idx), site = Index.Refs.app_node ar ->
    forall (h : Names.OrdinaryIdentifier) (r0 : BN.ResolutionRef (BN.use_env bp (Index.Edges.ah_child (Index.Edges.app_head ar))) h) (sn : BN.ShortNewRef idx),
    BN.resolution_object_view r0 = Some (BN.SourceObject (BN.DOShort sn)) -> Requirement bp site ApplicationKind.
Arguments ReqSourceTypeApp {p idx s bd bp site} ar _ h _ b _ _.
Arguments ReqSourceValueApp {p idx s bd bp site} ar _ h _ b _ _.
Arguments ReqShortOriginApp {p idx s bd bp site} ar _ h _ sn _.
Arguments RInitializerIdentity {p idx s bd bp site n} _ _ _ _ _ _ _ _.
Arguments RTypedTargetIdentity {p idx s bd bp site n} _ _ _ _ _ _ _ _.
Arguments RConstNoDefault {p idx s bd bp site} sp j e _ _ _.
Arguments RTypedTargetConstant {p idx s bd bp site} _ _.
Arguments RConversionUnmet {p idx s bd bp site} _ _ _.
Arguments ReqValueMeaning {p idx s bd bp site n} _ _ _. Arguments ReqComplexType {p idx s bd bp site} _.
Arguments ReqMainUse {p idx s bd bp site n} _ _ _. Arguments ReqConstDecl {p idx s bd bp site cs} _ _.
Arguments ReqDeclMeaningV {p idx s bd bp site} _. Arguments ReqApplication {p idx s bd bp site} _ _ _ _ _ _ _.
Arguments ReqTypeMeaning {p idx s bd bp site n} _ _ _.
Arguments ReqShortRedeclarationTypes {p idx s bd bp site} st _.
Arguments ReqShortRhsMeaning {p idx s bd bp site} st j edge _.
Arguments ReqShortUsage {p idx s bd bp site} st _.

(* §8 the exact structural edge from an expr-statement parent to its exact expression child (ExprStmtRef, +AppRef) *)
Inductive ChildFactEdge {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) : FactKind -> Type :=
| ExprStmtValueChild : forall (pr : Index.Refs.ExprStmtRef idx),
    site = Index.Refs.exs_node pr -> ChildFactEdge site StatementKind
| ExprStmtApplicationChild : forall (pr : Index.Refs.ExprStmtRef idx) (ar : Index.Refs.AppRef idx),
    site = Index.Refs.exs_node pr ->
    Index.Refs.app_node ar = Index.Edges.ee_child (Index.Edges.exprstmt_expr pr) ->
    ChildFactEdge site StatementKind
| ShortValueChild : forall (st : Index.Refs.ShortStmtRef idx) (j : nat) (edge : Index.Edges.ShortRhsEdge st j),
    site = Index.Refs.sh_node st -> ChildFactEdge site StatementKind
| ShortApplicationChild : forall (st : Index.Refs.ShortStmtRef idx) (j : nat) (edge : Index.Edges.ShortRhsEdge st j)
    (ar : Index.Refs.AppRef idx),
    site = Index.Refs.sh_node st ->
    Index.Refs.app_node ar = Index.Edges.sr_child edge ->
    ChildFactEdge site StatementKind.
Arguments ExprStmtValueChild {p idx site} _ _.
Arguments ExprStmtApplicationChild {p idx site} _ _ _ _.
Arguments ShortValueChild {p idx site} st j edge _.
Arguments ShortApplicationChild {p idx site} st j edge ar _ _.
(* the exact child site is a projection of the edge, never supplied independently; the child kind is closed by case *)
Definition cfe_child_site {p} {idx : Index.ProgramIndex p} {site : Index.NodeRef idx} {k : FactKind}
  (e : ChildFactEdge site k) : Index.NodeRef idx :=
  match e with
  | ExprStmtValueChild pr _ => Index.Edges.ee_child (Index.Edges.exprstmt_expr pr)
  | ExprStmtApplicationChild pr _ _ _ => Index.Edges.ee_child (Index.Edges.exprstmt_expr pr)
  | ShortValueChild _ _ edge _ => Index.Edges.sr_child edge
  | ShortApplicationChild _ _ edge _ _ _ => Index.Edges.sr_child edge
  end.
Definition cfe_child_kind {p} {idx : Index.ProgramIndex p} {site : Index.NodeRef idx} {k : FactKind}
  (e : ChildFactEdge site k) : FactKind :=
  match e with
  | ExprStmtValueChild _ _ => ValueKind | ExprStmtApplicationChild _ _ _ _ => ApplicationKind
  | ShortValueChild _ _ _ _ => ValueKind | ShortApplicationChild _ _ _ _ _ _ => ApplicationKind
  end.

(* the exact prerequisite of a dependent non-result: a redeclared/unbound name use, an invalid identity, or a child *)
Inductive Dependency {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) (site : Index.NodeRef idx) : FactKind -> Type :=
| DepRedeclaredNameV : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n) (root : BN.RedeclRoot bp n),
    BN.resolution_redecl_root r = Some root -> Dependency bp site ValueKind
| DepRedeclaredNameA : forall (ar : Index.Refs.AppRef idx), site = Index.Refs.app_node ar ->
    forall (n : Names.OrdinaryIdentifier)
      (r : BN.ResolutionRef (BN.use_env bp (Index.Edges.ah_child (Index.Edges.app_head ar))) n) (root : BN.RedeclRoot bp n),
    BN.resolution_redecl_root r = Some root -> Dependency bp site ApplicationKind
| DepRedeclaredNameT : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n) (root : BN.RedeclRoot bp n),
    BN.resolution_redecl_root r = Some root -> Dependency bp site TypeUseKind
| DepUnboundNameV : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n),
    BN.resolution_object_view r = None -> BN.resolution_redecl_root r = None -> Dependency bp site ValueKind
(* §8 a target-sensitive argument deferring to its non-AOK application, retaining that exact outcome *)
| DepArgInvalid : forall (ar : Index.Refs.AppRef idx) (i : nat),
    Index.node_parent site = Some (Index.Refs.app_node ar) -> Index.node_role site = Index.Model.RApplicationArg i ->
    Cause bp (Index.Refs.app_node ar) ApplicationKind -> Dependency bp site ValueKind
| DepArgUnmet : forall (ar : Index.Refs.AppRef idx) (i : nat),
    Index.node_parent site = Some (Index.Refs.app_node ar) -> Index.node_role site = Index.Model.RApplicationArg i ->
    Requirement bp (Index.Refs.app_node ar) ApplicationKind -> Dependency bp site ValueKind
| DepArgDependent : forall (ar : Index.Refs.AppRef idx) (i : nat),
    Index.node_parent site = Some (Index.Refs.app_node ar) -> Index.node_role site = Index.Model.RApplicationArg i ->
    Dependency bp (Index.Refs.app_node ar) ApplicationKind -> Dependency bp site ValueKind
(* §251 a target-sensitive value on a non-name application head, deferring to its non-callable app *)
| DepHeadInvalid : forall (ar : Index.Refs.AppRef idx),
    Index.node_parent site = Some (Index.Refs.app_node ar) -> Index.node_role site = Index.Model.RApplicationHead ->
    Cause bp (Index.Refs.app_node ar) ApplicationKind -> Dependency bp site ValueKind
(* §7 iota/nil and unbound application heads are now AInvalid causes on the app row, not dependencies *)
| DepChild : ChildFactEdge site StatementKind -> Dependency bp site StatementKind
| DepShortAmbiguous : forall (st : Index.Refs.ShortStmtRef idx)
    (i : nat) (row : BN.ShortDecisionRowRef (BN.short_event bp st) i) (a b : nat),
    BN.row_decision row = BN.ShortAmbiguousData a b ->
    site = Index.Refs.sh_node st -> Dependency bp site StatementKind.
Arguments DepRedeclaredNameV {p idx s bd bp site n} _ _ _.
Arguments DepRedeclaredNameA {p idx s bd bp site} _ _ _ _ _ _.
Arguments DepRedeclaredNameT {p idx s bd bp site n} _ _ _.
Arguments DepUnboundNameV {p idx s bd bp site n} _ _ _.
Arguments DepArgInvalid {p idx s bd bp site} _ _ _ _ _.
Arguments DepArgUnmet {p idx s bd bp site} _ _ _ _ _.
Arguments DepArgDependent {p idx s bd bp site} _ _ _ _ _.
Arguments DepHeadInvalid {p idx s bd bp site} _ _ _ _.
Arguments DepChild {p idx s bd bp site} _.
Arguments DepShortAmbiguous {p idx s bd bp site} st i row a b _ _.

(* each family judgment is independent per node; a prerequisite failure is a dependent non-result, never a success *)
Inductive ValueOutcome {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) (site : Index.NodeRef idx) : Type :=
| VOK : TR.ResolvedConstant -> ValueOutcome bp site
| VNonconst : ValueOutcome bp site
| VInvalid : Cause bp site ValueKind -> ValueOutcome bp site
| VUnmet : Requirement bp site ValueKind -> ValueOutcome bp site
| VDependent : Dependency bp site ValueKind -> ValueOutcome bp site.
Arguments VOK {p idx s bd bp site} _. Arguments VNonconst {p idx s bd bp site}.
Arguments VInvalid {p idx s bd bp site} _. Arguments VUnmet {p idx s bd bp site} _. Arguments VDependent {p idx s bd bp site} _.

Inductive AppOutcome {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) (site : Index.NodeRef idx) : Type :=
| AOK : AppOutcome bp site
| AInvalid : Cause bp site ApplicationKind -> AppOutcome bp site
| AUnmet : Requirement bp site ApplicationKind -> AppOutcome bp site
| ADependent : Dependency bp site ApplicationKind -> AppOutcome bp site.
Arguments AOK {p idx s bd bp site}. Arguments AInvalid {p idx s bd bp site} _.
Arguments AUnmet {p idx s bd bp site} _. Arguments ADependent {p idx s bd bp site} _.

Inductive StmtOutcome {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) (site : Index.NodeRef idx) : Type :=
| SOK : StmtOutcome bp site
| SInvalid : Cause bp site StatementKind -> StmtOutcome bp site
| SUnmet : Requirement bp site StatementKind -> StmtOutcome bp site
| SDependent : Dependency bp site StatementKind -> StmtOutcome bp site.
Arguments SOK {p idx s bd bp site}. Arguments SInvalid {p idx s bd bp site} _.
Arguments SUnmet {p idx s bd bp site} _. Arguments SDependent {p idx s bd bp site} _.

Inductive TypeUseOutcome {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) (site : Index.NodeRef idx) : Type :=
| TOK : TR.TypeForm -> TypeUseOutcome bp site
| TInvalid : Cause bp site TypeUseKind -> TypeUseOutcome bp site
| TUnmet : Requirement bp site TypeUseKind -> TypeUseOutcome bp site
| TDependent : Dependency bp site TypeUseKind -> TypeUseOutcome bp site.
Arguments TOK {p idx s bd bp site} _. Arguments TInvalid {p idx s bd bp site} _.
Arguments TUnmet {p idx s bd bp site} _. Arguments TDependent {p idx s bd bp site} _.

Inductive PMeaning : Type :=
| PMConvForm : TR.TypeForm -> PMeaning
| PMValue : TR.Constant -> PMeaning
| PMComplex | PMPrintln
| PMIota | PMNil
| PMUnmodelled.

Definition pmeaning (n : Names.PredeclaredName) : PMeaning :=
  match TR.predeclared_meaning n with
  | TR.NMConversionForm t => PMConvForm t
  | TR.NMValueConstant c => PMValue c
  | TR.NMNoFormMeaning =>
      match n with
      | Names.PComplex => PMComplex | Names.PPrintln => PMPrintln
      | Names.PIota => PMIota | Names.PNil => PMNil
      | _ => PMUnmodelled
      end
  end.

(* a dependent match on a scrutinee reduces to the arm a known equation picks: destruct H fires (rhs a bound var) *)
Lemma convoy_at {A : Type} {Ba : Type} (a : A) (g : forall x : A, a = x -> Ba) (v : A) (H : a = v) :
  g a eq_refl = g v H.
Proof. destruct H. reflexivity. Qed.

Section OverPhase.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} (bp : BN.BindingPhase s bd).

(* the form/value meaning of a name at a use, for constant folding; None for anything without one *)
Definition nm_at (use : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) : option TR.NameMeaning :=
  match BN.resolution_object_view (BN.resolve bp use n) with
  | Some o =>
      match o with
      | BN.PredeclaredObject pn =>
          match pmeaning pn with
          | PMConvForm t => Some (TR.NMConversionForm t)
          | PMValue c => Some (TR.NMValueConstant c)
          | _ => None
          end
      | BN.SourceObject _ => None
      end
  | None => None
  end.

(* the exact intrinsic result formed at a node before any outer use acts: lossless where an option cell was not *)
Inductive Intrinsic : Type :=
| INonconst                                                (* no exact constant forms here *)
| IUntyped : TR.Constant -> Intrinsic                      (* the exact untyped constant *)
| ITyped : TR.ResolvedConstant -> Intrinsic                (* the exact explicitly typed constant, form and value *)
| IUnaryMismatch : TR.ConstantInfo -> Intrinsic            (* unary minus over an exact non-numeric constant *)
| IUnaryOverflow : TR.ConstantInfo -> Intrinsic            (* unary minus leaving the child's explicit form *)
| IConvFail : forall (t : TR.TypeForm), TR.ConversionResult t -> Intrinsic   (* a conversion that did not convert *)
| IComplexMismatch : TR.ConstantInfo -> TR.ConstantInfo -> Intrinsic
| IComplexDefer : TR.ConstantInfo -> TR.ConstantInfo -> Intrinsic.

(* the ConstantInfo view of an exact constant cell: the untyped constant, or the typed value with its explicit form *)
Definition cell_info (c : Intrinsic) : option TR.ConstantInfo :=
  match c with
  | IUntyped k => Some (TR.mk_cinfo k TR.Untyped)
  | ITyped rc => Some (TR.mk_cinfo (TR.resolved_constant_exact rc) (TR.ExplicitlyTyped (TR.rc_form rc)))
  | _ => None
  end.

(* a complex builtin component must be an untyped numeric or a typed float; the pair class decides the call *)
Inductive ComplexClass := CxOk | CxDefer | CxError.
Definition complex_comp (ci : TR.ConstantInfo) : option (option Float.Kind) :=
  match TR.ci_const ci, TR.ci_typed ci with
  | TR.CInt _, TR.Untyped => Some None
  | TR.CFloat _, TR.Untyped => Some None
  | TR.CFloat _, TR.ExplicitlyTyped (TR.FloatForm ft) => Some (Some ft)
  | _, _ => None
  end.
Definition complex_class (cre cim : TR.ConstantInfo) : ComplexClass :=
  match complex_comp cre, complex_comp cim with
  | None, _ | _, None => CxError
  | Some None, Some None => CxOk
  | Some (Some a), Some (Some b) => if Float.kind_equalb a b then CxDefer else CxError
  | _, _ => CxDefer
  end.

(* the exact cell of a node in the file's intrinsic table; a key the file never carries reads as no constant *)
Definition mcell (m : Collections.NodeMap.t Intrinsic) (rc : Index.NodeRef idx) : Intrinsic :=
  match Collections.NodeMap.find (Index.nr_key rc) m with Some c => c | None => INonconst end.

(* unary minus consumes the exact operand cell and forms its own intrinsic: negation, then the child's form if typed *)
Definition unary_intrinsic (child : Intrinsic) : Intrinsic :=
  match cell_info child with
  | Some ci =>
      match TR.constant_neg (TR.ci_const ci) with
      | Some c' =>
          match TR.ci_typed ci with
          | TR.ExplicitlyTyped tf =>
              match TR.convert_constant tf (TR.mk_cinfo c' TR.Untyped) with
              | TR.Converted tc => ITyped (TR.mk_rc tf tc)
              | _ => IUnaryOverflow ci
              end
          | TR.Untyped => IUntyped c'
          end
      | None => IUnaryMismatch ci
      end
  | None => INonconst
  end.

(* a conversion consumes the exact argument cell ONCE: the typed result, or the exact failure with its source *)
Definition conversion_intrinsic (t : TR.TypeForm) (arg : Intrinsic) : Intrinsic :=
  match cell_info arg with
  | Some ci =>
      match TR.convert_constant t ci with
      | TR.Converted tc => ITyped (TR.mk_rc t tc)
      | res => IConvFail t res
      end
  | None => INonconst
  end.

(* the complex builtin consumes both exact component cells once and forms one exact untyped complex constant *)
Definition complex_intrinsic (re im : Intrinsic) : Intrinsic :=
  match cell_info re, cell_info im with
  | Some cre, Some cim =>
      match complex_class cre cim with
      | CxOk =>
          match TR.complex_of_constants (TR.ci_const cre) (TR.ci_const cim) with
          | Some c => IUntyped c
          | None => IComplexMismatch cre cim
          end
      | CxDefer => IComplexDefer cre cim
      | CxError => IComplexMismatch cre cim
      end
  | _, _ => INonconst
  end.

(* intrinsic formation at one node, child-first: literals and names are exact untyped, folds read child cells *)
Definition node_intrinsic_body (m : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx)
  (nv : Index.Model.NodeView) (Hnv : Index.node_view r = nv) : Intrinsic :=
  match nv as v return Index.node_view r = v -> Intrinsic with
  | Index.Model.VName n => fun _ =>
      match nm_at r n with Some (TR.NMValueConstant c) => IUntyped c | _ => INonconst end
  | Index.Model.VLiteral (Syntax.IntegerLiteral k) => fun _ => IUntyped (TR.CInt (Z.of_N k))
  | Index.Model.VLiteral (Syntax.FloatLiteral d) => fun _ => IUntyped (TR.CFloat (Float.nnd_value d))
  | Index.Model.VLiteral (Syntax.StringLiteral str) => fun _ => IUntyped (TR.CString str)
  | Index.Model.VUnary Syntax.UnaryMinus => fun Hv =>
      unary_intrinsic (mcell m (Index.Edges.uo_child (Index.Edges.unary_operand (Index.Refs.mkUnaryRef r Syntax.UnaryMinus Hv))))
  | Index.Model.VApplication => fun Hv =>
      match Index.node_view (Index.Edges.ah_child (Index.Edges.app_head (Index.Refs.mkAppRef r Hv))) with
      | Index.Model.VName h =>
          match map (fun x => Index.Edges.aa_child (projT2 x)) (Index.Edges.application_args (Index.Refs.mkAppRef r Hv)) with
          | x :: nil =>
              match nm_at r h with
              | Some (TR.NMConversionForm t) => conversion_intrinsic t (mcell m x)
              | _ => INonconst
              end
          | re :: im :: nil =>
              match BN.resolution_object_view (BN.resolve bp r h) with
              | Some (BN.PredeclaredObject Names.PComplex) => complex_intrinsic (mcell m re) (mcell m im)
              | _ => INonconst
              end
          | _ => INonconst
          end
      | _ => INonconst
      end
  | _ => fun _ => INonconst
  end Hnv.
Definition node_intrinsic (m : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx) : Intrinsic :=
  node_intrinsic_body m r (Index.node_view r) eq_refl.
(* the formation of a node reduces to its exact node_view branch — the convoy named so it is rewritable *)
Lemma node_intrinsic_at (m : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx)
  (v : Index.Model.NodeView) (H : Index.node_view r = v) : node_intrinsic m r = node_intrinsic_body m r v H.
Proof. unfold node_intrinsic. destruct H. reflexivity. Qed.
(* W5 formation never defaults or types: a literal forms its exact untyped constant, a name at most one *)
Lemma node_intrinsic_lit (m : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx) (l : Syntax.Literal)
  (Hv : Index.node_view r = Index.Model.VLiteral l) : exists c, node_intrinsic m r = IUntyped c.
Proof. rewrite (node_intrinsic_at m r _ Hv). destruct l; eexists; reflexivity. Qed.
Lemma node_intrinsic_name (m : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (Hv : Index.node_view r = Index.Model.VName n) : node_intrinsic m r = INonconst \/ exists c, node_intrinsic m r = IUntyped c.
Proof.
  rewrite (node_intrinsic_at m r _ Hv). cbn [node_intrinsic_body].
  destruct (nm_at r n) as [[t|c|]|]; [ left | right; eexists | left | left ]; reflexivity.
Qed.
(* W5 unary minus and a conversion consume the exact untyped child once, forming the parent's own intrinsic *)
Lemma unary_intrinsic_untyped (c : TR.Constant) :
  unary_intrinsic (IUntyped c)
  = match TR.constant_neg c with Some c' => IUntyped c' | None => IUnaryMismatch (TR.mk_cinfo c TR.Untyped) end.
Proof. reflexivity. Qed.
Lemma conversion_intrinsic_untyped (t : TR.TypeForm) (c : TR.Constant) :
  conversion_intrinsic t (IUntyped c)
  = match TR.convert_constant t (TR.mk_cinfo c TR.Untyped) with TR.Converted tc => ITyped (TR.mk_rc t tc) | res => IConvFail t res end.
Proof. reflexivity. Qed.
(* W5 a typed cell keeps its explicit form beside its exact value: the TypedFlag survives until the use *)
Lemma cell_info_typed (rc : TR.ResolvedConstant) :
  cell_info (ITyped rc) = Some (TR.mk_cinfo (TR.resolved_constant_exact rc) (TR.ExplicitlyTyped (TR.rc_form rc))).
Proof. reflexivity. Qed.
(* W8 nested unary forms fold to one exact intrinsic: negation is an involution on every numeric constant *)
Lemma unary_intrinsic_twice (c c' : TR.Constant) (Hn : TR.constant_neg c = Some c') :
  unary_intrinsic (unary_intrinsic (IUntyped c)) = IUntyped c.
Proof.
  rewrite unary_intrinsic_untyped, Hn, unary_intrinsic_untyped, (TR.constant_neg_involutive c c' Hn). reflexivity.
Qed.
(* the file's intrinsic cells folded in descending position order, children before parents (file_nodes is trie order) *)
Definition const_table (fr : Index.FileRef idx) : Collections.NodeMap.t Intrinsic :=
  fold_left (fun m pos =>
               match Index.mk_noderef fr (Pos.of_succ_nat pos) with
               | Some r => Collections.NodeMap.add (Index.nr_key r) (node_intrinsic m r) m
               | None => m
               end)
            (rev (seq 0 (Index.occ_count fr))) (Collections.NodeMap.empty _).
(* role decides value-use: an application head is a callee, not a value; expr-statement exprs go to own_stmt *)
Definition is_app_head (r : Index.NodeRef idx) : bool :=
  match Index.node_role r with Index.Model.RApplicationHead => true | _ => false end.
(* §7 a name on the application-head edge is callee-only: it carries no value row, only the application row *)
Definition is_name_head (r : Index.NodeRef idx) : bool :=
  is_app_head r && match Index.node_view r with Index.Model.VName _ => true | _ => false end.
Definition value_ctx (r : Index.NodeRef idx) : bool :=
  match Index.node_role r with Index.Model.RApplicationHead => false | Index.Model.RExprStatementExpr => false | _ => true end.

(* §251 a zero-result result is consumed unless discarded as a bare statement; a non-name app head still consumes it *)
Definition zero_result_consumed (r : Index.NodeRef idx) : bool := value_ctx r || is_app_head r.

(* the one selected use of an exact intrinsic result per judged occurrence, UADiscard the bare expression statement *)
Inductive UseAction : Type :=
| UADefault          (* a genuine defaulting use: the default type is applied once to the final untyped constant *)
| UAPreserve         (* a no-type const value: the untyped constant is kept exact, the declaration makes no default *)
| UAExplicitTarget   (* an explicit declaration target owns the conversion: an exact boundary today *)
| UAFold             (* a unary operand or a folding application argument: consumed into the parent's intrinsic *)
| UACallee           (* an application head: callability, never a value *)
| UADiscard.

(* an argument's use is fixed by its application head: a conversion or complex head folds it, any other head defaults *)
Definition arg_use_action (a : Index.Refs.AppRef idx) : UseAction :=
  match Index.node_view (Index.Edges.ah_child (Index.Edges.app_head a)) with
  | Index.Model.VName h =>
      match BN.resolution_object_view (BN.resolve bp (Index.Refs.app_node a) h) with
      | Some (BN.PredeclaredObject pn) =>
          match pmeaning pn with PMConvForm _ => UAFold | PMComplex => UAFold | _ => UADefault end
      | _ => UADefault
      end
  | _ => UADefault
  end.

(* the use action of a path is read from its exact top link: the immediate use-context selects it *)
Definition use_action {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r) : UseAction :=
  match path with
  | Index.Edges.EUPExprStmt _ _ => UADiscard
  | Index.Edges.EUPConst sp _ _ =>
      if Index.Refs.shape_has_type Index.Model.ConstSpecF (Index.Refs.sp_shape sp) then UAExplicitTarget else UAPreserve
  | Index.Edges.EUPVarExplicit _ _ _ _ => UAExplicitTarget
  | Index.Edges.EUPVarImplicit _ _ _ _ => UADefault
  | Index.Edges.EUPShort _ _ _ => UADefault
  | Index.Edges.EUPUnary _ _ _ => UAFold
  | Index.Edges.EUPArg a _ _ _ => arg_use_action a
  | Index.Edges.EUPHead _ _ _ => UACallee
  end.


(* a const spec: a first spec omitting its initializer, or a known result-count mismatch, is an exact invalidity *)
Definition const_spec_disposition (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF) : ValueOutcome bp (Index.Refs.sp_node cs) :=
  let cjr := BN.const_spec_judgment bp cs in
  match Index.Refs.sp_shape cs with
  | Index.Model.CSExplicit _ nn nv =>
      if Nat.eqb nn nv then VUnmet (ReqConstDecl cjr eq_refl) else VInvalid (ResultCountMismatch cs eq_refl nn nv)
  | Index.Model.CSInherited _ =>
      match projT2 (BN.cjr_row cjr) with
      | BN.CJFirstInherited _ _ _ => VInvalid (ConstMissingInit cjr eq_refl)
      | _ => VUnmet (ReqConstDecl cjr eq_refl)
      end
  end.

(* §24.3 const provenance: a const spec's outcome retains the exact ConstSpecJudgmentRef, never a projected row *)
Lemma const_disposition_exact (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF) :
  const_spec_disposition cs = VUnmet (ReqConstDecl (BN.const_spec_judgment bp cs) eq_refl)
  \/ const_spec_disposition cs = VInvalid (ConstMissingInit (BN.const_spec_judgment bp cs) eq_refl)
  \/ (exists nn nv, const_spec_disposition cs = VInvalid (ResultCountMismatch cs eq_refl nn nv)).
Proof.
  unfold const_spec_disposition. destruct (Index.Refs.sp_shape cs) as [b nn nv|b].
  - destruct (Nat.eqb nn nv); [ left; reflexivity | right; right; exists nn, nv; reflexivity ].
  - destruct (projT2 (BN.cjr_row (BN.const_spec_judgment bp cs)));
      solve [ left; reflexivity | right; left; reflexivity ].
Qed.

(* §271 a binder head by spec flavor: const is noncallable, type/var are source boundaries *)
Definition binder_head_app (ar : Index.Refs.AppRef idx) (h : Names.OrdinaryIdentifier)
  (r0 : BN.ResolutionRef (BN.use_env bp (Index.Edges.ah_child (Index.Edges.app_head ar))) h) (o : BN.ObjectRef idx)
  (Hov : BN.resolution_object_view r0 = Some o) (b : BN.BinderRef idx)
  (Hbind : BN.resolution_object_view r0 = Some (BN.SourceObject (BN.DOBinder b)))
  : AppOutcome bp (Index.Refs.app_node ar).
Proof.
  refine (match Index.node_role (BN.binder_node b) as rr
            return Index.node_role (BN.binder_node b) = rr -> AppOutcome bp (Index.Refs.app_node ar) with
          | Index.Model.RSpecName Index.Model.ConstSpecF => fun _ => AInvalid (NotCallable ar eq_refl h r0 o Hov)
          | Index.Model.RSpecName Index.Model.VarSpecF => fun Hrole => AUnmet (ReqSourceValueApp ar eq_refl h r0 b Hbind Hrole)
          | Index.Model.RSpecName Index.Model.TypeSpecF => fun Hrole => AUnmet (ReqSourceTypeApp ar eq_refl h r0 b Hbind Hrole)
          | _ => fun Hrr => _
          end eq_refl);
    exfalso; pose proof (BN.binder_ok b) as Hbo; rewrite Hrr in Hbo; discriminate Hbo.
Defined.

(* §10 own_app is applicability-first: it takes the exact AppRef, so there is no non-application self-dependency *)
Definition own_app (ar : Index.Refs.AppRef idx) : AppOutcome bp (Index.Refs.app_node ar) :=
  let r := Index.Refs.app_node ar in let Hv := Index.Refs.app_ok ar in
  let hd := Index.Edges.ah_child (Index.Edges.app_head ar) in
      let arg_vec := map (fun x => Index.Edges.aa_child (projT2 x)) (Index.Edges.application_args ar) in
      match Index.node_view hd with
      | Index.Model.VName h =>
          let r0 := BN.resolve bp hd h in
          match BN.resolution_object_view r0 as ov return BN.resolution_object_view r0 = ov -> AppOutcome bp r with
          | Some o => fun Hov =>
              match o as o' return o = o' -> AppOutcome bp r with
              | BN.PredeclaredObject pn => fun Ho =>
              let Hpre := eq_trans Hov (f_equal (@Some _) Ho) in
              match pmeaning pn with
              | PMConvForm _ => match arg_vec with _ :: nil => AOK | _ => AInvalid (ConversionArity Hv pn (Datatypes.length (arg_vec))) end
              | PMComplex =>
                  (* application family = callability + arity only; the complex value is own_value's exact judgment *)
                  match arg_vec with
                  | _ :: _ :: nil => AOK
                  | _ => AInvalid (ComplexArity Hv (Datatypes.length (arg_vec)))
                  end
              | PMPrintln => AOK
              | PMValue _ => AInvalid (NotCallable ar eq_refl h r0 o Hov)
              | PMIota => AInvalid (InvalidApplicationIdentity ar eq_refl h r0 pn Hpre)
              | PMNil => AInvalid (InvalidApplicationIdentity ar eq_refl h r0 pn Hpre)
              | PMUnmodelled => AUnmet (ReqApplication ar eq_refl h r0 pn Hpre (arg_vec))
              end
          | BN.SourceObject org => fun Ho =>
              let Hsrc := eq_trans Hov (f_equal (@Some _) Ho) in
              match org as org' return org = org' -> AppOutcome bp r with
              | BN.DOBinder b => fun Horg =>
                  binder_head_app ar h r0 o Hov b
                    (eq_trans Hsrc (f_equal (fun z => @Some _ (BN.SourceObject z)) Horg))
              | BN.DOShort sn => fun Horg =>
                  AUnmet (ReqShortOriginApp ar eq_refl h r0 sn
                    (eq_trans Hsrc (f_equal (fun z => @Some _ (BN.SourceObject z)) Horg)))
              | BN.DOFunc f => fun Horg =>
                  (* the fixed main is zero-parameter: a zero-argument call is a known zero-result call *)
                  let Hfunc := eq_trans Hsrc (f_equal (fun z => @Some _ (BN.SourceObject z)) Horg) in
                  match arg_vec with
                  | nil => AOK
                  | args => AInvalid (MainArity ar eq_refl h r0 f Hfunc args (Datatypes.length args))
                  end
              end eq_refl
              end eq_refl
          | None => fun Hov =>
              match BN.resolution_redecl_root r0 as rv return BN.resolution_redecl_root r0 = rv -> AppOutcome bp r with
              | Some root => fun Hrr => ADependent (DepRedeclaredNameA ar eq_refl h r0 root Hrr)
              | None => fun Hrv => AInvalid (UnresolvedApplicationHead ar eq_refl h r0 Hov Hrv)
              end eq_refl
          end eq_refl
      | _ => AInvalid (NotCallableExpr Hv)
      end.

(* §8/§251 an argument of a non-folding application reads that application's own outcome: the dependency wrap *)
Definition arg_dependency (a : Index.Refs.AppRef idx) (i : nat) {r : Index.NodeRef idx}
  (Hpar : Index.node_parent r = Some (Index.Refs.app_node a)) (Hrole : Index.node_role r = Index.Model.RApplicationArg i)
  (fallback : ValueOutcome bp r) : ValueOutcome bp r :=
  match own_app a with
  | AOK => fallback
  | AInvalid c => VDependent (DepArgInvalid a i Hpar Hrole c)
  | AUnmet q => VDependent (DepArgUnmet a i Hpar Hrole q)
  | ADependent d => VDependent (DepArgDependent a i Hpar Hrole d)
  end.

(* a non-name application head reads its application's invalidity, else keeps its own outcome *)
Definition head_dependency (a : Index.Refs.AppRef idx) {r : Index.NodeRef idx}
  (Hpar : Index.node_parent r = Some (Index.Refs.app_node a)) (Hrole : Index.node_role r = Index.Model.RApplicationHead)
  (fallback : ValueOutcome bp r) : ValueOutcome bp r :=
  match own_app a with
  | AInvalid c => VDependent (DepHeadInvalid a Hpar Hrole c)
  | _ => fallback
  end.

(* the one default application: the default form of the final untyped constant, or the exact default overflow *)
Definition default_verdict (r : Index.NodeRef idx) (Hdef : is_value_default_node r = true) (c : TR.Constant)
  : ValueOutcome bp r :=
  match TR.default_constant c with Some rc => VOK rc | None => VInvalid (DefaultOverflow Hdef c) end.

(* the untyped constant at a const value edge: an explicit target owns it, else the declaration makes no default *)
Definition const_root_verdict (sp : Index.Refs.SpecRef idx Index.Model.ConstSpecF) (j : nat)
  (e : Index.Edges.SpecValueEdge sp j) (c : TR.Constant) (b : bool)
  (H : Index.Refs.shape_has_type Index.Model.ConstSpecF (Index.Refs.sp_shape sp) = b)
  : option (ValueOutcome bp (Index.Edges.sv_child e)) :=
  match b as b0 return Index.Refs.shape_has_type Index.Model.ConstSpecF (Index.Refs.sp_shape sp) = b0
                       -> option (ValueOutcome bp (Index.Edges.sv_child e)) with
  | true => fun Ht => Some (VUnmet (RTypedTargetConstant (ERConst sp j e eq_refl Ht) c))
  | false => fun Hf => Some (VUnmet (RConstNoDefault sp j e eq_refl Hf c))
  end H.

(* the value row of an exact UNTYPED constant by the path's top link: dflt is its one default, None an operand site *)
Definition untyped_verdict {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r)
  (dflt : ValueOutcome bp r) (wrap : bool) (c : TR.Constant) : option (ValueOutcome bp r) :=
  match path in Index.Edges.ExprUsePath s return ValueOutcome bp s -> option (ValueOutcome bp s) with
  | Index.Edges.EUPExprStmt _ _ => fun _ => None
  | Index.Edges.EUPConst sp j e => fun _ =>
      const_root_verdict sp j e c (Index.Refs.shape_has_type Index.Model.ConstSpecF (Index.Refs.sp_shape sp)) eq_refl
  | Index.Edges.EUPVarExplicit sp j e Ht => fun _ => Some (VUnmet (RTypedTargetConstant (ERVar sp j e eq_refl Ht) c))
  | Index.Edges.EUPVarImplicit _ _ _ _ => fun d => Some d
  | Index.Edges.EUPShort _ _ _ => fun d => Some d
  | Index.Edges.EUPUnary _ _ _ => fun _ => None
  | Index.Edges.EUPArg a i e sub => fun d =>
      match arg_use_action a with
      | UAFold => None
      | _ => Some (if wrap
                   then arg_dependency a i (Index.Edges.up_iparent_ok (Index.Edges.EUPArg a i e sub))
                          (Index.Edges.up_role_ok (Index.Edges.EUPArg a i e sub)) d
                   else d)
      end
  | Index.Edges.EUPHead a e sub => fun _ =>
      match own_app a with
      | AInvalid c0 => Some (VDependent (DepHeadInvalid a (Index.Edges.up_iparent_ok (Index.Edges.EUPHead a e sub))
                                          (Index.Edges.up_role_ok (Index.Edges.EUPHead a e sub)) c0))
      | _ => None
      end
  end dflt.

(* the value row of an exact TYPED constant: its own typed value everywhere, wrapped by a non-folding parent app *)
Definition typed_verdict {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r) (wrap : bool)
  (rc : TR.ResolvedConstant) : option (ValueOutcome bp r) :=
  match path in Index.Edges.ExprUsePath s return option (ValueOutcome bp s) with
  | Index.Edges.EUPArg a i e sub =>
      Some (if wrap
            then match arg_use_action a with
                 | UAFold => VOK rc
                 | _ => arg_dependency a i (Index.Edges.up_iparent_ok (Index.Edges.EUPArg a i e sub))
                          (Index.Edges.up_role_ok (Index.Edges.EUPArg a i e sub)) (VOK rc)
                 end
            else VOK rc)
  | Index.Edges.EUPHead a e sub =>
      Some (if wrap
            then head_dependency a (Index.Edges.up_iparent_ok (Index.Edges.EUPHead a e sub))
                   (Index.Edges.up_role_ok (Index.Edges.EUPHead a e sub)) (VOK rc)
            else VOK rc)
  | _ => Some (VOK rc)
  end.

(* the exact constant cells' rows; dflt is the site's one default application, failure cells the view arm's *)
Definition exact_verdict {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r)
  (dflt : TR.Constant -> ValueOutcome bp r) (wrap : bool) (cell : Intrinsic) : option (ValueOutcome bp r) :=
  match cell with
  | IUntyped c => untyped_verdict path (dflt c) wrap c
  | ITyped rc => typed_verdict path wrap rc
  | _ => Some VNonconst
  end.

(* §264 nil by its exact path: an explicit-type var value edge at the top, else the app-wrapped invalid identity *)
Definition nil_verdict {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r) (n : Names.OrdinaryIdentifier)
  (pn : Names.PredeclaredName) (r0 : BN.ResolutionRef (BN.use_env bp r) n)
  (Hpre : BN.resolution_object_view r0 = Some (BN.PredeclaredObject pn)) : ValueOutcome bp r :=
  match path in Index.Edges.ExprUsePath s
        return forall (r1 : BN.ResolutionRef (BN.use_env bp s) n),
               BN.resolution_object_view r1 = Some (BN.PredeclaredObject pn) -> ValueOutcome bp s with
  | Index.Edges.EUPVarExplicit sp j e Ht => fun r1 H1 => VUnmet (RTypedTargetIdentity r1 pn H1 sp j e eq_refl Ht)
  | Index.Edges.EUPArg a i e sub => fun r1 H1 =>
      match arg_use_action a with
      | UAFold => VInvalid (InvalidIdentity r1 pn H1)
      | _ => arg_dependency a i (Index.Edges.up_iparent_ok (Index.Edges.EUPArg a i e sub))
               (Index.Edges.up_role_ok (Index.Edges.EUPArg a i e sub)) (VInvalid (InvalidIdentity r1 pn H1))
      end
  | Index.Edges.EUPHead a e sub => fun r1 H1 =>
      head_dependency a (Index.Edges.up_iparent_ok (Index.Edges.EUPHead a e sub))
        (Index.Edges.up_role_ok (Index.Edges.EUPHead a e sub)) (VInvalid (InvalidIdentity r1 pn H1))
  | _ => fun r1 H1 => VInvalid (InvalidIdentity r1 pn H1)
  end r0 Hpre.

(* §262 iota by its exact path: the retained initializer ancestry, or the invalid identity outside every ConstSpec *)
Definition iota_verdict {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r) (n : Names.OrdinaryIdentifier)
  (pn : Names.PredeclaredName) (r0 : BN.ResolutionRef (BN.use_env bp r) n)
  (Hpre : BN.resolution_object_view r0 = Some (BN.PredeclaredObject pn))
  (o0 : option { sp : Index.Refs.SpecRef idx Index.Model.ConstSpecF & { j : nat & Index.Edges.SpecValueEdge sp j } })
  (H : path_const_root path = o0) : ValueOutcome bp r :=
  match o0 as o1 return path_const_root path = o1 -> ValueOutcome bp r with
  | Some (existT _ sp (existT _ j e)) => fun Hcr =>
      VUnmet (RInitializerIdentity r0 pn Hpre path sp j e (path_const_root_at path sp j e Hcr))
  | None => fun _ => VInvalid (InvalidIdentity r0 pn Hpre)
  end H.

(* §6 the value-of-a-name decision, factored over the resolution so convoy_at reduces it at the known resolved object *)
Definition own_value_res_body (r : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (r0 : BN.ResolutionRef (BN.use_env bp r) n) (path : Index.Edges.ExprUsePath r)
  (ov : option (BN.ObjectRef idx)) (H : BN.resolution_object_view r0 = ov) : option (ValueOutcome bp r) :=
  match ov as ov' return BN.resolution_object_view r0 = ov' -> option (ValueOutcome bp r) with
  | Some o => fun Hov =>
      match o as o' return o = o' -> option (ValueOutcome bp r) with
      | BN.PredeclaredObject pn => fun Ho =>
          let Hpre := eq_trans Hov (f_equal (@Some _) Ho) in
          match pmeaning pn with
          | PMValue c =>
              exact_verdict path
                (fun c' => match TR.default_constant c' with Some rc => VOK rc | None => VInvalid (InvalidIdentity r0 pn Hpre) end)
                true (IUntyped c)
          | PMIota => Some (iota_verdict path n pn r0 Hpre (path_const_root path) eq_refl)
          | PMNil => Some (nil_verdict path n pn r0 Hpre)
          | _ => Some (if is_app_head r then VNonconst else VInvalid (TypeAsValue r0 o Hov))
          end
      | BN.SourceObject org => fun Ho =>
          let Hsrc := eq_trans Hov (f_equal (@Some _) Ho) in
          match org as org' return org = org' -> option (ValueOutcome bp r) with
          | BN.DOBinder _ => fun _ => Some (VUnmet (ReqValueMeaning r0 org Hsrc))
          | BN.DOShort _ => fun _ => Some VNonconst
          | BN.DOFunc f => fun Horg =>
              Some (if is_app_head r then VNonconst
                    else VUnmet (ReqMainUse r0 f (eq_trans Hsrc (f_equal (fun z => @Some _ (BN.SourceObject z)) Horg))))
          end eq_refl
      end eq_refl
  | None => fun Hov =>
      match BN.resolution_redecl_root r0 as rv return BN.resolution_redecl_root r0 = rv -> option (ValueOutcome bp r) with
      | Some root => fun Hrr => Some (VDependent (DepRedeclaredNameV r0 root Hrr))
      | None => fun Hrv => Some (VInvalid (UnresolvedNameV r0 Hov Hrv))
      end eq_refl
  end H.
(* a conversion that did not convert: the exact TR category projects directly onto the exact cause or boundary *)
Definition conversion_failure_verdict {r : Index.NodeRef idx} (Hv : Index.node_view r = Index.Model.VApplication)
  (t : TR.TypeForm) (x : Index.NodeRef idx) {t' : TR.TypeForm} (res : TR.ConversionResult t') : ValueOutcome bp r :=
  match res with
  | TR.Converted _ => VNonconst
  | TR.Overflows _ => VInvalid (ConversionOverflow Hv t x)
  | TR.NotRepresentable _ => VInvalid (ConversionNotRepresentable Hv t x)
  | TR.InvalidForm _ => VInvalid (ConversionNotRepresentable Hv t x)
  | TR.Unmet _ => VUnmet (RConversionUnmet Hv t x)
  end.

(* the application value judgment over its exact path, factored over the head's resolution so convoy_at reduces it *)
Definition app_judgment (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx)
  (Hv : Index.node_view r = Index.Model.VApplication) (path : Index.Edges.ExprUsePath r) (h : Names.OrdinaryIdentifier)
  (ov : option (BN.ObjectRef idx)) (H : BN.resolution_object_view (BN.resolve bp r h) = ov) : option (ValueOutcome bp r) :=
  match ov as ov' return BN.resolution_object_view (BN.resolve bp r h) = ov' -> option (ValueOutcome bp r) with
  | Some o => fun _ =>
      match o with
      | BN.PredeclaredObject pn =>
      match pmeaning pn, map (fun x => Index.Edges.aa_child (projT2 x)) (Index.Edges.application_args (Index.Refs.mkAppRef r Hv)) with
      | PMConvForm t, x :: nil =>
          match mcell ctab r with
          | IConvFail _ res => Some (conversion_failure_verdict Hv t x res)
          | cell => exact_verdict path (default_verdict r (is_value_default_app r Hv)) false cell
          end
      | PMComplex, re :: im :: nil =>
          match mcell ctab r with
          | IComplexDefer _ _ => Some (VUnmet (ReqComplexType Hv))
          | IComplexMismatch _ _ => Some (VInvalid (ComplexMismatch Hv re im))
          | cell => exact_verdict path (default_verdict r (is_value_default_app r Hv)) false cell
          end
      | PMPrintln, _ => Some (if zero_result_consumed r then VInvalid (NoValueUsed Hv) else VNonconst)
      | _, _ => Some VNonconst
      end
      | BN.SourceObject (BN.DOFunc _) =>
          match Index.Edges.application_args (Index.Refs.mkAppRef r Hv) with
          | nil => Some (if zero_result_consumed r then VInvalid (NoValueUsed Hv) else VNonconst)
          | _ :: _ => Some VNonconst
          end
      | BN.SourceObject _ => Some VNonconst
      end
  | None => fun Hov =>
      match BN.resolution_redecl_root (BN.resolve bp r h) as rv
            return BN.resolution_redecl_root (BN.resolve bp r h) = rv -> option (ValueOutcome bp r) with
      | Some root => fun Hrr => Some (VDependent (DepRedeclaredNameV (BN.resolve bp r h) root Hrr))
      | None => fun Hrv => Some (VDependent (DepUnboundNameV (BN.resolve bp r h) Hov Hrv))
      end eq_refl
  end H.

(* the value judgment of an expression node over an explicit path: path and cell select the row, None an operand *)
Definition expr_judgment_body (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx)
  (path : Index.Edges.ExprUsePath r) (nv : Index.Model.NodeView) (Hnv : Index.node_view r = nv) : option (ValueOutcome bp r) :=
  match nv as v return Index.node_view r = v -> option (ValueOutcome bp r) with
  | Index.Model.VName n => fun _ =>
      let r0 := BN.resolve bp r n in
      own_value_res_body r n r0 path (BN.resolution_object_view r0) eq_refl
  | Index.Model.VLiteral l => fun Hv => exact_verdict path (default_verdict r (is_value_default_lit r l Hv)) true (mcell ctab r)
  | Index.Model.VUnary Syntax.UnaryMinus => fun Hv =>
      match mcell ctab r with
      | IUnaryMismatch _ => Some (VInvalid (UnaryMismatch Hv))
      | IUnaryOverflow _ => Some (VInvalid (UnaryMismatch Hv))
      | cell => exact_verdict path (default_verdict r (is_value_default_unary r Syntax.UnaryMinus Hv)) true cell
      end
  | Index.Model.VApplication => fun Hv =>
      match Index.node_view (Index.Edges.ah_child (Index.Edges.app_head (Index.Refs.mkAppRef r Hv))) with
      | Index.Model.VName h => app_judgment ctab r Hv path h (BN.resolution_object_view (BN.resolve bp r h)) eq_refl
      | _ => Some VNonconst
      end
  | _ => fun _ => None
  end Hnv.
Definition expr_judgment (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx)
  (path : Index.Edges.ExprUsePath r) : option (ValueOutcome bp r) :=
  expr_judgment_body ctab r path (Index.node_view r) eq_refl.
(* the judgment over a path reduces to its exact node_view branch — the convoy named so it is rewritable *)
Lemma expr_judgment_at (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx)
  (path : Index.Edges.ExprUsePath r) (v : Index.Model.NodeView) (H : Index.node_view r = v) :
  expr_judgment ctab r path = expr_judgment_body ctab r path v H.
Proof. unfold expr_judgment. destruct H. reflexivity. Qed.

(* the per-node value verdict: an expression node is judged over its canonical use path, None an operand-only site *)
Definition own_value_body (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx)
  (nv : Index.Model.NodeView) (Hnv : Index.node_view r = nv) : option (ValueOutcome bp r) :=
  match nv as v return Index.node_view r = v -> option (ValueOutcome bp r) with
  | Index.Model.VName n => fun Hv => expr_judgment ctab r (Index.Edges.use_path r (Index.Edges.is_expr_node_name n Hv))
  | Index.Model.VLiteral l => fun Hv => expr_judgment ctab r (Index.Edges.use_path r (Index.Edges.is_expr_node_lit l Hv))
  | Index.Model.VUnary u => fun Hv => expr_judgment ctab r (Index.Edges.use_path r (Index.Edges.is_expr_node_unary u Hv))
  | Index.Model.VApplication => fun Hv => expr_judgment ctab r (Index.Edges.use_path r (is_expr_node_app Hv))
  (* declaration outcomes live on the declaration subject (spec / short statement), never on the binder *)
  | Index.Model.VConstSpec sh => fun Hv => Some (const_spec_disposition (Index.Refs.mkSpecRef (fl := Index.Model.ConstSpecF) r sh Hv))
  | Index.Model.VVarSpec v => fun Hv => Some (VUnmet (ReqDeclMeaningV (is_value_decl_var r v Hv)))
  | Index.Model.VTypeSpec t => fun Hv => Some (VUnmet (ReqDeclMeaningV (is_value_decl_type r t Hv)))
  | _ => fun _ => Some VNonconst
  end Hnv.
(* the one per-node verdict: computed once, it is both the retained row (when Some) and the operand-only bit *)
Definition own_verdict (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx) : option (ValueOutcome bp r) :=
  own_value_body ctab r (Index.node_view r) eq_refl.
(* the verdict's value projection; an operand-only site projects the neutral VNonconst and retains no row *)
Definition value_of_verdict {r : Index.NodeRef idx} (v : option (ValueOutcome bp r)) : ValueOutcome bp r :=
  match v with Some o => o | None => VNonconst end.
Definition own_value (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx) : ValueOutcome bp r :=
  value_of_verdict (own_verdict ctab r).
(* an operand-only site: an exact constant consumed by a fold, a callee, or a discarding statement — no value row *)
Definition operand_only (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx) : bool :=
  match own_verdict ctab r with None => true | Some _ => false end.
(* a site that is not operand-only carries its projected value as its exact retained verdict *)
Lemma verdict_of_not_operand (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx)
  (Hoo : operand_only ctab r = false) : own_verdict ctab r = Some (own_value ctab r).
Proof. unfold operand_only in Hoo. unfold own_value, value_of_verdict. destruct (own_verdict ctab r); [ reflexivity | discriminate Hoo ]. Qed.
(* the verdict of a node reduces to its exact node_view branch — the convoy named so it is rewritable *)
Lemma own_verdict_at (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx)
  (v : Index.Model.NodeView) (H : Index.node_view r = v) : own_verdict ctab r = own_value_body ctab r v H.
Proof. unfold own_verdict. destruct H. reflexivity. Qed.
(* the value fact of a node is the projection of its exact node_view branch's verdict *)
Lemma own_value_at (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx)
  (v : Index.Model.NodeView) (H : Index.node_view r = v) : own_value ctab r = value_of_verdict (own_value_body ctab r v H).
Proof. unfold own_value. rewrite (own_verdict_at ctab r v H). reflexivity. Qed.
(* a name's verdict is exactly the resolution decision over its exact path *)
Lemma own_verdict_name (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx)
  (n : Names.OrdinaryIdentifier) (Hn : Index.node_view r = Index.Model.VName n) :
  own_verdict ctab r = own_value_res_body r n (BN.resolve bp r n)
                         (Index.Edges.use_path r (Index.Edges.is_expr_node_name n Hn))
                         (BN.resolution_object_view (BN.resolve bp r n)) eq_refl.
Proof.
  rewrite (own_verdict_at ctab r (Index.Model.VName n) Hn). cbn [own_value_body].
  rewrite (expr_judgment_at ctab r _ (Index.Model.VName n) Hn). reflexivity.
Qed.
(* §9.1 exact short-origin positive case: a name resolving to a DOShort source object is a retained nonconstant value *)
Lemma own_verdict_doshort (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx)
  (n : Names.OrdinaryIdentifier) (Hn : Index.node_view r = Index.Model.VName n) (sn : BN.ShortNewRef idx)
  (Hres : BN.resolution_object_view (BN.resolve bp r n) = Some (BN.SourceObject (BN.DOShort sn))) :
  own_verdict ctab r = Some VNonconst.
Proof.
  rewrite (own_verdict_name ctab r n Hn).
  rewrite (convoy_at (BN.resolution_object_view (BN.resolve bp r n))
                     (own_value_res_body r n (BN.resolve bp r n) (Index.Edges.use_path r (Index.Edges.is_expr_node_name n Hn)))
                     (Some (BN.SourceObject (BN.DOShort sn))) Hres).
  reflexivity.
Qed.
Lemma own_value_doshort (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx)
  (n : Names.OrdinaryIdentifier) (Hn : Index.node_view r = Index.Model.VName n) (sn : BN.ShortNewRef idx)
  (Hres : BN.resolution_object_view (BN.resolve bp r n) = Some (BN.SourceObject (BN.DOShort sn))) :
  own_value ctab r = VNonconst.
Proof. unfold own_value. rewrite (own_verdict_doshort ctab r n Hn sn Hres). reflexivity. Qed.
(* §9.2 no generic boundary: the exact same case cannot be the ReqValueMeaning source boundary *)
Lemma own_value_doshort_not_boundary (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx)
  (n : Names.OrdinaryIdentifier) (Hn : Index.node_view r = Index.Model.VName n) (sn : BN.ShortNewRef idx)
  (Hres : BN.resolution_object_view (BN.resolve bp r n) = Some (BN.SourceObject (BN.DOShort sn)))
  (n' : Names.OrdinaryIdentifier) (r' : BN.ResolutionRef (BN.use_env bp r) n') (org' : BN.DeclOrigin idx)
  (H' : BN.resolution_object_view r' = Some (BN.SourceObject org')) :
  own_value ctab r <> VUnmet (ReqValueMeaning r' org' H').
Proof. rewrite (own_value_doshort ctab r n Hn sn Hres). discriminate. Qed.
(* §9.3 discrimination: a DOBinder source object is exactly the ReqValueMeaning boundary, not the VNonconst case *)
Lemma own_value_dobinder_boundary (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx)
  (n : Names.OrdinaryIdentifier) (Hn : Index.node_view r = Index.Model.VName n) (b : BN.BinderRef idx)
  (Hres : BN.resolution_object_view (BN.resolve bp r n) = Some (BN.SourceObject (BN.DOBinder b))) :
  own_value ctab r = VUnmet (ReqValueMeaning (BN.resolve bp r n) (BN.DOBinder b) Hres).
Proof.
  unfold own_value. rewrite (own_verdict_name ctab r n Hn). cbn [value_of_verdict].
  rewrite (convoy_at (BN.resolution_object_view (BN.resolve bp r n))
                     (own_value_res_body r n (BN.resolve bp r n) (Index.Edges.use_path r (Index.Edges.is_expr_node_name n Hn)))
                     (Some (BN.SourceObject (BN.DOBinder b))) Hres).
  reflexivity.
Qed.

(* W1 the verdict of every live expression node is the judgment of its one canonical use path *)
Lemma judgment_from_path (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx)
  (Hr : Index.Edges.is_expr_node r = true) : own_verdict ctab r = expr_judgment ctab r (Index.Edges.use_path r Hr).
Proof.
  assert (Hgen : forall v (H : Index.node_view r = v),
            own_value_body ctab r v H = expr_judgment ctab r (Index.Edges.use_path r Hr)).
  { intros v H. unfold Index.Edges.is_expr_node in Hr.
    destruct v as [n|l|u| |nt|nb|nc|nvv|nts|nd|nst| |ntp|]; cbn [own_value_body];
      try (f_equal; f_equal; apply (Eqdep_dec.UIP_dec Bool.bool_dec));
      exfalso; rewrite H in Hr; cbn in Hr; discriminate Hr. }
  exact (Hgen (Index.node_view r) eq_refl).
Qed.
(* W3 the link sequence is the path's exact constructor order: the subject's own link first, arg and head distinct *)
Lemma path_links_order {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r) :
  match path with
  | Index.Edges.EUPUnary u _ sub => path_links path = LUnary u :: path_links sub
  | Index.Edges.EUPArg a i _ sub => path_links path = LArg a i :: path_links sub
  | Index.Edges.EUPHead a _ sub => path_links path = LHead a :: path_links sub
  | _ => path_links path = []
  end.
Proof. destruct path; reflexivity. Qed.
Lemma link_arg_not_head (a a' : Index.Refs.AppRef idx) (i : nat) : LArg a i <> LHead a'.
Proof. discriminate. Qed.
(* W4 iota outside every ConstSpec is exactly the invalid identity; inside, exactly the retained initializer ancestry *)
Lemma iota_verdict_outside {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r) (n : Names.OrdinaryIdentifier)
  (pn : Names.PredeclaredName) (r0 : BN.ResolutionRef (BN.use_env bp r) n)
  (Hpre : BN.resolution_object_view r0 = Some (BN.PredeclaredObject pn)) (Hn : path_const_root path = None) :
  iota_verdict path n pn r0 Hpre (path_const_root path) eq_refl = VInvalid (InvalidIdentity r0 pn Hpre).
Proof. rewrite (convoy_at (path_const_root path) (iota_verdict path n pn r0 Hpre) None Hn). reflexivity. Qed.
Lemma iota_verdict_inside {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r) (n : Names.OrdinaryIdentifier)
  (pn : Names.PredeclaredName) (r0 : BN.ResolutionRef (BN.use_env bp r) n)
  (Hpre : BN.resolution_object_view r0 = Some (BN.PredeclaredObject pn))
  (sp : Index.Refs.SpecRef idx Index.Model.ConstSpecF) (j : nat) (e : Index.Edges.SpecValueEdge sp j)
  (Hc : path_const_root path = Some (existT _ sp (existT _ j e))) :
  iota_verdict path n pn r0 Hpre (path_const_root path) eq_refl
  = VUnmet (RInitializerIdentity r0 pn Hpre path sp j e (path_const_root_at path sp j e Hc)).
Proof. rewrite (convoy_at (path_const_root path) (iota_verdict path n pn r0 Hpre) _ Hc). reflexivity. Qed.
(* the name judgment at an iota resolution is exactly the path's iota verdict, no other reading of the identity *)
Lemma res_body_iota (r : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) (r0 : BN.ResolutionRef (BN.use_env bp r) n)
  (path : Index.Edges.ExprUsePath r) (pn : Names.PredeclaredName)
  (H : BN.resolution_object_view r0 = Some (BN.PredeclaredObject pn)) (Hpm : pmeaning pn = PMIota) :
  exists Hpre, own_value_res_body r n r0 path (Some (BN.PredeclaredObject pn)) H
               = Some (iota_verdict path n pn r0 Hpre (path_const_root path) eq_refl).
Proof. eexists. cbn [own_value_res_body]. rewrite Hpm. reflexivity. Qed.
(* an argument's use is one of exactly two actions: folded into a conversion or complex head, else defaulted *)
Lemma arg_use_action_cases (a : Index.Refs.AppRef idx) : arg_use_action a = UAFold \/ arg_use_action a = UADefault.
Proof.
  unfold arg_use_action.
  destruct (Index.node_view (Index.Edges.ah_child (Index.Edges.app_head a))) as [h|l|u| |nt|nb|nc|nvv|nts|nd|nst| |ntp|];
    try (right; reflexivity).
  destruct (BN.resolution_object_view (BN.resolve bp (Index.Refs.app_node a) h)) as [[pn|org]|]; try (right; reflexivity).
  destruct (pmeaning pn); solve [ left; reflexivity | right; reflexivity ].
Qed.
(* W6 one action per path; the untyped constant is defaulted only under UADefault and kept exact under every other *)
Lemma untyped_verdict_by_action {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r)
  (dflt : ValueOutcome bp r) (wrap : bool) (c : TR.Constant) :
  match use_action path with
  | UADefault => exists v, untyped_verdict path dflt wrap c = Some v
      /\ (v = dflt \/ exists a i Hpar Hrole, v = arg_dependency a i Hpar Hrole dflt)
  | UAPreserve => exists sp j e Hs Hf, untyped_verdict path dflt wrap c = Some (VUnmet (RConstNoDefault sp j e Hs Hf c))
  | UAExplicitTarget => exists root, untyped_verdict path dflt wrap c = Some (VUnmet (RTypedTargetConstant root c))
  | UAFold => untyped_verdict path dflt wrap c = None
  | UADiscard => untyped_verdict path dflt wrap c = None
  | UACallee => untyped_verdict path dflt wrap c = None
      \/ exists d, untyped_verdict path dflt wrap c = Some (VDependent d)
  end.
Proof.
  destruct path as [es e | sp j e | sp j e Ht | sp j e Ht | st j e | u e sub | a i e sub | a e sub];
    cbn [use_action untyped_verdict].
  - reflexivity.
  - assert (Hs : Index.Refs.shape_has_type Index.Model.ConstSpecF (Index.Refs.sp_shape sp) = true
              \/ Index.Refs.shape_has_type Index.Model.ConstSpecF (Index.Refs.sp_shape sp) = false)
      by (destruct (Index.Refs.shape_has_type Index.Model.ConstSpecF (Index.Refs.sp_shape sp)); [ left | right ]; reflexivity).
    destruct Hs as [Hs | Hs].
    + replace (if Index.Refs.shape_has_type Index.Model.ConstSpecF (Index.Refs.sp_shape sp) then UAExplicitTarget else UAPreserve)
        with UAExplicitTarget by (rewrite Hs; reflexivity).
      rewrite (convoy_at _ (const_root_verdict sp j e c) _ Hs). cbn [const_root_verdict]. eexists; reflexivity.
    + replace (if Index.Refs.shape_has_type Index.Model.ConstSpecF (Index.Refs.sp_shape sp) then UAExplicitTarget else UAPreserve)
        with UAPreserve by (rewrite Hs; reflexivity).
      rewrite (convoy_at _ (const_root_verdict sp j e c) _ Hs). cbn [const_root_verdict]. do 5 eexists; reflexivity.
  - eexists; reflexivity.
  - eexists; split; [ reflexivity | left; reflexivity ].
  - eexists; split; [ reflexivity | left; reflexivity ].
  - reflexivity.
  - destruct (arg_use_action_cases a) as [Hf | Hd]; (rewrite Hf || rewrite Hd).
    + reflexivity.
    + eexists; split; [ reflexivity | ]. destruct wrap; [ right; do 4 eexists; reflexivity | left; reflexivity ].
  - destruct (own_app a); [ left; reflexivity | right; eexists; reflexivity | left; reflexivity | left; reflexivity ].
Qed.
(* W6 a typed constant is never defaulted or re-converted: its row is its own value, or its parent's dependency *)
Lemma typed_verdict_exact {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r) (wrap : bool) (rc : TR.ResolvedConstant) :
  exists v, typed_verdict path wrap rc = Some v /\ (v = VOK rc \/ exists d, v = VDependent d).
Proof.
  destruct path as [es e | sp j e | sp j e Ht | sp j e Ht | st j e | u e sub | a i e sub | a e sub]; cbn [typed_verdict];
    try (eexists; split; [ reflexivity | left; reflexivity ]).
  - eexists; split; [ reflexivity | ]. destruct wrap; [ | left; reflexivity ].
    destruct (arg_use_action a); try (left; reflexivity);
      unfold arg_dependency; destruct (own_app a); solve [ left; reflexivity | right; eexists; reflexivity ].
  - eexists; split; [ reflexivity | ]. destruct wrap; [ | left; reflexivity ].
    unfold head_dependency; destruct (own_app a); solve [ left; reflexivity | right; eexists; reflexivity ].
Qed.
(* W7 a failed mandatory default of a known constant is exactly its DefaultOverflow: never VNonconst, never absent *)
Lemma default_verdict_failure (r : Index.NodeRef idx) (Hdef : is_value_default_node r = true) (c : TR.Constant)
  (Hn : TR.default_constant c = None) : default_verdict r Hdef c = VInvalid (DefaultOverflow Hdef c).
Proof. unfold default_verdict. rewrite Hn. reflexivity. Qed.
Lemma default_verdict_never_nonconst (r : Index.NodeRef idx) (Hdef : is_value_default_node r = true) (c : TR.Constant) :
  default_verdict r Hdef c <> VNonconst.
Proof. unfold default_verdict. destruct (TR.default_constant c); discriminate. Qed.
Lemma untyped_default_failure {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r)
  (Hdef : is_value_default_node r = true) (wrap : bool) (c : TR.Constant)
  (Ha : use_action path = UADefault) (Hn : TR.default_constant c = None) :
  exists v, untyped_verdict path (default_verdict r Hdef c) wrap c = Some v
            /\ (v = VInvalid (DefaultOverflow Hdef c) \/ exists d, v = VDependent d).
Proof.
  pose proof (untyped_verdict_by_action path (default_verdict r Hdef c) wrap c) as Hb. rewrite Ha in Hb.
  destruct Hb as [v [Hv Hcase]]. exists v. split; [ exact Hv | ].
  destruct Hcase as [Hd | [a [i [Hpar [Hrole Hd]]]]]; subst v.
  - left. apply default_verdict_failure. exact Hn.
  - unfold arg_dependency. destruct (own_app a);
      [ left; apply default_verdict_failure; exact Hn | right; eexists; reflexivity
      | right; eexists; reflexivity | right; eexists; reflexivity ].
Qed.
(* W9 the conversion projection is category-exact: overflow and invalid forms are causes, the absent rule a boundary *)
Lemma conversion_failure_exact {r : Index.NodeRef idx} (Hv : Index.node_view r = Index.Model.VApplication)
  (t : TR.TypeForm) (x : Index.NodeRef idx) (ci : TR.ConstantInfo) :
  conversion_failure_verdict Hv t x (@TR.Overflows t ci) = VInvalid (ConversionOverflow Hv t x)
  /\ conversion_failure_verdict Hv t x (@TR.NotRepresentable t ci) = VInvalid (ConversionNotRepresentable Hv t x)
  /\ conversion_failure_verdict Hv t x (@TR.InvalidForm t ci) = VInvalid (ConversionNotRepresentable Hv t x)
  /\ conversion_failure_verdict Hv t x (@TR.Unmet t ci) = VUnmet (RConversionUnmet Hv t x).
Proof. repeat split; reflexivity. Qed.
(* L9/L10 a conversion that did not convert projects its retained cell exactly: the row is the cell's own category *)
Lemma conversion_failure_row (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx)
  (Hv : Index.node_view r = Index.Model.VApplication) (h : Names.OrdinaryIdentifier)
  (Hh : Index.node_view (Index.Edges.ah_child (Index.Edges.app_head (Index.Refs.mkAppRef r Hv))) = Index.Model.VName h)
  (pn : Names.PredeclaredName)
  (Hres : BN.resolution_object_view (BN.resolve bp r h) = Some (BN.PredeclaredObject pn))
  (t : TR.TypeForm) (Hpm : pmeaning pn = PMConvForm t) (x : Index.NodeRef idx)
  (Hargs : map (fun y => Index.Edges.aa_child (projT2 y)) (Index.Edges.application_args (Index.Refs.mkAppRef r Hv)) = [x])
  (t' : TR.TypeForm) (res : TR.ConversionResult t') (Hcell : mcell ctab r = IConvFail t' res) :
  own_verdict ctab r = Some (conversion_failure_verdict Hv t x res).
Proof.
  rewrite (own_verdict_at ctab r _ Hv). cbn [own_value_body].
  rewrite (expr_judgment_at ctab r _ _ Hv). cbn [expr_judgment_body]. rewrite Hh.
  rewrite (convoy_at _ (app_judgment ctab r Hv (Index.Edges.use_path r (is_expr_node_app Hv)) h) _ Hres).
  cbn [app_judgment]. rewrite Hpm, Hargs, Hcell. reflexivity.
Qed.

(* the child-negativity bools an expr statement reads: whether its exact child value / application fact is negative *)
Definition value_neg_b {r' : Index.NodeRef idx} (ov : ValueOutcome bp r') : bool :=
  match ov with VInvalid _ | VUnmet _ | VDependent _ => true | _ => false end.
Definition app_neg_b {r' : Index.NodeRef idx} (oa : AppOutcome bp r') : bool :=
  match oa with AInvalid _ | AUnmet _ | ADependent _ => true | _ => false end.
(* §10 the child's application-negativity, guarded by its exact AppRef: a non-application child is never negative *)
Definition app_neg_body (e : Index.NodeRef idx) (v : Index.Model.NodeView) (H : Index.node_view e = v) : bool :=
  match v as v0 return Index.node_view e = v0 -> bool with
  | Index.Model.VApplication => fun He => app_neg_b (own_app (Index.Refs.mkAppRef e He))
  | _ => fun _ => false
  end H.
Definition app_neg_at (e : Index.NodeRef idx) : bool := app_neg_body e (Index.node_view e) eq_refl.

(* §8/§12 the application-child branch of an expr statement, named so its exact edge is convoy-reducible *)
Definition stmt_expr_app_branch (pr : Index.Refs.ExprStmtRef idx) (app_neg : bool)
  (He : Index.node_view (Index.Edges.ee_child (Index.Edges.exprstmt_expr pr)) = Index.Model.VApplication)
  : StmtOutcome bp (Index.Refs.exs_node pr) :=
  if app_neg
  then SDependent (DepChild (ExprStmtApplicationChild pr (Index.Refs.mkAppRef _ He) eq_refl eq_refl))
  else
    match Index.node_view (Index.Edges.ah_child (Index.Edges.app_head (Index.Refs.mkAppRef _ He))) with
    | Index.Model.VName h =>
        match BN.resolution_object_view (BN.resolve bp (Index.Refs.exs_node pr) h) with
        | Some o =>
            match o with
            | BN.PredeclaredObject Names.PPrintln => SOK
            | BN.SourceObject _ => SOK
            | _ => SInvalid (IllegalStatement (Index.Refs.exs_ok pr))
            end
        | None => SInvalid (IllegalStatement (Index.Refs.exs_ok pr))
        end
    | _ => SInvalid (IllegalStatement (Index.Refs.exs_ok pr))
    end.
(* the node_view convoy of an expr statement, named so convoy_at reduces it: application child, else illegal *)
Definition stmt_expr_body (pr : Index.Refs.ExprStmtRef idx) (app_neg : bool) (ve : Index.Model.NodeView)
  (H : Index.node_view (Index.Edges.ee_child (Index.Edges.exprstmt_expr pr)) = ve)
  : StmtOutcome bp (Index.Refs.exs_node pr) :=
  match ve as ve0 return Index.node_view (Index.Edges.ee_child (Index.Edges.exprstmt_expr pr)) = ve0
    -> StmtOutcome bp (Index.Refs.exs_node pr) with
  | Index.Model.VApplication => fun He => stmt_expr_app_branch pr app_neg He
  | _ => fun _ => SInvalid (IllegalStatement (Index.Refs.exs_ok pr))
  end H.
(* §8/§12 an expr statement over its exact ExprStmtRef: a negative value/application child retained as the exact edge *)
Definition own_stmt_expr (pr : Index.Refs.ExprStmtRef idx) (val_neg app_neg : bool)
  : StmtOutcome bp (Index.Refs.exs_node pr) :=
  if val_neg
  then SDependent (DepChild (ExprStmtValueChild pr eq_refl))
  else stmt_expr_body pr app_neg (Index.node_view (Index.Edges.ee_child (Index.Edges.exprstmt_expr pr))) eq_refl.

(* the represented but unmodelled predeclared types: real Go types with no current C4 TypeForm *)
Definition is_unmodeled_type (pn : Names.PredeclaredName) : bool :=
  match pn with Names.PUintptr | Names.PAny | Names.PComparable | Names.PError => true | _ => false end.

(* §10 own_type resolves the exact named-type name (view proof, no self-dep): its form, else a boundary/invalid *)
Definition own_type (r : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (H : Index.node_view r = Index.Model.VTypeExpr (Syntax.NamedType n)) : TypeUseOutcome bp r :=
  let r0 := BN.resolve bp r n in
      match BN.resolution_object_view r0 as ov return BN.resolution_object_view r0 = ov -> TypeUseOutcome bp r with
      | Some o => fun Hov =>
          match o with
          | BN.PredeclaredObject pn =>
              match TR.predeclared_meaning pn with
              | TR.NMConversionForm t => TOK t
              | _ => if is_unmodeled_type pn
                     then TUnmet (ReqTypeMeaning r0 o Hov)
                     else TInvalid (NotAType r0 o Hov)
              end
          | BN.SourceObject (BN.DOBinder _) => TUnmet (ReqTypeMeaning r0 o Hov)
          | BN.SourceObject (BN.DOShort _) => TUnmet (ReqTypeMeaning r0 o Hov)
          | BN.SourceObject (BN.DOFunc _) => TInvalid (NotAType r0 o Hov)
          end
      | None => fun Hov =>
          match BN.resolution_redecl_root r0 as rv return BN.resolution_redecl_root r0 = rv -> TypeUseOutcome bp r with
          | Some root => fun Hrr => TDependent (DepRedeclaredNameT r0 root Hrr)
          | None => fun Hrv => TInvalid (UnresolvedNameT r0 Hov Hrv)
          end eq_refl
      end eq_refl.

End OverPhase.

(* one applicability-first fact per applicable family; an application carries disjoint callability and value facts *)
Inductive OccFact {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) : Type :=
| OFValue : forall r : Index.NodeRef idx, ValueOutcome bp r -> OccFact bp
| OFApp   : forall r : Index.NodeRef idx, AppOutcome bp r -> OccFact bp
| OFStmt  : forall r : Index.NodeRef idx, StmtOutcome bp r -> OccFact bp
| OFType  : forall r : Index.NodeRef idx, TypeUseOutcome bp r -> OccFact bp.
Arguments OccFact {p idx s bd} bp.
Arguments OFValue {p idx s bd bp} _ _. Arguments OFApp {p idx s bd bp} _ _.
Arguments OFStmt {p idx s bd bp} _ _. Arguments OFType {p idx s bd bp} _ _.

(* proofs that a node is an application are unique — deciding only VApplication = y (no full NodeView eq_dec) *)
Lemma nodeview_app_dec (y : Index.Model.NodeView) : Index.Model.VApplication = y \/ Index.Model.VApplication <> y.
Proof. destruct y; try (right; discriminate). left; reflexivity. Qed.
Lemma app_proof_irrel {p} {idx : Index.ProgramIndex p} (e : Index.NodeRef idx)
  (H1 H2 : Index.node_view e = Index.Model.VApplication) : H1 = H2.
Proof.
  pose proof (Eqdep_dec.eq_proofs_unicity_on nodeview_app_dec (eq_sym H1) (eq_sym H2)) as E.
  rewrite <- (eq_sym_involutive H1), <- (eq_sym_involutive H2), E. reflexivity.
Qed.
(* decidable node identity from the boolean equality, so a same-site outcome equality is inj_pair2-extractable *)
Lemma noderef_eq_dec {p} {idx : Index.ProgramIndex p} (x y : Index.NodeRef idx) : {x = y} + {x <> y}.
Proof.
  destruct (BN.noderef_eqb x y) eqn:E; [ left | right ].
  - apply BN.noderef_eqb_spec. exact E.
  - intro Heq. subst y. rewrite (proj2 (BN.noderef_eqb_spec x x) eq_refl) in E. discriminate.
Qed.

Section Retain.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} (bp : BN.BindingPhase s bd).

(* §11/§10 the single application fact of a node, shared by neg_map and occ_facts_va so the AppRef proof is one term *)
Definition app_fact_body (r : Index.NodeRef idx) (v : Index.Model.NodeView) (H : Index.node_view r = v) : list (OccFact bp) :=
  match v as v0 return Index.node_view r = v0 -> list (OccFact bp) with
  | Index.Model.VApplication => fun H0 => [OFApp r (own_app bp (Index.Refs.mkAppRef r H0))]
  | _ => fun _ => []
  end H.
Definition app_fact_app (r : Index.NodeRef idx) : list (OccFact bp) := app_fact_body r (Index.node_view r) eq_refl.
Lemma app_fact_app_at (r : Index.NodeRef idx) (H : Index.node_view r = Index.Model.VApplication) :
  app_fact_app r = [OFApp r (own_app bp (Index.Refs.mkAppRef r H))].
Proof. exact (convoy_at (Index.node_view r) (app_fact_body r) Index.Model.VApplication H). Qed.
Lemma app_fact_app_none (r : Index.NodeRef idx) (v : Index.Model.NodeView) (H : Index.node_view r = v)
  (Hne : v <> Index.Model.VApplication) : app_fact_app r = [].
Proof.
  unfold app_fact_app. rewrite (convoy_at (Index.node_view r) (app_fact_body r) v H). unfold app_fact_body.
  destruct v; try reflexivity; exfalso; apply Hne; reflexivity.
Qed.
Lemma app_neg_at_app (e : Index.NodeRef idx) (He : Index.node_view e = Index.Model.VApplication) :
  app_neg_at bp e = app_neg_b bp (own_app bp (Index.Refs.mkAppRef e He)).
Proof. exact (convoy_at (Index.node_view e) (app_neg_body bp e) Index.Model.VApplication He). Qed.
Lemma app_neg_at_off (e : Index.NodeRef idx) (v : Index.Model.NodeView) (H : Index.node_view e = v)
  (Hne : v <> Index.Model.VApplication) : app_neg_at bp e = false.
Proof.
  unfold app_neg_at. rewrite (convoy_at (Index.node_view e) (app_neg_body bp e) v H). unfold app_neg_body.
  destruct v; try reflexivity; exfalso; apply Hne; reflexivity.
Qed.
(* §10 the type-use fact of a node, keyed to its exact named-type name, one term for the canonical builder *)
Definition type_fact_body (r : Index.NodeRef idx) (v : Index.Model.NodeView) (H : Index.node_view r = v) : list (OccFact bp) :=
  match v as v0 return Index.node_view r = v0 -> list (OccFact bp) with
  | Index.Model.VTypeExpr (Syntax.NamedType n) => fun H0 => [OFType r (own_type bp r n H0)]
  | _ => fun _ => []
  end H.
Definition type_fact (r : Index.NodeRef idx) : list (OccFact bp) := type_fact_body r (Index.node_view r) eq_refl.
Lemma type_fact_at (r : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (H : Index.node_view r = Index.Model.VTypeExpr (Syntax.NamedType n)) : type_fact r = [OFType r (own_type bp r n H)].
Proof. exact (convoy_at (Index.node_view r) (type_fact_body r) (Index.Model.VTypeExpr (Syntax.NamedType n)) H). Qed.
(* the map key faithfully names the node: same file + same key is the same node — proof-irrelevant membership *)
Lemma noderef_file_key_inj (a b : Index.NodeRef idx) :
  Index.nr_file a = Index.nr_file b -> Index.nr_key a = Index.nr_key b -> a = b.
Proof.
  destruct a as [fa ka Ha], b as [fb kb Hb]; cbn; intros Hf Hk; subst fb kb.
  f_equal. apply (UIP_dec Bool.bool_dec).
Qed.
(* §5 the child-read negativity cell — the small vm-safe projection a parent needs of a child, keyed once *)
Record NegCell : Type := mkNegCell { nc_val_neg : bool ; nc_app_neg : bool ; nc_val_nonconst : bool }.
(* the one-per-node cell: value fields skip name heads, the nonconst bit reads the retained verdict (no operand) *)
Definition neg_cell_of (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx) : NegCell :=
  mkNegCell
    (if is_name_head r then false else value_neg_b bp (own_value bp ctab r))
    (app_neg_at bp r)
    (if is_name_head r then false else match own_verdict bp ctab r with Some VNonconst => true | _ => false end).
Definition neg_map_step (ctab : Collections.NodeMap.t Intrinsic) (m : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) : Collections.NodeMap.t NegCell :=
  Collections.NodeMap.add (Index.nr_key r) (neg_cell_of ctab r) m.
(* §5 the ephemeral negativity carrier: one cell per node, keyed for a constant-event child read, no growing scan *)
Definition neg_map (ctab : Collections.NodeMap.t Intrinsic) (nodes : list (Index.NodeRef idx)) : Collections.NodeMap.t NegCell :=
  fold_left (neg_map_step ctab) nodes (Collections.NodeMap.empty NegCell).
(* a key no node in the pass carries reads straight through the fold to the accumulator — gso closure *)
Lemma neg_map_skip (ctab : Collections.NodeMap.t Intrinsic) (k : positive)
  (nodes : list (Index.NodeRef idx)) (acc : Collections.NodeMap.t NegCell) :
  (forall r, In r nodes -> Index.nr_key r <> k) ->
  Collections.NodeMap.find k (fold_left (neg_map_step ctab) nodes acc) = Collections.NodeMap.find k acc.
Proof.
  revert acc; induction nodes as [|n rest IH]; intros acc Hne; [ reflexivity | ].
  cbn [fold_left]. rewrite IH by (intros r Hr; exact (Hne r (or_intror Hr))).
  unfold neg_map_step. apply Collections.NodeMap.gso, not_eq_sym, (Hne n (or_introl eq_refl)).
Qed.
(* §5 the cell-read law: the carrier reads back each node's exact once-computed cell — a constant-event lookup *)
Lemma neg_map_at (ctab : Collections.NodeMap.t Intrinsic) (e : Index.NodeRef idx)
  (nodes : list (Index.NodeRef idx)) :
  In e nodes -> NoDup nodes ->
  (forall a b, In a nodes -> In b nodes -> Index.nr_key a = Index.nr_key b -> a = b) ->
  Collections.NodeMap.find (Index.nr_key e) (neg_map ctab nodes) = Some (neg_cell_of ctab e).
Proof.
  intros Hin Hnd Hkinj. unfold neg_map.
  remember (Collections.NodeMap.empty NegCell) as acc0 eqn:Ha0. clear Ha0.
  revert acc0 e Hin Hnd Hkinj. induction nodes as [|n rest IH]; intros acc e Hin Hnd Hkinj.
  - inversion Hin.
  - inversion Hnd as [|? ? Hnn Hnd']; subst. cbn [fold_left]. destruct Hin as [Heq | Hin'].
    + subst n. rewrite neg_map_skip.
      * unfold neg_map_step. apply Collections.NodeMap.gss.
      * intros r Hr Hk. apply Hnn. rewrite <- (Hkinj r e (or_intror Hr) (or_introl eq_refl) Hk). exact Hr.
    + apply (IH (neg_map_step ctab acc n) e Hin' Hnd').
      intros a b Ha Hb Hk. exact (Hkinj a b (or_intror Ha) (or_intror Hb) Hk).
Qed.

(* §10 the exact fact-row retention policy: which views retain a Value occurrence fact — not a value-expression claim *)
Definition retains_value_fact_view (v : Index.Model.NodeView) : bool :=
  match v with
  | Index.Model.VName _ | Index.Model.VLiteral _ | Index.Model.VUnary _ | Index.Model.VApplication
  | Index.Model.VConstSpec _ | Index.Model.VVarSpec _ | Index.Model.VTypeSpec _ => true
  | _ => false
  end.
Definition retains_value_fact (site : Index.NodeRef idx) : bool := retains_value_fact_view (Index.node_view site).
Definition va_value_negative (va : Collections.NodeMap.t NegCell) (e : Index.NodeRef idx) : bool :=
  match Collections.NodeMap.find (Index.nr_key e) va with Some c => nc_val_neg c | None => false end.
Definition va_app_negative (va : Collections.NodeMap.t NegCell) (e : Index.NodeRef idx) : bool :=
  match Collections.NodeMap.find (Index.nr_key e) va with Some c => nc_app_neg c | None => false end.
(* the child-first expr-statement driver: read the child's value/app negativity from va, then own_stmt_expr *)
Definition expr_sx_va (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx)
  (Hv : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr) : StmtOutcome bp r :=
  let e := Index.Edges.ee_child (Index.Edges.exprstmt_expr (Index.Refs.mkExprStmtRef r Hv)) in
  own_stmt_expr bp (Index.Refs.mkExprStmtRef r Hv) (va_value_negative va e) (va_app_negative va e).
(* the child-first read that a node's value is nonconstant AND its Value fact is retained by policy at that site *)
Definition va_value_nonconst (va : Collections.NodeMap.t NegCell) (e : Index.NodeRef idx) : bool :=
  retains_value_fact e &&
  match Collections.NodeMap.find (Index.nr_key e) va with Some c => nc_val_nonconst c | None => false end.
(* find returns the FIRST match: it splits its list at the match with every earlier element failing the test *)
Lemma find_prefix_false {A} (f : A -> bool) (l : list A) (x : A) :
  find f l = Some x -> exists l1 l2, l = l1 ++ x :: l2 /\ forallb (fun y => negb (f y)) l1 = true /\ f x = true.
Proof.
  induction l as [|a l IH]; cbn; [ discriminate | ]. destruct (f a) eqn:Ha; intro H.
  - injection H as H; subst. exists nil, l. split; [ reflexivity | split; [ reflexivity | exact Ha ] ].
  - destruct (IH H) as [l1 [l2 [Hl [Hf Hx]]]]. exists (a :: l1), l2.
    split; [ cbn; f_equal; exact Hl | split; [ cbn; rewrite Ha; exact Hf | exact Hx ] ].
Qed.
(* the first source-ordered short RHS whose exact child value is nonconstant — its value meaning is not yet known *)
Definition find_rhs_vnonconst (va : Collections.NodeMap.t NegCell) (st : Index.Refs.ShortStmtRef idx)
  : option { j : nat & Index.Edges.ShortRhsEdge st j } :=
  find (fun sig => va_value_nonconst va (Index.Edges.sr_child (projT2 sig))) (Index.Edges.short_rhs_edges st).
(* §19 RHS-meaning firstness: the selected nonconstant RHS is the first — every earlier RHS child is not VNonconst *)
Lemma find_rhs_vnonconst_first (va : Collections.NodeMap.t NegCell) (st : Index.Refs.ShortStmtRef idx)
  (j : nat) (edge : Index.Edges.ShortRhsEdge st j) :
  find_rhs_vnonconst va st = Some (existT _ j edge) ->
  exists l1 l2, Index.Edges.short_rhs_edges st = l1 ++ (existT _ j edge) :: l2
    /\ forallb (fun sig => negb (va_value_nonconst va (Index.Edges.sr_child (projT2 sig)))) l1 = true.
Proof.
  intro H. destruct (find_prefix_false _ _ _ H) as [l1 [l2 [Hl [Hf _]]]]. exists l1, l2. split; [ exact Hl | exact Hf ].
Qed.
(* the application-child branch at one RHS node, factored on the exact child view so a convoy step can invert it *)
Definition rhs_app_neg_at (va : Collections.NodeMap.t NegCell) (st : Index.Refs.ShortStmtRef idx) (j : nat)
  (edge : Index.Edges.ShortRhsEdge st j) (ve : Index.Model.NodeView)
  (He : Index.node_view (Index.Edges.sr_child edge) = ve) : option (StmtOutcome bp (Index.Refs.sh_node st)) :=
  match ve as ve0 return Index.node_view (Index.Edges.sr_child edge) = ve0 -> option (StmtOutcome bp (Index.Refs.sh_node st)) with
  | Index.Model.VApplication => fun H =>
      if va_app_negative va (Index.Edges.sr_child edge)
      then Some (SDependent (DepChild (ShortApplicationChild st j edge (Index.Refs.mkAppRef (Index.Edges.sr_child edge) H) eq_refl eq_refl)))
      else None
  | _ => fun _ => None
  end He.
(* the negative-child verdict at one exact RHS edge: value before application, or none *)
Definition rhs_neg_at (va : Collections.NodeMap.t NegCell) (st : Index.Refs.ShortStmtRef idx) (j : nat)
  (edge : Index.Edges.ShortRhsEdge st j) : option (StmtOutcome bp (Index.Refs.sh_node st)) :=
  if va_value_negative va (Index.Edges.sr_child edge)
  then Some (SDependent (DepChild (ShortValueChild st j edge eq_refl)))
  else rhs_app_neg_at va st j edge (Index.node_view (Index.Edges.sr_child edge)) eq_refl.
(* the first source-ordered negative short RHS, value before application, as its exact child edge *)
Definition short_rhs_neg (va : Collections.NodeMap.t NegCell) (st : Index.Refs.ShortStmtRef idx)
  : option (StmtOutcome bp (Index.Refs.sh_node st)) :=
  fold_right (fun sig acc => match sig with existT _ j edge =>
    match rhs_neg_at va st j edge with Some o => Some o | None => acc end end)
    None (Index.Edges.short_rhs_edges st).
(* §19 negative-RHS firstness: the selected negative RHS is the first — every earlier RHS edge is non-negative *)
Lemma short_rhs_neg_first (va : Collections.NodeMap.t NegCell) (st : Index.Refs.ShortStmtRef idx)
  (out : StmtOutcome bp (Index.Refs.sh_node st)) :
  short_rhs_neg va st = Some out ->
  exists l1 (sig : { j : nat & Index.Edges.ShortRhsEdge st j }) l2,
    Index.Edges.short_rhs_edges st = l1 ++ sig :: l2
    /\ (match sig with existT _ j edge => rhs_neg_at va st j edge end) = Some out
    /\ forallb (fun s => match s with existT _ j edge =>
         match rhs_neg_at va st j edge with Some _ => false | None => true end end) l1 = true.
Proof.
  unfold short_rhs_neg. induction (Index.Edges.short_rhs_edges st) as [|b l IH]; cbn; [ discriminate | ].
  destruct b as [j edge]. destruct (rhs_neg_at va st j edge) as [o|] eqn:Hb; intro H.
  - injection H as H; subst. exists nil, (existT _ j edge), l.
    split; [ reflexivity | split; [ exact Hb | reflexivity ] ].
  - destruct (IH H) as [l1 [sig [l2 [Hl [Hg Hf]]]]]. exists (existT _ j edge :: l1), sig, l2.
    split; [ cbn; f_equal; exact Hl | split; [ exact Hg | cbn; rewrite Hb; exact Hf ] ].
Qed.
(* inverting the application branch: it fires only at an application child that is application-negative *)
Lemma rhs_app_neg_at_inv (va : Collections.NodeMap.t NegCell) (st : Index.Refs.ShortStmtRef idx) (j : nat)
  (edge : Index.Edges.ShortRhsEdge st j) (ve : Index.Model.NodeView)
  (He : Index.node_view (Index.Edges.sr_child edge) = ve) (out : StmtOutcome bp (Index.Refs.sh_node st)) :
  rhs_app_neg_at va st j edge ve He = Some out ->
  exists (Hap : Index.node_view (Index.Edges.sr_child edge) = Index.Model.VApplication),
    out = SDependent (DepChild (ShortApplicationChild st j edge (Index.Refs.mkAppRef (Index.Edges.sr_child edge) Hap) eq_refl eq_refl))
    /\ va_app_negative va (Index.Edges.sr_child edge) = true.
Proof.
  unfold rhs_app_neg_at. revert He. destruct ve; intro He; try discriminate.
  destruct (va_app_negative va (Index.Edges.sr_child edge)); [ | discriminate ].
  intro Heq; injection Heq as Heq; subst out. exists He. split; reflexivity.
Qed.
(* inverting one RHS verdict: a fired negative names either a value-negative or an application-negative child *)
Lemma rhs_neg_at_inv (va : Collections.NodeMap.t NegCell) (st : Index.Refs.ShortStmtRef idx) (j : nat)
  (edge : Index.Edges.ShortRhsEdge st j) (out : StmtOutcome bp (Index.Refs.sh_node st)) :
  rhs_neg_at va st j edge = Some out ->
  (out = SDependent (DepChild (ShortValueChild st j edge eq_refl)) /\ va_value_negative va (Index.Edges.sr_child edge) = true)
  \/ (exists (Hap : Index.node_view (Index.Edges.sr_child edge) = Index.Model.VApplication),
        out = SDependent (DepChild (ShortApplicationChild st j edge (Index.Refs.mkAppRef (Index.Edges.sr_child edge) Hap) eq_refl eq_refl))
        /\ va_app_negative va (Index.Edges.sr_child edge) = true).
Proof.
  unfold rhs_neg_at. destruct (va_value_negative va (Index.Edges.sr_child edge)).
  - intro Heq; injection Heq as Heq; subst out. left. split; reflexivity.
  - intro Heq. right. exact (rhs_app_neg_at_inv va st j edge _ _ out Heq).
Qed.
(* inverting the fold: a fired first-negative RHS is exactly one exact source edge's negative verdict *)
Lemma short_rhs_neg_inv (va : Collections.NodeMap.t NegCell) (st : Index.Refs.ShortStmtRef idx)
  (out : StmtOutcome bp (Index.Refs.sh_node st)) :
  short_rhs_neg va st = Some out ->
  exists j (edge : Index.Edges.ShortRhsEdge st j), rhs_neg_at va st j edge = Some out.
Proof.
  unfold short_rhs_neg. induction (Index.Edges.short_rhs_edges st) as [|x l IH]; [ discriminate | ].
  destruct x as [j edge]. cbn. destruct (rhs_neg_at va st j edge) as [o|] eqn:Hr.
  - intro Heq; injection Heq as Heq; subst o. exists j, edge; exact Hr.
  - exact IH.
Qed.
(* a row that passes the new-binding test is exactly a New row; likewise the existing-variable test *)
Lemma is_new_row_ex (row : BN.ShortLeftDecisionData) : BN.is_new_row row = true -> exists n, row = BN.ShortNewData n.
Proof. destruct row as [|earlier|n|m1|m2|f1 f2]; cbn; intro H; try discriminate H. exists n; reflexivity. Qed.
Lemma is_existing_var_row_ex (row : BN.ShortLeftDecisionData) : BN.is_existing_var_row row = true -> exists m, row = BN.ShortExistingVariableData m.
Proof. destruct row as [|earlier|n|m1|m2|f1 f2]; cbn; intro H; try discriminate H. exists m1; reflexivity. Qed.
(* the collected New / existing-variable row refs each carry exactly that tag on their retained decision *)
Lemma short_new_rows_forall {st : Index.Refs.ShortStmtRef idx} (se : BN.ShortEventRef bp st) :
  Forall (fun x => exists n, BN.row_decision (projT2 x) = BN.ShortNewData n) (BN.short_rows_where se BN.is_new_row).
Proof.
  eapply Forall_impl; [ | exact (BN.short_rows_where_forall se BN.is_new_row) ].
  intros x Hx. exact (is_new_row_ex _ Hx).
Qed.
Lemma short_existing_var_rows_forall {st : Index.Refs.ShortStmtRef idx} (se : BN.ShortEventRef bp st) :
  Forall (fun x => exists m, BN.row_decision (projT2 x) = BN.ShortExistingVariableData m) (BN.short_rows_where se BN.is_existing_var_row).
Proof.
  eapply Forall_impl; [ | exact (BN.short_rows_where_forall se BN.is_existing_var_row) ].
  intros x Hx. exact (is_existing_var_row_ex _ Hx).
Qed.
(* the leftmost-duplicate precedence step: a named duplicate row is invalid, else the later precedence decides *)
Definition sdd_dup_branch (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (cont : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None -> StmtOutcome bp r)
  (dupn : option Names.OrdinaryIdentifier)
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = dupn)
  : StmtOutcome bp r :=
  match dupn as o
    return BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = o
      -> StmtOutcome bp r with
  | Some n => fun Hn => SInvalid (ShortDuplicate
      (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) n eq_refl Hn eq_refl)
  | None => fun Hn => cont Hn
  end Hdup.
Lemma sdd_dup_branch_dep_inv (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (cont : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None -> StmtOutcome bp r)
  (dupn : option Names.OrdinaryIdentifier)
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = dupn)
  (d : Dependency bp r StatementKind) :
  sdd_dup_branch r nn nv Hv cont dupn Hdup = SDependent d -> exists H, cont H = SDependent d.
Proof. unfold sdd_dup_branch. destruct dupn; cbn; intro Heq; [ discriminate Heq | exists Hdup; exact Heq ]. Qed.
(* the first-blocker step: nonvariable reuse is invalid, ambiguous depends, else later precedence decides *)
Definition sdd_blocker_branch (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (cont : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortNoBlocker -> StmtOutcome bp r)
  (blk : BN.ShortBlockerDecision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))
  (Hblk : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = blk)
  : StmtOutcome bp r :=
  match blk as b
    return BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = b -> StmtOutcome bp r with
  | BN.ShortNoBlocker => fun H => cont H
  | BN.ShortBlockNonvar i row m Hrow => fun _ =>
      SInvalid (ShortReusesNonVariable (Index.Refs.mkShortStmtRef r nn nv Hv) i row m Hrow eq_refl)
  | BN.ShortBlockAmbiguous i row a b Hrow => fun _ =>
      SDependent (DepShortAmbiguous (Index.Refs.mkShortStmtRef r nn nv Hv) i row a b Hrow eq_refl)
  end Hblk.
Lemma sdd_blocker_branch_dep_inv (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (cont : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortNoBlocker -> StmtOutcome bp r)
  (blk : BN.ShortBlockerDecision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))
  (Hblk : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = blk)
  (edge : ChildFactEdge r StatementKind) :
  sdd_blocker_branch r nn nv Hv cont blk Hblk = SDependent (DepChild edge) ->
  exists H, cont H = SDependent (DepChild edge).
Proof. unfold sdd_blocker_branch. destruct blk; cbn; intro Heq; [ exists Hblk; exact Heq | discriminate Heq | discriminate Heq ]. Qed.
(* peeling the duplicate layer to an unmet outcome: the duplicate is absent and the later precedence produced it *)
Lemma sdd_dup_branch_peel_unmet (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (cont : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None -> StmtOutcome bp r)
  (dupn : option Names.OrdinaryIdentifier)
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = dupn)
  (q : Requirement bp r StatementKind) :
  sdd_dup_branch r nn nv Hv cont dupn Hdup = SUnmet q ->
  BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None
  /\ exists H, cont H = SUnmet q.
Proof. unfold sdd_dup_branch. destruct dupn as [n|]; cbn; intro Heq; [ discriminate Heq | split; [ exact Hdup | exists Hdup; exact Heq ] ]. Qed.
(* peeling the blocker layer to an unmet outcome: no structural blocker fired and the later precedence produced it *)
Lemma sdd_blocker_branch_peel_unmet (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (cont : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortNoBlocker -> StmtOutcome bp r)
  (blk : BN.ShortBlockerDecision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))
  (Hblk : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = blk)
  (q : Requirement bp r StatementKind) :
  sdd_blocker_branch r nn nv Hv cont blk Hblk = SUnmet q ->
  BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortNoBlocker
  /\ exists H, cont H = SUnmet q.
Proof. unfold sdd_blocker_branch. destruct blk; cbn; intro Heq; [ split; [ exact Hblk | exists Hblk; exact Heq ] | discriminate Heq | discriminate Heq ]. Qed.
(* peeling the duplicate layer to a clean outcome: the duplicate is absent, so the later precedence produced it *)
Lemma sdd_dup_branch_ok_inv (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (cont : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None -> StmtOutcome bp r)
  (dupn : option Names.OrdinaryIdentifier)
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = dupn) :
  sdd_dup_branch r nn nv Hv cont dupn Hdup = SOK -> exists H, cont H = SOK.
Proof. unfold sdd_dup_branch. destruct dupn as [n|]; cbn; intro Heq; [ discriminate Heq | exists Hdup; exact Heq ]. Qed.
(* peeling the blocker layer to a clean outcome: no structural blocker fired, so the later precedence produced it *)
Lemma sdd_blocker_branch_ok_inv (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (cont : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortNoBlocker -> StmtOutcome bp r)
  (blk : BN.ShortBlockerDecision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))
  (Hblk : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = blk) :
  sdd_blocker_branch r nn nv Hv cont blk Hblk = SOK -> exists H, cont H = SOK.
Proof. unfold sdd_blocker_branch. destruct blk; cbn; intro Heq; [ exists Hblk; exact Heq | discriminate Heq | discriminate Heq ]. Qed.
(* the canonical short-declaration decision: the fixed precedence read off the exact retained rows and RHS facts *)
Definition short_decl_decision (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv)) : StmtOutcome bp r :=
  let st := Index.Refs.mkShortStmtRef r nn nv Hv in
  let se := BN.short_event bp st in
  sdd_dup_branch r nn nv Hv
    (fun Hdupnone =>
      match Nat.eq_dec (Index.Refs.sh_names st) (Index.Refs.sh_values st) with
      | right Hne => SInvalid (ShortCountMismatch st eq_refl Hne)
      | left Heq =>
        sdd_blocker_branch r nn nv Hv
          (fun Hblk =>
            match Bool.bool_dec (existsb BN.is_new_row (BN.se_rows se)) true with
            | right Hnt => SInvalid (ShortNoNewName st (Bool.not_true_is_false _ Hnt) eq_refl)
            | left Htrue =>
              match short_rhs_neg va st with
              | Some out => out
              | None => match find_rhs_vnonconst va st with
                | Some (existT _ j edge) => SUnmet (ReqShortRhsMeaning st j edge eq_refl)
                | None =>
                  match Bool.bool_dec (existsb BN.is_existing_var_row (BN.se_rows se)) true with
                  | left _ => SUnmet (ReqShortRedeclarationTypes st eq_refl)
                  | right _ => SUnmet (ReqShortUsage st eq_refl)
                  end
                end
              end
            end)
          (BN.short_blocker_decision se) eq_refl
      end)
    (BN.short_dup_decision_name (BN.short_duplicate_decision se)) eq_refl.
(* §19.3/§19.4 inverting a retained short child dependency: it names a value- or application-negative RHS child *)
Lemma short_decl_decision_dep_inv (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (edge : ChildFactEdge r StatementKind) :
  short_decl_decision va r nn nv Hv = SDependent (DepChild edge) ->
  (cfe_child_kind edge = ValueKind /\ va_value_negative va (cfe_child_site edge) = true)
  \/ (cfe_child_kind edge = ApplicationKind /\ va_app_negative va (cfe_child_site edge) = true
      /\ Index.node_view (cfe_child_site edge) = Index.Model.VApplication).
Proof.
  unfold short_decl_decision; cbv zeta. intro Heq.
  apply sdd_dup_branch_dep_inv in Heq. destruct Heq as [Hdupnone Heq]. cbv beta in Heq.
  destruct (Nat.eq_dec (Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv))
    (Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv))) as [Heqc | Hne]; [ | discriminate Heq ].
  apply sdd_blocker_branch_dep_inv in Heq. destruct Heq as [Hblk Heq]. cbv beta in Heq.
  destruct (Bool.bool_dec (existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true)
    as [Htrue | Hnt]; [ | discriminate Heq ].
  destruct (short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv)) as [out|] eqn:Hrhs.
  2:{ destruct (find_rhs_vnonconst va (Index.Refs.mkShortStmtRef r nn nv Hv)) as [[j e]|]; [ discriminate Heq | ].
      destruct (Bool.bool_dec (existsb BN.is_existing_var_row
        (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true); discriminate Heq. }
  destruct (short_rhs_neg_inv va (Index.Refs.mkShortStmtRef r nn nv Hv) out Hrhs) as [j [edge' Hr]].
  destruct (rhs_neg_at_inv va (Index.Refs.mkShortStmtRef r nn nv Hv) j edge' out Hr) as [[Hout Hvn] | [Hap [Hout Han]]].
  - rewrite Hout in Heq. injection Heq as Heq'. subst edge.
    cbn [cfe_child_kind cfe_child_site]. left. split; [ reflexivity | exact Hvn ].
  - rewrite Hout in Heq. injection Heq as Heq'. subst edge.
    cbn [cfe_child_kind cfe_child_site]. right. split; [ reflexivity | split; [ exact Han | exact Hap ] ].
Qed.
(* inverting the RHS-meaning branch: no earlier branch fired, no negative RHS, and a first nonconstant RHS exists *)
Lemma short_decl_decision_rhsmeaning_inv (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (st' : Index.Refs.ShortStmtRef idx) (j : nat) (edge : Index.Edges.ShortRhsEdge st' j)
  (Hs : r = Index.Refs.sh_node st') :
  short_decl_decision va r nn nv Hv = SUnmet (ReqShortRhsMeaning st' j edge Hs) ->
  short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv) = None
  /\ find_rhs_vnonconst va (Index.Refs.mkShortStmtRef r nn nv Hv) <> None.
Proof.
  unfold short_decl_decision; cbv zeta. intro Heq.
  apply sdd_dup_branch_peel_unmet in Heq. destruct Heq as [_ [Hdupn Heq]]. cbv beta in Heq.
  destruct (Nat.eq_dec (Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv))
    (Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv))) as [Heqc | Hne]; [ | discriminate Heq ].
  apply sdd_blocker_branch_peel_unmet in Heq. destruct Heq as [_ [Hblkn Heq]]. cbv beta in Heq.
  destruct (Bool.bool_dec (existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true)
    as [Htrue | Hnt]; [ | discriminate Heq ].
  destruct (short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv)) as [out|] eqn:Hrhs.
  { destruct (short_rhs_neg_inv va (Index.Refs.mkShortStmtRef r nn nv Hv) out Hrhs) as [jj [ee Hr]].
    destruct (rhs_neg_at_inv va (Index.Refs.mkShortStmtRef r nn nv Hv) jj ee out Hr) as [[Hout Hvn] | [Hap [Hout Han]]];
      rewrite Hout in Heq; discriminate Heq. }
  destruct (find_rhs_vnonconst va (Index.Refs.mkShortStmtRef r nn nv Hv)) as [[j0 edge0]|] eqn:Hfind.
  2:{ destruct (Bool.bool_dec (existsb BN.is_existing_var_row
        (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true); discriminate Heq. }
  split; [ reflexivity | discriminate ].
Qed.
(* forward reduction of the duplicate layer when no duplicate fired and the continuation ignores its proof *)
Lemma sdd_dup_branch_cont (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (cont : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None -> StmtOutcome bp r)
  (dupn : option Names.OrdinaryIdentifier)
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = dupn)
  (Hn : dupn = None)
  (H : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None)
  (Hg : forall H1 H2, cont H1 = cont H2) :
  sdd_dup_branch r nn nv Hv cont dupn Hdup = cont H.
Proof. unfold sdd_dup_branch. destruct dupn as [n|]; [ discriminate Hn | cbn; apply Hg ]. Qed.
(* forward reduction of the blocker layer when no structural blocker fired and the continuation ignores its proof *)
Lemma sdd_blocker_branch_cont (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (cont : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortNoBlocker -> StmtOutcome bp r)
  (blk : BN.ShortBlockerDecision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))
  (Hblk : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = blk)
  (Hn : blk = BN.ShortNoBlocker)
  (H : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortNoBlocker)
  (Hg : forall H1 H2, cont H1 = cont H2) :
  sdd_blocker_branch r nn nv Hv cont blk Hblk = cont H.
Proof. unfold sdd_blocker_branch. destruct blk; [ cbn; apply Hg | discriminate Hn | discriminate Hn ]. Qed.
(* the RHS-meaning branch soundness: the cleared guards, no negative RHS, and a first nonconstant RHS produce it *)
Lemma short_decl_decision_rhsmeaning_sound (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (j0 : nat) (edge0 : Index.Edges.ShortRhsEdge (Index.Refs.mkShortStmtRef r nn nv Hv) j0)
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None)
  (Hcount : Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv) = Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv))
  (Hblk : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortNoBlocker)
  (Hnew : existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = true)
  (Hneg : short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv) = None)
  (Hfind : find_rhs_vnonconst va (Index.Refs.mkShortStmtRef r nn nv Hv) = Some (existT _ j0 edge0)) :
  short_decl_decision va r nn nv Hv = SUnmet (ReqShortRhsMeaning (Index.Refs.mkShortStmtRef r nn nv Hv) j0 edge0 eq_refl).
Proof.
  unfold short_decl_decision; cbv zeta.
  rewrite (sdd_dup_branch_cont r nn nv Hv
    (fun Hdupnone => match Nat.eq_dec (Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv))
       (Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv)) with
     | right Hne => SInvalid (ShortCountMismatch (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl Hne)
     | left Heq => sdd_blocker_branch r nn nv Hv
         (fun Hblk0 => match Bool.bool_dec (existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true with
          | right Hnt => SInvalid (ShortNoNewName (Index.Refs.mkShortStmtRef r nn nv Hv) (Bool.not_true_is_false _ Hnt) eq_refl)
          | left Htrue => match short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv) with
            | Some out => out
            | None => match find_rhs_vnonconst va (Index.Refs.mkShortStmtRef r nn nv Hv) with
              | Some (existT _ j edge) => SUnmet (ReqShortRhsMeaning (Index.Refs.mkShortStmtRef r nn nv Hv) j edge eq_refl)
              | None => match Bool.bool_dec (existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true with
                | left _ => SUnmet (ReqShortRedeclarationTypes (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
                | right _ => SUnmet (ReqShortUsage (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
                end end end end)
         (BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) eq_refl
     end) _ eq_refl Hdup Hdup (fun _ _ => eq_refl)). cbv beta.
  destruct (Nat.eq_dec (Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv))
    (Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv))) as [Heqc | Hne]; [ | exfalso; exact (Hne Hcount) ].
  rewrite (sdd_blocker_branch_cont r nn nv Hv
    (fun Hblk0 => match Bool.bool_dec (existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true with
     | right Hnt => SInvalid (ShortNoNewName (Index.Refs.mkShortStmtRef r nn nv Hv) (Bool.not_true_is_false _ Hnt) eq_refl)
     | left Htrue => match short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv) with
       | Some out => out
       | None => match find_rhs_vnonconst va (Index.Refs.mkShortStmtRef r nn nv Hv) with
         | Some (existT _ j edge) => SUnmet (ReqShortRhsMeaning (Index.Refs.mkShortStmtRef r nn nv Hv) j edge eq_refl)
         | None => match Bool.bool_dec (existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true with
           | left _ => SUnmet (ReqShortRedeclarationTypes (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
           | right _ => SUnmet (ReqShortUsage (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
           end end end end) _ eq_refl Hblk Hblk (fun _ _ => eq_refl)). cbv beta.
  destruct (Bool.bool_dec (existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true)
    as [Htrue | Hnt]; [ | exfalso; exact (Hnt Hnew) ].
  rewrite Hneg, Hfind. reflexivity.
Qed.
(* the same soundness over an exact ShortStmtRef, so the decision names the caller's own statement, not a rebuild *)
Lemma short_decl_decision_rhsmeaning_sound_st (va : Collections.NodeMap.t NegCell) (st : Index.Refs.ShortStmtRef idx)
  (j0 : nat) (edge0 : Index.Edges.ShortRhsEdge st j0)
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp st)) = None)
  (Hcount : Index.Refs.sh_names st = Index.Refs.sh_values st)
  (Hblk : BN.short_blocker_decision (BN.short_event bp st) = BN.ShortNoBlocker)
  (Hnew : existsb BN.is_new_row (BN.se_rows (BN.short_event bp st)) = true)
  (Hneg : short_rhs_neg va st = None)
  (Hfind : find_rhs_vnonconst va st = Some (existT _ j0 edge0)) :
  short_decl_decision va (Index.Refs.sh_node st) (Index.Refs.sh_names st) (Index.Refs.sh_values st) (Index.Refs.sh_ok st)
  = SUnmet (ReqShortRhsMeaning st j0 edge0 eq_refl).
Proof. destruct st as [node names values ok]; apply short_decl_decision_rhsmeaning_sound; assumption. Qed.
(* the decision, past the cleared duplicate/count/blocker/no-new guards, is exactly its RHS-and-mixed tail *)
Lemma short_decl_decision_tail (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None)
  (Hcount : Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv) = Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv))
  (Hblk : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortNoBlocker)
  (Hnew : existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = true) :
  short_decl_decision va r nn nv Hv
  = match short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv) with
    | Some out => out
    | None => match find_rhs_vnonconst va (Index.Refs.mkShortStmtRef r nn nv Hv) with
      | Some (existT _ j edge) => SUnmet (ReqShortRhsMeaning (Index.Refs.mkShortStmtRef r nn nv Hv) j edge eq_refl)
      | None => match Bool.bool_dec (existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true with
        | left _ => SUnmet (ReqShortRedeclarationTypes (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
        | right _ => SUnmet (ReqShortUsage (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
        end end end.
Proof.
  unfold short_decl_decision; cbv zeta.
  rewrite (sdd_dup_branch_cont r nn nv Hv
    (fun Hdupnone => match Nat.eq_dec (Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv))
       (Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv)) with
     | right Hne => SInvalid (ShortCountMismatch (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl Hne)
     | left Heq => sdd_blocker_branch r nn nv Hv
         (fun Hblk0 => match Bool.bool_dec (existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true with
          | right Hnt => SInvalid (ShortNoNewName (Index.Refs.mkShortStmtRef r nn nv Hv) (Bool.not_true_is_false _ Hnt) eq_refl)
          | left Htrue => match short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv) with
            | Some out => out
            | None => match find_rhs_vnonconst va (Index.Refs.mkShortStmtRef r nn nv Hv) with
              | Some (existT _ j edge) => SUnmet (ReqShortRhsMeaning (Index.Refs.mkShortStmtRef r nn nv Hv) j edge eq_refl)
              | None => match Bool.bool_dec (existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true with
                | left _ => SUnmet (ReqShortRedeclarationTypes (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
                | right _ => SUnmet (ReqShortUsage (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
                end end end end)
         (BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) eq_refl
     end) _ eq_refl Hdup Hdup (fun _ _ => eq_refl)). cbv beta.
  destruct (Nat.eq_dec (Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv))
    (Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv))) as [Heqc | Hne]; [ | exfalso; exact (Hne Hcount) ].
  rewrite (sdd_blocker_branch_cont r nn nv Hv
    (fun Hblk0 => match Bool.bool_dec (existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true with
     | right Hnt => SInvalid (ShortNoNewName (Index.Refs.mkShortStmtRef r nn nv Hv) (Bool.not_true_is_false _ Hnt) eq_refl)
     | left Htrue => match short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv) with
       | Some out => out
       | None => match find_rhs_vnonconst va (Index.Refs.mkShortStmtRef r nn nv Hv) with
         | Some (existT _ j edge) => SUnmet (ReqShortRhsMeaning (Index.Refs.mkShortStmtRef r nn nv Hv) j edge eq_refl)
         | None => match Bool.bool_dec (existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true with
           | left _ => SUnmet (ReqShortRedeclarationTypes (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
           | right _ => SUnmet (ReqShortUsage (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
           end end end end) _ eq_refl Hblk Hblk (fun _ _ => eq_refl)). cbv beta.
  destruct (Bool.bool_dec (existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true)
    as [Htrue | Hnt]; [ | exfalso; exact (Hnt Hnew) ]. reflexivity.
Qed.
(* §18.8 usage soundness: all guards cleared, no negative or nonconstant RHS, and no existing-variable reuse *)
Lemma short_decl_decision_usage_sound_st (va : Collections.NodeMap.t NegCell) (st : Index.Refs.ShortStmtRef idx)
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp st)) = None)
  (Hcount : Index.Refs.sh_names st = Index.Refs.sh_values st)
  (Hblk : BN.short_blocker_decision (BN.short_event bp st) = BN.ShortNoBlocker)
  (Hnew : existsb BN.is_new_row (BN.se_rows (BN.short_event bp st)) = true)
  (Hneg : short_rhs_neg va st = None) (Hfind : find_rhs_vnonconst va st = None)
  (Hmix : existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp st)) = false) :
  short_decl_decision va (Index.Refs.sh_node st) (Index.Refs.sh_names st) (Index.Refs.sh_values st) (Index.Refs.sh_ok st)
  = SUnmet (ReqShortUsage st eq_refl).
Proof.
  destruct st as [node names values ok]; cbn [Index.Refs.sh_node Index.Refs.sh_names Index.Refs.sh_values Index.Refs.sh_ok].
  rewrite (short_decl_decision_tail va node names values ok Hdup Hcount Hblk Hnew), Hneg, Hfind.
  destruct (Bool.bool_dec (existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp _))) true) as [Ht | Hf];
    [ rewrite Hmix in Ht; discriminate Ht | reflexivity ].
Qed.
(* §18.7 mixed-redeclaration soundness: all guards cleared, no negative or nonconstant RHS, some existing variable *)
Lemma short_decl_decision_redecl_sound_st (va : Collections.NodeMap.t NegCell) (st : Index.Refs.ShortStmtRef idx)
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp st)) = None)
  (Hcount : Index.Refs.sh_names st = Index.Refs.sh_values st)
  (Hblk : BN.short_blocker_decision (BN.short_event bp st) = BN.ShortNoBlocker)
  (Hnew : existsb BN.is_new_row (BN.se_rows (BN.short_event bp st)) = true)
  (Hneg : short_rhs_neg va st = None) (Hfind : find_rhs_vnonconst va st = None)
  (Hmix : existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp st)) = true) :
  short_decl_decision va (Index.Refs.sh_node st) (Index.Refs.sh_names st) (Index.Refs.sh_values st) (Index.Refs.sh_ok st)
  = SUnmet (ReqShortRedeclarationTypes st eq_refl).
Proof.
  destruct st as [node names values ok]; cbn [Index.Refs.sh_node Index.Refs.sh_names Index.Refs.sh_values Index.Refs.sh_ok].
  rewrite (short_decl_decision_tail va node names values ok Hdup Hcount Hblk Hnew), Hneg, Hfind.
  destruct (Bool.bool_dec (existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp _))) true) as [Ht | Hf];
    [ reflexivity | exfalso; exact (Hf Hmix) ].
Qed.
(* every unmet short outcome sits past the cleared duplicate/count/blocker/no-new guards, with no negative RHS *)
Lemma short_decl_decision_unmet_guards (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv)) (q : Requirement bp r StatementKind) :
  short_decl_decision va r nn nv Hv = SUnmet q ->
  BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None
  /\ Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv) = Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv)
  /\ BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortNoBlocker
  /\ existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = true
  /\ short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv) = None.
Proof.
  unfold short_decl_decision; cbv zeta. intro Heq.
  apply sdd_dup_branch_peel_unmet in Heq. destruct Heq as [Hdup [Hd0 Heq]]. cbv beta in Heq.
  destruct (Nat.eq_dec (Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv))
    (Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv))) as [Hcount | Hne]; [ | discriminate Heq ].
  apply sdd_blocker_branch_peel_unmet in Heq. destruct Heq as [Hblk [Hb0 Heq]]. cbv beta in Heq.
  destruct (Bool.bool_dec (existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true)
    as [Hnew | Hnt]; [ | discriminate Heq ].
  destruct (short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv)) as [out|] eqn:Hrhs.
  { destruct (short_rhs_neg_inv va (Index.Refs.mkShortStmtRef r nn nv Hv) out Hrhs) as [jj [ee Hr]].
    destruct (rhs_neg_at_inv va (Index.Refs.mkShortStmtRef r nn nv Hv) jj ee out Hr) as [[Hout Hvn] | [Hap [Hout Han]]];
      rewrite Hout in Heq; discriminate Heq. }
  split; [ exact Hdup | split; [ exact Hcount | split; [ exact Hblk | split; [ exact Hnew | reflexivity ] ] ] ].
Qed.
(* the same unmet-guard inversion over an exact short statement ref, matching the case-ref construction hypotheses *)
Lemma short_decl_decision_unmet_guards_st (va : Collections.NodeMap.t NegCell) (st : Index.Refs.ShortStmtRef idx)
  {q : Requirement bp (Index.Refs.sh_node st) StatementKind} :
  short_decl_decision va (Index.Refs.sh_node st) (Index.Refs.sh_names st) (Index.Refs.sh_values st) (Index.Refs.sh_ok st)
  = SUnmet q ->
  BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp st)) = None
  /\ Index.Refs.sh_names st = Index.Refs.sh_values st
  /\ BN.short_blocker_decision (BN.short_event bp st) = BN.ShortNoBlocker
  /\ existsb BN.is_new_row (BN.se_rows (BN.short_event bp st)) = true
  /\ short_rhs_neg va st = None.
Proof.
  destruct st as [node names values ok]; cbn [Index.Refs.sh_node Index.Refs.sh_names Index.Refs.sh_values Index.Refs.sh_ok].
  apply short_decl_decision_unmet_guards.
Qed.
(* §18.8 usage completeness: the exact usage requirement implies every final guard, including no RHS meaning or mix *)
Lemma short_decl_decision_usage_complete (va : Collections.NodeMap.t NegCell) (st : Index.Refs.ShortStmtRef idx) :
  short_decl_decision va (Index.Refs.sh_node st) (Index.Refs.sh_names st) (Index.Refs.sh_values st) (Index.Refs.sh_ok st)
  = SUnmet (ReqShortUsage st eq_refl) ->
  BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp st)) = None
  /\ Index.Refs.sh_names st = Index.Refs.sh_values st
  /\ BN.short_blocker_decision (BN.short_event bp st) = BN.ShortNoBlocker
  /\ existsb BN.is_new_row (BN.se_rows (BN.short_event bp st)) = true
  /\ short_rhs_neg va st = None
  /\ find_rhs_vnonconst va st = None
  /\ existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp st)) = false.
Proof.
  intro Heq. pose proof (short_decl_decision_unmet_guards_st va st Heq) as Hg.
  revert Heq Hg. destruct st as [node names values ok]. intros Heq Hg.
  cbn [Index.Refs.sh_node Index.Refs.sh_names Index.Refs.sh_values Index.Refs.sh_ok] in Heq, Hg |- *.
  destruct Hg as [Hdup [Hcount [Hblk [Hnew Hneg]]]].
  rewrite (short_decl_decision_tail va node names values ok Hdup Hcount Hblk Hnew), Hneg in Heq.
  destruct (find_rhs_vnonconst va (Index.Refs.mkShortStmtRef node names values ok)) as [[j e]|] eqn:Hfind;
    [ discriminate Heq | ].
  destruct (Bool.bool_dec (existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp _))) true) as [Ht | Hf];
    [ discriminate Heq | ].
  repeat split; try assumption. apply Bool.not_true_is_false; exact Hf.
Qed.
(* §18.7 mixed completeness: the exact redeclaration-types requirement implies every guard, existing row present *)
Lemma short_decl_decision_redecl_complete (va : Collections.NodeMap.t NegCell) (st : Index.Refs.ShortStmtRef idx) :
  short_decl_decision va (Index.Refs.sh_node st) (Index.Refs.sh_names st) (Index.Refs.sh_values st) (Index.Refs.sh_ok st)
  = SUnmet (ReqShortRedeclarationTypes st eq_refl) ->
  BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp st)) = None
  /\ Index.Refs.sh_names st = Index.Refs.sh_values st
  /\ BN.short_blocker_decision (BN.short_event bp st) = BN.ShortNoBlocker
  /\ existsb BN.is_new_row (BN.se_rows (BN.short_event bp st)) = true
  /\ short_rhs_neg va st = None
  /\ find_rhs_vnonconst va st = None
  /\ existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp st)) = true.
Proof.
  intro Heq. pose proof (short_decl_decision_unmet_guards_st va st Heq) as Hg.
  revert Heq Hg. destruct st as [node names values ok]. intros Heq Hg.
  cbn [Index.Refs.sh_node Index.Refs.sh_names Index.Refs.sh_values Index.Refs.sh_ok] in Heq, Hg |- *.
  destruct Hg as [Hdup [Hcount [Hblk [Hnew Hneg]]]].
  rewrite (short_decl_decision_tail va node names values ok Hdup Hcount Hblk Hnew), Hneg in Heq.
  destruct (find_rhs_vnonconst va (Index.Refs.mkShortStmtRef node names values ok)) as [[j e]|] eqn:Hfind;
    [ discriminate Heq | ].
  destruct (Bool.bool_dec (existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp _))) true) as [Ht | Hf];
    [ | discriminate Heq ].
  repeat split; assumption.
Qed.
(* §18.5 negative-RHS soundness: past the cleared guards, a present negative RHS is the decision verbatim *)
Lemma short_decl_decision_rhsneg_sound (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None)
  (Hcount : Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv) = Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv))
  (Hblk : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortNoBlocker)
  (Hnew : existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = true)
  (out : StmtOutcome bp r) (Hrhs : short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv) = Some out) :
  short_decl_decision va r nn nv Hv = out.
Proof.
  rewrite (short_decl_decision_tail va r nn nv Hv Hdup Hcount Hblk Hnew), Hrhs. reflexivity.
Qed.
(* the duplicate layer at a present duplicate name is exactly the duplicate invalid, ignoring the later precedence *)
Lemma sdd_dup_branch_some (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (cont : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None -> StmtOutcome bp r)
  (dupn : option Names.OrdinaryIdentifier)
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = dupn)
  (n : Names.OrdinaryIdentifier) (Hn : dupn = Some n) :
  exists H, sdd_dup_branch r nn nv Hv cont dupn Hdup
    = SInvalid (ShortDuplicate (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) n eq_refl H eq_refl).
Proof.
  destruct dupn as [n0|]; [ | discriminate Hn ]. injection Hn as Hn; subst n0.
  exists Hdup. unfold sdd_dup_branch. reflexivity.
Qed.
(* §18.1 duplicate soundness: a present duplicate name makes the decision exactly the duplicate invalid *)
Lemma short_decl_decision_dup_sound (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv)) (n : Names.OrdinaryIdentifier)
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = Some n) :
  exists H, short_decl_decision va r nn nv Hv
    = SInvalid (ShortDuplicate (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) n eq_refl H eq_refl).
Proof.
  unfold short_decl_decision; cbv zeta.
  exact (sdd_dup_branch_some r nn nv Hv _ _ eq_refl n Hdup).
Qed.
(* past the cleared duplicate the decision is exactly its count/blocker continuation, written once for §18.2-18.4 *)
Lemma short_decl_decision_dup_none (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None) :
  short_decl_decision va r nn nv Hv =
    match Nat.eq_dec (Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv))
      (Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv)) with
    | right Hne => SInvalid (ShortCountMismatch (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl Hne)
    | left Heq => sdd_blocker_branch r nn nv Hv
        (fun Hblk => match Bool.bool_dec (existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true with
         | right Hnt => SInvalid (ShortNoNewName (Index.Refs.mkShortStmtRef r nn nv Hv) (Bool.not_true_is_false _ Hnt) eq_refl)
         | left Htrue => match short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv) with
           | Some out => out
           | None => match find_rhs_vnonconst va (Index.Refs.mkShortStmtRef r nn nv Hv) with
             | Some (existT _ j edge) => SUnmet (ReqShortRhsMeaning (Index.Refs.mkShortStmtRef r nn nv Hv) j edge eq_refl)
             | None => match Bool.bool_dec (existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true with
               | left _ => SUnmet (ReqShortRedeclarationTypes (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
               | right _ => SUnmet (ReqShortUsage (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
               end end end end)
        (BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) eq_refl
    end.
Proof.
  unfold short_decl_decision; cbv zeta.
  rewrite (sdd_dup_branch_cont r nn nv Hv
    (fun Hdupnone => match Nat.eq_dec (Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv))
       (Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv)) with
     | right Hne => SInvalid (ShortCountMismatch (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl Hne)
     | left Heq => sdd_blocker_branch r nn nv Hv
         (fun Hblk => match Bool.bool_dec (existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true with
          | right Hnt => SInvalid (ShortNoNewName (Index.Refs.mkShortStmtRef r nn nv Hv) (Bool.not_true_is_false _ Hnt) eq_refl)
          | left Htrue => match short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv) with
            | Some out => out
            | None => match find_rhs_vnonconst va (Index.Refs.mkShortStmtRef r nn nv Hv) with
              | Some (existT _ j edge) => SUnmet (ReqShortRhsMeaning (Index.Refs.mkShortStmtRef r nn nv Hv) j edge eq_refl)
              | None => match Bool.bool_dec (existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true with
                | left _ => SUnmet (ReqShortRedeclarationTypes (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
                | right _ => SUnmet (ReqShortUsage (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
                end end end end)
         (BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) eq_refl
     end)
    (BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))))
    eq_refl Hdup Hdup (fun _ _ => eq_refl)). cbv beta. reflexivity.
Qed.
(* §18.2 count-mismatch soundness: no duplicate and unequal projected counts is exactly the count-mismatch invalid *)
Lemma short_decl_decision_count_sound (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None)
  (Hne : Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv) <> Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv)) :
  exists H, short_decl_decision va r nn nv Hv = SInvalid (ShortCountMismatch (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl H).
Proof.
  rewrite (short_decl_decision_dup_none va r nn nv Hv Hdup).
  destruct (Nat.eq_dec (Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv))
    (Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv))) as [Heq | Hne']; [ exfalso; exact (Hne Heq) | ].
  exists Hne'. reflexivity.
Qed.
(* the blocker layer at a present nonvariable reuse is exactly that invalid, ignoring the later precedence *)
Lemma sdd_blocker_branch_nonvar (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (cont : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortNoBlocker -> StmtOutcome bp r)
  (blk : BN.ShortBlockerDecision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))
  (Hblk : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = blk)
  (i : nat) (row : BN.ShortDecisionRowRef (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) i) (m : nat)
  (Hrow : BN.row_decision row = BN.ShortExistingNonVariableData m) (Hn : blk = BN.ShortBlockNonvar i row m Hrow) :
  sdd_blocker_branch r nn nv Hv cont blk Hblk
    = SInvalid (ShortReusesNonVariable (Index.Refs.mkShortStmtRef r nn nv Hv) i row m Hrow eq_refl).
Proof. revert Hblk. rewrite Hn. intro Hblk. cbn [sdd_blocker_branch]. reflexivity. Qed.
(* the blocker layer at a present ambiguous reuse is exactly that dependent, ignoring the later precedence *)
Lemma sdd_blocker_branch_ambiguous (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (cont : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortNoBlocker -> StmtOutcome bp r)
  (blk : BN.ShortBlockerDecision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))
  (Hblk : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = blk)
  (i : nat) (row : BN.ShortDecisionRowRef (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) i) (a b : nat)
  (Hrow : BN.row_decision row = BN.ShortAmbiguousData a b) (Hn : blk = BN.ShortBlockAmbiguous i row a b Hrow) :
  sdd_blocker_branch r nn nv Hv cont blk Hblk
    = SDependent (DepShortAmbiguous (Index.Refs.mkShortStmtRef r nn nv Hv) i row a b Hrow eq_refl).
Proof. revert Hblk. rewrite Hn. intro Hblk. cbn [sdd_blocker_branch]. reflexivity. Qed.
(* §18.3 blocker soundness: past no duplicate and equal counts, a nonvariable reuse is exactly that invalid *)
Lemma short_decl_decision_blocker_nonvar_sound (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None)
  (Hcount : Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv) = Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv))
  (i : nat) (row : BN.ShortDecisionRowRef (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) i) (m : nat)
  (Hrow : BN.row_decision row = BN.ShortExistingNonVariableData m)
  (Hblk : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortBlockNonvar i row m Hrow) :
  short_decl_decision va r nn nv Hv = SInvalid (ShortReusesNonVariable (Index.Refs.mkShortStmtRef r nn nv Hv) i row m Hrow eq_refl).
Proof.
  rewrite (short_decl_decision_dup_none va r nn nv Hv Hdup).
  destruct (Nat.eq_dec (Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv))
    (Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv))) as [Heq | Hne]; [ | exfalso; exact (Hne Hcount) ].
  exact (sdd_blocker_branch_nonvar r nn nv Hv _ _ eq_refl i row m Hrow Hblk).
Qed.
(* §18.3 blocker soundness: past no duplicate and equal counts, an ambiguous reuse is exactly that dependent *)
Lemma short_decl_decision_blocker_ambiguous_sound (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None)
  (Hcount : Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv) = Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv))
  (i : nat) (row : BN.ShortDecisionRowRef (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) i) (a b : nat)
  (Hrow : BN.row_decision row = BN.ShortAmbiguousData a b)
  (Hblk : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortBlockAmbiguous i row a b Hrow) :
  short_decl_decision va r nn nv Hv = SDependent (DepShortAmbiguous (Index.Refs.mkShortStmtRef r nn nv Hv) i row a b Hrow eq_refl).
Proof.
  rewrite (short_decl_decision_dup_none va r nn nv Hv Hdup).
  destruct (Nat.eq_dec (Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv))
    (Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv))) as [Heq | Hne]; [ | exfalso; exact (Hne Hcount) ].
  exact (sdd_blocker_branch_ambiguous r nn nv Hv _ _ eq_refl i row a b Hrow Hblk).
Qed.
(* past the cleared duplicate, equal counts and no structural blocker: the no-new-name guard and its later tail *)
Lemma short_decl_decision_blocker_none (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None)
  (Hcount : Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv) = Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv))
  (Hblk : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortNoBlocker) :
  short_decl_decision va r nn nv Hv =
    match Bool.bool_dec (existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true with
    | right Hnt => SInvalid (ShortNoNewName (Index.Refs.mkShortStmtRef r nn nv Hv) (Bool.not_true_is_false _ Hnt) eq_refl)
    | left Htrue => match short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv) with
      | Some out => out
      | None => match find_rhs_vnonconst va (Index.Refs.mkShortStmtRef r nn nv Hv) with
        | Some (existT _ j edge) => SUnmet (ReqShortRhsMeaning (Index.Refs.mkShortStmtRef r nn nv Hv) j edge eq_refl)
        | None => match Bool.bool_dec (existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true with
          | left _ => SUnmet (ReqShortRedeclarationTypes (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
          | right _ => SUnmet (ReqShortUsage (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
          end end end
    end.
Proof.
  rewrite (short_decl_decision_dup_none va r nn nv Hv Hdup).
  destruct (Nat.eq_dec (Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv))
    (Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv))) as [Heqc | Hne]; [ | exfalso; exact (Hne Hcount) ].
  rewrite (sdd_blocker_branch_cont r nn nv Hv
    (fun Hblk0 => match Bool.bool_dec (existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true with
     | right Hnt => SInvalid (ShortNoNewName (Index.Refs.mkShortStmtRef r nn nv Hv) (Bool.not_true_is_false _ Hnt) eq_refl)
     | left Htrue => match short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv) with
       | Some out => out
       | None => match find_rhs_vnonconst va (Index.Refs.mkShortStmtRef r nn nv Hv) with
         | Some (existT _ j edge) => SUnmet (ReqShortRhsMeaning (Index.Refs.mkShortStmtRef r nn nv Hv) j edge eq_refl)
         | None => match Bool.bool_dec (existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true with
           | left _ => SUnmet (ReqShortRedeclarationTypes (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
           | right _ => SUnmet (ReqShortUsage (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
           end end end end) _ eq_refl Hblk Hblk (fun _ _ => eq_refl)). cbv beta. reflexivity.
Qed.
(* §18.4 no-new soundness: past all earlier cleared branches, an empty new-name filter is exactly that invalid *)
Lemma short_decl_decision_nonew_sound (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None)
  (Hcount : Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv) = Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv))
  (Hblk : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortNoBlocker)
  (Hnew : existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = false) :
  short_decl_decision va r nn nv Hv
  = SInvalid (ShortNoNewName (Index.Refs.mkShortStmtRef r nn nv Hv) Hnew eq_refl).
Proof.
  rewrite (short_decl_decision_blocker_none va r nn nv Hv Hdup Hcount Hblk).
  destruct (Bool.bool_dec (existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true)
    as [Ht | Hnt]; [ rewrite Hnew in Ht; discriminate Ht | ].
  f_equal. f_equal. apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.
(* §18.4 no-new completeness: the exact no-new invalid retains the exact empty new-name filter certificate *)
Lemma short_decl_decision_nonew_complete (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (st : Index.Refs.ShortStmtRef idx)
  (P : existsb BN.is_new_row (BN.se_rows (BN.short_event bp st)) = false) (e : r = Index.Refs.sh_node st) :
  short_decl_decision va r nn nv Hv = SInvalid (ShortNoNewName st P e) ->
  existsb BN.is_new_row (BN.se_rows (BN.short_event bp st)) = false.
Proof. intros _. exact P. Qed.
(* §18.4 the exact no-new invalid is impossible whenever any exact New row is present at the same statement *)
Lemma short_decl_decision_nonew_impossible (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (st : Index.Refs.ShortStmtRef idx)
  (P : existsb BN.is_new_row (BN.se_rows (BN.short_event bp st)) = false) (e : r = Index.Refs.sh_node st) :
  short_decl_decision va r nn nv Hv = SInvalid (ShortNoNewName st P e) ->
  existsb BN.is_new_row (BN.se_rows (BN.short_event bp st)) = true -> False.
Proof. intros _ Ht. rewrite P in Ht. discriminate Ht. Qed.
(* the empty new-name filter is exactly the all-not-new configuration, so an all-blank statement is a no-new invalid *)
Lemma existsb_false_forallb_negb {A : Type} (f : A -> bool) (l : list A) :
  forallb (fun x => negb (f x)) l = true -> existsb f l = false.
Proof.
  induction l as [| x xs IH]; cbn; [ reflexivity | ].
  intro H. apply andb_prop in H as [Hx Hxs]. rewrite (IH Hxs), Bool.orb_false_r.
  destruct (f x); [ discriminate Hx | reflexivity ].
Qed.
(* §18.4 all-blank inclusion: every row non-New is exactly the empty filter, hence that no-new invalid *)
Lemma short_decl_decision_nonew_allblank (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None)
  (Hcount : Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv) = Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv))
  (Hblk : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortNoBlocker)
  (Hblank : forallb (fun row => negb (BN.is_new_row row)) (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = true) :
  short_decl_decision va r nn nv Hv
  = SInvalid (ShortNoNewName (Index.Refs.mkShortStmtRef r nn nv Hv) (existsb_false_forallb_negb _ _ Hblank) eq_refl).
Proof. exact (short_decl_decision_nonew_sound va r nn nv Hv Hdup Hcount Hblk (existsb_false_forallb_negb _ _ Hblank)). Qed.
(* the short-declaration decision never returns the clean SOK outcome: every branch is invalid, dependent or unmet *)
Lemma short_decl_decision_not_ok (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv)) :
  short_decl_decision va r nn nv Hv <> SOK.
Proof.
  unfold short_decl_decision; cbv zeta. intro Heq.
  apply sdd_dup_branch_ok_inv in Heq. destruct Heq as [Hd0 Heq]. cbv beta in Heq.
  destruct (Nat.eq_dec (Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv))
    (Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv))) as [Hcount | Hne]; [ | discriminate Heq ].
  apply sdd_blocker_branch_ok_inv in Heq. destruct Heq as [Hb0 Heq]. cbv beta in Heq.
  destruct (Bool.bool_dec (existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true)
    as [Hnew | Hnt]; [ | discriminate Heq ].
  destruct (short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv)) as [out|] eqn:Hrhs.
  - destruct (short_rhs_neg_inv va (Index.Refs.mkShortStmtRef r nn nv Hv) out Hrhs) as [jj [ee Hr]].
    destruct (rhs_neg_at_inv va (Index.Refs.mkShortStmtRef r nn nv Hv) jj ee out Hr) as [[Hout Hvn] | [Hap [Hout Han]]];
      rewrite Hout in Heq; discriminate Heq.
  - destruct (find_rhs_vnonconst va (Index.Refs.mkShortStmtRef r nn nv Hv)) as [[jj ee]|]; [ discriminate Heq | ].
    destruct (Bool.bool_dec (existsb BN.is_existing_var_row
      (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true); discriminate Heq.
Qed.
(* §18.9 whole-decision: exactly one of the nine fixed-order cases holds, each paired with its exact outcome *)
Lemma short_decl_decision_cases (va : Collections.NodeMap.t NegCell) (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv)) :
  let st := Index.Refs.mkShortStmtRef r nn nv Hv in
  let se := BN.short_event bp st in
  let dec := short_decl_decision va r nn nv Hv in
  (exists n H, BN.short_dup_decision_name (BN.short_duplicate_decision se) = Some n
     /\ dec = SInvalid (ShortDuplicate (BN.short_duplicate_decision se) n eq_refl H eq_refl))
  \/ (BN.short_dup_decision_name (BN.short_duplicate_decision se) = None
     /\ Index.Refs.sh_names st <> Index.Refs.sh_values st
     /\ exists H, dec = SInvalid (ShortCountMismatch st eq_refl H))
  \/ (BN.short_dup_decision_name (BN.short_duplicate_decision se) = None
     /\ Index.Refs.sh_names st = Index.Refs.sh_values st
     /\ exists i row m Hrow, BN.short_blocker_decision se = BN.ShortBlockNonvar i row m Hrow
        /\ dec = SInvalid (ShortReusesNonVariable st i row m Hrow eq_refl))
  \/ (BN.short_dup_decision_name (BN.short_duplicate_decision se) = None
     /\ Index.Refs.sh_names st = Index.Refs.sh_values st
     /\ exists i row a b Hrow, BN.short_blocker_decision se = BN.ShortBlockAmbiguous i row a b Hrow
        /\ dec = SDependent (DepShortAmbiguous st i row a b Hrow eq_refl))
  \/ (BN.short_dup_decision_name (BN.short_duplicate_decision se) = None
     /\ Index.Refs.sh_names st = Index.Refs.sh_values st
     /\ BN.short_blocker_decision se = BN.ShortNoBlocker
     /\ exists Hnew : existsb BN.is_new_row (BN.se_rows se) = false,
          dec = SInvalid (ShortNoNewName st Hnew eq_refl))
  \/ (BN.short_dup_decision_name (BN.short_duplicate_decision se) = None
     /\ Index.Refs.sh_names st = Index.Refs.sh_values st
     /\ BN.short_blocker_decision se = BN.ShortNoBlocker
     /\ existsb BN.is_new_row (BN.se_rows se) = true
     /\ exists out, short_rhs_neg va st = Some out /\ dec = out)
  \/ (BN.short_dup_decision_name (BN.short_duplicate_decision se) = None
     /\ Index.Refs.sh_names st = Index.Refs.sh_values st
     /\ BN.short_blocker_decision se = BN.ShortNoBlocker
     /\ existsb BN.is_new_row (BN.se_rows se) = true
     /\ short_rhs_neg va st = None
     /\ exists j edge, find_rhs_vnonconst va st = Some (existT _ j edge)
        /\ dec = SUnmet (ReqShortRhsMeaning st j edge eq_refl))
  \/ (BN.short_dup_decision_name (BN.short_duplicate_decision se) = None
     /\ Index.Refs.sh_names st = Index.Refs.sh_values st
     /\ BN.short_blocker_decision se = BN.ShortNoBlocker
     /\ existsb BN.is_new_row (BN.se_rows se) = true
     /\ short_rhs_neg va st = None
     /\ find_rhs_vnonconst va st = None
     /\ existsb BN.is_existing_var_row (BN.se_rows se) = true
     /\ dec = SUnmet (ReqShortRedeclarationTypes st eq_refl))
  \/ (BN.short_dup_decision_name (BN.short_duplicate_decision se) = None
     /\ Index.Refs.sh_names st = Index.Refs.sh_values st
     /\ BN.short_blocker_decision se = BN.ShortNoBlocker
     /\ existsb BN.is_new_row (BN.se_rows se) = true
     /\ short_rhs_neg va st = None
     /\ find_rhs_vnonconst va st = None
     /\ existsb BN.is_existing_var_row (BN.se_rows se) = false
     /\ dec = SUnmet (ReqShortUsage st eq_refl)).
Proof.
  cbv zeta.
  (* each guard case-split is isolated so the outcome goal is never abstracted; one sound lemma per leaf *)
  assert (Hdcase : (exists n, BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = Some n)
                \/ BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = None)
    by (destruct (BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) as [n|]; [ left; exists n | right ]; reflexivity).
  assert (Hbcase : BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortNoBlocker
                \/ (exists i row m Hrow, BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortBlockNonvar i row m Hrow)
                \/ (exists i row a b Hrow, BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)) = BN.ShortBlockAmbiguous i row a b Hrow))
    by (destruct (BN.short_blocker_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) as [|i row m Hrow|i row a b Hrow];
        [ left | right; left; exists i, row, m, Hrow | right; right; exists i, row, a, b, Hrow ]; reflexivity).
  assert (Hncase : existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = true
                \/ existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = false)
    by (destruct (existsb BN.is_new_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))); [ left | right ]; reflexivity).
  assert (Hgcase : (exists out, short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv) = Some out)
                \/ short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv) = None)
    by (destruct (short_rhs_neg va (Index.Refs.mkShortStmtRef r nn nv Hv)) as [out|]; [ left; exists out | right ]; reflexivity).
  assert (Hfcase : (exists j edge, find_rhs_vnonconst va (Index.Refs.mkShortStmtRef r nn nv Hv) = Some (existT _ j edge))
                \/ find_rhs_vnonconst va (Index.Refs.mkShortStmtRef r nn nv Hv) = None)
    by (destruct (find_rhs_vnonconst va (Index.Refs.mkShortStmtRef r nn nv Hv)) as [[j edge]|]; [ left; exists j, edge | right ]; reflexivity).
  destruct Hdcase as [[n Hdup] | Hdup].
  { destruct (short_decl_decision_dup_sound va r nn nv Hv n Hdup) as [H Heq].
    left. exists n, H. split; [ exact Hdup | exact Heq ]. }
  destruct (Nat.eq_dec (Index.Refs.sh_names (Index.Refs.mkShortStmtRef r nn nv Hv))
    (Index.Refs.sh_values (Index.Refs.mkShortStmtRef r nn nv Hv))) as [Hcount | Hnec].
  2:{ destruct (short_decl_decision_count_sound va r nn nv Hv Hdup Hnec) as [H Heq].
      right; left. split; [ exact Hdup | split; [ exact Hnec | exists H; exact Heq ] ]. }
  destruct Hbcase as [Hblk | [ [i [row [m [Hrow Hblk]]]] | [i [row [a [b [Hrow Hblk]]]]] ]].
  2:{ right; right; left. split; [ exact Hdup | split; [ exact Hcount | exists i, row, m, Hrow;
        split; [ exact Hblk | exact (short_decl_decision_blocker_nonvar_sound va r nn nv Hv Hdup Hcount i row m Hrow Hblk) ] ] ]. }
  2:{ right; right; right; left. split; [ exact Hdup | split; [ exact Hcount | exists i, row, a, b, Hrow;
        split; [ exact Hblk | exact (short_decl_decision_blocker_ambiguous_sound va r nn nv Hv Hdup Hcount i row a b Hrow Hblk) ] ] ]. }
  destruct Hncase as [Hnew | Hnew].
  2:{ right; right; right; right; left. split; [ exact Hdup | split; [ exact Hcount | split; [ exact Hblk |
        exists Hnew; exact (short_decl_decision_nonew_sound va r nn nv Hv Hdup Hcount Hblk Hnew) ] ] ]. }
  destruct Hgcase as [[out Hneg] | Hneg].
  { right; right; right; right; right; left. split; [ exact Hdup | split; [ exact Hcount | split; [ exact Hblk |
      split; [ exact Hnew | exists out; split; [ exact Hneg | exact (short_decl_decision_rhsneg_sound va r nn nv Hv Hdup Hcount Hblk Hnew out Hneg) ] ] ] ] ]. }
  destruct Hfcase as [[j [edge Hfind]] | Hfind].
  { right; right; right; right; right; right; left. split; [ exact Hdup | split; [ exact Hcount | split; [ exact Hblk |
      split; [ exact Hnew | split; [ exact Hneg | exists j, edge; split; [ exact Hfind |
      exact (short_decl_decision_rhsmeaning_sound va r nn nv Hv j edge Hdup Hcount Hblk Hnew Hneg Hfind) ] ] ] ] ] ]. }
  destruct (Bool.bool_dec (existsb BN.is_existing_var_row (BN.se_rows (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) true) as [Hmix | Hmix].
  { right; right; right; right; right; right; right; left. split; [ exact Hdup | split; [ exact Hcount | split; [ exact Hblk |
      split; [ exact Hnew | split; [ exact Hneg | split; [ exact Hfind | split; [ exact Hmix |
      exact (short_decl_decision_redecl_sound_st va (Index.Refs.mkShortStmtRef r nn nv Hv) Hdup Hcount Hblk Hnew Hneg Hfind Hmix) ] ] ] ] ] ] ]. }
  { right; right; right; right; right; right; right; right. split; [ exact Hdup | split; [ exact Hcount | split; [ exact Hblk |
      split; [ exact Hnew | split; [ exact Hneg | split; [ exact Hfind | split; [ exact (Bool.not_true_is_false _ Hmix) |
      exact (short_decl_decision_usage_sound_st va (Index.Refs.mkShortStmtRef r nn nv Hv) Hdup Hcount Hblk Hnew Hneg Hfind (Bool.not_true_is_false _ Hmix)) ] ] ] ] ] ] ]. }
Qed.
(* §10 the statement fact: expr arm from the driver, short arm the canonical decision over va, else no fact *)
Definition stmt_fact_body (r : Index.NodeRef idx)
  (sx : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr -> StmtOutcome bp r)
  (va : Collections.NodeMap.t NegCell) (v : Index.Model.NodeView) (H : Index.node_view r = v) : list (OccFact bp) :=
  match v as v0 return Index.node_view r = v0 -> list (OccFact bp) with
  | Index.Model.VStmt Index.Model.SSExpr => fun Hv => [OFStmt r (sx Hv)]
  | Index.Model.VStmt (Index.Model.SSShort nn nv) => fun Hv => [OFStmt r (short_decl_decision va r nn nv Hv)]
  | _ => fun _ => []
  end H.
Definition stmt_fact (r : Index.NodeRef idx)
  (sx : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr -> StmtOutcome bp r)
  (va : Collections.NodeMap.t NegCell) : list (OccFact bp) :=
  stmt_fact_body r sx va (Index.node_view r) eq_refl.
Lemma stmt_fact_ssexpr (r : Index.NodeRef idx)
  (sx : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr -> StmtOutcome bp r) (va : Collections.NodeMap.t NegCell)
  (H : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr) : stmt_fact r sx va = [OFStmt r (sx H)].
Proof. exact (convoy_at (Index.node_view r) (stmt_fact_body r sx va) (Index.Model.VStmt Index.Model.SSExpr) H). Qed.
(* a short statement node's one retained fact is exactly its canonical short-declaration decision *)
Lemma stmt_fact_ssshort (r : Index.NodeRef idx)
  (sx : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr -> StmtOutcome bp r) (va : Collections.NodeMap.t NegCell)
  (nn nv : nat) (H : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv)) :
  stmt_fact r sx va = [OFStmt r (short_decl_decision va r nn nv H)].
Proof. exact (convoy_at (Index.node_view r) (stmt_fact_body r sx va) (Index.Model.VStmt (Index.Model.SSShort nn nv)) H). Qed.
(* every fact stmt_fact retains is an OFStmt at that exact node — and it retains one only at a statement node *)
Lemma stmt_fact_content (r : Index.NodeRef idx)
  (sx : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr -> StmtOutcome bp r) (va : Collections.NodeMap.t NegCell)
  (o : OccFact bp) (v : Index.Model.NodeView) (H : Index.node_view r = v) :
  In o (stmt_fact_body r sx va v H) -> (exists os, o = OFStmt r os) /\ exists st, Index.node_view r = Index.Model.VStmt st.
Proof.
  destruct v as [na|nl|nu| |nt|nb|nc|nvv|nts|nd|nst| |ntp| ]; try (cbn; intro Hin; exfalso; exact Hin).
  destruct nst; cbn; intro Hin; try (exfalso; exact Hin);
    (destruct Hin as [Hin|Hin]; [ subst o; split; [ eexists; reflexivity | eexists; exact H ] | exfalso; exact Hin ]).
Qed.
(* the node's own value row, direct at the node — a name head and an operand-only site carry none *)
Definition va_value_row (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx) : list (OccFact bp) :=
  if is_name_head r || operand_only bp ctab r then [] else [OFValue r (own_value bp ctab r)].
(* the node's own application row — the canonical app_fact_app, one own_app construction *)
Definition va_app_row (r : Index.NodeRef idx) : list (OccFact bp) := app_fact_app r.
(* the Value row is retained exactly when the shared policy admits the site's view — the one retention gate *)
Definition retained_value_row (ctab : Collections.NodeMap.t Intrinsic) (site : Index.NodeRef idx) : list (OccFact bp) :=
  if retains_value_fact site then va_value_row ctab site else [].
(* §11 raw_facts projects each node's own outcome directly; a statement reads its child via the carrier *)
Definition occ_facts_va (va : Collections.NodeMap.t NegCell) (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx) : list (OccFact bp) :=
  match Index.node_view r with
  | Index.Model.VApplication => va_app_row r ++ retained_value_row ctab r
  | Index.Model.VStmt _ => stmt_fact r (expr_sx_va va r) va
  | Index.Model.VTypeExpr _ => type_fact r
  | _ => retained_value_row ctab r
  end.

(* the carrier read at a file node is the exact once-computed cell — In + NoDup + key-injectivity are file facts *)
Lemma neg_map_cell (ctab : Collections.NodeMap.t Intrinsic) (fr : Index.FileRef idx)
  (e : Index.NodeRef idx) (Hf : Index.nr_file e = fr) :
  Collections.NodeMap.find (Index.nr_key e) (neg_map ctab (Index.file_nodes fr)) = Some (neg_cell_of ctab e).
Proof.
  apply neg_map_at.
  - exact (file_nodes_complete fr e Hf).
  - apply file_nodes_nodup.
  - intros a b Ha Hb Hk. apply noderef_file_key_inj; [ | exact Hk ].
    rewrite (file_nodes_file fr a Ha), (file_nodes_file fr b Hb); reflexivity.
Qed.
(* §7 a name head's value read is false — its cell carries a false value field (name heads skip the value row) *)
Lemma va_value_negative_name_head (ctab : Collections.NodeMap.t Intrinsic) (fr : Index.FileRef idx)
  (e : Index.NodeRef idx) (Hnh : is_name_head e = true) (Hf : Index.nr_file e = fr) :
  va_value_negative (neg_map ctab (Index.file_nodes fr)) e = false.
Proof. unfold va_value_negative. rewrite (neg_map_cell ctab fr e Hf). cbn [nc_val_neg neg_cell_of]. rewrite Hnh. reflexivity. Qed.
Lemma va_value_nonconst_name_head (ctab : Collections.NodeMap.t Intrinsic) (fr : Index.FileRef idx)
  (e : Index.NodeRef idx) (Hnh : is_name_head e = true) (Hf : Index.nr_file e = fr) :
  va_value_nonconst (neg_map ctab (Index.file_nodes fr)) e = false.
Proof.
  unfold va_value_nonconst. rewrite (neg_map_cell ctab fr e Hf). cbn [nc_val_nonconst neg_cell_of]. rewrite Hnh.
  destruct (retains_value_fact e); reflexivity.
Qed.
(* §7 a name application head contributes no canonical fact: its value row is skipped and it holds no app row *)
Lemma occ_facts_va_name_head (ctab : Collections.NodeMap.t Intrinsic) (fr : Index.FileRef idx)
  (r : Index.NodeRef idx) (Hnh : is_name_head r = true) :
  occ_facts_va (neg_map ctab (Index.file_nodes fr)) ctab r = [].
Proof.
  assert (E : exists nm, Index.node_view r = Index.Model.VName nm).
  { pose proof Hnh as Hcopy. unfold is_name_head in Hcopy. apply andb_true_iff in Hcopy. destruct Hcopy as [_ Hf].
    destruct (Index.node_view r) as [nm|nl|nu| |nt|nb|nc|nvv|nts|nd|nst| |ntp|]; try discriminate Hf; eauto. }
  destruct E as [nm E].
  unfold occ_facts_va. rewrite E. unfold retained_value_row, va_value_row. rewrite Hnh.
  destruct (retains_value_fact r); reflexivity.
Qed.

(* the node's own value / application row content at a file node — computed directly, the sole builder's row *)
Lemma va_value_row_at (ctab : Collections.NodeMap.t Intrinsic) (fr : Index.FileRef idx)
  (r : Index.NodeRef idx) (Hnh : is_name_head r = false) (Hoo : operand_only bp ctab r = false) (Hf : Index.nr_file r = fr) :
  va_value_row ctab r = [OFValue r (own_value bp ctab r)].
Proof. unfold va_value_row. rewrite Hnh, Hoo. reflexivity. Qed.
(* an operand-only site retains no value row: the exact constant it carries is consumed by its use, never reported *)
Lemma va_value_row_operand (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx)
  (Hoo : operand_only bp ctab r = true) : va_value_row ctab r = [].
Proof. unfold va_value_row. rewrite Hoo, orb_true_r. reflexivity. Qed.
(* an operand-only site's projected value is the neutral VNonconst, so it is never negative *)
Lemma operand_only_not_negative (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx)
  (Hoo : operand_only bp ctab r = true) : value_neg_b bp (own_value bp ctab r) = false.
Proof. unfold operand_only in Hoo. unfold own_value, value_of_verdict. destruct (own_verdict bp ctab r); [ discriminate Hoo | reflexivity ]. Qed.
Lemma va_app_row_at (ctab : Collections.NodeMap.t Intrinsic) (fr : Index.FileRef idx)
  (r : Index.NodeRef idx) (Hf : Index.nr_file r = fr) (Hva : Index.node_view r = Index.Model.VApplication) :
  va_app_row r = [OFApp r (own_app bp (Index.Refs.mkAppRef r Hva))].
Proof. unfold va_app_row. exact (app_fact_app_at r Hva). Qed.
Lemma va_app_row_none (ctab : Collections.NodeMap.t Intrinsic) (fr : Index.FileRef idx)
  (r : Index.NodeRef idx) (Hne : Index.node_view r <> Index.Model.VApplication) :
  va_app_row r = [].
Proof. unfold va_app_row. exact (app_fact_app_none r (Index.node_view r) eq_refl Hne). Qed.
(* the carrier child-read equals the canonical own_value / own_app negativity at a file node — the exact same fact *)
Lemma va_value_negative_correct (ctab : Collections.NodeMap.t Intrinsic) (fr : Index.FileRef idx)
  (e : Index.NodeRef idx) (Hnh : is_name_head e = false) (Hf : Index.nr_file e = fr) :
  va_value_negative (neg_map ctab (Index.file_nodes fr)) e = value_neg_b bp (own_value bp ctab e).
Proof. unfold va_value_negative. rewrite (neg_map_cell ctab fr e Hf). cbn [nc_val_neg neg_cell_of]. rewrite Hnh. reflexivity. Qed.
Lemma va_value_nonconst_correct (ctab : Collections.NodeMap.t Intrinsic) (fr : Index.FileRef idx)
  (e : Index.NodeRef idx) (Hnh : is_name_head e = false) (Hf : Index.nr_file e = fr) :
  va_value_nonconst (neg_map ctab (Index.file_nodes fr)) e
  = retains_value_fact e && match own_verdict bp ctab e with Some VNonconst => true | _ => false end.
Proof. unfold va_value_nonconst. rewrite (neg_map_cell ctab fr e Hf). cbn [nc_val_nonconst neg_cell_of]. rewrite Hnh. reflexivity. Qed.
Lemma va_app_negative_correct (ctab : Collections.NodeMap.t Intrinsic) (fr : Index.FileRef idx)
  (e : Index.NodeRef idx) (Hf : Index.nr_file e = fr) :
  va_app_negative (neg_map ctab (Index.file_nodes fr)) e = app_neg_at bp e.
Proof. unfold va_app_negative. rewrite (neg_map_cell ctab fr e Hf). reflexivity. Qed.

(* §19.4 a negative value fact sits only on a value-emitting node, so it is one of that node's canonical facts *)
Lemma occ_value_mem (ctab : Collections.NodeMap.t Intrinsic) (fr : Index.FileRef idx)
  (e : Index.NodeRef idx) (Hnh : is_name_head e = false) (Hf : Index.nr_file e = fr) :
  value_neg_b bp (own_value bp ctab e) = true ->
  In (OFValue e (own_value bp ctab e)) (occ_facts_va (neg_map ctab (Index.file_nodes fr)) ctab e).
Proof.
  intro Hneg.
  assert (Hoo : operand_only bp ctab e = false).
  { destruct (operand_only bp ctab e) eqn:Eoo; [ rewrite (operand_only_not_negative ctab e Eoo) in Hneg; discriminate Hneg | reflexivity ]. }
  unfold occ_facts_va, retained_value_row, retains_value_fact.
  destruct (Index.node_view e) as [na|nl|nu| |nt|nb|nc|nvv|nts|nd|nst| |ntp|] eqn:E; cbn [retains_value_fact_view];
    try (rewrite (va_value_row_at ctab fr e Hnh Hoo Hf); solve [ apply in_eq | apply in_or_app; right; apply in_eq ]);
    exfalso; rewrite (own_value_at bp ctab e _ E) in Hneg; cbn in Hneg; discriminate Hneg.
Qed.
(* the retained Value row of a policy-applicable, non-operand-only site is one of its canonical facts, any outcome *)
Lemma occ_value_mem_retained (ctab : Collections.NodeMap.t Intrinsic) (fr : Index.FileRef idx)
  (e : Index.NodeRef idx) (Hnh : is_name_head e = false) (Hoo : operand_only bp ctab e = false) (Hf : Index.nr_file e = fr) :
  retains_value_fact e = true ->
  In (OFValue e (own_value bp ctab e)) (occ_facts_va (neg_map ctab (Index.file_nodes fr)) ctab e).
Proof.
  unfold retains_value_fact, occ_facts_va, retained_value_row, retains_value_fact.
  destruct (Index.node_view e) as [na|nl|nu| |nt|nb|nc|nvv|nts|nd|nst| |ntp|] eqn:E; cbn [retains_value_fact_view];
    intro Hret; try discriminate Hret;
    rewrite (va_value_row_at ctab fr e Hnh Hoo Hf); solve [ apply in_eq | apply in_or_app; right; apply in_eq ].
Qed.
(* §19.4 the application fact of an application node is one of its canonical facts *)
Lemma occ_app_mem (ctab : Collections.NodeMap.t Intrinsic) (fr : Index.FileRef idx)
  (e : Index.NodeRef idx) (Hf : Index.nr_file e = fr) (He : Index.node_view e = Index.Model.VApplication) :
  In (OFApp e (own_app bp (Index.Refs.mkAppRef e He))) (occ_facts_va (neg_map ctab (Index.file_nodes fr)) ctab e).
Proof.
  assert (Hocc : occ_facts_va (neg_map ctab (Index.file_nodes fr)) ctab e
      = va_app_row e ++ retained_value_row ctab e)
    by (unfold occ_facts_va; rewrite He; reflexivity).
  rewrite Hocc, (va_app_row_at ctab fr e Hf He). apply in_or_app. left. apply in_eq.
Qed.
(* the short-declaration decision of a short statement node is that node's one canonical fact *)
Lemma occ_stmt_mem (ctab : Collections.NodeMap.t Intrinsic) (fr : Index.FileRef idx)
  (e : Index.NodeRef idx) (Hf : Index.nr_file e = fr) (nn nv : nat)
  (Hv : Index.node_view e = Index.Model.VStmt (Index.Model.SSShort nn nv)) :
  In (OFStmt e (short_decl_decision (neg_map ctab (Index.file_nodes fr)) e nn nv Hv))
     (occ_facts_va (neg_map ctab (Index.file_nodes fr)) ctab e).
Proof.
  assert (Hocc : occ_facts_va (neg_map ctab (Index.file_nodes fr)) ctab e
      = stmt_fact e (expr_sx_va (neg_map ctab (Index.file_nodes fr)) e) (neg_map ctab (Index.file_nodes fr)))
    by (unfold occ_facts_va; rewrite Hv; reflexivity).
  rewrite Hocc, (stmt_fact_ssshort e (expr_sx_va (neg_map ctab (Index.file_nodes fr)) e)
    (neg_map ctab (Index.file_nodes fr)) nn nv Hv). apply in_eq.
Qed.
(* §5 fused pieces: own_verdict/own_app computed once per node, feeding the rows AND the cell *)
Definition node_rows_of (r : Index.NodeRef idx) (v : option (ValueOutcome bp r)) (oa : list (OccFact bp)) : list (OccFact bp) :=
  let row := if is_name_head r || match v with None => true | Some _ => false end then [] else [OFValue r (value_of_verdict bp v)] in
  match Index.node_view r with
  | Index.Model.VApplication => oa ++ (if retains_value_fact r then row else [])
  | Index.Model.VStmt _ => []
  | Index.Model.VTypeExpr _ => type_fact r
  | _ => if retains_value_fact r then row else []
  end.
Definition cell_of' (r : Index.NodeRef idx) (v : option (ValueOutcome bp r)) (oa : list (OccFact bp)) : NegCell :=
  mkNegCell (if is_name_head r then false else value_neg_b bp (value_of_verdict bp v))
            (match oa with OFApp _ o :: _ => app_neg_b bp o | _ => false end)
            (if is_name_head r then false else match v with Some VNonconst => true | _ => false end).
(* the fused per-file pass: ONE fold; own_verdict/own_app (via the let) computed once per node, fed to both outputs *)
Definition file_pass (ctab : Collections.NodeMap.t Intrinsic) (nodes : list (Index.NodeRef idx))
  : list (list (OccFact bp)) * Collections.NodeMap.t NegCell :=
  fold_left (fun st r =>
       let v := own_verdict bp ctab r in
       let oa := app_fact_app r in
       (node_rows_of r v oa :: fst st, Collections.NodeMap.add (Index.nr_key r) (cell_of' r v oa) (snd st)))
     nodes ([], Collections.NodeMap.empty NegCell).
(* the fused fact list: the pass's own rows, each statement's row assembled from the complete carrier *)
Definition file_facts (ctab : Collections.NodeMap.t Intrinsic) (nodes : list (Index.NodeRef idx)) : list (OccFact bp) :=
  let pass := file_pass ctab nodes in
  List.concat (map (fun ro => match Index.node_view (fst ro) with
                         | Index.Model.VStmt _ => stmt_fact (fst ro) (expr_sx_va (snd pass) (fst ro)) (snd pass)
                         | _ => snd ro end)
              (combine nodes (rev (fst pass)))).
(* the cell's app field reads back the exact once-built app row's negativity — the same own_app app_neg_at names *)
Lemma app_row_neg_eq (r : Index.NodeRef idx) :
  (match app_fact_app r with OFApp _ o :: _ => app_neg_b bp o | _ => false end) = app_neg_at bp r.
Proof.
  destruct (Index.node_view r) as [na|nl|nu| |nt|nb|nc|nvv|nts|nd|nst| |ntp|] eqn:E;
    try (rewrite (app_fact_app_none r _ E ltac:(discriminate)); rewrite (app_neg_at_off r _ E ltac:(discriminate)); reflexivity).
  rewrite (app_fact_app_at r E). cbn [app_neg_b]. rewrite (app_neg_at_app r E). reflexivity.
Qed.
(* the fused cell equals the canonical neg_cell_of — value fields share own_verdict, app shares own_app *)
Lemma cell_of'_eq (ctab : Collections.NodeMap.t Intrinsic) (r : Index.NodeRef idx) :
  cell_of' r (own_verdict bp ctab r) (app_fact_app r) = neg_cell_of ctab r.
Proof. unfold cell_of', neg_cell_of, own_value. rewrite app_row_neg_eq. reflexivity. Qed.
(* the fold decomposition: the rows accumulate reversed, the carrier is exactly the canonical neg_map fold *)
Lemma file_pass_spec (ctab : Collections.NodeMap.t Intrinsic) (nodes : list (Index.NodeRef idx))
  (ar : list (list (OccFact bp))) (ac : Collections.NodeMap.t NegCell) :
  fold_left (fun st r => let v := own_verdict bp ctab r in let oa := app_fact_app r in
                (node_rows_of r v oa :: fst st, Collections.NodeMap.add (Index.nr_key r) (cell_of' r v oa) (snd st)))
            nodes (ar, ac)
  = (rev (map (fun r => node_rows_of r (own_verdict bp ctab r) (app_fact_app r)) nodes) ++ ar,
     fold_left (fun c r => Collections.NodeMap.add (Index.nr_key r) (neg_cell_of ctab r) c) nodes ac).
Proof.
  revert ar ac. induction nodes as [|n rest IH]; intros ar ac; [ reflexivity | ].
  cbn [fold_left]. rewrite cell_of'_eq. rewrite IH. cbn [map rev].
  rewrite <- app_assoc. reflexivity.
Qed.
(* the assembled contribution of a node is exactly its occ_facts_va contribution over the complete carrier *)
Lemma assembly_eq (ctab : Collections.NodeMap.t Intrinsic) (nodes : list (Index.NodeRef idx)) (r : Index.NodeRef idx) :
  (match Index.node_view r with
   | Index.Model.VStmt _ => stmt_fact r (expr_sx_va (neg_map ctab nodes) r) (neg_map ctab nodes)
   | _ => node_rows_of r (own_verdict bp ctab r) (app_fact_app r) end)
  = occ_facts_va (neg_map ctab nodes) ctab r.
Proof.
  unfold occ_facts_va, node_rows_of, va_app_row, retained_value_row, va_value_row, own_value, operand_only.
  destruct (Index.node_view r); reflexivity.
Qed.
(* combine with the mapped self-rows collapses to a pointwise map — the plumbing lemma for the assembly *)
Lemma combine_map_self {A B C} (f : A * B -> C) (h : A -> B) (l : list A) :
  map f (combine l (map h l)) = map (fun x => f (x, h x)) l.
Proof. induction l as [|a l IH]; [ reflexivity | cbn; f_equal; exact IH ]. Qed.
(* the pass evaluates to the reversed self-rows and exactly the canonical neg_map carrier *)
Lemma file_pass_val (ctab : Collections.NodeMap.t Intrinsic) (nodes : list (Index.NodeRef idx)) :
  file_pass ctab nodes
  = (rev (map (fun r => node_rows_of r (own_verdict bp ctab r) (app_fact_app r)) nodes), neg_map ctab nodes).
Proof.
  unfold file_pass. rewrite file_pass_spec, app_nil_r. reflexivity.
Qed.
(* the fused fact list equals the canonical raw projection over the complete carrier — the byte-identity bridge *)
Lemma file_facts_eq (ctab : Collections.NodeMap.t Intrinsic) (nodes : list (Index.NodeRef idx)) :
  file_facts ctab nodes = flat_map (occ_facts_va (neg_map ctab nodes) ctab) nodes.
Proof.
  unfold file_facts. cbv zeta. unfold file_pass. rewrite !file_pass_spec. cbn [fst snd].
  rewrite !app_nil_r, rev_involutive.
  rewrite combine_map_self. rewrite flat_map_concat_map. f_equal. apply map_ext. intro r. cbn [fst snd]. apply assembly_eq.
Qed.
(* uc_own_app_once: the app node's own_app is ONE construction — its OFApp is the fact row, its projection the cell *)
Lemma own_app_once (ctab : Collections.NodeMap.t Intrinsic) (fr : Index.FileRef idx)
  (r : Index.NodeRef idx) (Hf : Index.nr_file r = fr) (Hv : Index.node_view r = Index.Model.VApplication) :
  In (OFApp r (own_app bp (Index.Refs.mkAppRef r Hv))) (file_facts ctab (Index.file_nodes fr))
  /\ va_app_negative (neg_map ctab (Index.file_nodes fr)) r = app_neg_b bp (own_app bp (Index.Refs.mkAppRef r Hv)).
Proof.
  split.
  - rewrite file_facts_eq. apply in_flat_map. exists r.
    split; [ exact (file_nodes_complete fr r Hf) | apply (occ_app_mem ctab fr r Hf Hv) ].
  - rewrite (va_app_negative_correct ctab fr r Hf). apply (app_neg_at_app r Hv).
Qed.

Local Definition raw_facts : list (OccFact bp) :=
  flat_map (fun fr => file_facts (const_table bp fr) (Index.file_nodes fr))
           (flat_map BN.PI.pkg_members (BN.PI.packages s)).
(* the fused raw list projects to the canonical per-file occ_facts_va form — the retention proofs read this *)
Lemma raw_facts_flat : raw_facts =
  flat_map (fun fr => let ctab := const_table bp fr in
                      let va := neg_map ctab (Index.file_nodes fr) in
                      flat_map (occ_facts_va va ctab) (Index.file_nodes fr))
           (flat_map BN.PI.pkg_members (BN.PI.packages s)).
Proof.
  unfold raw_facts. rewrite !flat_map_concat_map. f_equal. apply map_ext. intro fr. apply file_facts_eq.
Qed.

Definition FactPhase : Type := { m : list (OccFact bp) | m = raw_facts }.

End Retain.

Arguments FactPhase {p idx s bd} bp.

Section Laws.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} (bp : BN.BindingPhase s bd).

(* the phase content is built once; every phase carries exactly the canonical classification, none caller-supplied *)
Local Lemma fact_once (fp : FactPhase bp) : proj1_sig fp = raw_facts bp.
Proof. exact (proj2_sig fp). Qed.

(* statement and type-use families have no Nonconst constructor: OK / invalid / unmet / dependent exhaust each *)
Lemma only_lawful_per_family (r : Index.NodeRef idx) :
  (forall o : StmtOutcome bp r, o = SOK \/ (exists c, o = SInvalid c) \/ (exists q, o = SUnmet q) \/ (exists d, o = SDependent d))
  /\ (forall o : TypeUseOutcome bp r, (exists f, o = TOK f) \/ (exists c, o = TInvalid c) \/ (exists q, o = TUnmet q) \/ (exists d, o = TDependent d)).
Proof.
  split; intro o; destruct o.
  - left; reflexivity.
  - right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; right; eexists; reflexivity.
  - left; eexists; reflexivity.
  - right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; right; eexists; reflexivity.
Qed.

End Laws.

(* the fresh-build preflight: naming and root entries are PackageIdentity facts; Analysis owns only the collision *)

Inductive FreshBuildDisposition {p} {idx : Index.ProgramIndex p} (s : BN.PI.PackageSurface idx) : Type :=
| FreshOk : FreshBuildDisposition s
| FreshCollision : BN.PI.PackageRef s -> BN.PI.RootEntryRef idx -> FreshBuildDisposition s.
Arguments FreshOk {p idx s}.
Arguments FreshCollision {p idx s} _ _.

(* collision applicability is exactly OneSelected, independent of any package's main multiplicity *)
Local Definition raw_preflight {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}
  {bd : BN.PhaseData s} (bp : BN.BindingPhase s bd) : FreshBuildDisposition s :=
  let _ := bp in
  match BN.PI.package_selection s with
  | BN.PI.OneSelected pr =>
      match find (fun rr => andb (String.eqb (BN.PI.default_exec_name pr) (BN.PI.re_name rr))
                                 (match BN.PI.re_kind rr with BN.PI.RootDir => true | BN.PI.RootFile => false end))
                 (BN.PI.root_entries idx) with
      | Some rr => FreshCollision pr rr
      | None => FreshOk
      end
  | _ => FreshOk
  end.

Definition PackageFacts {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}
  {bd : BN.PhaseData s} (bp : BN.BindingPhase s bd) : Type := { d : FreshBuildDisposition s | d = raw_preflight bp }.

(* small helper: a per-element singleton-or-empty flat_map is exactly the filter of its boolean condition *)
Lemma flat_map_match_filter {A} (f : A -> bool) (g : A -> list A) (l : list A)
  (Hg : forall a, g a = if f a then [a] else []) : flat_map g l = filter f l.
Proof. induction l as [|a t IH]; cbn; [reflexivity|]. rewrite Hg. destruct (f a); cbn; rewrite IH; reflexivity. Qed.


(* the one canonical transparent analysis DATA over p; a public constructor is fine because it is data, not authority *)
Record ResultData (p : Syntax.Program) : Type := mk_result_data {
  rd_index     : Index.ProgramIndex p ;
  rd_surface   : BN.PI.PackageSurface rd_index ;
  rd_bind_data : BN.PhaseData rd_surface ;
  rd_binds     : BN.BindingPhase rd_surface rd_bind_data ;
  rd_facts     : FactPhase rd_binds ;
  rd_pkg       : PackageFacts rd_binds
}.
Arguments mk_result_data {p} _ _ _ _ _ _.
Arguments rd_index {p} _. Arguments rd_surface {p} _.
Arguments rd_bind_data {p} _. Arguments rd_binds {p} _.
Arguments rd_facts {p} _. Arguments rd_pkg {p} _.

(* the one canonical data computation: the whole Analysis, built once and reducible for vm_compute/materialization *)
Definition result_data (p : Syntax.Program) : ResultData p :=
  let i := Index.index_program p in
  let s := BN.PI.package_surface i in
  let b := BN.bindings s in
  mk_result_data i s (BN.phase_data s) b (exist _ (raw_facts b) eq_refl) (exist _ (raw_preflight b) eq_refl).

(* the sealed abstract Result authority: a value minted only by analyze, retaining one ResultData, forge-proof *)
Module Type RESULT_AUTHORITY.
  Parameter Result : Syntax.Program -> Type.
  Parameter analyze : forall p, Result p.
  Parameter data_of_result : forall {p}, Result p -> ResultData p.
  (* the sole public mint-computation law: the minted Result observes exactly the canonical data *)
  Parameter analyze_observe_data : forall p, data_of_result (analyze p) = result_data p.
End RESULT_AUTHORITY.
Module ResultSeal : RESULT_AUTHORITY.
  Record ResultR (p : Syntax.Program) : Type := mkResultR { retained_data : ResultData p }.
  Arguments mkResultR {p} _.
  Arguments retained_data {p} _.
  Definition Result (p : Syntax.Program) : Type := ResultR p.
  Definition pack {p} (d : ResultData p) : Result p := mkResultR d.
  Definition read {p} (r : Result p) : ResultData p := retained_data r.
  Local Lemma read_pack {p} (d : ResultData p) : read (pack d) = d.
  Proof. reflexivity. Qed.
  Definition analyze (p : Syntax.Program) : Result p := pack (result_data p).
  Definition data_of_result {p} (r : Result p) : ResultData p := read r.
  Theorem analyze_observe_data (p : Syntax.Program) : data_of_result (analyze p) = result_data p.
  Proof. reflexivity. Qed.
End ResultSeal.
Definition Result (p : Syntax.Program) : Type := ResultSeal.Result p.
Definition analyze (p : Syntax.Program) : Result p := ResultSeal.analyze p.
(* the data of a Result is the DIRECT read of the supplied r; the body never mentions result_data *)
Definition data_of_result {p} (r : Result p) : ResultData p := ResultSeal.data_of_result r.
Definition analyze_observe_data (p : Syntax.Program) : data_of_result (analyze p) = result_data p :=
  ResultSeal.analyze_observe_data p.

(* the res_* projections read from the canonical data; none inspects or matches the sealed authority *)
Definition res_index {p} (r : Result p) : Index.ProgramIndex p := rd_index (data_of_result r).
Definition res_surface {p} (r : Result p) : BN.PI.PackageSurface (res_index r) := rd_surface (data_of_result r).
Definition res_bind_data {p} (r : Result p) : BN.PhaseData (res_surface r) := rd_bind_data (data_of_result r).
Definition res_binds {p} (r : Result p) : BN.BindingPhase (res_surface r) (res_bind_data r) := rd_binds (data_of_result r).
Definition res_facts {p} (r : Result p) : FactPhase (res_binds r) := rd_facts (data_of_result r).
Definition res_pkg {p} (r : Result p) : PackageFacts (res_binds r) := rd_pkg (data_of_result r).

(* the semantic family of an occurrence issue: declaration specs and short-decls are distinct from plain uses *)
Inductive Family : Type := FamValue | FamApplication | FamStatement | FamTypeUse | FamDeclaration.
(* §13 the exact negative class of a child fact: invalid, unmet, or dependent — the three ways a child blocks *)
Inductive NegClass : Type := NegInvalid | NegUnmet | NegDependent.

(* the displayed family is a TOTAL projection of the exact site and fact kind, never a caller-supplied field *)
Definition displayed_family {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) (k : FactKind) : Family :=
  match k with
  | ApplicationKind => FamApplication
  | TypeUseKind => FamTypeUse
  | StatementKind => match Index.node_view site with Index.Model.VStmt (Index.Model.SSShort _ _) => FamDeclaration | _ => FamStatement end
  | ValueKind => match Index.node_view site with
                 | Index.Model.VConstSpec _ | Index.Model.VVarSpec _ | Index.Model.VTypeSpec _ => FamDeclaration
                 | _ => FamValue end
  end.

Section OccFactProj.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} {bp : BN.BindingPhase s bd}.
(* the exact occurrence and applicable fact kind an occurrence fact carries; the displayed family is derived *)
Definition fact_site (o : OccFact bp) : Index.NodeRef idx :=
  match o with OFValue r _ | OFApp r _ | OFStmt r _ | OFType r _ => r end.
Definition fact_kind (o : OccFact bp) : FactKind :=
  match o with OFValue _ _ => ValueKind | OFApp _ _ => ApplicationKind | OFStmt _ _ => StatementKind | OFType _ _ => TypeUseKind end.
Definition fact_family (o : OccFact bp) : Family := displayed_family (fact_site o) (fact_kind o).
(* §11 the exact canonical key: an occurrence's exact site paired with its exact fact kind *)
Definition fact_key (o : OccFact bp) : Index.NodeRef idx * FactKind := (fact_site o, fact_kind o).
(* the exact cause/requirement/dependency an occurrence fact retains, determined by its exact outcome *)
Definition occ_cause (o : OccFact bp) : option (Cause bp (fact_site o) (fact_kind o)) :=
  match o as o' return option (Cause bp (fact_site o') (fact_kind o')) with
  | OFValue _ ov => match ov with VInvalid c => Some c | _ => None end
  | OFApp _ oa => match oa with AInvalid c => Some c | _ => None end
  | OFStmt _ os => match os with SInvalid c => Some c | _ => None end
  | OFType _ ot => match ot with TInvalid c => Some c | _ => None end
  end.
Definition occ_req (o : OccFact bp) : option (Requirement bp (fact_site o) (fact_kind o)) :=
  match o as o' return option (Requirement bp (fact_site o') (fact_kind o')) with
  | OFValue _ ov => match ov with VUnmet q => Some q | _ => None end
  | OFApp _ oa => match oa with AUnmet q => Some q | _ => None end
  | OFStmt _ os => match os with SUnmet q => Some q | _ => None end
  | OFType _ ot => match ot with TUnmet q => Some q | _ => None end
  end.
Definition occ_dep (o : OccFact bp) : option (Dependency bp (fact_site o) (fact_kind o)) :=
  match o as o' return option (Dependency bp (fact_site o') (fact_kind o')) with
  | OFValue _ ov => match ov with VDependent dd => Some dd | _ => None end
  | OFApp _ oa => match oa with ADependent dd => Some dd | _ => None end
  | OFStmt _ os => match os with SDependent dd => Some dd | _ => None end
  | OFType _ ot => match ot with TDependent dd => Some dd | _ => None end
  end.
End OccFactProj.

Section FactBuilderLaws.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
        {bp : BN.BindingPhase s bd}.

(* every fact the one canonical builder retains at a node carries that exact node as its site *)
Lemma occ_facts_va_site (ctab : Collections.NodeMap.t Intrinsic) (fr : Index.FileRef idx)
  (r : Index.NodeRef idx) (Hf : Index.nr_file r = fr) (o : OccFact bp) :
  In o (occ_facts_va bp (neg_map bp ctab (Index.file_nodes fr)) ctab r) -> fact_site o = r.
Proof.
  intro Hin. destruct (is_name_head r) eqn:Hnh.
  { rewrite (occ_facts_va_name_head bp ctab fr r Hnh) in Hin. inversion Hin. }
  destruct (operand_only bp ctab r) eqn:Hoo;
  unfold occ_facts_va, retained_value_row, retains_value_fact in Hin;
  destruct (Index.node_view r) as [n|l|u| |[nt]|b|c|v|ts|d|st| |tp| ] eqn:E; cbn [retains_value_fact_view] in Hin;
    try (rewrite (va_value_row_at bp ctab fr r Hnh Hoo Hf) in Hin);
    try (rewrite (va_value_row_operand bp ctab r Hoo) in Hin);
    try (rewrite (va_app_row_at bp ctab fr r Hf E) in Hin);
    try (rewrite (type_fact_at bp r nt E) in Hin);
    try (destruct (stmt_fact_content bp r _ _ _ (Index.node_view r) eq_refl Hin) as [[os Hos] _]; subst o; reflexivity);
    cbn in Hin; repeat (destruct Hin as [Hin|Hin]); solve [ exfalso; exact Hin | subst o; reflexivity ].
Qed.

(* stmt_fact is a singleton or empty, so its site+kind keys are trivially duplicate-free *)
Lemma stmt_fact_key_nodup (r : Index.NodeRef idx)
  (sx : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr -> StmtOutcome bp r) (va : Collections.NodeMap.t NegCell)
  (v : Index.Model.NodeView) (H : Index.node_view r = v) :
  NoDup (map fact_key (stmt_fact_body bp r sx va v H)).
Proof.
  destruct v as [na|nl|nu| |nt|nb|nc|nvv|nts|nd|nst| |ntp| ]; try (cbn; apply NoDup_nil).
  destruct nst; cbn; try apply NoDup_nil.
  all: apply NoDup_cons; [ intro Hc; exact Hc | apply NoDup_nil ].
Qed.

(* the facts the one canonical builder retains at a node have duplicate-free keys: one per family, app's two distinct *)
Lemma occ_facts_va_key_nodup (ctab : Collections.NodeMap.t Intrinsic) (fr : Index.FileRef idx)
  (r : Index.NodeRef idx) (Hf : Index.nr_file r = fr) :
  NoDup (map fact_key (occ_facts_va bp (neg_map bp ctab (Index.file_nodes fr)) ctab r)).
Proof.
  destruct (is_name_head r) eqn:Hnh.
  { rewrite (occ_facts_va_name_head bp ctab fr r Hnh). apply NoDup_nil. }
  destruct (operand_only bp ctab r) eqn:Hoo;
  unfold occ_facts_va, retained_value_row, retains_value_fact;
  destruct (Index.node_view r) as [n|l|u| |[nt]|b|c|v|ts|d|st| |tp| ] eqn:E; cbn [retains_value_fact_view];
    try (rewrite (va_value_row_at bp ctab fr r Hnh Hoo Hf)); try (rewrite (va_value_row_operand bp ctab r Hoo));
    try (rewrite (va_app_row_at bp ctab fr r Hf E));
    try (rewrite (type_fact_at bp r nt E));
    try (exact (stmt_fact_key_nodup r (expr_sx_va bp (neg_map bp ctab (Index.file_nodes fr)) r) (neg_map bp ctab (Index.file_nodes fr)) (Index.node_view r) eq_refl));
    cbn [map fact_key fact_site fact_kind app];
    repeat (apply NoDup_cons; [ intro H; cbn in H; repeat (destruct H as [H|H]); solve [ discriminate H | exfalso; exact H ] | ]);
    apply NoDup_nil.
Qed.

(* the package member files, in package order, are duplicate-free: no file belongs to two packages or repeats *)
Lemma files_nodup : NoDup (flat_map BN.PI.pkg_members (BN.PI.packages s)).
Proof.
  apply (BN.flat_map_nodup_key _ (BN.PI.package_of_file s) (fun pr => pr)).
  - rewrite map_id. apply BN.packages_nodup.
  - intros pr _. apply BN.pkg_members_nodup.
  - intros pr fr _ Hin. exact (BN.PI.package_of_file_member s pr fr Hin).
Qed.

(* §11 canonical-key soundness at the source: no two retained facts share a site+kind key across the whole program *)
Lemma raw_facts_key_nodup : NoDup (map fact_key (raw_facts bp)).
Proof.
  rewrite raw_facts_flat; cbv zeta. rewrite map_flat_map.
  apply (BN.flat_map_nodup _ (fun sk => Index.nr_file (fst sk))).
  - apply files_nodup.
  - intros fr _. rewrite map_flat_map. apply (BN.flat_map_nodup _ (fun sk => fst sk)).
    + apply file_nodes_nodup.
    + intros r Hr. apply (occ_facts_va_key_nodup (const_table bp fr) fr r (Index.file_nodes_file fr r Hr)).
    + intros r sk Hr Hin. apply in_map_iff in Hin. destruct Hin as [o [Hk Ho]].
      subst sk. cbn. exact (occ_facts_va_site (const_table bp fr) fr r (Index.file_nodes_file fr r Hr) o Ho).
  - intros fr sk _ Hin. apply in_map_iff in Hin. destruct Hin as [o [Hk Ho]].
    apply in_flat_map in Ho. destruct Ho as [r [Hr Ho]].
    subst sk. cbn. rewrite (occ_facts_va_site (const_table bp fr) fr r (Index.file_nodes_file fr r Hr) o Ho).
    exact (Index.file_nodes_file fr r Hr).
Qed.

(* every retained fact decomposes to the exact package file and node the one canonical builder produced it at *)
Lemma raw_facts_node (o : OccFact bp) :
  In o (raw_facts bp) -> exists fr r, In r (Index.file_nodes fr)
    /\ In o (occ_facts_va bp (neg_map bp (const_table bp fr) (Index.file_nodes fr)) (const_table bp fr) r).
Proof.
  rewrite raw_facts_flat; cbv zeta. intro Hin. apply in_flat_map in Hin. destruct Hin as [fr [_ Hin]].
  apply in_flat_map in Hin. destruct Hin as [r [Hr Ho]]. exists fr, r. split; [ exact Hr | exact Ho ].
Qed.

(* §19.3/§19.4 inverting the retained child edge: SDependent names e at the selected kind, its guard bool true *)
Lemma own_stmt_expr_dep_inv (pr : Index.Refs.ExprStmtRef idx) (val_neg app_neg : bool)
  (edge : ChildFactEdge (Index.Refs.exs_node pr) StatementKind) :
  own_stmt_expr bp pr val_neg app_neg = SDependent (DepChild edge) ->
  cfe_child_site edge = Index.Edges.ee_child (Index.Edges.exprstmt_expr pr)
  /\ ( (cfe_child_kind edge = ValueKind /\ val_neg = true)
       \/ (cfe_child_kind edge = ApplicationKind /\ val_neg = false /\ app_neg = true
           /\ Index.node_view (Index.Edges.ee_child (Index.Edges.exprstmt_expr pr)) = Index.Model.VApplication) ).
Proof.
  unfold own_stmt_expr. destruct val_neg; intro H.
  - injection H as H'. subst edge. cbn [cfe_child_site cfe_child_kind].
    split; [ reflexivity | left; split; reflexivity ].
  - assert (Hgen : forall (v : Index.Model.NodeView)
      (Hv : Index.node_view (Index.Edges.ee_child (Index.Edges.exprstmt_expr pr)) = v),
      stmt_expr_body bp pr app_neg v Hv = SDependent (DepChild edge) ->
      cfe_child_site edge = Index.Edges.ee_child (Index.Edges.exprstmt_expr pr)
      /\ ( (cfe_child_kind edge = ValueKind /\ false = true)
           \/ (cfe_child_kind edge = ApplicationKind /\ false = false /\ app_neg = true
               /\ Index.node_view (Index.Edges.ee_child (Index.Edges.exprstmt_expr pr)) = Index.Model.VApplication) )).
    { intros v Hv HH. destruct v; cbn [stmt_expr_body] in HH; try discriminate HH.
      destruct app_neg; cbn [stmt_expr_app_branch] in HH.
      - injection HH as H'. subst edge. cbn [cfe_child_site cfe_child_kind].
        split; [ reflexivity | right; repeat split; try reflexivity; exact Hv ].
      - exfalso. repeat (match goal with
          | _ : context [ match ?x with _ => _ end ] |- _ => destruct x end); discriminate HH. }
    exact (Hgen _ eq_refl H).
Qed.

(* raw_facts_node keeping the file's package membership, so a sibling child fact can be shown retained too *)
Lemma raw_facts_node_file (o : OccFact bp) :
  In o (raw_facts bp) ->
  exists fr r, In fr (flat_map BN.PI.pkg_members (BN.PI.packages s))
               /\ In r (Index.file_nodes fr)
               /\ In o (occ_facts_va bp (neg_map bp (const_table bp fr) (Index.file_nodes fr)) (const_table bp fr) r).
Proof.
  rewrite raw_facts_flat; cbv zeta. intro Hin. apply in_flat_map in Hin. destruct Hin as [fr [Hfr Hin]].
  apply in_flat_map in Hin. destruct Hin as [r [Hr Ho]]. exists fr, r. split; [exact Hfr | split; [exact Hr | exact Ho]].
Qed.

(* a retained SDependent statement fact came from the expr-statement arm: its outcome is the exact driver result *)
Lemma stmt_fact_dependent (r : Index.NodeRef idx)
  (sx : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr -> StmtOutcome bp r) (va : Collections.NodeMap.t NegCell)
  (d : Dependency bp r StatementKind) :
  In (OFStmt r (SDependent d)) (stmt_fact bp r sx va) ->
  (exists (Hv : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr), SDependent d = sx Hv) \/
  (exists nn nv (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv)),
     SDependent d = short_decl_decision bp va r nn nv Hv).
Proof.
  unfold stmt_fact.
  assert (Hgen : forall (v : Index.Model.NodeView) (H : Index.node_view r = v),
    In (OFStmt r (SDependent d)) (stmt_fact_body bp r sx va v H) ->
    (exists (Hv : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr), SDependent d = sx Hv) \/
    (exists nn nv (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv)),
       SDependent d = short_decl_decision bp va r nn nv Hv)).
  { intros v H Hin. destruct v as [na|nl|nu| |nt|nb|nc|nvv|nts|nd0|nst| |ntp|];
      cbn [stmt_fact_body] in Hin; try (exfalso; exact Hin).
    destruct nst as [ | | sn sv ]; cbn [stmt_fact_body] in Hin.
    - destruct Hin as [Heq | []]. injection Heq as Heq'.
      apply (Eqdep_dec.inj_pair2_eq_dec _ noderef_eq_dec) in Heq'. left. exists H. symmetry; exact Heq'.
    - exfalso; exact Hin.
    - destruct Hin as [Heq | []]. injection Heq as Heq'.
      apply (Eqdep_dec.inj_pair2_eq_dec _ noderef_eq_dec) in Heq'. right. exists sn, sv, H. symmetry; exact Heq'. }
  exact (Hgen (Index.node_view r) eq_refl).
Qed.

(* §12 canonical-row truth over a generic phase: a retained raw fact is exactly the own_* the builder selected *)
Lemma raw_fact_is_own (o : OccFact bp) :
  In o (raw_facts bp) ->
  match o with
  | OFValue r ov => own_verdict bp (const_table bp (Index.nr_file r)) r = Some ov
  | OFApp r oa => exists H : Index.node_view r = Index.Model.VApplication, oa = own_app bp (Index.Refs.mkAppRef r H)
  | OFStmt r os => In (OFStmt r os)
      (stmt_fact bp r (expr_sx_va bp (neg_map bp (const_table bp (Index.nr_file r)) (Index.file_nodes (Index.nr_file r))) r) (neg_map bp (const_table bp (Index.nr_file r)) (Index.file_nodes (Index.nr_file r))))
  | OFType r ot => exists n (H : Index.node_view r = Index.Model.VTypeExpr (Syntax.NamedType n)),
      ot = own_type bp r n H
  end.
Proof.
  intro Hin.
  destruct (raw_facts_node o Hin) as [fr [r [Hr Ho]]]. pose proof (Index.file_nodes_file fr r Hr) as Hfile.
  destruct (is_name_head r) eqn:Hnh.
  { rewrite (occ_facts_va_name_head bp (const_table bp fr) fr r Hnh) in Ho. inversion Ho. }
  destruct (operand_only bp (const_table bp fr) r) eqn:Hoo;
  unfold occ_facts_va, retained_value_row, retains_value_fact in Ho;
  destruct (Index.node_view r) as [n|l|u| |[nt]|b|c|v|ts|d|st| |tp| ] eqn:E; cbn [retains_value_fact_view] in Ho;
    try (rewrite (va_value_row_at bp (const_table bp fr) fr r Hnh Hoo Hfile) in Ho);
    try (rewrite (va_value_row_operand bp (const_table bp fr) r Hoo) in Ho);
    try (rewrite (va_app_row_at bp (const_table bp fr) fr r Hfile E) in Ho);
    try (rewrite (type_fact_at bp r nt E) in Ho);
    try (destruct (stmt_fact_content bp r _ _ _ (Index.node_view r) eq_refl Ho) as [[os Hos] _]; subst o; rewrite Hfile; exact Ho);
    cbn in Ho; repeat (destruct Ho as [Ho|Ho]); try (exfalso; exact Ho);
    subst o; cbn; rewrite ?Hfile; try reflexivity.
  all: solve [ exists E; reflexivity | exists nt, E; reflexivity | exact (verdict_of_not_operand bp _ r Hoo) ].
Qed.

End FactBuilderLaws.

(* the exact retained package decisions of one Result: its canonical preflight and per-package main rule, projected *)
Definition result_preflight {p} (r : Result p) : FreshBuildDisposition (res_surface r) := proj1_sig (res_pkg r).
Definition result_package_rule {p} (r : Result p) (pr : BN.PI.PackageRef (res_surface r)) : BN.MainStatus (res_surface r) pr :=
  BN.package_main (res_binds r) pr.

(* an exact missing-main case of one Result: a package whose canonical main decision IS MainMissing, proof retained *)
Record MissingMainRef {p} (r : Result p) : Type := mk_missing_main_ref {
  mmr_package : BN.PI.PackageRef (res_surface r) ;
  mmr_case    : result_package_rule r mmr_package = BN.MainMissing
}.
Arguments mk_missing_main_ref {p r} _ _.
Arguments mmr_package {p r} _. Arguments mmr_case {p r} _.

(* an exact output-collision case of one Result: the exact retained preflight IS FreshCollision at that package+root *)
Record CollisionRef {p} (r : Result p) : Type := mk_collision_ref {
  cr_package : BN.PI.PackageRef (res_surface r) ;
  cr_root    : BN.PI.RootEntryRef (res_index r) ;
  cr_case    : result_preflight r = FreshCollision cr_package cr_root
}.
Arguments mk_collision_ref {p r} _ _ _.
Arguments cr_package {p r} _. Arguments cr_root {p r} _. Arguments cr_case {p r} _.

Section PackageCases.
Context {p : Syntax.Program} (r : Result p).

(* the exact missing-main case at a package, when its canonical status is MainMissing; other statuses yield none *)
Definition mm_of (pr : BN.PI.PackageRef (res_surface r)) (st : BN.MainStatus (res_surface r) pr)
  : result_package_rule r pr = st -> list (MissingMainRef r) :=
  match st as st0 return result_package_rule r pr = st0 -> list (MissingMainRef r) with
  | BN.MainMissing => fun H => [mk_missing_main_ref pr H]
  | _ => fun _ => []
  end.
Definition result_missing_main_refs : list (MissingMainRef r) :=
  flat_map (fun pr => mm_of pr (result_package_rule r pr) eq_refl) (BN.PI.packages (res_surface r)).

(* the exact collision case, when the retained preflight IS a collision; FreshOk yields none *)
Definition coll_of (d : FreshBuildDisposition (res_surface r)) : result_preflight r = d -> option (CollisionRef r) :=
  match d as d0 return result_preflight r = d0 -> option (CollisionRef r) with
  | FreshOk => fun _ => None
  | FreshCollision pr rr => fun H => Some (mk_collision_ref pr rr H)
  end.
Definition result_collision_ref : option (CollisionRef r) := coll_of (result_preflight r) eq_refl.

(* the boolean the missing-main enumeration selects on: exactly the MainMissing decision at a package *)
Definition is_missing (pr : BN.PI.PackageRef (res_surface r)) : bool :=
  match result_package_rule r pr with BN.MainMissing => true | _ => false end.
(* mm_of projects to exactly [pr] on the MainMissing decision, and to nothing on MainOne / MainMultiple *)
Lemma mm_of_package (pr : BN.PI.PackageRef (res_surface r)) (st : BN.MainStatus (res_surface r) pr)
  (H : result_package_rule r pr = st) :
  map mmr_package (mm_of pr st H) = match st with BN.MainMissing => [pr] | _ => [] end.
Proof. destruct st; reflexivity. Qed.

(* §11.1/§19.1 the missing-main packages are exactly the MainMissing packages of packages s, in package order *)
Lemma missing_main_packages : map mmr_package result_missing_main_refs = filter is_missing (BN.PI.packages (res_surface r)).
Proof.
  unfold result_missing_main_refs. rewrite BN.map_flat_map.
  apply flat_map_match_filter. intro pr. rewrite mm_of_package. unfold is_missing.
  destruct (result_package_rule r pr); reflexivity.
Qed.
(* §19.1 soundness: every retained missing-main ref carries the exact MainMissing decision of its package *)
Lemma missing_main_sound (mmr : MissingMainRef r) : result_package_rule r (mmr_package mmr) = BN.MainMissing.
Proof. exact (mmr_case mmr). Qed.
(* §19.1 a MainOne or MainMultiple package can never inhabit MissingMainRef: its exact decision is not MainMissing *)
Lemma no_missing_of_main_one (mmr : MissingMainRef r) (e : BN.Est (res_surface r)) :
  result_package_rule r (mmr_package mmr) = BN.MainOne e -> False.
Proof. intro H. rewrite (mmr_case mmr) in H. discriminate H. Qed.
Lemma no_missing_of_main_multiple (mmr : MissingMainRef r) (a b : BN.Est (res_surface r)) (rest : list (BN.Est (res_surface r))) :
  result_package_rule r (mmr_package mmr) = BN.MainMultiple a b rest -> False.
Proof. intro H. rewrite (mmr_case mmr) in H. discriminate H. Qed.
(* §11.1/§19.1 completeness: a MainMissing package appears exactly once among the enumerated missing-main packages *)
Lemma missing_main_complete (pr : BN.PI.PackageRef (res_surface r)) :
  In pr (BN.PI.packages (res_surface r)) -> result_package_rule r pr = BN.MainMissing ->
  In pr (map mmr_package result_missing_main_refs).
Proof.
  intros Hin Hmm. rewrite missing_main_packages. apply filter_In. split; [exact Hin | unfold is_missing; rewrite Hmm; reflexivity].
Qed.
(* §11.1/§19.1 no duplicate package among the missing-main refs *)
Lemma missing_main_nodup : NoDup (map mmr_package result_missing_main_refs).
Proof. rewrite missing_main_packages. apply nodup_filter. apply BN.packages_nodup. Qed.

(* §11.2/§19.2 a collision ref exists exactly when the exact retained preflight is a collision at that package+root *)
Lemma coll_of_none (d : FreshBuildDisposition (res_surface r)) (H : result_preflight r = d) : coll_of d H = None <-> d = FreshOk.
Proof. destruct d; cbn; split; solve [ reflexivity | discriminate | intro; reflexivity ]. Qed.
Lemma collision_ref_none : result_collision_ref = None <-> result_preflight r = FreshOk.
Proof. exact (coll_of_none (result_preflight r) eq_refl). Qed.
(* §19.2 soundness: a collision ref carries the exact FreshCollision decision at its exact package and root *)
Lemma collision_case (cr : CollisionRef r) : result_preflight r = FreshCollision (cr_package cr) (cr_root cr).
Proof. exact (cr_case cr). Qed.
(* §19.2 a FreshCollision preflight yields a collision ref (not None) *)
Lemma collision_ref_of_fresh (pr : BN.PI.PackageRef (res_surface r)) (rr : BN.PI.RootEntryRef (res_index r)) :
  result_preflight r = FreshCollision pr rr -> result_collision_ref <> None.
Proof. intros Hf Hn. apply collision_ref_none in Hn. rewrite Hf in Hn. discriminate Hn. Qed.
(* §19.2 the collision case is unique: any two collision refs name the same exact package and root *)
Lemma collision_unique (cr1 cr2 : CollisionRef r) :
  cr_package cr1 = cr_package cr2 /\ cr_root cr1 = cr_root cr2.
Proof.
  pose proof (cr_case cr1) as H1. pose proof (cr_case cr2) as H2. rewrite H1 in H2. injection H2 as Hp Hr.
  split; [ exact Hp | exact Hr ].
Qed.

End PackageCases.
Arguments mm_of {p r} pr st H.
Arguments coll_of {p r} d H.
Arguments is_missing {p r} pr.

(* the exact retained fact list of one Result: the canonical row list its res_facts holds, projected once *)
Definition result_fact_list {p} (r : Result p) : list (OccFact (res_binds r)) := proj1_sig (res_facts r).

Section FactRow.
Context {p : Syntax.Program} (r : Result p).
Let idx := res_index r.
Let bp  := res_binds r.

(* an exact retained fact-row identity of r: an ordinal into result_fact_list r with the exact row retained there *)
Record FactRowRef : Type := mk_frr {
  frr_ord : nat ;
  frr_row : OccFact bp ;
  frr_at  : nth_error (result_fact_list r) frr_ord = Some frr_row
}.
Definition frr_site (ref : FactRowRef) : Index.NodeRef idx := fact_site (frr_row ref).
Definition frr_kind (ref : FactRowRef) : FactKind := fact_kind (frr_row ref).
Definition frr_family (ref : FactRowRef) : Family := fact_family (frr_row ref).

(* the exact row at ordinal k: retains the row and its membership proof; None ordinals yield no ref *)
Definition row_of (k : nat) (o : option (OccFact bp)) : nth_error (result_fact_list r) k = o -> list FactRowRef :=
  match o with Some x => fun H => [mk_frr k x H] | None => fun _ => [] end.

(* canonical ordered row enumeration; the row list is bound once so vm_compute shares one analysis, never per-ordinal *)
Definition fact_rows : list FactRowRef :=
  let facts := result_fact_list r in
  flat_map (fun k => row_of k (nth_error facts k) eq_refl) (seq 0%nat (List.length facts)).

(* an exact invalid fact ref: a retained row whose exact retained outcome is the invalid case, carrying its cause *)
Record InvalidFactRef : Type := mk_ifr {
  ifr_rowref : FactRowRef ;
  ifr_cause  : Cause bp (fact_site (frr_row ifr_rowref)) (fact_kind (frr_row ifr_rowref)) ;
  ifr_ok     : occ_cause (frr_row ifr_rowref) = Some ifr_cause
}.
Definition ifr_fact (ir : InvalidFactRef) : OccFact bp := frr_row (ifr_rowref ir).
Definition ifr_ord (ir : InvalidFactRef) : nat := frr_ord (ifr_rowref ir).

(* an exact unmet fact ref: a retained row whose exact retained outcome is the unmet case, carrying its requirement *)
Record UnmetFactRef : Type := mk_ufr {
  ufr_rowref : FactRowRef ;
  ufr_req    : Requirement bp (fact_site (frr_row ufr_rowref)) (fact_kind (frr_row ufr_rowref)) ;
  ufr_ok     : occ_req (frr_row ufr_rowref) = Some ufr_req
}.
Definition ufr_fact (ur : UnmetFactRef) : OccFact bp := frr_row (ufr_rowref ur).
Definition ufr_ord (ur : UnmetFactRef) : nat := frr_ord (ufr_rowref ur).

(* an exact dependent fact ref: a retained row whose exact outcome is the dependent case; yields no issue row *)
Record DependentFactRef : Type := mk_dfr {
  dfr_rowref : FactRowRef ;
  dfr_dep    : Dependency bp (fact_site (frr_row dfr_rowref)) (fact_kind (frr_row dfr_rowref)) ;
  dfr_ok     : occ_dep (frr_row dfr_rowref) = Some dfr_dep
}.
Definition dfr_fact (dr : DependentFactRef) : OccFact bp := frr_row (dfr_rowref dr).
Definition dfr_ord (dr : DependentFactRef) : nat := frr_ord (dfr_rowref dr).

End FactRow.
Arguments mk_frr {p r} _ _ _.
Arguments frr_ord {p r} _. Arguments frr_row {p r} _. Arguments frr_at {p r} _.
Arguments frr_site {p r} _. Arguments frr_kind {p r} _. Arguments frr_family {p r} _.
Arguments row_of {p r} k o H.
Arguments mk_ifr {p r} _ _ _.
Arguments ifr_rowref {p r} _. Arguments ifr_cause {p r} _. Arguments ifr_ok {p r} _.
Arguments ifr_fact {p r} _. Arguments ifr_ord {p r} _.
Arguments mk_ufr {p r} _ _ _.
Arguments ufr_rowref {p r} _. Arguments ufr_req {p r} _. Arguments ufr_ok {p r} _.
Arguments ufr_fact {p r} _. Arguments ufr_ord {p r} _.
Arguments mk_dfr {p r} _ _ _.
Arguments dfr_rowref {p r} _. Arguments dfr_dep {p r} _. Arguments dfr_ok {p r} _.
Arguments dfr_fact {p r} _. Arguments dfr_ord {p r} _.

(* §10 canonical row enumeration laws: the enumeration IS exactly fact_list fp, once, in retained order *)
Section FactRowLaws.
Context {p : Syntax.Program} (res : Result p).

Lemma map_flat_map_rows {A B C} (f : B -> C) (g : A -> list B) (l : list A) :
  map f (flat_map g l) = flat_map (fun x => map f (g x)) l.
Proof. induction l as [|a l' IH]; [reflexivity|]. cbn. rewrite map_app, IH. reflexivity. Qed.
Lemma flat_map_ext_rows {A B} (f g : A -> list B) (l : list A) (H : forall a, f a = g a) :
  flat_map f l = flat_map g l.
Proof. induction l as [|a l' IH]; [reflexivity|]. cbn. rewrite (H a), IH. reflexivity. Qed.
Lemma flat_map_map_rows {A B C} (f : B -> list C) (g : A -> B) (l : list A) :
  flat_map f (map g l) = flat_map (fun x => f (g x)) l.
Proof. induction l as [|a l' IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma opt_flatmap_full {A} (L : list A) :
  flat_map (fun k => match nth_error L k with Some x => [x] | None => [] end) (seq 0 (List.length L)) = L.
Proof.
  induction L as [|a L' IH]; [reflexivity|].
  cbn [List.length seq flat_map nth_error app]. f_equal.
  rewrite <- seq_shift, flat_map_map_rows. exact IH.
Qed.
Lemma idx_flatmap_all {A} (L : list A) (ks : list nat) (Hall : forall k, In k ks -> (k < List.length L)%nat) :
  flat_map (fun k => match nth_error L k with Some _ => [k] | None => [] end) ks = ks.
Proof.
  induction ks as [|k ks' IH]; [reflexivity|]. cbn [flat_map].
  destruct (nth_error L k) as [x|] eqn:E.
  - cbn [app]. f_equal. apply IH. intros k' Hk'. apply Hall. right; exact Hk'.
  - exfalso. apply nth_error_None in E. specialize (Hall k (or_introl eq_refl)). lia.
Qed.

(* row_of at ordinal k projects to the exact row (its element) and to the exact ordinal k *)
Lemma row_of_row (k : nat) (o : option (OccFact (res_binds res))) (H : nth_error (result_fact_list res) k = o) :
  map frr_row (row_of k o H) = match o with Some x => [x] | None => [] end.
Proof. destruct o; reflexivity. Qed.
Lemma row_of_ord (k : nat) (o : option (OccFact (res_binds res))) (H : nth_error (result_fact_list res) k = o) :
  map frr_ord (row_of k o H) = match o with Some _ => [k] | None => [] end.
Proof. destruct o; reflexivity. Qed.
(* nth_error into seq start n at a valid ordinal is exactly Some (start + k) *)
Lemma seq_nth_error_id (n : nat) : forall (start k : nat), (k < n)%nat -> nth_error (seq start n) k = Some (start + k)%nat.
Proof.
  induction n as [|n' IH]; intros start k Hk; [ lia | ].
  destruct k as [|k']; cbn [seq nth_error].
  - f_equal; lia.
  - rewrite IH by lia. f_equal; lia.
Qed.

(* §10 the retained rows project exactly to result_fact_list res, in retained order; the ordinals are exactly seq 0 n *)
Lemma fact_rows_rows : map frr_row (fact_rows res) = result_fact_list res.
Proof.
  unfold fact_rows; cbv zeta. rewrite map_flat_map_rows.
  rewrite (flat_map_ext_rows _ (fun k => match nth_error (result_fact_list res) k with Some x => [x] | None => [] end))
    by (intro k; apply row_of_row).
  apply opt_flatmap_full.
Qed.
Lemma fact_rows_ords : map frr_ord (fact_rows res) = seq 0 (List.length (result_fact_list res)).
Proof.
  unfold fact_rows; cbv zeta. rewrite map_flat_map_rows.
  rewrite (flat_map_ext_rows _ (fun k => match nth_error (result_fact_list res) k with Some _ => [k] | None => [] end))
    by (intro k; apply row_of_ord).
  apply idx_flatmap_all. intros k Hk. apply in_seq in Hk. lia.
Qed.
(* §10 ordinal identity: the row ordinals are duplicate-free *)
Lemma fact_rows_ord_nodup : NoDup (map frr_ord (fact_rows res)).
Proof. rewrite fact_rows_ords. apply seq_NoDup. Qed.
(* §10 completeness + positional uniqueness: every list member is enumerated at its exact position, retaining it *)
Lemma fact_rows_complete (k : nat) (row : OccFact (res_binds res)) (Hk : nth_error (result_fact_list res) k = Some row) :
  exists ref, nth_error (fact_rows res) k = Some ref /\ frr_ord ref = k /\ frr_row ref = row.
Proof.
  assert (Hlt : (k < List.length (result_fact_list res))%nat) by (apply nth_error_Some; rewrite Hk; discriminate).
  destruct (nth_error (fact_rows res) k) as [ref|] eqn:E.
  2:{ exfalso. apply nth_error_None in E. rewrite <- (length_map frr_row), fact_rows_rows in E. lia. }
  exists ref. split; [reflexivity | split].
  - assert (Ho : nth_error (seq 0 (List.length (result_fact_list res))) k = Some (frr_ord ref))
      by (rewrite <- fact_rows_ords, nth_error_map, E; reflexivity).
    rewrite (seq_nth_error_id (List.length (result_fact_list res)) 0 k Hlt) in Ho. injection Ho as Ho. lia.
  - assert (Hr : nth_error (result_fact_list res) k = Some (frr_row ref))
      by (rewrite <- fact_rows_rows, nth_error_map, E; reflexivity).
    rewrite Hk in Hr. injection Hr as Hr. symmetry. exact Hr.
Qed.

(* §11 the exact canonical row key of a retained row: the occurrence's exact site paired with its exact fact kind *)
Definition frr_key (ref : FactRowRef res) : Index.NodeRef (res_index res) * FactKind := fact_key (frr_row ref).


(* the retained fact list, and the row enumeration, inherit the duplicate-free site+kind key *)
Lemma fact_list_key_nodup : NoDup (map fact_key (result_fact_list res)).
Proof. unfold result_fact_list. rewrite fact_once. apply raw_facts_key_nodup. Qed.
Lemma fact_rows_key_nodup : NoDup (map frr_key (fact_rows res)).
Proof. unfold frr_key. rewrite <- map_map, fact_rows_rows. apply fact_list_key_nodup. Qed.
(* §24.2 row uniqueness: two retained rows with equal site and equal kind are the same exact row *)
Lemma fact_row_key_unique (r1 r2 : FactRowRef res) :
  In r1 (fact_rows res) -> In r2 (fact_rows res) -> frr_site r1 = frr_site r2 -> frr_kind r1 = frr_kind r2 -> r1 = r2.
Proof.
  intros H1 H2 Hs Hk. apply (nodup_map_inj frr_key (fact_rows res) fact_rows_key_nodup r1 r2 H1 H2).
  change (frr_key r1) with (frr_site r1, frr_kind r1). change (frr_key r2) with (frr_site r2, frr_kind r2).
  rewrite Hs, Hk. reflexivity.
Qed.

(* a decidable fact-kind equality, so the site+kind lookup is a total boolean search over the retained rows *)
Definition fact_kind_eqb (a b : FactKind) : bool :=
  match a, b with
  | ValueKind, ValueKind | ApplicationKind, ApplicationKind
  | StatementKind, StatementKind | TypeUseKind, TypeUseKind => true
  | _, _ => false
  end.
Lemma fact_kind_eqb_spec (a b : FactKind) : fact_kind_eqb a b = true <-> a = b.
Proof. destruct a, b; cbn; split; intro H; solve [ discriminate H | reflexivity ]. Qed.

(* §11 canonical site+kind lookup: search the retained rows only; never rebuild an outcome through own_* *)
Definition fact_row_for (site : Index.NodeRef (res_index res)) (kind : FactKind) : option (FactRowRef res) :=
  find (fun ref => andb (BN.noderef_eqb (frr_site ref) site) (fact_kind_eqb (frr_kind ref) kind)) (fact_rows res).

(* §24.2 soundness: a found row is a retained row with exactly the requested site and kind *)
Lemma fact_row_for_sound (site : Index.NodeRef (res_index res)) (kind : FactKind) (ref : FactRowRef res) :
  fact_row_for site kind = Some ref -> In ref (fact_rows res) /\ frr_site ref = site /\ frr_kind ref = kind.
Proof.
  intro H. apply find_some in H. destruct H as [Hin Hp]. apply andb_prop in Hp. destruct Hp as [Hs Hk].
  apply BN.noderef_eqb_spec in Hs. apply fact_kind_eqb_spec in Hk. split; [ exact Hin | split; [ exact Hs | exact Hk ] ].
Qed.
(* §24.2 completeness: any retained row with that site and kind is exactly the one the lookup returns *)
Lemma fact_row_for_complete (site : Index.NodeRef (res_index res)) (kind : FactKind) (ref : FactRowRef res) :
  In ref (fact_rows res) -> frr_site ref = site -> frr_kind ref = kind -> fact_row_for site kind = Some ref.
Proof.
  intros Hin Hs Hk. destruct (fact_row_for site kind) as [ref'|] eqn:E.
  - f_equal. apply fact_row_for_sound in E. destruct E as [Hin' [Hs' Hk']].
    apply (fact_row_key_unique ref' ref Hin' Hin); [ rewrite Hs', Hs; reflexivity | rewrite Hk', Hk; reflexivity ].
  - exfalso. unfold fact_row_for in E. pose proof (find_none _ _ E ref Hin) as Hno. cbv beta in Hno.
    rewrite (proj2 (BN.noderef_eqb_spec (frr_site ref) site) Hs) in Hno.
    rewrite (proj2 (fact_kind_eqb_spec (frr_kind ref) kind) Hk) in Hno. discriminate Hno.
Qed.
(* §24.2 None soundness: no retained row of that exact site and kind means the lookup is None *)
Lemma fact_row_for_none (site : Index.NodeRef (res_index res)) (kind : FactKind) :
  (forall ref, In ref (fact_rows res) -> ~ (frr_site ref = site /\ frr_kind ref = kind)) -> fact_row_for site kind = None.
Proof.
  intro Hno. destruct (fact_row_for site kind) as [ref|] eqn:E; [ | reflexivity ].
  exfalso. apply fact_row_for_sound in E. destruct E as [Hin [Hs Hk]]. exact (Hno ref Hin (conj Hs Hk)).
Qed.
(* §24.2 None completeness: a None lookup means no retained row carries that exact site and kind *)
Lemma fact_row_for_none_inv (site : Index.NodeRef (res_index res)) (kind : FactKind) (ref : FactRowRef res) :
  fact_row_for site kind = None -> In ref (fact_rows res) -> ~ (frr_site ref = site /\ frr_kind ref = kind).
Proof.
  intros E Hin [Hs Hk]. pose proof (fact_row_for_complete site kind ref Hin Hs Hk) as Hc. rewrite E in Hc. discriminate.
Qed.
(* §24.2 non-conflation: an application site's Application-key and Value-key lookups return two distinct rows *)
Lemma fact_row_for_kind_distinct (site : Index.NodeRef (res_index res)) (r1 r2 : FactRowRef res) :
  fact_row_for site ApplicationKind = Some r1 -> fact_row_for site ValueKind = Some r2 -> r1 <> r2.
Proof.
  intros H1 H2 Heq. apply fact_row_for_sound in H1. apply fact_row_for_sound in H2.
  destruct H1 as [_ [_ Hk1]]. destruct H2 as [_ [_ Hk2]]. subst r2. rewrite Hk1 in Hk2. discriminate.
Qed.

(* §12 canonical-row truth: a retained row's exact outcome is the own_* result the one canonical builder selected *)
Lemma fact_row_is_own (ref : FactRowRef res) :
  match frr_row ref with
  | OFValue r ov => own_verdict (res_binds res) (const_table (res_binds res) (Index.nr_file r)) r = Some ov
  | OFApp r oa => exists H : Index.node_view r = Index.Model.VApplication, oa = own_app (res_binds res) (Index.Refs.mkAppRef r H)
  | OFStmt r os => In (OFStmt r os)
      (stmt_fact (res_binds res) r (expr_sx_va (res_binds res) (neg_map (res_binds res) (const_table (res_binds res) (Index.nr_file r)) (Index.file_nodes (Index.nr_file r))) r)
        (neg_map (res_binds res) (const_table (res_binds res) (Index.nr_file r)) (Index.file_nodes (Index.nr_file r))))
  | OFType r ot => exists n (H : Index.node_view r = Index.Model.VTypeExpr (Syntax.NamedType n)),
      ot = own_type (res_binds res) r n H
  end.
Proof.
  destruct ref as [k o Hat]; cbn [frr_row].
  assert (Hin : In o (raw_facts (res_binds res))) by (rewrite <- (fact_once (res_binds res) (res_facts res)); exact (nth_error_In _ _ Hat)).
  exact (raw_fact_is_own o Hin).
Qed.
(* §12 no false peer: the only retained fact at an exact site+kind is that one; no fabricated peer joins the list *)
Lemma no_false_row (o o' : OccFact (res_binds res)) :
  In o (result_fact_list res) -> In o' (result_fact_list res) -> fact_site o' = fact_site o -> fact_kind o' = fact_kind o -> o' = o.
Proof.
  intros Ho Ho' Hs Hk. apply (nodup_map_inj fact_key (result_fact_list res) fact_list_key_nodup o' o Ho' Ho).
  exact (f_equal2 (@pair _ _) Hs Hk).
Qed.
(* §24.3 a row with no retained cause admits no invalid-case ref: a success/nonconstant row is never invalid *)
Lemma no_invalid_of_no_cause (ref : FactRowRef res) (ir : InvalidFactRef res) :
  ifr_rowref ir = ref -> occ_cause (frr_row ref) = None -> False.
Proof. intros Href Hnone. subst ref. pose proof (ifr_ok ir) as Hok. rewrite Hnone in Hok. discriminate Hok. Qed.
(* §24.3 a row with no retained requirement admits no unmet-case ref: a success/nonconstant row is never unmet *)
Lemma no_unmet_of_no_req (ref : FactRowRef res) (ur : UnmetFactRef res) :
  ufr_rowref ur = ref -> occ_req (frr_row ref) = None -> False.
Proof. intros Href Hnone. subst ref. pose proof (ufr_ok ur) as Hok. rewrite Hnone in Hok. discriminate Hok. Qed.

(* §13 the exact negative case of a child row, projected from that exact row: invalid, unmet, or dependent *)
Inductive NegativeFactRef (child_row : FactRowRef res) : Type :=
| ChildInvalid   : forall c : Cause (res_binds res) (frr_site child_row) (frr_kind child_row),
    occ_cause (frr_row child_row) = Some c -> NegativeFactRef child_row
| ChildUnmet     : forall rq : Requirement (res_binds res) (frr_site child_row) (frr_kind child_row),
    occ_req (frr_row child_row) = Some rq -> NegativeFactRef child_row
| ChildDependent : forall d : Dependency (res_binds res) (frr_site child_row) (frr_kind child_row),
    occ_dep (frr_row child_row) = Some d -> NegativeFactRef child_row.
Arguments ChildInvalid {child_row} _ _. Arguments ChildUnmet {child_row} _ _. Arguments ChildDependent {child_row} _ _.
(* the exact negative class, a proof-insensitive descriptive projection *)
Definition nfr_class {child_row : FactRowRef res} (n : NegativeFactRef child_row) : NegClass :=
  match n with ChildInvalid _ _ => NegInvalid | ChildUnmet _ _ => NegUnmet | ChildDependent _ _ => NegDependent end.
(* the exact negative case of a retained row, projected from its own outcome; none for a success/nonconstant row *)
Definition negative_case (child_row : FactRowRef res) : option (NegativeFactRef child_row) :=
  match occ_cause (frr_row child_row) as oc return occ_cause (frr_row child_row) = oc -> option (NegativeFactRef child_row) with
  | Some c => fun H => Some (ChildInvalid c H)
  | None => fun _ =>
    match occ_req (frr_row child_row) as oq return occ_req (frr_row child_row) = oq -> option (NegativeFactRef child_row) with
    | Some rq => fun H => Some (ChildUnmet rq H)
    | None => fun _ =>
      match occ_dep (frr_row child_row) as od return occ_dep (frr_row child_row) = od -> option (NegativeFactRef child_row) with
      | Some d => fun H => Some (ChildDependent d H)
      | None => fun _ => None
      end eq_refl
    end eq_refl
  end eq_refl.

(* §14 an exact child-dependent parent: a retained statement row whose exact outcome is SDependent of a DepChild edge *)
Record ChildDependentFactRef : Type := mk_cdfr {
  cdfr_rowref : FactRowRef res ;
  cdfr_site   : Index.NodeRef (res_index res) ;
  cdfr_edge   : ChildFactEdge cdfr_site StatementKind ;
  cdfr_ok     : frr_row cdfr_rowref = OFStmt cdfr_site (SDependent (DepChild cdfr_edge))
}.
Definition cdfr_edge_site (c : ChildDependentFactRef) : Index.NodeRef (res_index res) := cfe_child_site (cdfr_edge c).
Definition cdfr_edge_kind (c : ChildDependentFactRef) : FactKind := cfe_child_kind (cdfr_edge c).
(* a statement dependency is DepChild or DepShortAmbiguous; only DepChild has a child edge — a partial projection *)
Definition dep_child_edge_opt {site : Index.NodeRef (res_index res)} (d : Dependency (res_binds res) site StatementKind) : option (ChildFactEdge site StatementKind) :=
  match d in Dependency _ _ k return (match k with StatementKind => option (ChildFactEdge site StatementKind) | _ => unit end) with
  | DepChild e => Some e | DepShortAmbiguous _ _ _ _ _ _ _ => None | _ => tt end.
Lemma dep_child_eq_some {site : Index.NodeRef (res_index res)} (d : Dependency (res_binds res) site StatementKind)
  (e : ChildFactEdge site StatementKind) : dep_child_edge_opt d = Some e -> d = DepChild e.
Proof.
  refine (match d as d0 in Dependency _ _ k
    return (match k as k0 return Dependency (res_binds res) site k0 -> Prop with
            | StatementKind => fun dd => dep_child_edge_opt dd = Some e -> dd = DepChild e | _ => fun _ => True end d0)
  with DepChild e0 => _ | DepShortAmbiguous _ _ _ _ _ _ _ => _ | _ => I end); cbn.
  - intro H. injection H as H. rewrite H. reflexivity.
  - discriminate.
Qed.
(* every child-dependent parent row is exactly a retained OFStmt at cdfr_site carrying the exact DepChild edge *)
Definition child_dep_of_body (row : FactRowRef res) (o : OccFact (res_binds res)) (Ho : frr_row row = o) : option ChildDependentFactRef :=
  match o as o0 return frr_row row = o0 -> option ChildDependentFactRef with
  | OFStmt r os =>
      match os as os0 return frr_row row = OFStmt r os0 -> option ChildDependentFactRef with
      | SDependent d =>
          match d as d0 in Dependency _ _ k
            return (match k return Dependency (res_binds res) r k -> Type with
                    | StatementKind => fun d1 => frr_row row = OFStmt r (SDependent d1) -> option ChildDependentFactRef
                    | _ => fun _ => unit end d0) with
          | DepChild e => fun Hr => Some (mk_cdfr row r e Hr)
          | DepShortAmbiguous _ _ _ _ _ _ _ => fun _ => None
          | _ => tt
          end
      | _ => fun _ => None
      end
  | _ => fun _ => None
  end Ho.
Definition child_dep_of (row : FactRowRef res) : option ChildDependentFactRef :=
  child_dep_of_body row (frr_row row) eq_refl.
(* a child-dependent row's retained ref is exactly that row: the enumeration keeps the parent's own ordinal *)
Lemma child_dep_of_rowref (row : FactRowRef res) (cdfr : ChildDependentFactRef) :
  child_dep_of row = Some cdfr -> cdfr_rowref cdfr = row.
Proof.
  unfold child_dep_of.
  assert (Hg : forall (o : OccFact (res_binds res)) (Ho : frr_row row = o),
    child_dep_of_body row o Ho = Some cdfr -> cdfr_rowref cdfr = row).
  { intros o Ho Heq. destruct o as [r ov|r oa|r os|r ot]; try (cbn [child_dep_of_body] in Heq; discriminate Heq).
    destruct os as [ | | | d ]; try (cbn [child_dep_of_body] in Heq; discriminate Heq).
    generalize dependent Ho.
    refine (match d as d0 in Dependency _ _ k
      return (match k return Dependency (res_binds res) r k -> Prop with
              | StatementKind => fun d1 => forall (Ho1 : frr_row row = OFStmt r (SDependent d1)),
                  child_dep_of_body row (OFStmt r (SDependent d1)) Ho1 = Some cdfr -> cdfr_rowref cdfr = row
              | _ => fun _ => True end d0)
      with DepChild e => _ | DepShortAmbiguous _ _ _ _ _ _ _ => _ | _ => I end);
      intros Ho1 Heq1; cbn [child_dep_of_body] in Heq1; try discriminate Heq1.
    injection Heq1 as Heq1. subst cdfr. reflexivity. }
  exact (Hg (frr_row row) eq_refl).
Qed.

(* §15 the central relation: the parent's retained edge names the exact child fact_row_for finds, + its negative case *)
Record ChildPrerequisiteRef (cdfr : ChildDependentFactRef) : Type := mk_cpr {
  cpr_child_row : FactRowRef res ;
  cpr_lookup    : fact_row_for (cdfr_edge_site cdfr) (cdfr_edge_kind cdfr) = Some cpr_child_row ;
  cpr_neg       : NegativeFactRef cpr_child_row
}.
(* §15 the one total builder from the exact parent child-dependency view: look up the exact child, retain its case *)
Definition child_prerequisite_body (cdfr : ChildDependentFactRef) (fr : option (FactRowRef res))
  (Hfr : fact_row_for (cdfr_edge_site cdfr) (cdfr_edge_kind cdfr) = fr) : option (ChildPrerequisiteRef cdfr) :=
  match fr as fr0 return fact_row_for (cdfr_edge_site cdfr) (cdfr_edge_kind cdfr) = fr0 -> option (ChildPrerequisiteRef cdfr) with
  | Some child_row => fun Hlk =>
      match negative_case child_row with Some neg => Some (mk_cpr cdfr child_row Hlk neg) | None => None end
  | None => fun _ => None
  end Hfr.
Definition child_prerequisite (cdfr : ChildDependentFactRef) : option (ChildPrerequisiteRef cdfr) :=
  child_prerequisite_body cdfr (fact_row_for (cdfr_edge_site cdfr) (cdfr_edge_kind cdfr)) eq_refl.

(* §16 the canonical ordered prerequisites: one per child-dependent parent row, in retained fact-row order *)
Definition child_prerequisite_refs : list { cdfr : ChildDependentFactRef & ChildPrerequisiteRef cdfr } :=
  flat_map (fun row => match child_dep_of row with
    | Some cdfr => match child_prerequisite cdfr with Some cpr => [existT _ cdfr cpr] | None => [] end
    | None => [] end) (fact_rows res).


(* a retained row's own file: its package membership, exact file, and the node the one builder produced it at *)
Lemma row_file (row : FactRowRef res) :
  In row (fact_rows res) ->
  exists fr, In fr (flat_map BN.PI.pkg_members (BN.PI.packages (res_surface res)))
             /\ Index.nr_file (frr_site row) = fr
             /\ In (frr_row row)
                  (occ_facts_va (res_binds res) (neg_map (res_binds res) (const_table (res_binds res) fr) (Index.file_nodes fr)) (const_table (res_binds res) fr) (frr_site row)).
Proof.
  intro Hin. assert (Hil : In (frr_row row) (result_fact_list res))
    by (rewrite <- fact_rows_rows; apply in_map; exact Hin).
  unfold result_fact_list in Hil. rewrite fact_once in Hil. destruct (raw_facts_node_file (frr_row row) Hil) as [fr [r' [Hfr [Hr' Ho]]]].
  pose proof (occ_facts_va_site (const_table (res_binds res) fr) fr r' (Index.file_nodes_file fr r' Hr') (frr_row row) Ho) as Hsite.
  exists fr. unfold frr_site. rewrite Hsite. split; [exact Hfr | split].
  - exact (Index.file_nodes_file fr r' Hr').
  - exact Ho.
Qed.
(* a negative value child's exact value fact is retained in the same FactPhase, in its own file *)
Lemma value_fact_retained (fr : Index.FileRef (res_index res))
  (Hfr : In fr (flat_map BN.PI.pkg_members (BN.PI.packages (res_surface res))))
  (e : Index.NodeRef (res_index res)) (Hnh : is_name_head e = false) (He : Index.nr_file e = fr)
  (Hneg : value_neg_b (res_binds res) (own_value (res_binds res) (const_table (res_binds res) fr) e) = true) :
  In (OFValue e (own_value (res_binds res) (const_table (res_binds res) fr) e)) (result_fact_list res).
Proof.
  unfold result_fact_list; rewrite fact_once; rewrite raw_facts_flat; cbv zeta. apply in_flat_map. exists fr. split; [exact Hfr|].
  apply in_flat_map. exists e. split;
    [ exact (file_nodes_complete fr e He) | apply (occ_value_mem (res_binds res) (const_table (res_binds res) fr) fr e Hnh He); exact Hneg ].
Qed.
(* a negative application child's exact application fact is retained in the same FactPhase, in its own file *)
Lemma app_fact_retained (fr : Index.FileRef (res_index res))
  (Hfr : In fr (flat_map BN.PI.pkg_members (BN.PI.packages (res_surface res))))
  (e : Index.NodeRef (res_index res)) (He : Index.nr_file e = fr) (Hva : Index.node_view e = Index.Model.VApplication) :
  In (OFApp e (own_app (res_binds res) (Index.Refs.mkAppRef e Hva))) (result_fact_list res).
Proof.
  unfold result_fact_list; rewrite fact_once; rewrite raw_facts_flat; cbv zeta. apply in_flat_map. exists fr. split; [exact Hfr|].
  apply in_flat_map. exists e. split;
    [ exact (file_nodes_complete fr e He) | apply (occ_app_mem (res_binds res) (const_table (res_binds res) fr) fr e He Hva) ].
Qed.
(* a short statement node's exact canonical decision is retained as its exact statement fact in its own file *)
Lemma stmt_fact_retained (fr : Index.FileRef (res_index res))
  (Hfr : In fr (flat_map BN.PI.pkg_members (BN.PI.packages (res_surface res))))
  (e : Index.NodeRef (res_index res)) (He : Index.nr_file e = fr) (nn nv : nat)
  (Hv : Index.node_view e = Index.Model.VStmt (Index.Model.SSShort nn nv)) :
  In (OFStmt e (short_decl_decision (res_binds res)
       (neg_map (res_binds res) (const_table (res_binds res) fr) (Index.file_nodes fr)) e nn nv Hv))
     (result_fact_list res).
Proof.
  unfold result_fact_list; rewrite fact_once; rewrite raw_facts_flat; cbv zeta. apply in_flat_map. exists fr. split; [exact Hfr|].
  apply in_flat_map. exists e. split;
    [ exact (file_nodes_complete fr e He) | apply (occ_stmt_mem (res_binds res) (const_table (res_binds res) fr) fr e He nn nv Hv) ].
Qed.
(* a negative value / application outcome makes one of the row's own cause/req/dep present *)
Lemma value_neg_disj (child_row : FactRowRef res) (e : Index.NodeRef (res_index res)) (ov : ValueOutcome (res_binds res) e)
  (Hrow : frr_row child_row = OFValue e ov) (Hneg : value_neg_b (res_binds res) ov = true) :
  occ_cause (frr_row child_row) <> None \/ occ_req (frr_row child_row) <> None \/ occ_dep (frr_row child_row) <> None.
Proof.
  rewrite Hrow. destruct ov; cbn in Hneg |- *; try discriminate Hneg;
    first [ left; discriminate | right; left; discriminate | right; right; discriminate ].
Qed.
Lemma app_neg_disj (child_row : FactRowRef res) (e : Index.NodeRef (res_index res)) (oa : AppOutcome (res_binds res) e)
  (Hrow : frr_row child_row = OFApp e oa) (Hneg : app_neg_b (res_binds res) oa = true) :
  occ_cause (frr_row child_row) <> None \/ occ_req (frr_row child_row) <> None \/ occ_dep (frr_row child_row) <> None.
Proof.
  rewrite Hrow. destruct oa; cbn in Hneg |- *; try discriminate Hneg;
    first [ left; discriminate | right; left; discriminate | right; right; discriminate ].
Qed.
(* §19.4/§19.5 a row with a present cause/req/dep has an exact negative case *)
Lemma negative_case_some (child_row : FactRowRef res)
  (H : occ_cause (frr_row child_row) <> None \/ occ_req (frr_row child_row) <> None
       \/ occ_dep (frr_row child_row) <> None) :
  negative_case child_row <> None.
Proof.
  unfold negative_case.
  assert (Hg : forall
    (oc : option (Cause (res_binds res) (fact_site (frr_row child_row)) (fact_kind (frr_row child_row))))
    (Hoc : occ_cause (frr_row child_row) = oc)
    (oq : option (Requirement (res_binds res) (fact_site (frr_row child_row)) (fact_kind (frr_row child_row))))
    (Hoq : occ_req (frr_row child_row) = oq)
    (od : option (Dependency (res_binds res) (fact_site (frr_row child_row)) (fact_kind (frr_row child_row))))
    (Hod : occ_dep (frr_row child_row) = od),
    (oc <> None \/ oq <> None \/ od <> None) ->
    (match oc as oc0 return occ_cause (frr_row child_row) = oc0 -> option (NegativeFactRef child_row) with
     | Some c => fun H0 => Some (ChildInvalid c H0)
     | None => fun _ =>
       match oq as oq0 return occ_req (frr_row child_row) = oq0 -> option (NegativeFactRef child_row) with
       | Some rq => fun H0 => Some (ChildUnmet rq H0)
       | None => fun _ =>
         match od as od0 return occ_dep (frr_row child_row) = od0 -> option (NegativeFactRef child_row) with
         | Some dd => fun H0 => Some (ChildDependent dd H0)
         | None => fun _ => None
         end Hod
       end Hoq
     end Hoc) <> None).
  { intros oc Hoc oq Hoq od Hod Hd. destruct oc as [c|]; [ cbn; discriminate | cbn ].
    destruct oq as [rq|]; [ cbn; discriminate | cbn ].
    destruct od as [dd|]; [ cbn; discriminate | cbn ].
    exfalso. destruct Hd as [Hd|[Hd|Hd]]; apply Hd; reflexivity. }
  exact (Hg (occ_cause (frr_row child_row)) eq_refl (occ_req (frr_row child_row)) eq_refl
            (occ_dep (frr_row child_row)) eq_refl H).
Qed.
(* §19.4 the prerequisite builder succeeds once the exact negative child row is looked up *)
Lemma child_prerequisite_some (cdfr : ChildDependentFactRef) (child_row : FactRowRef res)
  (Hlk : fact_row_for (cdfr_edge_site cdfr) (cdfr_edge_kind cdfr) = Some child_row)
  (Hneg : negative_case child_row <> None) :
  child_prerequisite cdfr <> None.
Proof.
  unfold child_prerequisite.
  rewrite (convoy_at (fact_row_for (cdfr_edge_site cdfr) (cdfr_edge_kind cdfr))
             (child_prerequisite_body cdfr) (Some child_row) Hlk).
  cbn -[negative_case]. destruct (negative_case child_row) as [neg|] eqn:En;
    [ discriminate | exfalso; apply Hneg; reflexivity ].
Qed.
(* a retained fact of the list is exactly a retained fact-row *)
Lemma fact_list_row (o : OccFact (res_binds res)) : In o (result_fact_list res) -> exists ref, In ref (fact_rows res) /\ frr_row ref = o.
Proof.
  intro Hin. apply In_nth_error in Hin. destruct Hin as [k Hk].
  destruct (fact_rows_complete k o Hk) as [ref [Hnth [_ Hrow]]].
  exists ref. split; [ exact (nth_error_In _ _ Hnth) | exact Hrow ].
Qed.
(* §10 a policy-applicable node whose retained verdict is nonconstant has its exact VNonconst Value row in the Result *)
Lemma nonconst_value_fact_retained (fr : Index.FileRef (res_index res))
  (Hfr : In fr (flat_map BN.PI.pkg_members (BN.PI.packages (res_surface res))))
  (e : Index.NodeRef (res_index res)) (Hnh : is_name_head e = false) (He : Index.nr_file e = fr)
  (Hret : retains_value_fact e = true)
  (Hnc : own_verdict (res_binds res) (const_table (res_binds res) fr) e = Some VNonconst) :
  In (OFValue e VNonconst) (result_fact_list res).
Proof.
  assert (Hoo : operand_only (res_binds res) (const_table (res_binds res) fr) e = false) by (unfold operand_only; rewrite Hnc; reflexivity).
  assert (Hown : own_value (res_binds res) (const_table (res_binds res) fr) e = VNonconst) by (unfold own_value; rewrite Hnc; reflexivity).
  unfold result_fact_list; rewrite fact_once; rewrite raw_facts_flat; cbv zeta. apply in_flat_map. exists fr. split; [exact Hfr|].
  apply in_flat_map. exists e. split; [ exact (file_nodes_complete fr e He) | ].
  rewrite <- Hown. apply (occ_value_mem_retained (res_binds res) (const_table (res_binds res) fr) fr e Hnh Hoo He Hret).
Qed.
(* §10/§11 the retention bridge: a canonical nonconstant child value is retrievable as its exact retained Result row *)
Lemma nonconst_child_retained (fr : Index.FileRef (res_index res))
  (Hfr : In fr (flat_map BN.PI.pkg_members (BN.PI.packages (res_surface res))))
  (child : Index.NodeRef (res_index res)) (Hf : Index.nr_file child = fr) :
  va_value_nonconst
    (neg_map (res_binds res) (const_table (res_binds res) fr) (Index.file_nodes fr)) child = true ->
  exists child_row : FactRowRef res,
    fact_row_for child ValueKind = Some child_row
    /\ frr_row child_row = OFValue child VNonconst.
Proof.
  intro Hva.
  assert (Hnh : is_name_head child = false).
  { destruct (is_name_head child) eqn:Enh; [ | reflexivity ].
    rewrite (va_value_nonconst_name_head (res_binds res) (const_table (res_binds res) fr) fr child Enh Hf) in Hva; discriminate Hva. }
  rewrite (va_value_nonconst_correct (res_binds res) (const_table (res_binds res) fr) fr child Hnh Hf) in Hva.
  apply andb_prop in Hva. destruct Hva as [Hret Hnc].
  assert (Hown : own_verdict (res_binds res) (const_table (res_binds res) fr) child = Some VNonconst)
    by (destruct (own_verdict (res_binds res) (const_table (res_binds res) fr) child) as [ov|];
        [ destruct ov; try discriminate Hnc; reflexivity | discriminate Hnc ]).
  destruct (fact_list_row _ (nonconst_value_fact_retained fr Hfr child Hnh Hf Hret Hown)) as [child_row [Hcin Hcrow]].
  exists child_row. split.
  - apply fact_row_for_complete;
      [ exact Hcin | unfold frr_site; rewrite Hcrow; reflexivity | unfold frr_kind; rewrite Hcrow; reflexivity ].
  - exact Hcrow.
Qed.
(* §19.1 the exact child fact's node is a real structural descendant: node_parent child = the parent statement *)
Lemma cdfr_child_parent (cdfr : ChildDependentFactRef) :
  Index.node_parent (cdfr_edge_site cdfr) = Some (cdfr_site cdfr).
Proof.
  unfold cdfr_edge_site. destruct (cdfr_edge cdfr) as [pr Hp | pr ar Hp Ha | st j edge Hp | st j edge ar Hp Ha];
    cbn [cfe_child_site]; rewrite Hp.
  - exact (Index.Child.ca_node_parent (Index.Edges.ee_at (Index.Edges.exprstmt_expr pr))).
  - exact (Index.Child.ca_node_parent (Index.Edges.ee_at (Index.Edges.exprstmt_expr pr))).
  - exact (Index.Edges.sr_parent edge).
  - exact (Index.Edges.sr_parent edge).
Qed.
(* §19.4 completeness: every child-dependent parent row has its exact negative child prerequisite, same FactPhase *)
Lemma child_prerequisite_complete (cdfr : ChildDependentFactRef) :
  In (cdfr_rowref cdfr) (fact_rows res) -> child_prerequisite cdfr <> None.
Proof.
  intro Hin. pose proof (cdfr_ok cdfr) as Hok.
  destruct (row_file (cdfr_rowref cdfr) Hin) as [fr [Hfr [Hfile _]]].
  assert (Hsite : frr_site (cdfr_rowref cdfr) = cdfr_site cdfr) by (unfold frr_site; rewrite Hok; reflexivity).
  rewrite Hsite in Hfile.
  pose proof (fact_row_is_own (cdfr_rowref cdfr)) as Hown. rewrite Hok in Hown.
  set (e0 := cdfr_edge_site cdfr) in *.
  set (ctab := const_table (res_binds res) (Index.nr_file (cdfr_site cdfr))) in *.
  set (va := neg_map (res_binds res) ctab (Index.file_nodes (Index.nr_file (cdfr_site cdfr)))) in *.
  assert (Hfe : Index.nr_file e0 = fr)
    by (unfold e0; rewrite <- (proj2 (Index.node_parent_inv _ _ (cdfr_child_parent cdfr))); exact Hfile).
  assert (Hctab : ctab = const_table (res_binds res) fr) by (unfold ctab; rewrite Hfile; reflexivity).
  assert (Hfe' : Index.nr_file e0 = Index.nr_file (cdfr_site cdfr)) by (rewrite Hfe, Hfile; reflexivity).
  assert (Hcase : (cdfr_edge_kind cdfr = ValueKind /\ va_value_negative va e0 = true)
                \/ (cdfr_edge_kind cdfr = ApplicationKind /\ va_app_negative va e0 = true
                    /\ Index.node_view e0 = Index.Model.VApplication)).
  { destruct (stmt_fact_dependent (cdfr_site cdfr) _ _ (DepChild (cdfr_edge cdfr)) Hown) as [[Hv Hsx] | [nn [nv [Hv Hsx]]]].
    - symmetry in Hsx. unfold expr_sx_va in Hsx.
      destruct (own_stmt_expr_dep_inv (Index.Refs.mkExprStmtRef (cdfr_site cdfr) Hv) _ _ (cdfr_edge cdfr) Hsx) as [Hcs Hc].
      rewrite <- Hcs in Hc. destruct Hc as [[Hk Hvn] | [Hk [_ [Han Hva]]]].
      + left; split; [ exact Hk | exact Hvn ].
      + right; split; [ exact Hk | split; [ exact Han | exact Hva ] ].
    - symmetry in Hsx.
      exact (short_decl_decision_dep_inv (res_binds res) va (cdfr_site cdfr) nn nv Hv (cdfr_edge cdfr) Hsx). }
  destruct Hcase as [[Hk Hvn] | [Hk [Han Hva]]].
  - assert (Hnh : is_name_head e0 = false).
    { destruct (is_name_head e0) eqn:Enh; [ | reflexivity ].
      assert (Hf0 : va_value_negative va e0 = false)
        by (unfold va; exact (va_value_negative_name_head (res_binds res) ctab (Index.nr_file (cdfr_site cdfr)) e0 Enh Hfe')).
      rewrite Hf0 in Hvn; discriminate Hvn. }
    assert (Hvnb : value_neg_b (res_binds res) (own_value (res_binds res) ctab e0) = true)
      by (rewrite <- (va_value_negative_correct (res_binds res) ctab (Index.nr_file (cdfr_site cdfr)) e0 Hnh Hfe'); exact Hvn).
    assert (Hret : In (OFValue e0 (own_value (res_binds res) (const_table (res_binds res) fr) e0)) (result_fact_list res))
      by (apply (value_fact_retained fr Hfr e0 Hnh Hfe); rewrite <- Hctab; exact Hvnb).
    destruct (fact_list_row _ Hret) as [child_row [Hcin Hcrow]].
    apply (child_prerequisite_some cdfr child_row).
    + rewrite Hk.
      apply (fact_row_for_complete e0 ValueKind child_row Hcin);
        [ unfold frr_site; rewrite Hcrow; reflexivity | unfold frr_kind; rewrite Hcrow; reflexivity ].
    + apply negative_case_some. apply (value_neg_disj child_row e0 (own_value (res_binds res) (const_table (res_binds res) fr) e0) Hcrow).
      rewrite <- Hctab; exact Hvnb.
  - assert (Hanb : app_neg_at (res_binds res) e0 = true)
      by (rewrite <- (va_app_negative_correct (res_binds res) ctab (Index.nr_file (cdfr_site cdfr)) e0 Hfe'); exact Han).
    assert (Hret : In (OFApp e0 (own_app (res_binds res) (Index.Refs.mkAppRef e0 Hva))) (result_fact_list res))
      by (apply (app_fact_retained fr Hfr e0 Hfe Hva)).
    destruct (fact_list_row _ Hret) as [child_row [Hcin Hcrow]].
    apply (child_prerequisite_some cdfr child_row).
    + rewrite Hk.
      apply (fact_row_for_complete e0 ApplicationKind child_row Hcin);
        [ unfold frr_site; rewrite Hcrow; reflexivity | unfold frr_kind; rewrite Hcrow; reflexivity ].
    + apply negative_case_some. apply (app_neg_disj child_row e0 (own_app (res_binds res) (Index.Refs.mkAppRef e0 Hva)) Hcrow).
      rewrite (app_neg_at_app (res_binds res) e0 Hva) in Hanb; exact Hanb.
Qed.
(* §19.1 the retained parent row's site is exactly the edge's parent index *)
Lemma cdfr_parent_site (cdfr : ChildDependentFactRef) : frr_site (cdfr_rowref cdfr) = cdfr_site cdfr.
Proof. unfold frr_site; rewrite (cdfr_ok cdfr); reflexivity. Qed.
(* §8 strict structural progress: the exact child fact's node position strictly follows the parent statement's *)
Lemma cpr_parent_lt_child (cdfr : ChildDependentFactRef) :
  (Index.nr_pos (cdfr_site cdfr) < Index.nr_pos (cdfr_edge_site cdfr))%nat.
Proof.
  unfold cdfr_edge_site. destruct (cdfr_edge cdfr) as [pr Hp | pr ar Hp Ha | st j edge Hp | st j edge ar Hp Ha];
    cbn [cfe_child_site]; rewrite Hp.
  - exact (Index.Child.child_pos_gt_parent (Index.Edges.ee_at (Index.Edges.exprstmt_expr pr))).
  - exact (Index.Child.child_pos_gt_parent (Index.Edges.ee_at (Index.Edges.exprstmt_expr pr))).
  - exact (Index.Child.child_pos_gt_parent (Index.Edges.sr_at edge)).
  - exact (Index.Child.child_pos_gt_parent (Index.Edges.sr_at edge)).
Qed.
(* §8 and therefore the parent statement node is never its own child: exact structural source-node progress *)
Lemma cpr_parent_neq_child (cdfr : ChildDependentFactRef) : cdfr_site cdfr <> cdfr_edge_site cdfr.
Proof.
  intro Heq. pose proof (cpr_parent_lt_child cdfr) as Hlt. rewrite Heq in Hlt. exact (Nat.lt_irrefl _ Hlt).
Qed.
(* §19.1 the retained child kind is exactly value or application, never statement or type-use *)
Lemma cdfr_child_kind_va (cdfr : ChildDependentFactRef) :
  cdfr_edge_kind cdfr = ValueKind \/ cdfr_edge_kind cdfr = ApplicationKind.
Proof. unfold cdfr_edge_kind; destruct (cdfr_edge cdfr); [ left | right | left | right ]; reflexivity. Qed.
(* §19.4 soundness: a prerequisite names the exact retained child row fact_row_for selects *)
Lemma cpr_lookup_exact (cdfr : ChildDependentFactRef) (cpr : ChildPrerequisiteRef cdfr) :
  fact_row_for (cdfr_edge_site cdfr) (cdfr_edge_kind cdfr) = Some (cpr_child_row cdfr cpr).
Proof. exact (cpr_lookup cdfr cpr). Qed.
(* §19.4 soundness: that exact child row is negative — its own cause, requirement, or dependency is present *)
Lemma cpr_child_negative (cdfr : ChildDependentFactRef) (cpr : ChildPrerequisiteRef cdfr) :
  occ_cause (frr_row (cpr_child_row cdfr cpr)) <> None \/ occ_req (frr_row (cpr_child_row cdfr cpr)) <> None
  \/ occ_dep (frr_row (cpr_child_row cdfr cpr)) <> None.
Proof. destruct (cpr_neg cdfr cpr) as [c Hc | rq Hq | d Hd]; [ left | right; left | right; right ]; congruence. Qed.
(* §19.4 the parent statement row and the child value/application row are distinct rows *)
Lemma cdfr_rows_distinct (cdfr : ChildDependentFactRef) (cpr : ChildPrerequisiteRef cdfr) :
  cdfr_rowref cdfr <> cpr_child_row cdfr cpr.
Proof.
  intro Heq. pose proof (cpr_lookup cdfr cpr) as Hlk. apply fact_row_for_sound in Hlk. destruct Hlk as [_ [_ Hck]].
  assert (Hpk : frr_kind (cdfr_rowref cdfr) = StatementKind) by (unfold frr_kind; rewrite (cdfr_ok cdfr); reflexivity).
  rewrite Heq, Hck in Hpk. destruct (cdfr_child_kind_va cdfr) as [Hv|Hv]; rewrite Hv in Hpk; discriminate Hpk.
Qed.
(* §19.5 a success / nonconstant child row has no negative case — none of cause, requirement, dependency present *)
Lemma negative_case_none (child_row : FactRowRef res) :
  occ_cause (frr_row child_row) = None -> occ_req (frr_row child_row) = None ->
  occ_dep (frr_row child_row) = None -> negative_case child_row = None.
Proof.
  intros Hc Hq Hd. unfold negative_case.
  assert (Hg : forall
    (oc : option (Cause (res_binds res) (fact_site (frr_row child_row)) (fact_kind (frr_row child_row))))
    (Hoc : occ_cause (frr_row child_row) = oc)
    (oq : option (Requirement (res_binds res) (fact_site (frr_row child_row)) (fact_kind (frr_row child_row))))
    (Hoq : occ_req (frr_row child_row) = oq)
    (od : option (Dependency (res_binds res) (fact_site (frr_row child_row)) (fact_kind (frr_row child_row))))
    (Hod : occ_dep (frr_row child_row) = od),
    oc = None -> oq = None -> od = None ->
    (match oc as oc0 return occ_cause (frr_row child_row) = oc0 -> option (NegativeFactRef child_row) with
     | Some c => fun H0 => Some (ChildInvalid c H0)
     | None => fun _ =>
       match oq as oq0 return occ_req (frr_row child_row) = oq0 -> option (NegativeFactRef child_row) with
       | Some rq => fun H0 => Some (ChildUnmet rq H0)
       | None => fun _ =>
         match od as od0 return occ_dep (frr_row child_row) = od0 -> option (NegativeFactRef child_row) with
         | Some dd => fun H0 => Some (ChildDependent dd H0)
         | None => fun _ => None
         end Hod
       end Hoq
     end Hoc) = None).
  { intros oc Hoc oq Hoq od Hod Hoc' Hoq' Hod'.
    destruct oc; [ discriminate Hoc' | ]. destruct oq; [ discriminate Hoq' | ].
    destruct od; [ discriminate Hod' | ]. reflexivity. }
  exact (Hg _ eq_refl _ eq_refl _ eq_refl Hc Hq Hd).
Qed.
(* §19.5 the negative class is exactly the case retained: invalid, unmet, or dependent, and just one *)
Lemma nfr_class_invalid (child_row : FactRowRef res) (n : NegativeFactRef child_row) :
  nfr_class n = NegInvalid <-> exists c H, n = ChildInvalid c H.
Proof.
  split; [ destruct n as [c Hc|rq Hq|d Hd]; cbn; try discriminate; intros _; exists c, Hc; reflexivity
         | intros [c [H ->]]; reflexivity ].
Qed.
(* §19.3 a value-negative child is selected first: the retained edge is the exact value-child edge *)
Lemma stmt_expr_value_first (pr : Index.Refs.ExprStmtRef (res_index res)) (an : bool) :
  own_stmt_expr (res_binds res) pr true an = SDependent (DepChild (ExprStmtValueChild pr eq_refl)).
Proof. reflexivity. Qed.
(* §19.3 an application-negative child is selected only when the value child is nonnegative — the app-child edge *)
Lemma stmt_expr_app_second (pr : Index.Refs.ExprStmtRef (res_index res))
  (He : Index.node_view (Index.Edges.ee_child (Index.Edges.exprstmt_expr pr)) = Index.Model.VApplication) :
  own_stmt_expr (res_binds res) pr false true
  = SDependent (DepChild (ExprStmtApplicationChild pr (Index.Refs.mkAppRef _ He) eq_refl eq_refl)).
Proof.
  unfold own_stmt_expr.
  rewrite (convoy_at (Index.node_view (Index.Edges.ee_child (Index.Edges.exprstmt_expr pr)))
             (stmt_expr_body (res_binds res) pr true) Index.Model.VApplication He).
  reflexivity.
Qed.
(* §19.3 no child dependency when both applicable child facts are nonnegative *)
Lemma stmt_expr_none (pr : Index.Refs.ExprStmtRef (res_index res)) (d : Dependency (res_binds res) (Index.Refs.exs_node pr) StatementKind) :
  own_stmt_expr (res_binds res) pr false false = SDependent d -> False.
Proof.
  unfold own_stmt_expr.
  assert (Hgen : forall v Hv, stmt_expr_body (res_binds res) pr false v Hv = SDependent d -> False).
  { intros v Hv HH. destruct v; cbn [stmt_expr_body] in HH; try discriminate HH.
    cbn [stmt_expr_app_branch] in HH.
    repeat (match goal with | _ : context [ match ?x with _ => _ end ] |- _ => destruct x end); discriminate HH. }
  exact (Hgen _ eq_refl).
Qed.
(* §19.6 enumeration completeness: every child-dependent parent row is enumerated with its exact prerequisite *)
Lemma child_prerequisite_refs_complete (row : FactRowRef res) (cdfr : ChildDependentFactRef) :
  In row (fact_rows res) -> child_dep_of row = Some cdfr ->
  exists cpr, In (existT _ cdfr cpr) child_prerequisite_refs.
Proof.
  intros Hin Hcd.
  assert (Hrr : cdfr_rowref cdfr = row) by (exact (child_dep_of_rowref row cdfr Hcd)).
  assert (Hpre : child_prerequisite cdfr <> None)
    by (apply child_prerequisite_complete; rewrite Hrr; exact Hin).
  destruct (child_prerequisite cdfr) as [cpr|] eqn:Hcp; [ | exfalso; apply Hpre; reflexivity ].
  exists cpr. unfold child_prerequisite_refs. apply in_flat_map. exists row. split; [ exact Hin | ].
  rewrite Hcd, Hcp. left. reflexivity.
Qed.
(* §19.6 enumeration parent order: the enumeration is exactly the ordered flat_map over the retained fact rows *)
Lemma child_prerequisite_refs_order :
  child_prerequisite_refs = flat_map (fun row => match child_dep_of row with
    | Some cdfr => match child_prerequisite cdfr with Some cpr => [existT _ cdfr cpr] | None => [] end
    | None => [] end) (fact_rows res).
Proof. reflexivity. Qed.
(* a projection of a ≤1-per-element flat_map over a NoDup list, where each output points back at its input, is NoDup *)
Lemma nodup_flat_map_proj {A B} (h : B -> A) (g : A -> list B) (l : list A)
  (Hg : forall row x, In x (g row) -> h x = row) (Hle : forall row, (List.length (g row) <= 1)%nat)
  (Hnd : NoDup l) : NoDup (map h (flat_map g l)).
Proof.
  induction l as [|a l' IH]; cbn; [ constructor | ].
  inversion Hnd as [|? ? Hna Hnd']; subst. specialize (IH Hnd').
  assert (Hsub : forall y, In y (map h (flat_map g l')) -> In y l').
  { intros y Hy. apply in_map_iff in Hy. destruct Hy as [x [Hxy Hxin]].
    apply in_flat_map in Hxin. destruct Hxin as [row [Hrow Hxg]]. rewrite <- Hxy, (Hg row x Hxg). exact Hrow. }
  rewrite map_app. pose proof (Hle a) as Hla.
  destruct (g a) as [|x [|y gr]] eqn:Hga; cbn [List.length] in Hla; try (exfalso; lia); cbn [map app].
  - exact IH.
  - assert (Hin_x : In x (g a)) by (rewrite Hga; left; reflexivity).
    rewrite (Hg a x Hin_x).
    constructor; [ intro Hin; exact (Hna (Hsub a Hin)) | exact IH ].
Qed.
(* §19.6 enumeration no-duplicates: no two enumerated prerequisites share a parent fact row *)
Lemma child_prerequisite_refs_nodup :
  NoDup (map (fun x => cdfr_rowref (projT1 x)) child_prerequisite_refs).
Proof.
  unfold child_prerequisite_refs.
  apply nodup_flat_map_proj.
  - intros row x Hx. destruct (child_dep_of row) as [cdfr|] eqn:Hcd; cbn in Hx; [ | exact (match Hx with end) ].
    destruct (child_prerequisite cdfr) as [cpr|]; cbn in Hx; [ | exact (match Hx with end) ].
    destruct Hx as [Hx|[]]. subst x. cbn. exact (child_dep_of_rowref row cdfr Hcd).
  - intro row. destruct (child_dep_of row) as [cdfr|]; [ destruct (child_prerequisite cdfr) | ]; cbn; lia.
  - exact (NoDup_map_inv frr_ord (fact_rows res) fact_rows_ord_nodup).
Qed.
(* an option-convoy builder that wraps its Some payload is non-None exactly when its scrutinee is Some *)
Lemma match_some_not_none {A B : Type} (o : option A) (h : forall a : A, o = Some a -> B) (a0 : A) (E : o = Some a0) :
  (match o as o0 return (o = o0 -> option B) with
   | Some a => fun Ha => Some (h a Ha) | None => fun _ => None end eq_refl) <> None.
Proof.
  assert (Hg : forall (o1 : option A) (Ho : o = o1), o = Some a0 ->
    (match o1 as o0 return (o = o0 -> option B) with Some a => fun Ha => Some (h a Ha) | None => fun _ => None end Ho) <> None).
  { intros o1 Ho HE. destruct o1 as [a1|]; [ discriminate | ]. rewrite Ho in HE. discriminate HE. }
  exact (Hg o eq_refl E).
Qed.
(* §8 an exact Result-owned short statement fact: the exact ShortStmtRef and its exact retained statement row *)
Record ShortStatementFactRef : Type := mk_ssfr {
  ssfr_stmt   : Index.Refs.ShortStmtRef (res_index res) ;
  ssfr_row    : FactRowRef res ;
  ssfr_lookup : fact_row_for (Index.Refs.sh_node ssfr_stmt) StatementKind = Some ssfr_row
}.
(* the row's site and kind are exactly the queried statement site and StatementKind, read off the lookup *)
Definition ssfr_site (ssfr : ShortStatementFactRef) : frr_site (ssfr_row ssfr) = Index.Refs.sh_node (ssfr_stmt ssfr)
  := proj1 (proj2 (fact_row_for_sound _ _ _ (ssfr_lookup ssfr))).
Definition ssfr_kind (ssfr : ShortStatementFactRef) : frr_kind (ssfr_row ssfr) = StatementKind
  := proj2 (proj2 (fact_row_for_sound _ _ _ (ssfr_lookup ssfr))).
(* the canonical lookup begins from fact_row_for at the exact statement site and StatementKind, never a raw OccFact *)
Definition short_statement_fact (st : Index.Refs.ShortStmtRef (res_index res)) : option ShortStatementFactRef :=
  match fact_row_for (Index.Refs.sh_node st) StatementKind as o
    return fact_row_for (Index.Refs.sh_node st) StatementKind = o -> option ShortStatementFactRef with
  | Some row => fun E => Some (mk_ssfr st row E)
  | None => fun _ => None
  end eq_refl.
(* every represented short statement has its exact retained statement row: the lookup never fails *)
Lemma short_statement_fact_complete (st : Index.Refs.ShortStmtRef (res_index res)) : short_statement_fact st <> None.
Proof.
  assert (Hfr : In (Index.nr_file (Index.Refs.sh_node st)) (flat_map BN.PI.pkg_members (BN.PI.packages (res_surface res)))).
  { apply in_flat_map. exists (BN.PI.package_of_file (res_surface res) (Index.nr_file (Index.Refs.sh_node st))).
    split; [ apply BN.PI.packages_complete | apply BN.PI.pkg_members_of_file ]. }
  destruct (fact_list_row _ (stmt_fact_retained (Index.nr_file (Index.Refs.sh_node st)) Hfr (Index.Refs.sh_node st) eq_refl
              (Index.Refs.sh_names st) (Index.Refs.sh_values st) (Index.Refs.sh_ok st))) as [row [Hrin Hrow]].
  assert (HSome : fact_row_for (Index.Refs.sh_node st) StatementKind = Some row)
    by (apply fact_row_for_complete;
        [ exact Hrin | unfold frr_site; rewrite Hrow; reflexivity | unfold frr_kind; rewrite Hrow; reflexivity ]).
  unfold short_statement_fact. exact (match_some_not_none _ (fun row0 E => mk_ssfr st row0 E) row HSome).
Qed.
(* the looked-up fact carries exactly the queried statement *)
Lemma short_statement_fact_stmt (st : Index.Refs.ShortStmtRef (res_index res)) (ssfr : ShortStatementFactRef) :
  short_statement_fact st = Some ssfr -> ssfr_stmt ssfr = st.
Proof.
  unfold short_statement_fact.
  assert (Hg : forall (o : option (FactRowRef res)) (Ho : fact_row_for (Index.Refs.sh_node st) StatementKind = o),
    (match o as o0 return (fact_row_for (Index.Refs.sh_node st) StatementKind = o0 -> option ShortStatementFactRef)
       with Some row => fun E => Some (mk_ssfr st row E) | None => fun _ => None end Ho) = Some ssfr -> ssfr_stmt ssfr = st).
  { intros o Ho. destruct o as [row0|]; [ | discriminate ]. intro H. injection H as H. rewrite <- H. reflexivity. }
  exact (Hg (fact_row_for (Index.Refs.sh_node st) StatementKind) eq_refl).
Qed.
(* §8 the retained statement row's outcome IS the one canonical short-declaration decision — never a recomputation *)
Lemma ssfr_is_short_decl (ssfr : ShortStatementFactRef) :
  frr_row (ssfr_row ssfr) = OFStmt (Index.Refs.sh_node (ssfr_stmt ssfr))
    (short_decl_decision (res_binds res)
      (neg_map (res_binds res) (const_table (res_binds res) (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))
        (Index.file_nodes (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr)))))
      (Index.Refs.sh_node (ssfr_stmt ssfr))
      (Index.Refs.sh_names (ssfr_stmt ssfr)) (Index.Refs.sh_values (ssfr_stmt ssfr)) (Index.Refs.sh_ok (ssfr_stmt ssfr))).
Proof.
  pose proof (ssfr_site ssfr) as Hsite. pose proof (ssfr_kind ssfr) as Hkind.
  pose proof (fact_row_is_own (ssfr_row ssfr)) as Hown.
  destruct (frr_row (ssfr_row ssfr)) as [r' ov|r' oa|r' os|r' ot] eqn:Hfrow;
    [ exfalso; unfold frr_kind in Hkind; rewrite Hfrow in Hkind; cbn in Hkind; discriminate Hkind
    | exfalso; unfold frr_kind in Hkind; rewrite Hfrow in Hkind; cbn in Hkind; discriminate Hkind
    | | exfalso; unfold frr_kind in Hkind; rewrite Hfrow in Hkind; cbn in Hkind; discriminate Hkind ].
  assert (Hr' : r' = Index.Refs.sh_node (ssfr_stmt ssfr))
    by (unfold frr_site in Hsite; rewrite Hfrow in Hsite; cbn in Hsite; exact Hsite).
  subst r'. cbn [fact_site] in Hown.
  set (va := neg_map (res_binds res) (const_table (res_binds res) (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))
             (Index.file_nodes (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))) in *.
  rewrite (stmt_fact_ssshort (res_binds res) (Index.Refs.sh_node (ssfr_stmt ssfr))
    (expr_sx_va (res_binds res) va (Index.Refs.sh_node (ssfr_stmt ssfr))) va
    (Index.Refs.sh_names (ssfr_stmt ssfr)) (Index.Refs.sh_values (ssfr_stmt ssfr)) (Index.Refs.sh_ok (ssfr_stmt ssfr))) in Hown.
  destruct Hown as [Heq | []].
  exact (eq_sym Heq).
Qed.
(* §10 an exact Result-owned nonconstant Value fact: a retained row whose exact outcome is OFValue site VNonconst *)
Record NonconstValueFactRef : Type := mk_nvfr {
  nvfr_rowref : FactRowRef res ;
  nvfr_site   : Index.NodeRef (res_index res) ;
  nvfr_is     : frr_row nvfr_rowref = OFValue nvfr_site VNonconst
}.
Lemma nvfr_kind (n : NonconstValueFactRef) : frr_kind (nvfr_rowref n) = ValueKind.
Proof. unfold frr_kind; rewrite (nvfr_is n); reflexivity. Qed.
Lemma nvfr_frr_site (n : NonconstValueFactRef) : frr_site (nvfr_rowref n) = nvfr_site n.
Proof. unfold frr_site; rewrite (nvfr_is n); reflexivity. Qed.
(* Step 6 the Result-owned short-origin value ref: a name use resolving to DOShort, with its retained VNonconst row *)
Record ShortOriginValueRef : Type := mk_sovr {
  sovr_site   : Index.NodeRef (res_index res) ;
  sovr_name   : Names.OrdinaryIdentifier ;
  sovr_view   : Index.node_view sovr_site = Index.Model.VName sovr_name ;
  sovr_sn     : BN.ShortNewRef (res_index res) ;
  sovr_res    : BN.resolution_object_view (BN.resolve (res_binds res) sovr_site sovr_name)
                  = Some (BN.SourceObject (BN.DOShort sovr_sn)) ;
  sovr_row    : NonconstValueFactRef ;
  sovr_at     : nvfr_site sovr_row = sovr_site ;
  sovr_lookup : fact_row_for sovr_site ValueKind = Some (nvfr_rowref sovr_row)
}.
(* §9.4 retained row round trip: the ref's row is exactly the retained VNonconst Value fact at its use site *)
Lemma sovr_row_is (sovr : ShortOriginValueRef) :
  frr_row (nvfr_rowref (sovr_row sovr)) = OFValue (sovr_site sovr) VNonconst.
Proof. rewrite (nvfr_is (sovr_row sovr)), (sovr_at sovr). reflexivity. Qed.
Lemma sovr_round_trip (sovr : ShortOriginValueRef) :
  fact_row_for (sovr_site sovr) ValueKind = Some (nvfr_rowref (sovr_row sovr))
  /\ frr_row (nvfr_rowref (sovr_row sovr)) = OFValue (sovr_site sovr) VNonconst.
Proof. split; [ exact (sovr_lookup sovr) | exact (sovr_row_is sovr) ]. Qed.
(* §9.5 cross-origin rejection: the use's exact resolution is provably neither a binder nor a func source origin *)
Lemma sovr_not_dobinder (sovr : ShortOriginValueRef) (b : BN.BinderRef (res_index res)) :
  BN.resolution_object_view (BN.resolve (res_binds res) (sovr_site sovr) (sovr_name sovr))
    <> Some (BN.SourceObject (BN.DOBinder b)).
Proof. rewrite (sovr_res sovr). discriminate. Qed.
Lemma sovr_not_dofunc (sovr : ShortOriginValueRef) (f : BN.FunctionDeclRef (res_index res)) :
  BN.resolution_object_view (BN.resolve (res_binds res) (sovr_site sovr) (sovr_name sovr))
    <> Some (BN.SourceObject (BN.DOFunc f)).
Proof. rewrite (sovr_res sovr). discriminate. Qed.
(* §9.5 origin uniqueness: the same use site and spelling force the same DOShort origin — resolution is deterministic *)
Lemma sovr_origin_unique (sovr1 sovr2 : ShortOriginValueRef)
  (Hsite : sovr_site sovr1 = sovr_site sovr2) (Hname : sovr_name sovr1 = sovr_name sovr2) :
  sovr_sn sovr1 = sovr_sn sovr2.
Proof.
  pose proof (sovr_res sovr1) as H1. pose proof (sovr_res sovr2) as H2.
  rewrite Hsite, Hname in H1. rewrite H1 in H2. injection H2 as H2. exact H2.
Qed.
(* §9.6 origin projections: the retained DOShort origin projects to its exact short statement, lhs index, and edge *)
Definition sovr_origin_stmt (sovr : ShortOriginValueRef) : Index.Refs.ShortStmtRef (res_index res) :=
  BN.snr_stmt (sovr_sn sovr).
Definition sovr_origin_ix (sovr : ShortOriginValueRef) : nat := BN.snr_ix (sovr_sn sovr).
Definition sovr_origin_edge (sovr : ShortOriginValueRef)
  : Index.Edges.ShortLhsEdge (sovr_origin_stmt sovr) (sovr_origin_ix sovr) := BN.snr_edge (sovr_sn sovr).
(* Step 6 construction: a value-position DOShort use yields the ref, its row the one canonical builder's *)
Lemma short_origin_value_construct (fr : Index.FileRef (res_index res))
  (Hfr : In fr (flat_map BN.PI.pkg_members (BN.PI.packages (res_surface res))))
  (e : Index.NodeRef (res_index res)) (Hnh : is_name_head e = false) (He : Index.nr_file e = fr)
  (n : Names.OrdinaryIdentifier) (Hview : Index.node_view e = Index.Model.VName n)
  (sn : BN.ShortNewRef (res_index res))
  (Hres : BN.resolution_object_view (BN.resolve (res_binds res) e n) = Some (BN.SourceObject (BN.DOShort sn))) :
  exists sovr : ShortOriginValueRef, sovr_site sovr = e /\ sovr_name sovr = n /\ sovr_sn sovr = sn.
Proof.
  assert (Hown : own_verdict (res_binds res) (const_table (res_binds res) fr) e = Some VNonconst)
    by exact (own_verdict_doshort (res_binds res) (const_table (res_binds res) fr) e n Hview sn Hres).
  assert (Hret : retains_value_fact e = true) by (unfold retains_value_fact; rewrite Hview; reflexivity).
  destruct (fact_list_row _ (nonconst_value_fact_retained fr Hfr e Hnh He Hret Hown)) as [row [Hin Hrow]].
  assert (Hlk : fact_row_for e ValueKind = Some row)
    by (apply fact_row_for_complete;
        [ exact Hin | unfold frr_site; rewrite Hrow; reflexivity | unfold frr_kind; rewrite Hrow; reflexivity ]).
  exists (mk_sovr e n Hview sn Hres (mk_nvfr row e Hrow) eq_refl Hlk).
  split; [ reflexivity | split; reflexivity ].
Qed.
(* §11 the Result-owned RHS-meaning boundary: parent fact, RHS edge, and the exact retained VNonconst child row *)
Record ShortRhsMeaningRef : Type := mk_srmr {
  srmr_parent : ShortStatementFactRef ;
  srmr_j      : nat ;
  srmr_edge   : Index.Edges.ShortRhsEdge (ssfr_stmt srmr_parent) srmr_j ;
  srmr_child  : NonconstValueFactRef ;
  srmr_req    : frr_row (ssfr_row srmr_parent) = OFStmt (Index.Refs.sh_node (ssfr_stmt srmr_parent))
                  (SUnmet (ReqShortRhsMeaning (ssfr_stmt srmr_parent) srmr_j srmr_edge eq_refl)) ;
  srmr_child_at : nvfr_site srmr_child = Index.Edges.sr_child srmr_edge ;
  srmr_lookup   : fact_row_for (Index.Edges.sr_child srmr_edge) ValueKind = Some (nvfr_rowref srmr_child)
}.
(* §11 the RHS-meaning boundary is constructible whenever the decision reaches that branch, in the one Result *)
Lemma short_rhs_meaning_construct (ssfr : ShortStatementFactRef)
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event (res_binds res) (ssfr_stmt ssfr))) = None)
  (Hcount : Index.Refs.sh_names (ssfr_stmt ssfr) = Index.Refs.sh_values (ssfr_stmt ssfr))
  (Hblk : BN.short_blocker_decision (BN.short_event (res_binds res) (ssfr_stmt ssfr)) = BN.ShortNoBlocker)
  (Hnew : existsb BN.is_new_row (BN.se_rows (BN.short_event (res_binds res) (ssfr_stmt ssfr))) = true)
  (Hneg : short_rhs_neg (res_binds res)
            (neg_map (res_binds res) (const_table (res_binds res) (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))
              (Index.file_nodes (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))) (ssfr_stmt ssfr) = None)
  (j0 : nat) (edge0 : Index.Edges.ShortRhsEdge (ssfr_stmt ssfr) j0)
  (Hfind : find_rhs_vnonconst
             (neg_map (res_binds res) (const_table (res_binds res) (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))
               (Index.file_nodes (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))) (ssfr_stmt ssfr)
           = Some (existT _ j0 edge0)) :
  exists srmr : ShortRhsMeaningRef, srmr_parent srmr = ssfr /\ srmr_j srmr = j0.
Proof.
  set (fr := Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))) in *.
  assert (Hfr : In fr (flat_map BN.PI.pkg_members (BN.PI.packages (res_surface res)))).
  { apply in_flat_map. exists (BN.PI.package_of_file (res_surface res) fr).
    split; [ apply BN.PI.packages_complete | apply BN.PI.pkg_members_of_file ]. }
  assert (Hcf : Index.nr_file (Index.Edges.sr_child edge0) = fr)
    by (unfold fr; rewrite <- (proj2 (Index.node_parent_inv _ _ (Index.Edges.sr_parent edge0))); reflexivity).
  pose proof (find_some _ _ Hfind) as [_ Hnc0]. cbn in Hnc0.
  destruct (nonconst_child_retained fr Hfr (Index.Edges.sr_child edge0) Hcf Hnc0) as [child_row [Hlk Hcrow]].
  pose proof (ssfr_is_short_decl ssfr) as Hrow. fold fr in Hrow.
  rewrite (short_decl_decision_rhsmeaning_sound_st (res_binds res)
    (neg_map (res_binds res) (const_table (res_binds res) fr) (Index.file_nodes fr))
    (ssfr_stmt ssfr) j0 edge0 Hdup Hcount Hblk Hnew Hneg Hfind) in Hrow.
  exists (mk_srmr ssfr j0 edge0 (mk_nvfr child_row (Index.Edges.sr_child edge0) Hcrow) Hrow eq_refl Hlk).
  split; reflexivity.
Qed.
(* §16 the Result-owned usage boundary: the parent statement fact carrying the exact unmet usage requirement *)
Record ShortUsageRef : Type := mk_sur {
  sur_parent : ShortStatementFactRef ;
  sur_req    : frr_row (ssfr_row sur_parent)
             = OFStmt (Index.Refs.sh_node (ssfr_stmt sur_parent)) (SUnmet (ReqShortUsage (ssfr_stmt sur_parent) eq_refl))
}.
(* the exact canonical New rows the usage boundary certifies: the source-ordered New left rows of its event *)
Definition sur_new_rows (sur : ShortUsageRef)
  : list { i : nat & BN.ShortDecisionRowRef (BN.short_event (res_binds res) (ssfr_stmt (sur_parent sur))) i }
  := BN.short_rows_where (BN.short_event (res_binds res) (ssfr_stmt (sur_parent sur))) BN.is_new_row.
(* §14 the Result-owned mixed-redeclaration boundary: the parent fact carrying the exact unmet type requirement *)
Record ShortRedeclarationTypesRef : Type := mk_srtr {
  srtr_parent : ShortStatementFactRef ;
  srtr_req    : frr_row (ssfr_row srtr_parent)
              = OFStmt (Index.Refs.sh_node (ssfr_stmt srtr_parent)) (SUnmet (ReqShortRedeclarationTypes (ssfr_stmt srtr_parent) eq_refl))
}.
(* the exact canonical source-ordered ExistingVariable rows whose type equality the mixed boundary still requires *)
Definition srtr_existing_rows (srtr : ShortRedeclarationTypesRef)
  : list { i : nat & BN.ShortDecisionRowRef (BN.short_event (res_binds res) (ssfr_stmt (srtr_parent srtr))) i }
  := BN.short_rows_where (BN.short_event (res_binds res) (ssfr_stmt (srtr_parent srtr))) BN.is_existing_var_row.
(* the exact canonical source-ordered New rows the mixed boundary also carries *)
Definition srtr_new_rows (srtr : ShortRedeclarationTypesRef)
  : list { i : nat & BN.ShortDecisionRowRef (BN.short_event (res_binds res) (ssfr_stmt (srtr_parent srtr))) i }
  := BN.short_rows_where (BN.short_event (res_binds res) (ssfr_stmt (srtr_parent srtr))) BN.is_new_row.
(* §16 the usage boundary is constructible whenever the decision reaches its final structurally-valid branch *)
Lemma short_usage_construct (ssfr : ShortStatementFactRef)
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event (res_binds res) (ssfr_stmt ssfr))) = None)
  (Hcount : Index.Refs.sh_names (ssfr_stmt ssfr) = Index.Refs.sh_values (ssfr_stmt ssfr))
  (Hblk : BN.short_blocker_decision (BN.short_event (res_binds res) (ssfr_stmt ssfr)) = BN.ShortNoBlocker)
  (Hnew : existsb BN.is_new_row (BN.se_rows (BN.short_event (res_binds res) (ssfr_stmt ssfr))) = true)
  (Hneg : short_rhs_neg (res_binds res) (neg_map (res_binds res) (const_table (res_binds res) (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))
            (Index.file_nodes (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))) (ssfr_stmt ssfr) = None)
  (Hfind : find_rhs_vnonconst (neg_map (res_binds res) (const_table (res_binds res) (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))
            (Index.file_nodes (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))) (ssfr_stmt ssfr) = None)
  (Hmix : existsb BN.is_existing_var_row (BN.se_rows (BN.short_event (res_binds res) (ssfr_stmt ssfr))) = false) :
  exists sur : ShortUsageRef, sur_parent sur = ssfr.
Proof.
  pose proof (ssfr_is_short_decl ssfr) as Hrow.
  rewrite (short_decl_decision_usage_sound_st (res_binds res)
    (neg_map (res_binds res) (const_table (res_binds res) (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))
      (Index.file_nodes (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))) (ssfr_stmt ssfr)
    Hdup Hcount Hblk Hnew Hneg Hfind Hmix) in Hrow.
  exists (mk_sur ssfr Hrow). reflexivity.
Qed.
(* §14 the mixed-redeclaration boundary is constructible whenever the decision reaches that branch *)
Lemma short_redecl_construct (ssfr : ShortStatementFactRef)
  (Hdup : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event (res_binds res) (ssfr_stmt ssfr))) = None)
  (Hcount : Index.Refs.sh_names (ssfr_stmt ssfr) = Index.Refs.sh_values (ssfr_stmt ssfr))
  (Hblk : BN.short_blocker_decision (BN.short_event (res_binds res) (ssfr_stmt ssfr)) = BN.ShortNoBlocker)
  (Hnew : existsb BN.is_new_row (BN.se_rows (BN.short_event (res_binds res) (ssfr_stmt ssfr))) = true)
  (Hneg : short_rhs_neg (res_binds res) (neg_map (res_binds res) (const_table (res_binds res) (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))
            (Index.file_nodes (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))) (ssfr_stmt ssfr) = None)
  (Hfind : find_rhs_vnonconst (neg_map (res_binds res) (const_table (res_binds res) (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))
            (Index.file_nodes (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))) (ssfr_stmt ssfr) = None)
  (Hmix : existsb BN.is_existing_var_row (BN.se_rows (BN.short_event (res_binds res) (ssfr_stmt ssfr))) = true) :
  exists srtr : ShortRedeclarationTypesRef, srtr_parent srtr = ssfr.
Proof.
  pose proof (ssfr_is_short_decl ssfr) as Hrow.
  rewrite (short_decl_decision_redecl_sound_st (res_binds res)
    (neg_map (res_binds res) (const_table (res_binds res) (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))
      (Index.file_nodes (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))) (ssfr_stmt ssfr)
    Hdup Hcount Hblk Hnew Hneg Hfind Hmix) in Hrow.
  exists (mk_srtr ssfr Hrow). reflexivity.
Qed.
(* same-site statement outcome injectivity, proved once over abstract outcomes so callers never inject a huge term *)
Lemma ofstmt_outcome_inj (s : Index.NodeRef (res_index res)) (os1 os2 : StmtOutcome (res_binds res) s) :
  OFStmt s os1 = OFStmt s os2 -> os1 = os2.
Proof. intro H. injection H as H. apply (Eqdep_dec.inj_pair2_eq_dec _ noderef_eq_dec) in H. exact H. Qed.
(* §16 the usage New rows are every canonical New row of the event, each tagged New, exactly by construction *)
Lemma sur_new_rows_forall (sur : ShortUsageRef) :
  Forall (fun x => BN.is_new_row (BN.row_decision (projT2 x)) = true) (sur_new_rows sur).
Proof. apply BN.short_rows_where_forall. Qed.
(* §16 the usage New-row decisions are exactly the New-filtered retained rows: complete, no extra member *)
Lemma sur_new_rows_complete (sur : ShortUsageRef) :
  map (fun x => BN.row_decision (projT2 x)) (sur_new_rows sur)
  = filter BN.is_new_row (BN.se_rows (BN.short_event (res_binds res) (ssfr_stmt (sur_parent sur)))).
Proof. apply BN.short_rows_where_map. Qed.
(* the usage boundary's own event carries a New row: read back from the exact usage requirement via completeness *)
Lemma sur_has_new (sur : ShortUsageRef) :
  existsb BN.is_new_row (BN.se_rows (BN.short_event (res_binds res) (ssfr_stmt (sur_parent sur)))) = true.
Proof.
  pose proof (sur_req sur) as Hreq. rewrite (ssfr_is_short_decl (sur_parent sur)) in Hreq.
  apply ofstmt_outcome_inj in Hreq.
  destruct (short_decl_decision_usage_complete (res_binds res)
    (neg_map (res_binds res) (const_table (res_binds res) (Index.nr_file (Index.Refs.sh_node (ssfr_stmt (sur_parent sur)))))
      (Index.file_nodes (Index.nr_file (Index.Refs.sh_node (ssfr_stmt (sur_parent sur))))))
    (ssfr_stmt (sur_parent sur)) Hreq) as [_ [_ [_ [Hnew _]]]]. exact Hnew.
Qed.
(* §16 the usage New-row list is nonempty: the final branch requires at least one New name *)
Lemma sur_new_rows_nonempty (sur : ShortUsageRef) : sur_new_rows sur <> nil.
Proof. apply BN.short_rows_where_nonempty. apply sur_has_new. Qed.
(* §14 the mixed ExistingVariable rows are every canonical existing-variable row, each so tagged *)
Lemma srtr_existing_rows_forall (srtr : ShortRedeclarationTypesRef) :
  Forall (fun x => BN.is_existing_var_row (BN.row_decision (projT2 x)) = true) (srtr_existing_rows srtr).
Proof. apply BN.short_rows_where_forall. Qed.
(* §14 the mixed New rows are every canonical New row, each so tagged *)
Lemma srtr_new_rows_forall (srtr : ShortRedeclarationTypesRef) :
  Forall (fun x => BN.is_new_row (BN.row_decision (projT2 x)) = true) (srtr_new_rows srtr).
Proof. apply BN.short_rows_where_forall. Qed.
(* §14 the mixed ExistingVariable decisions are exactly the existing-variable-filtered retained rows *)
Lemma srtr_existing_rows_complete (srtr : ShortRedeclarationTypesRef) :
  map (fun x => BN.row_decision (projT2 x)) (srtr_existing_rows srtr)
  = filter BN.is_existing_var_row (BN.se_rows (BN.short_event (res_binds res) (ssfr_stmt (srtr_parent srtr)))).
Proof. apply BN.short_rows_where_map. Qed.
(* §14 the mixed New decisions are exactly the New-filtered retained rows *)
Lemma srtr_new_rows_complete (srtr : ShortRedeclarationTypesRef) :
  map (fun x => BN.row_decision (projT2 x)) (srtr_new_rows srtr)
  = filter BN.is_new_row (BN.se_rows (BN.short_event (res_binds res) (ssfr_stmt (srtr_parent srtr)))).
Proof. apply BN.short_rows_where_map. Qed.
(* the mixed boundary's event carries both an existing-variable row and a New row, via completeness *)
Lemma srtr_has_rows (srtr : ShortRedeclarationTypesRef) :
  existsb BN.is_existing_var_row (BN.se_rows (BN.short_event (res_binds res) (ssfr_stmt (srtr_parent srtr)))) = true
  /\ existsb BN.is_new_row (BN.se_rows (BN.short_event (res_binds res) (ssfr_stmt (srtr_parent srtr)))) = true.
Proof.
  pose proof (srtr_req srtr) as Hreq. rewrite (ssfr_is_short_decl (srtr_parent srtr)) in Hreq.
  apply ofstmt_outcome_inj in Hreq.
  destruct (short_decl_decision_redecl_complete (res_binds res)
    (neg_map (res_binds res) (const_table (res_binds res) (Index.nr_file (Index.Refs.sh_node (ssfr_stmt (srtr_parent srtr)))))
      (Index.file_nodes (Index.nr_file (Index.Refs.sh_node (ssfr_stmt (srtr_parent srtr))))))
    (ssfr_stmt (srtr_parent srtr)) Hreq) as [_ [_ [_ [Hnew [_ [_ Hmix]]]]]]. split; [ exact Hmix | exact Hnew ].
Qed.
(* §14 both mixed row lists are nonempty: the branch requires at least one existing variable and one New name *)
Lemma srtr_existing_rows_nonempty (srtr : ShortRedeclarationTypesRef) : srtr_existing_rows srtr <> nil.
Proof. apply BN.short_rows_where_nonempty. apply srtr_has_rows. Qed.
Lemma srtr_new_rows_nonempty (srtr : ShortRedeclarationTypesRef) : srtr_new_rows srtr <> nil.
Proof. apply BN.short_rows_where_nonempty. apply srtr_has_rows. Qed.
(* §16/§14 each canonical row list carries every exact ordinal once, hence each exact row ref once, in source order *)
Lemma sur_new_rows_ord_nodup (sur : ShortUsageRef) : NoDup (map (@projT1 _ _) (sur_new_rows sur)).
Proof. apply BN.short_rows_where_ord_nodup. Qed.
Lemma sur_new_rows_nodup (sur : ShortUsageRef) : NoDup (sur_new_rows sur).
Proof. apply BN.short_rows_where_nodup. Qed.
Lemma srtr_existing_rows_ord_nodup (srtr : ShortRedeclarationTypesRef) :
  NoDup (map (@projT1 _ _) (srtr_existing_rows srtr)).
Proof. apply BN.short_rows_where_ord_nodup. Qed.
Lemma srtr_existing_rows_nodup (srtr : ShortRedeclarationTypesRef) : NoDup (srtr_existing_rows srtr).
Proof. apply BN.short_rows_where_nodup. Qed.
Lemma srtr_new_rows_ord_nodup (srtr : ShortRedeclarationTypesRef) : NoDup (map (@projT1 _ _) (srtr_new_rows srtr)).
Proof. apply BN.short_rows_where_ord_nodup. Qed.
Lemma srtr_new_rows_nodup (srtr : ShortRedeclarationTypesRef) : NoDup (srtr_new_rows srtr).
Proof. apply BN.short_rows_where_nodup. Qed.
(* the mixed boundary's own count-equality over its event's statement, read back from its exact requirement *)
Lemma srtr_count (srtr : ShortRedeclarationTypesRef) :
  Index.Refs.sh_names (BN.se_stmt (BN.short_event (res_binds res) (ssfr_stmt (srtr_parent srtr))))
  = Index.Refs.sh_values (BN.se_stmt (BN.short_event (res_binds res) (ssfr_stmt (srtr_parent srtr)))).
Proof.
  rewrite (BN.short_event_subject (res_binds res) (ssfr_stmt (srtr_parent srtr))).
  pose proof (srtr_req srtr) as Hreq. rewrite (ssfr_is_short_decl (srtr_parent srtr)) in Hreq.
  apply ofstmt_outcome_inj in Hreq.
  destruct (short_decl_decision_redecl_complete (res_binds res)
    (neg_map (res_binds res) (const_table (res_binds res) (Index.nr_file (Index.Refs.sh_node (ssfr_stmt (srtr_parent srtr)))))
      (Index.file_nodes (Index.nr_file (Index.Refs.sh_node (ssfr_stmt (srtr_parent srtr)))))) (ssfr_stmt (srtr_parent srtr)) Hreq)
    as [_ [Hcount _]]. exact Hcount.
Qed.
(* §14 the mixed boundary's existing-variable pairs: each retained ExistingVariable row with its exact RHS edge *)
Definition srtr_existing_pairs (srtr : ShortRedeclarationTypesRef)
  : list (BN.ShortRowRhsRef (BN.short_event (res_binds res) (ssfr_stmt (srtr_parent srtr)))) :=
  BN.short_existing_variable_pairs (BN.short_event (res_binds res) (ssfr_stmt (srtr_parent srtr))) (srtr_count srtr).
(* §17 total classification: every retained short statement fact is exactly an invalid, dependent or unmet row *)
Lemma short_fact_case_total (ssfr : ShortStatementFactRef) :
  (exists ifr : InvalidFactRef res, ifr_rowref ifr = ssfr_row ssfr)
  \/ (exists dfr : DependentFactRef res, dfr_rowref dfr = ssfr_row ssfr)
  \/ (exists ufr : UnmetFactRef res, ufr_rowref ufr = ssfr_row ssfr).
Proof.
  destruct (occ_cause (frr_row (ssfr_row ssfr))) as [c|] eqn:Hc.
  { left. exists (mk_ifr (ssfr_row ssfr) c Hc). reflexivity. }
  destruct (occ_dep (frr_row (ssfr_row ssfr))) as [d|] eqn:Hd.
  { right; left. exists (mk_dfr (ssfr_row ssfr) d Hd). reflexivity. }
  destruct (occ_req (frr_row (ssfr_row ssfr))) as [q|] eqn:Hq.
  { right; right. exists (mk_ufr (ssfr_row ssfr) q Hq). reflexivity. }
  exfalso.
  pose proof (ssfr_is_short_decl ssfr) as Hrow.
  rewrite Hrow in Hc, Hd, Hq.
  destruct (short_decl_decision (res_binds res)
    (neg_map (res_binds res) (const_table (res_binds res) (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))
      (Index.file_nodes (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr)))))
    (Index.Refs.sh_node (ssfr_stmt ssfr)) (Index.Refs.sh_names (ssfr_stmt ssfr))
    (Index.Refs.sh_values (ssfr_stmt ssfr)) (Index.Refs.sh_ok (ssfr_stmt ssfr))) eqn:Hdec.
  - revert Hdec. apply short_decl_decision_not_ok.
  - cbn in Hc; discriminate Hc.
  - cbn in Hq; discriminate Hq.
  - cbn in Hd; discriminate Hd.
Qed.
(* §17.2 the unmet case is never generic: an unmet short row is exactly RHS-meaning, mixed or usage, with its ref *)
Lemma short_unmet_refines (ssfr : ShortStatementFactRef) (ufr : UnmetFactRef res)
  (Hu : ufr_rowref ufr = ssfr_row ssfr) :
  (exists srmr : ShortRhsMeaningRef, srmr_parent srmr = ssfr)
  \/ (exists srtr : ShortRedeclarationTypesRef, srtr_parent srtr = ssfr)
  \/ (exists sur : ShortUsageRef, sur_parent sur = ssfr).
Proof.
  assert (Hne : occ_req (frr_row (ssfr_row ssfr)) <> None).
  { rewrite <- Hu, (ufr_ok ufr). discriminate. }
  rewrite (ssfr_is_short_decl ssfr) in Hne.
  destruct (short_decl_decision (res_binds res)
    (neg_map (res_binds res) (const_table (res_binds res) (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))
      (Index.file_nodes (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr)))))
    (Index.Refs.sh_node (ssfr_stmt ssfr)) (Index.Refs.sh_names (ssfr_stmt ssfr))
    (Index.Refs.sh_values (ssfr_stmt ssfr)) (Index.Refs.sh_ok (ssfr_stmt ssfr))) eqn:Hdec;
    cbn in Hne; try (exfalso; apply Hne; reflexivity). clear Hne.
  pose proof (short_decl_decision_unmet_guards_st (res_binds res) _ (ssfr_stmt ssfr) Hdec) as Hg.
  destruct Hg as [Hdup [Hcount [Hblk [Hnew Hneg]]]].
  destruct (find_rhs_vnonconst
    (neg_map (res_binds res) (const_table (res_binds res) (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))
      (Index.file_nodes (Index.nr_file (Index.Refs.sh_node (ssfr_stmt ssfr))))) (ssfr_stmt ssfr)) as [[j0 e0]|] eqn:Hfind.
  - left. destruct (short_rhs_meaning_construct ssfr Hdup Hcount Hblk Hnew Hneg j0 e0 Hfind) as [srmr [Hpar _]].
    exists srmr. exact Hpar.
  - destruct (Bool.bool_dec (existsb BN.is_existing_var_row
      (BN.se_rows (BN.short_event (res_binds res) (ssfr_stmt ssfr)))) true) as [Hmix | Hmix].
    + right; left. destruct (short_redecl_construct ssfr Hdup Hcount Hblk Hnew Hneg Hfind Hmix) as [srtr Hpar].
      exists srtr. exact Hpar.
    + right; right. apply Bool.not_true_is_false in Hmix.
      destruct (short_usage_construct ssfr Hdup Hcount Hblk Hnew Hneg Hfind Hmix) as [sur Hpar].
      exists sur. exact Hpar.
Qed.
(* §20 result-level reachability: every short statement reaches its exact retained fact and its exact case ref *)
Lemma short_case_for (st : Index.Refs.ShortStmtRef (res_index res)) :
  exists ssfr : ShortStatementFactRef, ssfr_stmt ssfr = st
    /\ ( (exists ifr : InvalidFactRef res, ifr_rowref ifr = ssfr_row ssfr)
       \/ (exists dfr : DependentFactRef res, dfr_rowref dfr = ssfr_row ssfr)
       \/ (exists srmr : ShortRhsMeaningRef, srmr_parent srmr = ssfr)
       \/ (exists srtr : ShortRedeclarationTypesRef, srtr_parent srtr = ssfr)
       \/ (exists sur : ShortUsageRef, sur_parent sur = ssfr) ).
Proof.
  destruct (short_statement_fact st) as [ssfr|] eqn:E;
    [ | exfalso; exact (short_statement_fact_complete st E) ].
  exists ssfr. split; [ exact (short_statement_fact_stmt st ssfr E) | ].
  destruct (short_fact_case_total ssfr) as [Hi | [Hd | Hu]].
  - left. exact Hi.
  - right; left. exact Hd.
  - right; right. destruct Hu as [ufr Hufr].
    destruct (short_unmet_refines ssfr ufr Hufr) as [Hm | [Hr | Hg]].
    + left. exact Hm.
    + right; left. exact Hr.
    + right; right. exact Hg.
Qed.
End FactRowLaws.
Arguments frr_key {p res} ref.
Arguments nfr_class {p res child_row} _.
Arguments cdfr_site {p res} _. Arguments cdfr_edge_site {p res} _.
Arguments cdfr_edge_kind {p res} _. Arguments cpr_neg {p res cdfr} _.
Arguments mk_cdfr {p res} _ _ _ _. Arguments mk_cpr {p res cdfr} _ _ _.
Arguments ChildInvalid {p res child_row} _ _.
Arguments ChildUnmet {p res child_row} _ _.
Arguments ChildDependent {p res child_row} _ _.
Arguments cpr_child_row {p res cdfr} _. Arguments cpr_lookup {p res cdfr} _.
Arguments ssfr_stmt {p res} _. Arguments ssfr_row {p res} _. Arguments ssfr_site {p res} _. Arguments ssfr_kind {p res} _.
Arguments nvfr_rowref {p res} _. Arguments nvfr_site {p res} _. Arguments nvfr_is {p res} _. Arguments nvfr_kind {p res} _.
Arguments srmr_parent {p res} _. Arguments srmr_j {p res} _. Arguments srmr_edge {p res} _. Arguments srmr_child {p res} _.
Arguments srmr_req {p res} _. Arguments srmr_child_at {p res} _. Arguments srmr_lookup {p res} _.
Arguments sovr_site {p res} _. Arguments sovr_name {p res} _. Arguments sovr_view {p res} _.
Arguments sovr_sn {p res} _. Arguments sovr_res {p res} _. Arguments sovr_row {p res} _.
Arguments sovr_at {p res} _. Arguments sovr_lookup {p res} _.
Arguments sovr_origin_stmt {p res} _. Arguments sovr_origin_ix {p res} _. Arguments sovr_origin_edge {p res} _.
Arguments sur_parent {p res} _. Arguments sur_req {p res} _. Arguments sur_new_rows {p res} _.
Arguments srtr_parent {p res} _. Arguments srtr_req {p res} _.
Arguments srtr_existing_rows {p res} _. Arguments srtr_new_rows {p res} _.

(* an exact use context of a redeclared root: a name occurrence whose exact resolution yields that exact root *)
Record RedeclaredUseRef {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} {n : Names.OrdinaryIdentifier} (root : BN.RedeclRoot bp n) : Type := mk_redeclared_use {
  ruc_node   : Index.NodeRef idx ;
  ruc_res    : BN.ResolutionRef (BN.use_env bp ruc_node) n ;
  ruc_yields : BN.resolution_redecl_root ruc_res = Some root
}.
Arguments mk_redeclared_use {p idx s bd bp n root} _ _ _.
Arguments ruc_node {p idx s bd bp n root} _.
Arguments ruc_res {p idx s bd bp n root} _.
Arguments ruc_yields {p idx s bd bp n root} _.

(* an issue roots at an exact node, an exact package, or an exact redeclaration root; never a self-fallback *)
Inductive IssueRoot {p} (r : Result p) : Type :=
| RootNode : Index.NodeRef (res_index r) -> IssueRoot r
| RootPackage : BN.PI.PackageRef (res_surface r) -> IssueRoot r
| RootGroup : forall (n : Names.OrdinaryIdentifier), BN.RedeclRoot (res_binds r) n -> IssueRoot r.
Arguments RootNode {p r} _.
Arguments RootPackage {p r} _.
Arguments RootGroup {p r n} _.

(* the exact diagnostics of one Result: a package invalidity is exactly its retained decision case ref of r *)
Inductive Diagnostic {p} (r : Result p) : Type :=
| DOcc : InvalidFactRef r -> Diagnostic r
| DMissingMain : MissingMainRef r -> Diagnostic r
| DOutputCollision : CollisionRef r -> Diagnostic r
| DRedeclaredGroup : forall (n : Names.OrdinaryIdentifier), BN.RedeclRoot (res_binds r) n -> Diagnostic r.
Arguments DOcc {p r} _.
Arguments DMissingMain {p r} _.
Arguments DOutputCollision {p r} _.
Arguments DRedeclaredGroup {p r n} _.

(* the exact boundaries of one Result: an occurrence-family unmet requirement is exactly its unmet fact-row ref *)
Inductive Boundary {p} (r : Result p) : Type :=
| BOcc : UnmetFactRef r -> Boundary r.
Arguments BOcc {p r} _.

(* the issue cause a reader projects from a diagnostic row, exactly as retained, never re-derived from a weaker site *)
Inductive IssueCause {p} (r : Result p) : Type :=
| OccCause : InvalidFactRef r -> IssueCause r
| MissingMainCause : MissingMainRef r -> IssueCause r
| OutputCollisionCause : CollisionRef r -> IssueCause r
| RedeclaredGroupCause : forall (n : Names.OrdinaryIdentifier), BN.RedeclRoot (res_binds r) n -> IssueCause r.
Arguments OccCause {p r} _.
Arguments MissingMainCause {p r} _.
Arguments OutputCollisionCause {p r} _.
Arguments RedeclaredGroupCause {p r n} _.

Section IssueProjections.
Context {p : Syntax.Program} {r : Result p}.
Let idx := res_index r.
Let bp  := res_binds r.

(* related nodes a cause carries: a complex mismatch's two components (all other causes carry none directly) *)
Definition cause_related {site : Index.NodeRef idx} {k : FactKind} (c : Cause bp site k) : list (Index.NodeRef idx) :=
  match c with ComplexMismatch _ a b => [a; b] | _ => [] end.
(* the cause a row retains: the exact invalid fact-row ref or exact package-decision case, projected exactly *)
Definition diag_cause (d : Diagnostic r) : IssueCause r :=
  match d with
  | DOcc ifr => OccCause ifr
  | DMissingMain mmr => MissingMainCause mmr
  | DOutputCollision cr => OutputCollisionCause cr
  | DRedeclaredGroup root => RedeclaredGroupCause root
  end.
Definition diag_family (d : Diagnostic r) : option Family :=
  match d with DOcc ifr => Some (fact_family (ifr_fact ifr)) | _ => None end.
(* related nodes a row projects: the cause's components, or a group's exact members (use contexts via Report) *)
Definition diag_related (d : Diagnostic r) : list (Index.NodeRef idx) :=
  match d with
  | DOcc ifr => cause_related (ifr_cause ifr)
  | DRedeclaredGroup root => map (fun m => BN.est_node (BN.es_est m)) (BN.bg_members (BN.rr_group (projT2 root)))
  | _ => []
  end.
Definition diag_root (d : Diagnostic r) : IssueRoot r :=
  match d with
  | DOcc ifr => RootNode (fact_site (ifr_fact ifr))
  | DMissingMain mmr => RootPackage (mmr_package mmr)
  | DOutputCollision cr => RootPackage (cr_package cr)
  | DRedeclaredGroup root => RootGroup root
  end.
Definition bound_req_ref (b : Boundary r) : UnmetFactRef r := match b with BOcc ufr => ufr end.
Definition bound_family (b : Boundary r) : Family := match b with BOcc ufr => fact_family (ufr_fact ufr) end.
Definition bound_root (b : Boundary r) : IssueRoot r := match b with BOcc ufr => RootNode (fact_site (ufr_fact ufr)) end.

(* §18.3 occurrence-row projections are exact: cause/family/root of a DOcc project from its retained invalid fact *)
Lemma docc_cause (ifr : InvalidFactRef r) : diag_cause (DOcc ifr) = OccCause ifr.
Proof. reflexivity. Qed.
Lemma docc_family (ifr : InvalidFactRef r) : diag_family (DOcc ifr) = Some (fact_family (ifr_fact ifr)).
Proof. reflexivity. Qed.
Lemma docc_root (ifr : InvalidFactRef r) : diag_root (DOcc ifr) = RootNode (fact_site (ifr_fact ifr)).
Proof. reflexivity. Qed.
(* §18.3 the invalid fact ref's exact cause is exactly the outcome payload its retained fact carries *)
Lemma ifr_cause_of_fact (ifr : InvalidFactRef r) : occ_cause (ifr_fact ifr) = Some (ifr_cause ifr).
Proof. exact (ifr_ok ifr). Qed.
(* §18.3 boundary-row projections are exact: requirement/family/root of a BOcc project from its retained unmet fact *)
Lemma bocc_req (ufr : UnmetFactRef r) : bound_req_ref (BOcc ufr) = ufr.
Proof. reflexivity. Qed.
Lemma bocc_family (ufr : UnmetFactRef r) : bound_family (BOcc ufr) = fact_family (ufr_fact ufr).
Proof. reflexivity. Qed.
Lemma bocc_root (ufr : UnmetFactRef r) : bound_root (BOcc ufr) = RootNode (fact_site (ufr_fact ufr)).
Proof. reflexivity. Qed.
Lemma ufr_req_of_fact (ufr : UnmetFactRef r) : occ_req (ufr_fact ufr) = Some (ufr_req ufr).
Proof. exact (ufr_ok ufr). Qed.

End IssueProjections.

Section IssueTable.
Context {p : Syntax.Program} (res : Result p).

(* one retained row yields one diagnostic iff its outcome is invalid: the exact invalid fact-row ref, no free fields *)
Definition occ_diag_rows (ref : FactRowRef res) : list (Diagnostic res) :=
  match occ_cause (frr_row ref) as oc return occ_cause (frr_row ref) = oc -> list (Diagnostic res) with
  | Some c => fun H => [DOcc (mk_ifr ref c H)]
  | None => fun _ => []
  end eq_refl.
(* one exact retained row yields one boundary exactly when its outcome is unmet; invalid and unmet coexist (§6) *)
Definition occ_bound_rows (ref : FactRowRef res) : list (Boundary res) :=
  match occ_req (frr_row ref) as oq return occ_req (frr_row ref) = oq -> list (Boundary res) with
  | Some q => fun H => [BOcc (mk_ufr ref q H)]
  | None => fun _ => []
  end eq_refl.

(* the sole selected package's default-output collision projects the exact retained preflight collision case *)
Definition collision_rows : list (Diagnostic res) :=
  match result_collision_ref res with Some cr => [DOutputCollision cr] | None => [] end.
(* one missing-executable-entry diagnostic per package whose exact canonical main decision IS MainMissing *)
Definition main_rows : list (Diagnostic res) :=
  map DMissingMain (result_missing_main_refs res).

(* every package-member name occurrence: the use sites a redeclared group can contextualize *)
Definition name_uses : list (Index.NodeRef (res_index res)) :=
  filter (fun r => match Index.node_view r with Index.Model.VName _ => true | _ => false end)
         (flat_map Index.file_nodes (flat_map BN.PI.pkg_members (BN.PI.packages (res_surface res)))).
(* one exact use context: a use of root's name resolving by exact-identity check to that exact root, with proof *)
Definition use_context_of {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot (res_binds res) n0)
  (r : Index.NodeRef (res_index res)) : option (RedeclaredUseRef root) :=
  match Index.node_view r with
  | Index.Model.VName n =>
      match BN.ordinary_eq_dec n n0 with
      | left _ =>
          match BN.option_redeclroot_eq_dec (BN.resolution_redecl_root (BN.resolve (res_binds res) r n0)) (Some root) with
          | left Hyields => Some (mk_redeclared_use r (BN.resolve (res_binds res) r n0) Hyields)
          | right _ => None
          end
      | right _ => None
      end
  | _ => None
  end.
(* the exact use-site contexts of a redeclared root: uses of its name resolving, by exact identity, to it *)
Definition group_use_contexts {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot (res_binds res) n0)
  : list (RedeclaredUseRef root) :=
  flat_map (fun r => match use_context_of root r with Some c => [c] | None => [] end) name_uses.

(* a returned use context's node is exactly the name occurrence it was built from *)
Lemma use_context_of_node {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot (res_binds res) n0)
  (r : Index.NodeRef (res_index res)) (c : RedeclaredUseRef root) : use_context_of root r = Some c -> ruc_node c = r.
Proof.
  intro H. unfold use_context_of in H.
  destruct (Index.node_view r); try discriminate H.
  match type of H with context[BN.ordinary_eq_dec ?a ?b] => destruct (BN.ordinary_eq_dec a b) end; try discriminate H.
  match type of H with context[BN.option_redeclroot_eq_dec ?a ?b] => destruct (BN.option_redeclroot_eq_dec a b) end;
    try discriminate H.
  injection H as H. subst c. reflexivity.
Qed.

(* map proj over an option-collecting flat_map = filter, when proj recovers each collected element's source *)
Lemma flatmap_option_filter {A B} (f : A -> option B) (g : B -> A)
  (Hg : forall a b, f a = Some b -> g b = a) (L : list A) :
  map g (flat_map (fun a => match f a with Some b => [b] | None => nil end) L)
  = filter (fun a => match f a with Some _ => true | None => false end) L.
Proof.
  induction L as [|a rest IH]; [reflexivity|]. cbn. destruct (f a) as [b|] eqn:E.
  - cbn. rewrite (Hg a b E), IH. reflexivity.
  - exact IH.
Qed.

(* §24.4 ordering + completeness handle: the context nodes are exactly the qualifying name uses, in source order *)
Definition context_qualifies {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot (res_binds res) n0) (r : Index.NodeRef (res_index res)) : bool :=
  match use_context_of root r with Some _ => true | None => false end.
Lemma group_use_contexts_nodes {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot (res_binds res) n0) :
  map ruc_node (group_use_contexts root) = filter (context_qualifies root) name_uses.
Proof. exact (flatmap_option_filter (use_context_of root) ruc_node (use_context_of_node root) name_uses). Qed.

(* the package name occurrences are duplicate-free: distinct positions within a file, distinct files across packages *)
Lemma name_uses_nodup : NoDup name_uses.
Proof.
  unfold name_uses. apply nodup_filter.
  apply (BN.flat_map_nodup_key _ Index.nr_file (fun fr => fr)).
  - rewrite map_id.
    apply (BN.flat_map_nodup_key _ (BN.PI.package_of_file (res_surface res)) (fun pr => pr)).
    + rewrite map_id. apply BN.packages_nodup.
    + intros pr _. apply BN.pkg_members_nodup.
    + intros pr fr _ Hin. exact (BN.PI.package_of_file_member (res_surface res) pr fr Hin).
  - intros fr _. apply file_nodes_nodup.
  - intros fr r _ Hin. exact (Index.file_nodes_file fr r Hin).
Qed.

(* §24.4 uniqueness / no-duplication: no name occurrence appears twice as a use context of a root *)
Lemma group_use_contexts_nodup {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot (res_binds res) n0) :
  NoDup (map ruc_node (group_use_contexts root)).
Proof. rewrite group_use_contexts_nodes. apply nodup_filter. exact name_uses_nodup. Qed.

(* a name occurrence of the root's name resolving to that exact root does have a context *)
Lemma use_context_of_complete {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot (res_binds res) n0) (r : Index.NodeRef (res_index res)) :
  Index.node_view r = Index.Model.VName n0 ->
  BN.resolution_redecl_root (BN.resolve (res_binds res) r n0) = Some root ->
  exists c, use_context_of root r = Some c.
Proof.
  intros Hv Hres. unfold use_context_of. rewrite Hv.
  destruct (BN.ordinary_eq_dec n0 n0) as [_|Hne]; [| exfalso; apply Hne; reflexivity].
  destruct (BN.option_redeclroot_eq_dec (BN.resolution_redecl_root (BN.resolve (res_binds res) r n0)) (Some root)) as [Hy|Hne];
    [ eexists; reflexivity | exfalso; apply Hne; exact Hres ].
Qed.

(* §24.4 completeness: every relevant use of the root's name resolving to it appears among its contexts *)
Lemma group_use_context_complete {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot (res_binds res) n0) (r : Index.NodeRef (res_index res)) :
  In r name_uses -> Index.node_view r = Index.Model.VName n0 ->
  BN.resolution_redecl_root (BN.resolve (res_binds res) r n0) = Some root ->
  In r (map ruc_node (group_use_contexts root)).
Proof.
  intros Hin Hv Hres. destruct (use_context_of_complete root r Hv Hres) as [c HE].
  rewrite <- (use_context_of_node root r c HE). apply in_map. unfold group_use_contexts.
  apply in_flat_map. exists r. split; [ exact Hin | rewrite HE; left; reflexivity ].
Qed.
(* one redeclared-group diagnostic per exact enumerated root; use contexts stay off the disposition path (on demand) *)
Definition group_rows : list (Diagnostic res) :=
  map (fun rr => DRedeclaredGroup (projT2 rr)) (BN.redeclaration_roots (res_binds res)).

(* §24.4 diagnostic enumeration: the group diagnostics are exactly one DRedeclaredGroup per exact enumerated root *)
Lemma group_rows_enumerated :
  group_rows = map (fun rr => DRedeclaredGroup (projT2 rr)) (BN.redeclaration_roots (res_binds res)).
Proof. reflexivity. Qed.

(* the diagnostics and boundaries over a given row enumeration, so result_issues can bind and share it once *)
Definition result_diagnostic_rows (rows : list (FactRowRef res)) : list (Diagnostic res) :=
  collision_rows ++ main_rows ++ group_rows ++ flat_map occ_diag_rows rows.
Definition result_boundary_rows (rows : list (FactRowRef res)) : list (Boundary res) :=
  flat_map occ_bound_rows rows.
(* occurrence diagnostics/boundaries derive FROM the exact retained rows (fact_rows res), not from standalone facts *)
Definition occ_diags : list (Diagnostic res) := flat_map occ_diag_rows (fact_rows res).

(* the canonical order: output collision, package main, ordinary redeclaration, then occurrence in fact-row order *)
Definition result_diagnostics : list (Diagnostic res) := collision_rows ++ main_rows ++ group_rows ++ occ_diags.
Definition result_boundaries : list (Boundary res) := flat_map occ_bound_rows (fact_rows res).

(* §19.3 the package diagnostic rows ARE the exact case-ref projections; neither re-tests the semantic condition *)
Lemma collision_rows_ref : collision_rows = match result_collision_ref res with Some cr => [DOutputCollision cr] | None => [] end.
Proof. reflexivity. Qed.
Lemma main_rows_refs : main_rows = map DMissingMain (result_missing_main_refs res).
Proof. reflexivity. Qed.
(* §19.3/§21 the collision-before-main-before-redeclaration-before-occurrence category order is unchanged *)
Lemma diagnostics_order : result_diagnostics = collision_rows ++ main_rows ++ group_rows ++ occ_diags.
Proof. reflexivity. Qed.

(* one row yields a diagnostic XOR a boundary; distinct-family facts of one subject still coexist across rows (§6) *)
Lemma occ_row_exclusive (ref : FactRowRef res) : occ_diag_rows ref <> [] -> occ_bound_rows ref = [].
Proof.
  destruct ref as [o row Hat]; destruct row as [r ov | r oa | r os | r ot];
    [ destruct ov | destruct oa | destruct os | destruct ot ];
    cbn; intro H; solve [ reflexivity | exfalso; exact (H eq_refl) ].
Qed.

(* §18.1 the displayed family is exactly the total projection of the exact site and fact kind, never a stored field *)
Lemma fact_family_projection (o : OccFact (res_binds res)) : fact_family o = displayed_family (fact_site o) (fact_kind o).
Proof. reflexivity. Qed.
(* §18.2 an occurrence fact's exact site and kind round-trip from the constructor that built it *)
Lemma occfact_roundtrip (r : Index.NodeRef (res_index res)) (ov : ValueOutcome (res_binds res) r) (oa : AppOutcome (res_binds res) r)
  (os : StmtOutcome (res_binds res) r) (ot : TypeUseOutcome (res_binds res) r) :
  (fact_site (OFValue r ov) = r /\ fact_kind (OFValue r ov) = ValueKind)
  /\ (fact_site (OFApp r oa) = r /\ fact_kind (OFApp r oa) = ApplicationKind)
  /\ (fact_site (OFStmt r os) = r /\ fact_kind (OFStmt r os) = StatementKind)
  /\ (fact_site (OFType r ot) = r /\ fact_kind (OFType r ot) = TypeUseKind).
Proof. repeat split; reflexivity. Qed.

(* §18.3 diagnostic completeness: an invalid row yields exactly one DOcc retaining that exact row *)
Lemma occ_diag_complete (ref : FactRowRef res) (c : Cause (res_binds res) (fact_site (frr_row ref)) (fact_kind (frr_row ref))) :
  occ_cause (frr_row ref) = Some c -> exists ifr, occ_diag_rows ref = [DOcc ifr] /\ ifr_rowref ifr = ref.
Proof.
  destruct ref as [o row Hat]; destruct row as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; intro H; try discriminate H; eexists; split; reflexivity.
Qed.
(* a row with no invalid outcome yields no diagnostic row *)
Lemma occ_diag_none (ref : FactRowRef res) : occ_cause (frr_row ref) = None -> occ_diag_rows ref = [].
Proof.
  destruct ref as [o row Hat]; destruct row as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; intro H; solve [ reflexivity | discriminate H ].
Qed.
(* §18.3 diagnostic soundness: every occurrence diagnostic row is a DOcc of the exact retained row, no free fields *)
Lemma occ_diag_row_shape (ref : FactRowRef res) (d : Diagnostic res) :
  In d (occ_diag_rows ref) -> exists ifr, d = DOcc ifr /\ ifr_rowref ifr = ref.
Proof.
  destruct ref as [o row Hat]; destruct row as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; intro Hin; try (exfalso; exact Hin);
    destruct Hin as [Heq|[]]; subst d; eexists; split; reflexivity.
Qed.
(* §18.3 boundary completeness: an unmet row yields exactly one BOcc retaining that exact row *)
Lemma occ_bound_complete (ref : FactRowRef res) (q : Requirement (res_binds res) (fact_site (frr_row ref)) (fact_kind (frr_row ref))) :
  occ_req (frr_row ref) = Some q -> exists ufr, occ_bound_rows ref = [BOcc ufr] /\ ufr_rowref ufr = ref.
Proof.
  destruct ref as [o row Hat]; destruct row as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; intro H; try discriminate H; eexists; split; reflexivity.
Qed.
(* a row with no unmet outcome yields no boundary row *)
Lemma occ_bound_none (ref : FactRowRef res) : occ_req (frr_row ref) = None -> occ_bound_rows ref = [].
Proof.
  destruct ref as [o row Hat]; destruct row as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; intro H; solve [ reflexivity | discriminate H ].
Qed.
(* §18.3 boundary soundness: every occurrence boundary row is a BOcc of the exact retained row, no free fields *)
Lemma occ_bound_row_shape (ref : FactRowRef res) (b : Boundary res) :
  In b (occ_bound_rows ref) -> exists ufr, b = BOcc ufr /\ ufr_rowref ufr = ref.
Proof.
  destruct ref as [o row Hat]; destruct row as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; intro Hin; try (exfalso; exact Hin);
    destruct Hin as [Heq|[]]; subst b; eexists; split; reflexivity.
Qed.
(* §18.3 at most one row of each class per retained row: the row lists are empty or a single exact row *)
Lemma occ_diag_rows_le1 (ref : FactRowRef res) : occ_diag_rows ref = [] \/ exists d, occ_diag_rows ref = [d].
Proof.
  destruct ref as [o row Hat]; destruct row as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; solve [ left; reflexivity | right; eexists; reflexivity ].
Qed.
Lemma occ_bound_rows_le1 (ref : FactRowRef res) : occ_bound_rows ref = [] \/ exists b, occ_bound_rows ref = [b].
Proof.
  destruct ref as [o row Hat]; destruct row as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; solve [ left; reflexivity | right; eexists; reflexivity ].
Qed.
(* §17.3/§18.3 a dependent outcome retains no cause or requirement, so its exact row yields no occurrence row *)
Lemma occ_dep_no_cause (o : OccFact (res_binds res)) (d : Dependency (res_binds res) (fact_site o) (fact_kind o)) :
  occ_dep o = Some d -> occ_cause o = None.
Proof.
  destruct o as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; intro H; solve [ reflexivity | discriminate H ].
Qed.
Lemma occ_dep_no_req (o : OccFact (res_binds res)) (d : Dependency (res_binds res) (fact_site o) (fact_kind o)) :
  occ_dep o = Some d -> occ_req o = None.
Proof.
  destruct o as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; intro H; solve [ reflexivity | discriminate H ].
Qed.
Lemma dependent_fact_no_rows (dfr : DependentFactRef res) :
  occ_diag_rows (dfr_rowref dfr) = [] /\ occ_bound_rows (dfr_rowref dfr) = [].
Proof.
  destruct dfr as [ref d Hok]; cbn; split;
    [ apply occ_diag_none; exact (occ_dep_no_cause (frr_row ref) d Hok)
    | apply occ_bound_none; exact (occ_dep_no_req (frr_row ref) d Hok) ].
Qed.

End IssueTable.

(* b46901b4 data-threaded disposition kernel — the data_* readers below derive emptiness from ONE d, no ref built *)
Lemma map_eq_nil_iff {A B} (f : A -> B) (l : list A) : map f l = [] <-> l = [].
Proof. destruct l; cbn; (split; [ | ]); intro H; solve [ reflexivity | discriminate H ]. Qed.

Lemma flat_map_eq_nil {A B} (f : A -> list B) (l : list A) :
  flat_map f l = [] <-> (forall x, In x l -> f x = []).
Proof.
  induction l as [|a l IH]; cbn.
  - split; [ intros _ x Hx; destruct Hx | reflexivity ].
  - split.
    + intro H. apply app_eq_nil in H as [Ha Hl]. intros x [->|Hx]; [ exact Ha | exact (proj1 IH Hl x Hx) ].
    + intro H. rewrite (H a (or_introl eq_refl)); cbn. apply (proj2 IH). intros x Hx. apply H. right; exact Hx.
Qed.

Lemma forallb_negb_filter {A} (f : A -> bool) (l : list A) :
  forallb (fun x => negb (f x)) l = true <-> filter f l = [].
Proof.
  induction l as [|a l IH]; cbn; [ split; reflexivity | ].
  destruct (f a) eqn:Ea; cbn; [ split; intro H; discriminate H | exact IH ].
Qed.

Lemma app4_nil {A} (a b c d : list A) :
  a ++ b ++ c ++ d = [] <-> a = [] /\ b = [] /\ c = [] /\ d = [].
Proof.
  split.
  - destruct a, b, c, d; cbn; intro H; try discriminate H; repeat split.
  - intros [-> [-> [-> ->]]]; reflexivity.
Qed.

Lemma forallb_ext {A} (f g : A -> bool) (l : list A) :
  (forall x, f x = g x) -> forallb f l = forallb g l.
Proof. intro H. induction l as [|a l IH]; cbn; [ reflexivity | rewrite H, IH; reflexivity ]. Qed.

Lemma opt_match_none {A} (o : option A) :
  match o with Some _ => false | None => true end = true -> o = None.
Proof. destruct o; [ discriminate | reflexivity ]. Qed.

Lemma opt_none_match {A} (o : option A) :
  o = None -> match o with Some _ => false | None => true end = true.
Proof. intro H; rewrite H; reflexivity. Qed.

(* every emptiness the branch decision needs, computed from the one d, no ref built *)
Definition data_no_collision {p} (d : ResultData p) : bool :=
  match proj1_sig (rd_pkg d) with FreshOk => true | FreshCollision _ _ => false end.
Definition data_no_missing {p} (d : ResultData p) : bool :=
  forallb (fun pr => match BN.package_main (rd_binds d) pr with BN.MainMissing => false | _ => true end)
          (BN.PI.packages (rd_surface d)).
Definition data_no_redecl {p} (d : ResultData p) : bool :=
  match BN.redeclaration_roots (rd_binds d) with nil => true | _ :: _ => false end.
Definition data_no_cause {p} (d : ResultData p) : bool :=
  forallb (fun row => match occ_cause row with Some _ => false | None => true end) (proj1_sig (rd_facts d)).
Definition data_no_req {p} (d : ResultData p) : bool :=
  forallb (fun row => match occ_req row with Some _ => false | None => true end) (proj1_sig (rd_facts d)).

Definition data_diagnostics_empty {p} (d : ResultData p) : bool :=
  data_no_collision d && data_no_missing d && data_no_redecl d && data_no_cause d.
Definition data_boundaries_empty {p} (d : ResultData p) : bool := data_no_req d.

(* each d-level emptiness matches the exact list builder over the same Result, one category at a time *)
Lemma dnc_iff {p} (r : Result p) : data_no_collision (data_of_result r) = true <-> collision_rows r = [].
Proof.
  unfold data_no_collision, collision_rows.
  change (proj1_sig (rd_pkg (data_of_result r))) with (result_preflight r).
  destruct (result_preflight r) as [|pr rr] eqn:E.
  - rewrite (proj2 (collision_ref_none r) E); cbn. split; reflexivity.
  - assert (result_collision_ref r <> None) as Hne
      by (intro Hn; apply collision_ref_none in Hn; rewrite Hn in E; discriminate E).
    destruct (result_collision_ref r) as [cr|]; [ | exfalso; apply Hne; reflexivity ].
    cbn. split; intro H; discriminate H.
Qed.

(* per package: "not MainMissing" is the negation of is_missing — negb outside the match, so only propositionally *)
Lemma data_no_missing_pred {p} (r : Result p) (pr : BN.PI.PackageRef (res_surface r)) :
  (match BN.package_main (rd_binds (data_of_result r)) pr with BN.MainMissing => false | _ => true end)
  = negb (@is_missing p r pr).
Proof.
  unfold is_missing.
  change (BN.package_main (rd_binds (data_of_result r)) pr) with (result_package_rule r pr).
  destruct (result_package_rule r pr); reflexivity.
Qed.

Lemma dnm_iff {p} (r : Result p) : data_no_missing (data_of_result r) = true <-> main_rows r = [].
Proof.
  unfold main_rows. rewrite map_eq_nil_iff.
  assert (data_no_missing (data_of_result r)
          = forallb (fun pr => negb (@is_missing p r pr)) (BN.PI.packages (res_surface r))) as Hrw.
  { unfold data_no_missing.
    change (BN.PI.packages (rd_surface (data_of_result r))) with (BN.PI.packages (res_surface r)).
    apply forallb_ext. intro pr. apply data_no_missing_pred. }
  rewrite Hrw, forallb_negb_filter.
  split.
  - intro H. apply (proj1 (map_eq_nil_iff mmr_package (result_missing_main_refs r))).
    rewrite missing_main_packages. exact H.
  - intro H. rewrite <- missing_main_packages, H. reflexivity.
Qed.

Lemma dnr_iff {p} (r : Result p) : data_no_redecl (data_of_result r) = true <-> group_rows r = [].
Proof.
  unfold group_rows.
  replace (data_no_redecl (data_of_result r))
     with (match BN.redeclaration_roots (res_binds r) with nil => true | _ :: _ => false end) by reflexivity.
  destruct (BN.redeclaration_roots (res_binds r)) as [|x xs]; cbn;
    [ split; reflexivity | split; intro H; discriminate H ].
Qed.

(* an empty occ-diagnostic/boundary row list means the retained row carried no invalid/unmet outcome *)
Lemma occ_cause_of_diag_none {p} (r : Result p) (ref : FactRowRef r) :
  occ_diag_rows r ref = [] -> occ_cause (frr_row ref) = None.
Proof.
  intro H. remember (occ_cause (frr_row ref)) as oc eqn:Ec. destruct oc as [c|]; [ | reflexivity ].
  exfalso. symmetry in Ec. destruct (occ_diag_complete r ref c Ec) as [ifr [Hd _]]. rewrite Hd in H. discriminate H.
Qed.
Lemma occ_req_of_bound_none {p} (r : Result p) (ref : FactRowRef r) :
  occ_bound_rows r ref = [] -> occ_req (frr_row ref) = None.
Proof.
  intro H. remember (occ_req (frr_row ref)) as oq eqn:Ec. destruct oq as [q|]; [ | reflexivity ].
  exfalso. symmetry in Ec. destruct (occ_bound_complete r ref q Ec) as [ufr [Hb _]]. rewrite Hb in H. discriminate H.
Qed.

Lemma dncause_iff {p} (r : Result p) : data_no_cause (data_of_result r) = true <-> occ_diags r = [].
Proof.
  unfold data_no_cause, occ_diags.
  change (proj1_sig (rd_facts (data_of_result r))) with (result_fact_list r).
  split.
  - intro Hf. apply (proj2 (flat_map_eq_nil _ _)). intros ref Href. apply occ_diag_none.
    assert (In (frr_row ref) (result_fact_list r)) as Hin
      by (rewrite <- fact_rows_rows; apply in_map; exact Href).
    pose proof (proj1 (forallb_forall _ _) Hf (frr_row ref) Hin) as Hrow. cbv beta in Hrow.
    exact (opt_match_none _ Hrow).
  - intro Hnil. apply (proj2 (forallb_forall _ _)). intros row Hrow.
    destruct (fact_list_row r row Hrow) as [ref [Href Hrow_eq]].
    pose proof (proj1 (flat_map_eq_nil _ _) Hnil ref Href) as Hdr.
    rewrite <- Hrow_eq; cbv beta.
    apply opt_none_match. exact (occ_cause_of_diag_none r ref Hdr).
Qed.

Lemma dnreq_iff {p} (r : Result p) : data_no_req (data_of_result r) = true <-> result_boundaries r = [].
Proof.
  unfold data_no_req, result_boundaries.
  change (proj1_sig (rd_facts (data_of_result r))) with (result_fact_list r).
  split.
  - intro Hf. apply (proj2 (flat_map_eq_nil _ _)). intros ref Href. apply occ_bound_none.
    assert (In (frr_row ref) (result_fact_list r)) as Hin
      by (rewrite <- fact_rows_rows; apply in_map; exact Href).
    pose proof (proj1 (forallb_forall _ _) Hf (frr_row ref) Hin) as Hrow. cbv beta in Hrow.
    exact (opt_match_none _ Hrow).
  - intro Hnil. apply (proj2 (forallb_forall _ _)). intros row Hrow.
    destruct (fact_list_row r row Hrow) as [ref [Href Hrow_eq]].
    pose proof (proj1 (flat_map_eq_nil _ _) Hnil ref Href) as Hbr.
    rewrite <- Hrow_eq; cbv beta.
    apply opt_none_match. exact (occ_req_of_bound_none r ref Hbr).
Qed.

(* the two public bridges: the branch decision's emptiness IS the exact diagnostics/boundaries emptiness *)
Lemma data_diagnostics_empty_correct {p} (r : Result p) :
  data_diagnostics_empty (data_of_result r) = true <-> result_diagnostics r = [].
Proof.
  unfold data_diagnostics_empty, result_diagnostics.
  rewrite !andb_true_iff, dnc_iff, dnm_iff, dnr_iff, dncause_iff, app4_nil. tauto.
Qed.

Lemma data_boundaries_empty_correct {p} (r : Result p) :
  data_boundaries_empty (data_of_result r) = true <-> result_boundaries r = [].
Proof. unfold data_boundaries_empty. apply dnreq_iff. Qed.


Section IssueLaws.
Context {p : Syntax.Program} {r : Result p}.
Let bp := res_binds r.

(* the root algebra is total: every diagnostic roots at an exact node, package, or group, never a self-fallback *)
Lemma root_algebra_total (d : Diagnostic r) :
  (exists nd, diag_root d = RootNode nd) \/ (exists pr, diag_root d = RootPackage pr)
  \/ (exists (n : Names.OrdinaryIdentifier) (root : BN.RedeclRoot bp n), diag_root d = RootGroup root).
Proof. destruct d; cbn; eauto 8. Qed.

(* §24.4 soundness: every exact use context's exact resolution yields exactly the root it is a context of *)
Lemma redeclared_use_sound {n0 : Names.OrdinaryIdentifier} {root : BN.RedeclRoot bp n0}
  (c : RedeclaredUseRef root) : BN.resolution_redecl_root (ruc_res c) = Some root.
Proof. exact (ruc_yields c). Qed.

(* §24.4 exact-root identity: a context belongs to no root other than the exact one its resolution yields *)
Lemma redeclared_use_root_unique {n0 : Names.OrdinaryIdentifier} {r1 r2 : BN.RedeclRoot bp n0}
  (c : RedeclaredUseRef r1) : BN.resolution_redecl_root (ruc_res c) = Some r2 -> r1 = r2.
Proof. intro H. pose proof (ruc_yields c) as Hy. rewrite Hy in H. injection H as H. exact H. Qed.

(* §24.4 diagnostic-root identity: a redeclared-group diagnostic roots at exactly the exact root it retains *)
Lemma diag_group_root {n : Names.OrdinaryIdentifier} (root : BN.RedeclRoot bp n) :
  diag_root (DRedeclaredGroup root : Diagnostic r) = RootGroup root.
Proof. reflexivity. Qed.

End IssueLaws.

(* §17 the child prerequisites of the one retained result, a narrow projection from its exact res_facts *)
Definition result_child_prerequisites {p} (r : Result p)
  : list { cdfr : ChildDependentFactRef r & ChildPrerequisiteRef r cdfr } :=
  child_prerequisite_refs r.

(* an issue is a diagnostic or a boundary; the two classes partition the one canonical sequence *)
Inductive IssueClass : Type := ClassDiagnostic | ClassBoundary.

Inductive Issue {p} (r : Result p) : Type :=
| IDiag  : Diagnostic r -> Issue r
| IBound : Boundary r -> Issue r.
Arguments IDiag {p r} _.
Arguments IBound {p r} _.

(* the one canonical issue sequence: every diagnostic then every boundary, each kept in its own source order *)
Definition result_issues {p} (r : Result p) : list (Issue r) :=
  let rows := fact_rows r in
  map IDiag (result_diagnostic_rows r rows) ++ map IBound (result_boundary_rows r rows).

Section IssueIdentity.
Context {p : Syntax.Program}.

(* an issue's class, root, family, subject, and cause-or-requirement, projected from whichever row it is *)
Definition issue_class {r : Result p} (i : Issue r) : IssueClass :=
  match i with IDiag _ => ClassDiagnostic | IBound _ => ClassBoundary end.
Definition issue_root {r : Result p} (i : Issue r) : IssueRoot r :=
  match i with IDiag d => diag_root d | IBound b => bound_root b end.
Definition issue_family {r : Result p} (i : Issue r) : option Family :=
  match i with IDiag d => diag_family d | IBound b => Some (bound_family b) end.
Definition issue_cause_or_req {r : Result p} (i : Issue r)
  : IssueCause r + UnmetFactRef r :=
  match i with IDiag d => inl (diag_cause d) | IBound b => inr (bound_req_ref b) end.
Definition issue_related {r : Result p} (i : Issue r) : list (Index.NodeRef (res_index r)) :=
  match i with IDiag d => diag_related d | IBound _ => [] end.

(* an issue identity: an exact ordinal into result_issues, retaining the exact row it indexes there *)
Record IssueRef (r : Result p) : Type := mkIssueRef {
  ir_ord : nat ;
  ir_row : Issue r ;
  ir_at  : nth_error (result_issues r) ir_ord = Some ir_row
}.
Arguments mkIssueRef {r} _ _ _.
Arguments ir_ord {r} _.
Arguments ir_row {r} _.
Arguments ir_at {r} _.

(* Diagnostic and Boundary are projections of an issue ref: exactly the row it references, never a synthesis *)
Definition iref_diagnostic {r : Result p} (ref : IssueRef r) : option (Diagnostic r) :=
  match ir_row ref with IDiag d => Some d | IBound _ => None end.
Definition iref_boundary {r : Result p} (ref : IssueRef r) : option (Boundary r) :=
  match ir_row ref with IBound b => Some b | IDiag _ => None end.

(* bidirectional membership: a ref is exactly a position that indexes an issue in the one sequence *)
Lemma issue_ref_sound (r : Result p) (ref : IssueRef r) :
  nth_error (result_issues r) (ir_ord ref) = Some (ir_row ref).
Proof. exact (ir_at ref). Qed.
Lemma issue_ref_complete (r : Result p) (n : nat) (i : Issue r) :
  nth_error (result_issues r) n = Some i -> exists ref : IssueRef r, ir_ord ref = n /\ ir_row ref = i.
Proof. intro H. exists (mkIssueRef n i H). split; reflexivity. Qed.

(* exact identity: the ordinal alone determines the issue a ref names *)
Lemma issue_ref_ord_identity (r : Result p) (a b : IssueRef r) : ir_ord a = ir_ord b -> ir_row a = ir_row b.
Proof. intro H. pose proof (ir_at a); pose proof (ir_at b); congruence. Qed.

(* class partition: the sequence is exactly the diagnostics block followed by the boundaries block *)
Lemma result_issues_class_split (r : Result p) :
  result_issues r = map IDiag (result_diagnostics r) ++ map IBound (result_boundaries r).
Proof. reflexivity. Qed.

(* the row any position names is exactly a canonical diagnostic or boundary, never a fabricated one *)
Lemma idiag_in (r : Result p) (n : nat) (d : Diagnostic r) :
  nth_error (result_issues r) n = Some (IDiag d) -> In d (result_diagnostics r).
Proof.
  intro H. apply nth_error_In in H. unfold result_issues in H. apply in_app_or in H.
  destruct H as [Hd|Hb].
  - apply in_map_iff in Hd. destruct Hd as [d' [Heq Hin]]. injection Heq as Heq. subst d'. exact Hin.
  - apply in_map_iff in Hb. destruct Hb as [b' [Heq _]]. discriminate Heq.
Qed.
Lemma ibound_in (r : Result p) (n : nat) (b : Boundary r) :
  nth_error (result_issues r) n = Some (IBound b) -> In b (result_boundaries r).
Proof.
  intro H. apply nth_error_In in H. unfold result_issues in H. apply in_app_or in H.
  destruct H as [Hd|Hb].
  - apply in_map_iff in Hd. destruct Hd as [d' [Heq _]]. discriminate Heq.
  - apply in_map_iff in Hb. destruct Hb as [b' [Heq Hin]]. injection Heq as Heq. subst b'. exact Hin.
Qed.

(* payload: the exact row a ref names is a canonical row of its class *)
Lemma iref_payload (r : Result p) (ref : IssueRef r) :
  match ir_row ref with
  | IDiag d => In d (result_diagnostics r)
  | IBound b => In b (result_boundaries r)
  end.
Proof.
  pose proof (ir_at ref) as H. set (row := ir_row ref) in *. clearbody row.
  destruct row as [d|b].
  - exact (idiag_in r (ir_ord ref) d H).
  - exact (ibound_in r (ir_ord ref) b H).
Qed.

(* stable order: the k-th diagnostic sits at ordinal k; the j-th boundary at ordinal (#diagnostics + j) *)
Lemma issue_diag_at (r : Result p) (n : nat) (d : Diagnostic r) :
  nth_error (result_diagnostics r) n = Some d -> nth_error (result_issues r) n = Some (IDiag d).
Proof.
  intro H. unfold result_issues.
  rewrite nth_error_app1 by (rewrite <- nth_error_Some; rewrite (map_nth_error _ _ _ H); discriminate).
  exact (map_nth_error _ _ _ H).
Qed.
Lemma issue_bound_at (r : Result p) (n : nat) (b : Boundary r) :
  nth_error (result_boundaries r) n = Some b ->
  nth_error (result_issues r) ((Datatypes.length (result_diagnostics r) + n)%nat) = Some (IBound b).
Proof.
  intro H. unfold result_issues.
  rewrite nth_error_app2 by (first [rewrite length_map | rewrite map_length]; apply Nat.le_add_r).
  first [rewrite length_map | rewrite map_length]. rewrite Nat.add_comm, Nat.add_sub.
  exact (map_nth_error _ _ _ H).
Qed.

(* no collapse: N diagnostics and M boundaries give exactly N+M distinct ordinal slots, none merged or dropped *)
Lemma result_issues_length (r : Result p) :
  Datatypes.length (result_issues r)
  = (Datatypes.length (result_diagnostics r) + Datatypes.length (result_boundaries r))%nat.
Proof.
  unfold result_issues.
  first [rewrite app_length | rewrite length_app];
  first [rewrite !length_map | rewrite !map_length]; reflexivity.
Qed.
Lemma iref_ord_bound (r : Result p) (ref : IssueRef r) :
  (ir_ord ref < Datatypes.length (result_issues r))%nat.
Proof. rewrite <- nth_error_Some. rewrite (ir_at ref). discriminate. Qed.

End IssueIdentity.

(* the record parameters generalize over p and r on section close; keep both implicit for external readers *)
Arguments mkIssueRef {p r} _ _ _.
Arguments ir_ord {p r} _.
Arguments ir_row {p r} _.
Arguments ir_at {p r} _.
