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

(* a value-producing literal or unary node: the exact subject of a default-int overflow *)
Definition is_value_default_node {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) : bool :=
  match Index.node_view site with Index.Model.VLiteral _ | Index.Model.VUnary _ => true | _ => false end.
(* a var/type-spec declaration node: the exact subject of a deferred value-declaration meaning *)
Definition is_value_decl_node {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) : bool :=
  match Index.node_view site with Index.Model.VVarSpec _ | Index.Model.VTypeSpec _ => true | _ => false end.
Lemma is_value_default_lit {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) (l : Syntax.Literal) :
  Index.node_view site = Index.Model.VLiteral l -> is_value_default_node site = true.
Proof. intro H. unfold is_value_default_node. rewrite H. reflexivity. Qed.
Lemma is_value_default_unary {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) (u : Syntax.UnaryOp) :
  Index.node_view site = Index.Model.VUnary u -> is_value_default_node site = true.
Proof. intro H. unfold is_value_default_node. rewrite H. reflexivity. Qed.
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
| NotCallable : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n) (o : BN.ObjectRef idx),
    BN.resolution_object_view r = Some o -> Cause bp site ApplicationKind
| NotCallableExpr : Index.node_view site = Index.Model.VApplication -> Cause bp site ApplicationKind
| ConversionArity : Index.node_view site = Index.Model.VApplication ->
    Names.PredeclaredName -> nat -> Cause bp site ApplicationKind
| ComplexArity : Index.node_view site = Index.Model.VApplication -> nat -> Cause bp site ApplicationKind
| MainArity : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n) (f : BN.FunctionDeclRef idx),
    BN.resolution_object_view r = Some (BN.SourceObject (BN.DOFunc f)) ->
    list (Index.NodeRef idx) -> nat -> Cause bp site ApplicationKind
| UnresolvedNameT : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n),
    BN.resolution_object_view r = None -> BN.resolution_redecl_root r = None -> Cause bp site TypeUseKind
| NotAType : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n) (o : BN.ObjectRef idx),
    BN.resolution_object_view r = Some o -> Cause bp site TypeUseKind
| IllegalStatement : Index.node_view site = Index.Model.VStmt Index.Model.SSExpr -> Cause bp site StatementKind
| ShortDuplicate : forall (st : Index.Refs.ShortStmtRef idx) (se : BN.ShortEventRef bp st)
    (dd : BN.ShortDuplicateDecision se) (n : Names.OrdinaryIdentifier),
    dd = BN.short_duplicate_decision se -> BN.short_dup_decision_name dd = Some n ->
    site = Index.Refs.sh_node st -> Cause bp site StatementKind.
Arguments InvalidIdentity {p idx s bd bp site n} _ _ _.
Arguments UnresolvedNameV {p idx s bd bp site n} _ _ _.
Arguments TypeAsValue {p idx s bd bp site n} _ _ _.
Arguments ComplexMismatch {p idx s bd bp site} _ _ _. Arguments ConversionOverflow {p idx s bd bp site} _ _ _.
Arguments ConversionNotRepresentable {p idx s bd bp site} _ _ _. Arguments NoValueUsed {p idx s bd bp site} _.
Arguments UnaryMismatch {p idx s bd bp site} _. Arguments DefaultOverflow {p idx s bd bp site} _ _.
Arguments ConstMissingInit {p idx s bd bp site cs} _ _. Arguments ResultCountMismatch {p idx s bd bp site} cs _ _ _.
Arguments NotCallable {p idx s bd bp site n} _ _ _. Arguments NotCallableExpr {p idx s bd bp site} _.
Arguments ConversionArity {p idx s bd bp site} _ _ _. Arguments ComplexArity {p idx s bd bp site} _ _.
Arguments MainArity {p idx s bd bp site n} _ _ _ _ _.
Arguments UnresolvedNameT {p idx s bd bp site n} _ _ _. Arguments NotAType {p idx s bd bp site n} _ _ _.
Arguments IllegalStatement {p idx s bd bp site} _. Arguments ShortDuplicate {p idx s bd bp site st se} _ _ _ _ _.

Inductive Requirement {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) (site : Index.NodeRef idx) : FactKind -> Type :=
| ReqValueMeaning : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n) (org : BN.DeclOrigin idx),
    BN.resolution_object_view r = Some (BN.SourceObject org) -> Requirement bp site ValueKind
| ReqComplexType : Index.node_view site = Index.Model.VApplication -> Requirement bp site ValueKind
| ReqMainUse : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n) (f : BN.FunctionDeclRef idx),
    BN.resolution_object_view r = Some (BN.SourceObject (BN.DOFunc f)) -> Requirement bp site ValueKind
| ReqConstDecl : forall (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF),
    BN.ConstSpecJudgmentRef bp cs -> site = Index.Refs.sp_node cs -> Requirement bp site ValueKind
| ReqDeclMeaningV : is_value_decl_node site = true -> Requirement bp site ValueKind
| ReqApplication : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n) (pn : Names.PredeclaredName),
    BN.resolution_object_view r = Some (BN.PredeclaredObject pn) ->
    list (Index.NodeRef idx) -> Requirement bp site ApplicationKind
| ReqTypeMeaning : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n) (o : BN.ObjectRef idx),
    BN.resolution_object_view r = Some o -> Requirement bp site TypeUseKind
| ReqDeclMeaningS : forall (st : Index.Refs.ShortStmtRef idx), site = Index.Refs.sh_node st -> Requirement bp site StatementKind.
Arguments ReqValueMeaning {p idx s bd bp site n} _ _ _. Arguments ReqComplexType {p idx s bd bp site} _.
Arguments ReqMainUse {p idx s bd bp site n} _ _ _. Arguments ReqConstDecl {p idx s bd bp site cs} _ _.
Arguments ReqDeclMeaningV {p idx s bd bp site} _. Arguments ReqApplication {p idx s bd bp site n} _ _ _ _.
Arguments ReqTypeMeaning {p idx s bd bp site n} _ _ _. Arguments ReqDeclMeaningS {p idx s bd bp site} st _.

(* §8 the exact structural edge from an expr-statement parent to its exact expression child (ExprStmtRef, +AppRef) *)
Inductive ChildFactEdge {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) : FactKind -> Type :=
| ExprStmtValueChild : forall (pr : Index.Refs.ExprStmtRef idx),
    site = Index.Refs.exs_node pr -> ChildFactEdge site StatementKind
| ExprStmtApplicationChild : forall (pr : Index.Refs.ExprStmtRef idx) (ar : Index.Refs.AppRef idx),
    site = Index.Refs.exs_node pr ->
    Index.Refs.app_node ar = Index.Edges.ee_child (Index.Edges.exprstmt_expr pr) ->
    ChildFactEdge site StatementKind.
Arguments ExprStmtValueChild {p idx site} _ _.
Arguments ExprStmtApplicationChild {p idx site} _ _ _ _.
(* the exact child site is a projection of the edge, never supplied independently; the child kind is closed by case *)
Definition cfe_child_site {p} {idx : Index.ProgramIndex p} {site : Index.NodeRef idx} {k : FactKind}
  (e : ChildFactEdge site k) : Index.NodeRef idx :=
  match e with
  | ExprStmtValueChild pr _ => Index.Edges.ee_child (Index.Edges.exprstmt_expr pr)
  | ExprStmtApplicationChild pr _ _ _ => Index.Edges.ee_child (Index.Edges.exprstmt_expr pr)
  end.
Definition cfe_child_kind {p} {idx : Index.ProgramIndex p} {site : Index.NodeRef idx} {k : FactKind}
  (e : ChildFactEdge site k) : FactKind :=
  match e with ExprStmtValueChild _ _ => ValueKind | ExprStmtApplicationChild _ _ _ _ => ApplicationKind end.

(* the exact prerequisite of a dependent non-result: a redeclared/unbound name use, an invalid identity, or a child *)
Inductive Dependency {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) (site : Index.NodeRef idx) : FactKind -> Type :=
| DepRedeclaredNameV : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n) (root : BN.RedeclRoot bp n),
    BN.resolution_redecl_root r = Some root -> Dependency bp site ValueKind
| DepRedeclaredNameA : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n) (root : BN.RedeclRoot bp n),
    BN.resolution_redecl_root r = Some root -> Dependency bp site ApplicationKind
| DepRedeclaredNameT : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n) (root : BN.RedeclRoot bp n),
    BN.resolution_redecl_root r = Some root -> Dependency bp site TypeUseKind
| DepUnboundNameV : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n),
    BN.resolution_object_view r = None -> BN.resolution_redecl_root r = None -> Dependency bp site ValueKind
| DepUnboundNameA : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n),
    BN.resolution_object_view r = None -> BN.resolution_redecl_root r = None -> Dependency bp site ApplicationKind
| DepInvalidId : forall (n : Names.OrdinaryIdentifier) (r : BN.ResolutionRef (BN.use_env bp site) n) (pn : Names.PredeclaredName),
    BN.resolution_object_view r = Some (BN.PredeclaredObject pn) -> Dependency bp site ApplicationKind
| DepChild : ChildFactEdge site StatementKind -> Dependency bp site StatementKind.
Arguments DepRedeclaredNameV {p idx s bd bp site n} _ _ _.
Arguments DepRedeclaredNameA {p idx s bd bp site n} _ _ _.
Arguments DepRedeclaredNameT {p idx s bd bp site n} _ _ _.
Arguments DepUnboundNameV {p idx s bd bp site n} _ _ _.
Arguments DepUnboundNameA {p idx s bd bp site n} _ _ _.
Arguments DepInvalidId {p idx s bd bp site n} _ _ _. Arguments DepChild {p idx s bd bp site} _.

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
| PMInvalidId
| PMUnmodelled.

Definition pmeaning (n : Names.PredeclaredName) : PMeaning :=
  match TR.predeclared_meaning n with
  | TR.NMConversionForm t => PMConvForm t
  | TR.NMValueConstant c => PMValue c
  | TR.NMNoFormMeaning =>
      match n with
      | Names.PComplex => PMComplex | Names.PPrintln => PMPrintln
      | Names.PIota => PMInvalidId | Names.PNil => PMInvalidId
      | _ => PMUnmodelled
      end
  end.

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

Definition resolve_constant_info (ci : TR.ConstantInfo) : option TR.ResolvedConstant :=
  match TR.ci_typed ci with
  | TR.ExplicitlyTyped tf =>
      match TR.convert_constant tf (TR.mk_cinfo (TR.ci_const ci) TR.Untyped) with
      | TR.Converted tc => Some (TR.mk_rc tf tc)
      | _ => None
      end
  | TR.Untyped => TR.default_constant (TR.ci_const ci)
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

Definition mconst (m : Collections.NodeMap.t (option TR.ConstantInfo)) (rc : Index.NodeRef idx)
  : option TR.ConstantInfo :=
  match Collections.NodeMap.find (Index.nr_key rc) m with Some oc => oc | None => None end.
Definition node_const (m : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx)
  : option TR.ConstantInfo :=
  match Index.node_view r as v return Index.node_view r = v -> option TR.ConstantInfo with
  | Index.Model.VName n => fun _ =>
      match nm_at r n with Some (TR.NMValueConstant c) => Some (TR.mk_cinfo c TR.Untyped) | _ => None end
  | Index.Model.VLiteral (Syntax.IntegerLiteral k) => fun _ => Some (TR.mk_cinfo (TR.CInt (Z.of_N k)) TR.Untyped)
  | Index.Model.VLiteral (Syntax.FloatLiteral d) => fun _ => Some (TR.mk_cinfo (TR.CFloat (Float.nnd_value d)) TR.Untyped)
  | Index.Model.VLiteral (Syntax.StringLiteral str) => fun _ => Some (TR.mk_cinfo (TR.CString str) TR.Untyped)
  | Index.Model.VUnary Syntax.UnaryMinus => fun Hv =>
      match mconst m (Index.Edges.uo_child (Index.Edges.unary_operand (Index.Refs.mkUnaryRef r Syntax.UnaryMinus Hv))) with
      | Some ci =>
          match TR.constant_neg (TR.ci_const ci) with
          | Some c' =>
              match TR.ci_typed ci with
              | TR.ExplicitlyTyped tf =>
                  match TR.convert_constant tf (TR.mk_cinfo c' TR.Untyped) with
                  | TR.Converted _ => Some (TR.mk_cinfo c' (TR.ExplicitlyTyped tf))
                  | _ => None
                  end
              | TR.Untyped => Some (TR.mk_cinfo c' TR.Untyped)
              end
          | None => None
          end
      | None => None
      end
  | Index.Model.VApplication => fun Hv =>
      match Index.node_view (Index.Edges.ah_child (Index.Edges.app_head (Index.Refs.mkAppRef r Hv))) with
      | Index.Model.VName h =>
          match map (fun x => Index.Edges.aa_child (projT2 x)) (Index.Edges.application_args (Index.Refs.mkAppRef r Hv)) with
          | x :: nil =>
              match nm_at r h with
              | Some (TR.NMConversionForm t) =>
                  match mconst m x with
                  | Some ci => match TR.convert_constant t ci with
                               | TR.Converted tc => Some (TR.mk_cinfo (TR.typed_exact tc) (TR.ExplicitlyTyped t))
                               | _ => None
                               end
                  | None => None
                  end
              | _ => None
              end
          | re :: im :: nil =>
              match BN.resolution_object_view (BN.resolve bp r h) with
              | Some o =>
                  match o, mconst m re, mconst m im with
                  | BN.PredeclaredObject Names.PComplex, Some cre, Some cim =>
                      match TR.constant_to_float (TR.ci_const cre), TR.constant_to_float (TR.ci_const cim) with
                      | Some _, Some _ =>
                          option_map (fun c => TR.mk_cinfo c TR.Untyped)
                            (TR.complex_of_constants (TR.ci_const cre) (TR.ci_const cim))
                      | _, _ => None
                      end
                  | _, _, _ => None
                  end
              | None => None
              end
          | _ => None
          end
      | _ => None
      end
  | _ => fun _ => None
  end eq_refl.
(* the file's constants folded in descending position order — children before parents (file_nodes is trie order) *)
Definition const_table (fr : Index.FileRef idx) : Collections.NodeMap.t (option TR.ConstantInfo) :=
  fold_left (fun m pos =>
               match Index.mk_noderef fr (Pos.of_succ_nat pos) with
               | Some r => Collections.NodeMap.add (Index.nr_key r) (node_const m r) m
               | None => m
               end)
            (rev (seq 0 (Index.occ_count fr))) (Collections.NodeMap.empty _).
(* role decides value-use: an application head is a callee, not a value; expr-statement exprs go to own_stmt *)
Definition is_app_head (r : Index.NodeRef idx) : bool :=
  match Index.node_role r with Index.Model.RApplicationHead => true | _ => false end.
Definition value_ctx (r : Index.NodeRef idx) : bool :=
  match Index.node_role r with Index.Model.RApplicationHead => false | Index.Model.RExprStatementExpr => false | _ => true end.

(* a conversion/complex head folds its argument, so a folded value's default-int type is never forced *)
Definition head_folds (par : Index.NodeRef idx) : bool :=
  match Index.node_view par as v return Index.node_view par = v -> bool with
  | Index.Model.VApplication => fun Hv =>
      match Index.node_view (Index.Edges.ah_child (Index.Edges.app_head (Index.Refs.mkAppRef par Hv))) with
      | Index.Model.VName h =>
          match BN.resolution_object_view (BN.resolve bp par h) with
          | Some o =>
              match o with
              | BN.PredeclaredObject pn =>
                  match pmeaning pn with PMConvForm _ => true | PMComplex => true | _ => false end
              | BN.SourceObject _ => false
              end
          | None => false
          end
      | _ => false
      end
  | _ => fun _ => false
  end eq_refl.
Definition fold_consumed (r : Index.NodeRef idx) : bool :=
  match Index.node_role r with
  | Index.Model.RUnaryOperand => true
  | Index.Model.RApplicationArg _ => match Index.node_parent r with Some par => head_folds par | None => false end
  | _ => false
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

Definition own_value_body (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx)
  (nv : Index.Model.NodeView) (Hnv : Index.node_view r = nv) : ValueOutcome bp r :=
  match nv as v return Index.node_view r = v -> ValueOutcome bp r with
  | Index.Model.VName n => fun _ =>
      let r0 := BN.resolve bp r n in
      match BN.resolution_object_view r0 as ov return BN.resolution_object_view r0 = ov -> ValueOutcome bp r with
      | Some o => fun Hov =>
          match o as o' return o = o' -> ValueOutcome bp r with
          | BN.PredeclaredObject pn => fun Ho =>
              let Hpre := eq_trans Hov (f_equal (@Some _) Ho) in
              match pmeaning pn with
              | PMValue c => match TR.default_constant c with Some rc => VOK rc | None => VInvalid (InvalidIdentity r0 pn Hpre) end
              | PMInvalidId => VInvalid (InvalidIdentity r0 pn Hpre)
              | _ => if is_app_head r then VNonconst else VInvalid (TypeAsValue r0 o Hov)
              end
          | BN.SourceObject org => fun Ho =>
              let Hsrc := eq_trans Hov (f_equal (@Some _) Ho) in
              match org as org' return org = org' -> ValueOutcome bp r with
              | BN.DOBinder _ => fun _ => VUnmet (ReqValueMeaning r0 org Hsrc)
              | BN.DOShort _ => fun _ => VUnmet (ReqValueMeaning r0 org Hsrc)
              | BN.DOFunc f => fun Horg =>
                  if is_app_head r then VNonconst
                  else VUnmet (ReqMainUse r0 f (eq_trans Hsrc (f_equal (fun z => @Some _ (BN.SourceObject z)) Horg)))
              end eq_refl
          end eq_refl
      | None => fun Hov =>
          match BN.resolution_redecl_root r0 as rv return BN.resolution_redecl_root r0 = rv -> ValueOutcome bp r with
          | Some root => fun Hrr => VDependent (DepRedeclaredNameV r0 root Hrr)
          | None => fun Hrv => VInvalid (UnresolvedNameV r0 Hov Hrv)
          end eq_refl
      end eq_refl
  | Index.Model.VLiteral l => fun Hv =>
      match mconst ctab r with
      | Some ci => match resolve_constant_info ci with
                   | Some rc => VOK rc
                   | None => if fold_consumed r then VNonconst
                             else VInvalid (DefaultOverflow (is_value_default_lit r l Hv) (TR.ci_const ci))
                   end
      | None => VNonconst
      end
  | Index.Model.VUnary Syntax.UnaryMinus => fun Hv =>
      match mconst ctab (Index.Edges.uo_child (Index.Edges.unary_operand (Index.Refs.mkUnaryRef r Syntax.UnaryMinus Hv))) with
      | Some _ =>
          match mconst ctab r with
          | Some ci => match resolve_constant_info ci with
                       | Some rc => VOK rc
                       | None => if fold_consumed r then VNonconst
                                 else VInvalid (DefaultOverflow (is_value_default_unary r Syntax.UnaryMinus Hv) (TR.ci_const ci))
                       end
          | None => VInvalid (UnaryMismatch Hv)
          end
      | None => VNonconst
      end
  | Index.Model.VApplication => fun Hv =>
      match Index.node_view (Index.Edges.ah_child (Index.Edges.app_head (Index.Refs.mkAppRef r Hv))) with
      | Index.Model.VName h =>
          let r0 := BN.resolve bp r h in
          match BN.resolution_object_view r0 as ov return BN.resolution_object_view r0 = ov -> ValueOutcome bp r with
          | Some o => fun _ =>
              match o with
              | BN.PredeclaredObject pn =>
              match pmeaning pn, map (fun x => Index.Edges.aa_child (projT2 x)) (Index.Edges.application_args (Index.Refs.mkAppRef r Hv)) with
              | PMConvForm t, x :: nil =>
                  match mconst ctab x with
                  | Some ci => match TR.convert_constant t ci with
                               | TR.Converted tc => VOK (TR.mk_rc t tc)
                               | TR.Overflows _ => VInvalid (ConversionOverflow Hv t x)
                               | TR.NotForm _ => VInvalid (ConversionNotRepresentable Hv t x)
                               end
                  | None => VNonconst
                  end
              | PMComplex, re :: im :: nil =>
                  match mconst ctab re, mconst ctab im with
                  | Some cre, Some cim =>
                      match complex_class cre cim with
                      | CxOk => match mconst ctab r with
                                | Some ci => match resolve_constant_info ci with Some rc => VOK rc | None => VNonconst end
                                | None => VNonconst end
                      | CxDefer => VUnmet (ReqComplexType Hv)
                      | CxError => VInvalid (ComplexMismatch Hv re im)
                      end
                  | _, _ => VNonconst
                  end
              | PMPrintln, _ => if value_ctx r then VInvalid (NoValueUsed Hv) else VNonconst
              | _, _ => VNonconst
              end
              | BN.SourceObject _ => VNonconst
              end
          | None => fun Hov =>
              match BN.resolution_redecl_root r0 as rv return BN.resolution_redecl_root r0 = rv -> ValueOutcome bp r with
              | Some root => fun Hrr => VDependent (DepRedeclaredNameV r0 root Hrr)
              | None => fun Hrv => VDependent (DepUnboundNameV r0 Hov Hrv)
              end eq_refl
          end eq_refl
      | _ => VNonconst
      end
  (* declaration outcomes live on the declaration subject (spec / short statement), never on the binder *)
  | Index.Model.VConstSpec sh => fun Hv => const_spec_disposition (Index.Refs.mkSpecRef (fl := Index.Model.ConstSpecF) r sh Hv)
  | Index.Model.VVarSpec v => fun Hv => VUnmet (ReqDeclMeaningV (is_value_decl_var r v Hv))
  | Index.Model.VTypeSpec t => fun Hv => VUnmet (ReqDeclMeaningV (is_value_decl_type r t Hv))
  | _ => fun _ => VNonconst
  end Hnv.
Definition own_value (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx) : ValueOutcome bp r :=
  own_value_body ctab r (Index.node_view r) eq_refl.
(* the value fact of a node reduces to its exact node_view branch — the convoy named so it is rewritable *)
Lemma own_value_at (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx)
  (v : Index.Model.NodeView) (H : Index.node_view r = v) : own_value ctab r = own_value_body ctab r v H.
Proof. unfold own_value. destruct H. reflexivity. Qed.

(* §10 own_app is applicability-first: it takes the exact AppRef, so there is no non-application self-dependency *)
Definition own_app (ar : Index.Refs.AppRef idx) : AppOutcome bp (Index.Refs.app_node ar) :=
  let r := Index.Refs.app_node ar in let Hv := Index.Refs.app_ok ar in
  let hd := Index.Edges.ah_child (Index.Edges.app_head (Index.Refs.mkAppRef r Hv)) in
      match Index.node_view hd with
      | Index.Model.VName h =>
          let r0 := BN.resolve bp r h in
          match BN.resolution_object_view r0 as ov return BN.resolution_object_view r0 = ov -> AppOutcome bp r with
          | Some o => fun Hov =>
              match o as o' return o = o' -> AppOutcome bp r with
              | BN.PredeclaredObject pn => fun Ho =>
              let Hpre := eq_trans Hov (f_equal (@Some _) Ho) in
              match pmeaning pn with
              | PMConvForm _ => match map (fun x => Index.Edges.aa_child (projT2 x)) (Index.Edges.application_args (Index.Refs.mkAppRef r Hv)) with _ :: nil => AOK | _ => AInvalid (ConversionArity Hv pn (Datatypes.length (map (fun x => Index.Edges.aa_child (projT2 x)) (Index.Edges.application_args (Index.Refs.mkAppRef r Hv))))) end
              | PMComplex =>
                  (* application family = callability + arity only; the complex value is own_value's exact judgment *)
                  match map (fun x => Index.Edges.aa_child (projT2 x)) (Index.Edges.application_args (Index.Refs.mkAppRef r Hv)) with
                  | _ :: _ :: nil => AOK
                  | _ => AInvalid (ComplexArity Hv (Datatypes.length (map (fun x => Index.Edges.aa_child (projT2 x)) (Index.Edges.application_args (Index.Refs.mkAppRef r Hv)))))
                  end
              | PMPrintln => AOK
              | PMValue _ => AInvalid (NotCallable r0 o Hov)
              | PMInvalidId => ADependent (DepInvalidId r0 pn Hpre)
              | PMUnmodelled => AUnmet (ReqApplication r0 pn Hpre (map (fun x => Index.Edges.aa_child (projT2 x)) (Index.Edges.application_args (Index.Refs.mkAppRef r Hv))))
              end
          | BN.SourceObject org => fun Ho =>
              let Hsrc := eq_trans Hov (f_equal (@Some _) Ho) in
              match org as org' return org = org' -> AppOutcome bp r with
              | BN.DOBinder _ => fun _ => AInvalid (NotCallable r0 o Hov)
              | BN.DOShort _ => fun _ => AInvalid (NotCallable r0 o Hov)
              | BN.DOFunc f => fun Horg =>
                  (* the fixed main is zero-parameter: a zero-argument call is a known zero-result call *)
                  let Hfunc := eq_trans Hsrc (f_equal (fun z => @Some _ (BN.SourceObject z)) Horg) in
                  match map (fun x => Index.Edges.aa_child (projT2 x)) (Index.Edges.application_args (Index.Refs.mkAppRef r Hv)) with
                  | nil => AOK
                  | args => AInvalid (MainArity r0 f Hfunc args (Datatypes.length args))
                  end
              end eq_refl
              end eq_refl
          | None => fun Hov =>
              match BN.resolution_redecl_root r0 as rv return BN.resolution_redecl_root r0 = rv -> AppOutcome bp r with
              | Some root => fun Hrr => ADependent (DepRedeclaredNameA r0 root Hrr)
              | None => fun Hrv => ADependent (DepUnboundNameA r0 Hov Hrv)
              end eq_refl
          end eq_refl
      | _ => AInvalid (NotCallableExpr Hv)
      end.

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

(* the current expr-statement driver: read its child's value/app negativity directly, then own_stmt_expr *)
Definition expr_sx_own (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx)
  (Hv : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr) : StmtOutcome bp r :=
  let e := Index.Edges.ee_child (Index.Edges.exprstmt_expr (Index.Refs.mkExprStmtRef r Hv)) in
  own_stmt_expr (Index.Refs.mkExprStmtRef r Hv) (value_neg_b (own_value ctab e)) (app_neg_at e).

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
(* a dependent match on node_view r reduces to the arm a known equation picks: destruct H fires (rhs a bound var) *)
Lemma convoy_at {A : Type} {Ba : Type} (a : A) (g : forall x : A, a = x -> Ba) (v : A) (H : a = v) :
  g a eq_refl = g v H.
Proof. destruct H. reflexivity. Qed.
(* decidable node identity from the boolean equality, so a same-site outcome equality is inj_pair2-extractable *)
Lemma noderef_eq_dec {p} {idx : Index.ProgramIndex p} (x y : Index.NodeRef idx) : {x = y} + {x <> y}.
Proof.
  destruct (BN.noderef_eqb x y) eqn:E; [ left | right ].
  - apply BN.noderef_eqb_spec. exact E.
  - intro Heq. subst y. rewrite (proj2 (BN.noderef_eqb_spec x x) eq_refl) in E. discriminate.
Qed.

Section Retain.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} (bp : BN.BindingPhase s bd).

(* §11/§10 the single application fact of a node, shared by va_facts and occ_facts so the AppRef proof is one term *)
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
(* §10 the type-use fact of a node, keyed to its exact named-type name, shared by occ_facts and occ_facts_va *)
Definition type_fact_body (r : Index.NodeRef idx) (v : Index.Model.NodeView) (H : Index.node_view r = v) : list (OccFact bp) :=
  match v as v0 return Index.node_view r = v0 -> list (OccFact bp) with
  | Index.Model.VTypeExpr (Syntax.NamedType n) => fun H0 => [OFType r (own_type bp r n H0)]
  | _ => fun _ => []
  end H.
Definition type_fact (r : Index.NodeRef idx) : list (OccFact bp) := type_fact_body r (Index.node_view r) eq_refl.
Lemma type_fact_at (r : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (H : Index.node_view r = Index.Model.VTypeExpr (Syntax.NamedType n)) : type_fact r = [OFType r (own_type bp r n H)].
Proof. exact (convoy_at (Index.node_view r) (type_fact_body r) (Index.Model.VTypeExpr (Syntax.NamedType n)) H). Qed.
(* the short-declaration duplicate decision, named so its non-dependent outcome is provable off the convoy *)
Definition short_stmt_body (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (nm : option Names.OrdinaryIdentifier)
  (Hnm : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = nm)
  : StmtOutcome bp r :=
  match nm as nm0 return
    BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = nm0
    -> StmtOutcome bp r with
  | Some n => fun Hn => SInvalid (ShortDuplicate
      (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) n eq_refl Hn eq_refl)
  | None => fun _ => SUnmet (ReqDeclMeaningS (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
  end Hnm.
(* §10 the statement fact: expr arm from the driver, short arm its exact decision, any other node yields no fact *)
Definition stmt_fact_body (r : Index.NodeRef idx)
  (sx : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr -> StmtOutcome bp r)
  (v : Index.Model.NodeView) (H : Index.node_view r = v) : list (OccFact bp) :=
  match v as v0 return Index.node_view r = v0 -> list (OccFact bp) with
  | Index.Model.VStmt Index.Model.SSExpr => fun Hv => [OFStmt r (sx Hv)]
  | Index.Model.VStmt (Index.Model.SSShort nn nv) => fun Hv =>
      [OFStmt r (short_stmt_body r nn nv Hv
        (BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv)))) eq_refl)]
  | _ => fun _ => []
  end H.
(* the short-declaration outcome is a duplicate diagnostic, never a child dependency *)
Lemma short_stmt_body_not_dep (r : Index.NodeRef idx) (nn nv : nat)
  (Hv : Index.node_view r = Index.Model.VStmt (Index.Model.SSShort nn nv))
  (nm : option Names.OrdinaryIdentifier)
  (Hnm : BN.short_dup_decision_name (BN.short_duplicate_decision (BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv))) = nm)
  (d : Dependency bp r StatementKind) : short_stmt_body r nn nv Hv nm Hnm <> SDependent d.
Proof. unfold short_stmt_body. destruct nm; cbn; discriminate. Qed.
Definition stmt_fact (r : Index.NodeRef idx)
  (sx : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr -> StmtOutcome bp r) : list (OccFact bp) :=
  stmt_fact_body r sx (Index.node_view r) eq_refl.
Lemma stmt_fact_ssexpr (r : Index.NodeRef idx)
  (sx : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr -> StmtOutcome bp r)
  (H : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr) : stmt_fact r sx = [OFStmt r (sx H)].
Proof. exact (convoy_at (Index.node_view r) (stmt_fact_body r sx) (Index.Model.VStmt Index.Model.SSExpr) H). Qed.
(* every fact stmt_fact retains is an OFStmt at that exact node — and it retains one only at a statement node *)
Lemma stmt_fact_content (r : Index.NodeRef idx)
  (sx : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr -> StmtOutcome bp r) (o : OccFact bp)
  (v : Index.Model.NodeView) (H : Index.node_view r = v) :
  In o (stmt_fact_body r sx v H) -> (exists os, o = OFStmt r os) /\ exists st, Index.node_view r = Index.Model.VStmt st.
Proof.
  destruct v as [na|nl|nu| |nt|nb|nc|nvv|nts|nd|nst| |ntp| ]; try (cbn; intro Hin; exfalso; exact Hin).
  destruct nst; cbn; intro Hin; try (exfalso; exact Hin);
    (destruct Hin as [Hin|Hin]; [ subst o; split; [ eexists; reflexivity | eexists; exact H ] | exfalso; exact Hin ]).
Qed.

(* exactly the facts of the families that apply to a node, in family order; an inapplicable family yields none *)
Definition occ_facts (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx) : list (OccFact bp) :=
  match Index.node_view r with
  | Index.Model.VName _ | Index.Model.VLiteral _ | Index.Model.VUnary _ => [OFValue r (own_value bp ctab r)]
  | Index.Model.VApplication => app_fact_app r ++ [OFValue r (own_value bp ctab r)]
  | Index.Model.VStmt _ => stmt_fact r (expr_sx_own bp ctab r)
  | Index.Model.VTypeExpr _ => type_fact r
  | Index.Model.VConstSpec _ | Index.Model.VVarSpec _ | Index.Model.VTypeSpec _ => [OFValue r (own_value bp ctab r)]
  | _ => []
  end.

(* nonapplicability: occ_facts retains an application fact only at an application role, never elsewhere *)
Lemma no_app_fact_off_application (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r r' : Index.NodeRef idx) (o : AppOutcome bp r') :
  In (OFApp r' o) (occ_facts ctab r) -> Index.node_view r = Index.Model.VApplication.
Proof.
  intro Hin. unfold occ_facts in Hin. destruct (Index.node_view r) as [na|nl|nu| |[nt]|nb|nc|nv|nts|nd|nst| |ntp| ] eqn:E;
    try (rewrite (app_fact_app_at r E) in Hin); try (rewrite (type_fact_at r nt E) in Hin);
    try (destruct (stmt_fact_content r _ _ (Index.node_view r) eq_refl Hin) as [[os Hos] _]; discriminate Hos);
    cbn in Hin;
    try (match type of Hin with context [match ?x with _ => _ end] => destruct x end; cbn in Hin);
    solve [ reflexivity | exfalso; intuition discriminate ].
Qed.
(* nonapplicability: occ_facts retains a statement fact only at a statement role *)
Lemma no_stmt_fact_off_statement (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r r' : Index.NodeRef idx) (o : StmtOutcome bp r') :
  In (OFStmt r' o) (occ_facts ctab r) -> exists st, Index.node_view r = Index.Model.VStmt st.
Proof.
  intro Hin. unfold occ_facts in Hin. destruct (Index.node_view r) as [na|nl|nu| |[nt]|nb|nc|nv|nts|nd|nst| |ntp| ] eqn:E;
    try (rewrite (app_fact_app_at r E) in Hin); try (rewrite (type_fact_at r nt E) in Hin);
    try (destruct (stmt_fact_content r _ _ (Index.node_view r) eq_refl Hin) as [[os Hos] _]; discriminate Hos);
    cbn in Hin;
    try (match type of Hin with context [match ?x with _ => _ end] => destruct x end; cbn in Hin);
    solve [ eexists; reflexivity | exfalso; intuition discriminate ].
Qed.
(* nonapplicability: occ_facts retains a type-use fact only at a type-use role *)
Lemma no_type_fact_off_typeuse (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r r' : Index.NodeRef idx) (o : TypeUseOutcome bp r') :
  In (OFType r' o) (occ_facts ctab r) -> exists t, Index.node_view r = Index.Model.VTypeExpr t.
Proof.
  intro Hin. unfold occ_facts in Hin. destruct (Index.node_view r) as [na|nl|nu| |[nt]|nb|nc|nv|nts|nd|nst| |ntp| ] eqn:E;
    try (rewrite (app_fact_app_at r E) in Hin); try (rewrite (type_fact_at r nt E) in Hin);
    try (destruct (stmt_fact_content r _ _ (Index.node_view r) eq_refl Hin) as [[os Hos] _]; discriminate Hos);
    cbn in Hin;
    try (match type of Hin with context [match ?x with _ => _ end] => destruct x end; cbn in Hin);
    solve [ eexists; reflexivity | exfalso; intuition discriminate ].
Qed.
(* §19.4 a negative value fact sits only on a value-emitting node, so it is exactly one of that node's occ_facts *)
Lemma occ_value_mem (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (e : Index.NodeRef idx) :
  value_neg_b bp (own_value bp ctab e) = true -> In (OFValue e (own_value bp ctab e)) (occ_facts ctab e).
Proof.
  intro Hneg. unfold occ_facts.
  destruct (Index.node_view e) as [na|nl|nu| |nt|nb|nc|nvv|nts|nd|nst| |ntp|] eqn:E;
    try (apply in_or_app; right; cbn; left; reflexivity);
    try (cbn; left; reflexivity);
    exfalso; rewrite (own_value_at bp ctab e _ E) in Hneg; cbn in Hneg; discriminate Hneg.
Qed.
(* §19.4 the application fact of an application node is exactly one of its occ_facts *)
Lemma occ_app_mem (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (e : Index.NodeRef idx)
  (He : Index.node_view e = Index.Model.VApplication) :
  In (OFApp e (own_app bp (Index.Refs.mkAppRef e He))) (occ_facts ctab e).
Proof.
  assert (Hocc : occ_facts ctab e = app_fact_app e ++ [OFValue e (own_value bp ctab e)])
    by (unfold occ_facts; rewrite He; reflexivity).
  rewrite Hocc, (app_fact_app_at e He). apply in_or_app. left. apply in_eq.
Qed.

(* the value (and, at applications, application) facts of a file's nodes, computed once: the child-read pre-pass *)
Definition va_facts (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (nodes : list (Index.NodeRef idx)) : list (OccFact bp) :=
  flat_map (fun r => OFValue r (own_value bp ctab r) :: app_fact_app r) nodes.
Definition va_value_negative (va : list (OccFact bp)) (e : Index.NodeRef idx) : bool :=
  match find (fun o => match o with OFValue r _ => BN.noderef_eqb r e | _ => false end) va with
  | Some (OFValue _ ov) => match ov with VInvalid _ | VUnmet _ | VDependent _ => true | _ => false end | _ => false end.
Definition va_app_negative (va : list (OccFact bp)) (e : Index.NodeRef idx) : bool :=
  match find (fun o => match o with OFApp r _ => BN.noderef_eqb r e | _ => false end) va with
  | Some (OFApp _ oa) => match oa with AInvalid _ | AUnmet _ | ADependent _ => true | _ => false end | _ => false end.
(* the child-first expr-statement driver: read the child's value/app negativity from va, then own_stmt_expr *)
Definition expr_sx_va (va : list (OccFact bp)) (r : Index.NodeRef idx)
  (Hv : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr) : StmtOutcome bp r :=
  let e := Index.Edges.ee_child (Index.Edges.exprstmt_expr (Index.Refs.mkExprStmtRef r Hv)) in
  own_stmt_expr bp (Index.Refs.mkExprStmtRef r Hv) (va_value_negative va e) (va_app_negative va e).
(* the exact value / application row a node already has in the child-first table — projected, never recomputed *)
Definition va_value_row (va : list (OccFact bp)) (r : Index.NodeRef idx) : list (OccFact bp) :=
  match find (fun o => match o with OFValue r' _ => BN.noderef_eqb r' r | _ => false end) va with Some o => [o] | None => [] end.
Definition va_app_row (va : list (OccFact bp)) (r : Index.NodeRef idx) : list (OccFact bp) :=
  match find (fun o => match o with OFApp r' _ => BN.noderef_eqb r' r | _ => false end) va with Some o => [o] | None => [] end.
(* §11 raw_facts projects the one va computation: value/app rows from va, statement rows read their child from va *)
Definition occ_facts_va (va : list (OccFact bp)) (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx) : list (OccFact bp) :=
  match Index.node_view r with
  | Index.Model.VName _ | Index.Model.VLiteral _ | Index.Model.VUnary _ => va_value_row va r
  | Index.Model.VApplication => va_app_row va r ++ va_value_row va r
  | Index.Model.VStmt _ => stmt_fact r (expr_sx_va va r)
  | Index.Model.VTypeExpr _ => type_fact r
  | Index.Model.VConstSpec _ | Index.Model.VVarSpec _ | Index.Model.VTypeSpec _ => va_value_row va r
  | _ => []
  end.

(* va computes own_value for every file node once, so the child-read finds exactly own_value at that child *)
Lemma va_value_at (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (e : Index.NodeRef idx) (nodes : list (Index.NodeRef idx)) :
  In e nodes -> NoDup nodes ->
  find (fun o => match o with OFValue r _ => BN.noderef_eqb r e | _ => false end) (va_facts ctab nodes)
  = Some (OFValue e (own_value bp ctab e)).
Proof.
  induction nodes as [|n rest IH]; intros Hin Hnd; [ inversion Hin | ].
  inversion Hnd as [|? ? Hnn Hnd']; subst. cbn [va_facts flat_map app find].
  destruct (BN.noderef_eqb n e) eqn:E.
  - apply BN.noderef_eqb_spec in E; subst e; reflexivity.
  - destruct Hin as [Heq|Hin'];
      [ subst n; rewrite (proj2 (BN.noderef_eqb_spec e e) eq_refl) in E; discriminate E | ].
    destruct (Index.node_view n) as [na|nl|nu| |nt|nb|nc|nvv|nts|nd|nst| |ntp|] eqn:En;
      try (rewrite (app_fact_app_none n _ En) by discriminate; cbn [app find]; apply IH; assumption).
    rewrite (app_fact_app_at n En). cbn [app find]. apply IH; assumption.
Qed.
(* likewise the child-read finds own_app at an application child — the exact OFApp app_fact_app built there *)
Lemma va_app_at (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (e : Index.NodeRef idx)
  (Hva : Index.node_view e = Index.Model.VApplication) (nodes : list (Index.NodeRef idx)) :
  In e nodes -> NoDup nodes ->
  find (fun o => match o with OFApp r _ => BN.noderef_eqb r e | _ => false end) (va_facts ctab nodes)
  = Some (OFApp e (own_app bp (Index.Refs.mkAppRef e Hva))).
Proof.
  induction nodes as [|n rest IH]; intros Hin Hnd; [ inversion Hin | ].
  inversion Hnd as [|? ? Hnn Hnd']; subst. cbn [va_facts flat_map]. rewrite <- app_comm_cons. cbn [find].
  destruct Hin as [Heq|Hin'].
  - subst n. rewrite (app_fact_app_at e Hva). cbn [app find].
    rewrite (proj2 (BN.noderef_eqb_spec e e) eq_refl). reflexivity.
  - assert (Hne : BN.noderef_eqb n e = false)
      by (destruct (BN.noderef_eqb n e) eqn:E; [ apply BN.noderef_eqb_spec in E; subst n; contradiction | reflexivity ]).
    destruct (Index.node_view n) as [na|nl|nu| |nt|nb|nc|nvv|nts|nd|nst| |ntp|] eqn:En;
      try (rewrite (app_fact_app_none n _ En) by discriminate; cbn [app find]; apply IH; assumption).
    rewrite (app_fact_app_at n En). cbn [app find]. rewrite Hne. apply IH; assumption.
Qed.
(* off an application node the child-read finds no OFApp — va only ever records one at the exact application node *)
Lemma va_app_none (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (e : Index.NodeRef idx)
  (Hne : Index.node_view e <> Index.Model.VApplication) (nodes : list (Index.NodeRef idx)) :
  find (fun o => match o with OFApp r _ => BN.noderef_eqb r e | _ => false end) (va_facts ctab nodes) = None.
Proof.
  induction nodes as [|n rest IH]; [ reflexivity | ].
  cbn [va_facts flat_map]. rewrite <- app_comm_cons. cbn [find].
  destruct (Index.node_view n) as [na|nl|nu| |nt|nb|nc|nvv|nts|nd|nst| |ntp|] eqn:En;
    try (rewrite (app_fact_app_none n _ En) by discriminate; cbn [app find]; exact IH).
  rewrite (app_fact_app_at n En). cbn [app find].
  assert (Hnn : BN.noderef_eqb n e = false)
    by (destruct (BN.noderef_eqb n e) eqn:E; [ apply BN.noderef_eqb_spec in E; subst n; exfalso; apply Hne; exact En | reflexivity ]).
  rewrite Hnn. exact IH.
Qed.

(* the va child-read equals the canonical own_value / own_app negativity at a file node — the exact same fact *)
Lemma va_value_negative_correct (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (fr : Index.FileRef idx)
  (e : Index.NodeRef idx) (Hf : Index.nr_file e = fr) :
  va_value_negative (va_facts ctab (Index.file_nodes fr)) e = value_neg_b bp (own_value bp ctab e).
Proof.
  unfold va_value_negative.
  rewrite (va_value_at ctab e (Index.file_nodes fr) (file_nodes_complete fr e Hf) (file_nodes_nodup fr)); reflexivity.
Qed.
Lemma va_app_negative_correct (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (fr : Index.FileRef idx)
  (e : Index.NodeRef idx) (Hf : Index.nr_file e = fr) :
  va_app_negative (va_facts ctab (Index.file_nodes fr)) e = app_neg_at bp e.
Proof.
  unfold va_app_negative.
  destruct (Index.node_view e) as [na|nl|nu| |nt|nb|nc|nvv|nts|nd|nst| |ntp|] eqn:Ee;
    try (rewrite (va_app_none ctab e ltac:(rewrite Ee; discriminate) (Index.file_nodes fr));
         rewrite (app_neg_at_off e _ Ee ltac:(discriminate)); reflexivity).
  rewrite (va_app_at ctab e Ee (Index.file_nodes fr) (file_nodes_complete fr e Hf) (file_nodes_nodup fr)).
  rewrite (app_neg_at_app e Ee); reflexivity.
Qed.
(* the child-first expr statement equals the current one: it reads from va the child value/app own_stmt recomputes *)
Lemma occ_facts_va_eq (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (fr : Index.FileRef idx)
  (r : Index.NodeRef idx) (Hf : Index.nr_file r = fr) :
  occ_facts_va (va_facts ctab (Index.file_nodes fr)) ctab r = occ_facts ctab r.
Proof.
  pose proof (file_nodes_complete fr r Hf) as Hin. pose proof (file_nodes_nodup fr) as Hnd.
  unfold occ_facts_va, occ_facts, va_value_row, va_app_row.
  destruct (Index.node_view r) as [n|l|u| |t|b|c|vv|ts|d|st| |tp|] eqn:Hview;
    rewrite ?(va_value_at ctab r (Index.file_nodes fr) Hin Hnd);
    try reflexivity;
    try (rewrite (va_app_at ctab r Hview (Index.file_nodes fr) Hin Hnd), (app_fact_app_at r Hview); reflexivity).
  destruct st as [ | | sn sv ].
  - (* SSExpr: read the child value/app from va, the exact bools own_stmt_expr recomputes *)
    rewrite (stmt_fact_ssexpr r (expr_sx_va (va_facts ctab (Index.file_nodes fr)) r) Hview),
            (stmt_fact_ssexpr r (expr_sx_own bp ctab r) Hview).
    do 2 f_equal. unfold expr_sx_va, expr_sx_own.
    set (e := Index.Edges.ee_child (Index.Edges.exprstmt_expr (Index.Refs.mkExprStmtRef r Hview))).
    assert (Hfe : Index.nr_file e = fr) by (unfold e; rewrite ee_child_file; exact Hf).
    rewrite (va_value_negative_correct ctab fr e Hfe), (va_app_negative_correct ctab fr e Hfe). reflexivity.
  - (* SSDecl: the statement driver is unused, both project the same (empty) fact *)
    unfold stmt_fact;
    rewrite (convoy_at (Index.node_view r) (stmt_fact_body r (expr_sx_va (va_facts ctab (Index.file_nodes fr)) r))
              (Index.Model.VStmt Index.Model.SSDecl) Hview),
            (convoy_at (Index.node_view r) (stmt_fact_body r (expr_sx_own bp ctab r))
              (Index.Model.VStmt Index.Model.SSDecl) Hview). reflexivity.
  - (* SSShort: the driver is unused, both retain the same exact duplicate decision *)
    unfold stmt_fact;
    rewrite (convoy_at (Index.node_view r) (stmt_fact_body r (expr_sx_va (va_facts ctab (Index.file_nodes fr)) r))
              (Index.Model.VStmt (Index.Model.SSShort sn sv)) Hview),
            (convoy_at (Index.node_view r) (stmt_fact_body r (expr_sx_own bp ctab r))
              (Index.Model.VStmt (Index.Model.SSShort sn sv)) Hview). reflexivity.
Qed.

(* one const table per file, built once child-first: every fact is a projection of the same va computation, no rerun *)
Definition raw_facts : list (OccFact bp) :=
  flat_map (fun fr => let ctab := const_table bp fr in
                      let va := va_facts ctab (Index.file_nodes fr) in
                      flat_map (occ_facts_va va ctab) (Index.file_nodes fr))
           (flat_map BN.PI.pkg_members (BN.PI.packages s)).

Definition FactPhase : Type := { m : list (OccFact bp) | m = raw_facts }.
Definition facts : FactPhase := exist _ raw_facts eq_refl.
Definition fact_list (fp : FactPhase) : list (OccFact bp) := proj1_sig fp.

End Retain.

Arguments FactPhase {p idx s bd} bp.
Arguments facts {p idx s bd} bp.
Arguments fact_list {p idx s bd bp} _.

Section Laws.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} (bp : BN.BindingPhase s bd).

(* the phase content is built once; every phase carries exactly the canonical classification, none caller-supplied *)
Lemma fact_once (fp : FactPhase bp) : fact_list fp = raw_facts bp.
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
Definition raw_preflight {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}
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
Definition package_facts {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}
  {bd : BN.PhaseData s} (bp : BN.BindingPhase s bd) : PackageFacts bp := exist _ (raw_preflight bp) eq_refl.
Definition preflight {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} {bp : BN.BindingPhase s bd}
  (pf : PackageFacts bp) : FreshBuildDisposition s := proj1_sig pf.
Definition package_rule {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} {bp : BN.BindingPhase s bd}
  (pf : PackageFacts bp) (pr : BN.PI.PackageRef s) : BN.MainStatus s pr := BN.package_main bp pr.

Lemma package_rule_is_projection {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}
  {bd : BN.PhaseData s} {bp : BN.BindingPhase s bd} (pf : PackageFacts bp) (pr : BN.PI.PackageRef s) :
  package_rule pf pr = BN.package_main bp pr.
Proof. reflexivity. Qed.

Lemma packages_consume_one_surface {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}
  {bd : BN.PhaseData s} {bp : BN.BindingPhase s bd} (pf : PackageFacts bp) : preflight pf = raw_preflight bp.
Proof. exact (proj2_sig pf). Qed.

(* an exact missing-main case: a package whose canonical main decision IS MainMissing, retaining that exact proof *)
Record MissingMainRef {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} (pf : PackageFacts bp) : Type := mk_missing_main_ref {
  mmr_package : BN.PI.PackageRef s ;
  mmr_case    : package_rule pf mmr_package = BN.MainMissing
}.
Arguments MissingMainRef {p idx s bd bp} pf.
Arguments mk_missing_main_ref {p idx s bd bp pf} _ _.
Arguments mmr_package {p idx s bd bp pf} _. Arguments mmr_case {p idx s bd bp pf} _.

(* an exact output-collision case: the exact retained preflight decision IS FreshCollision at that package+root *)
Record CollisionRef {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} (pf : PackageFacts bp) : Type := mk_collision_ref {
  cr_package : BN.PI.PackageRef s ;
  cr_root    : BN.PI.RootEntryRef idx ;
  cr_case    : preflight pf = FreshCollision cr_package cr_root
}.
Arguments CollisionRef {p idx s bd bp} pf.
Arguments mk_collision_ref {p idx s bd bp pf} _ _ _.
Arguments cr_package {p idx s bd bp pf} _. Arguments cr_root {p idx s bd bp pf} _. Arguments cr_case {p idx s bd bp pf} _.

Section PackageCases.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
        {bp : BN.BindingPhase s bd} (pf : PackageFacts bp).

(* the exact missing-main case at a package, when its canonical status is MainMissing; other statuses yield none *)
Definition mm_of (pr : BN.PI.PackageRef s) (st : BN.MainStatus s pr) : package_rule pf pr = st -> list (MissingMainRef pf) :=
  match st as st0 return package_rule pf pr = st0 -> list (MissingMainRef pf) with
  | BN.MainMissing => fun H => [mk_missing_main_ref pr H]
  | _ => fun _ => []
  end.
Definition missing_main_refs : list (MissingMainRef pf) :=
  flat_map (fun pr => mm_of pr (package_rule pf pr) eq_refl) (BN.PI.packages s).

(* the exact collision case, when the retained preflight IS a collision; FreshOk yields none *)
Definition coll_of (d : FreshBuildDisposition s) : preflight pf = d -> option (CollisionRef pf) :=
  match d as d0 return preflight pf = d0 -> option (CollisionRef pf) with
  | FreshOk => fun _ => None
  | FreshCollision pr rr => fun H => Some (mk_collision_ref pr rr H)
  end.
Definition collision_ref : option (CollisionRef pf) := coll_of (preflight pf) eq_refl.

End PackageCases.
Arguments mm_of {p idx s bd bp pf} pr st H.
Arguments missing_main_refs {p idx s bd bp} pf.
Arguments coll_of {p idx s bd bp pf} d H.
Arguments collision_ref {p idx s bd bp} pf.

(* small helper: a per-element singleton-or-empty flat_map is exactly the filter of its boolean condition *)
Lemma flat_map_match_filter {A} (f : A -> bool) (g : A -> list A) (l : list A)
  (Hg : forall a, g a = if f a then [a] else []) : flat_map g l = filter f l.
Proof. induction l as [|a t IH]; cbn; [reflexivity|]. rewrite Hg. destruct (f a); cbn; rewrite IH; reflexivity. Qed.

Section PackageCaseLaws.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
        {bp : BN.BindingPhase s bd} (pf : PackageFacts bp).

(* the boolean the missing-main enumeration selects on: exactly the MainMissing decision at a package *)
Definition is_missing (pr : BN.PI.PackageRef s) : bool :=
  match package_rule pf pr with BN.MainMissing => true | _ => false end.
(* mm_of projects to exactly [pr] on the MainMissing decision, and to nothing on MainOne / MainMultiple *)
Lemma mm_of_package (pr : BN.PI.PackageRef s) (st : BN.MainStatus s pr) (H : package_rule pf pr = st) :
  map mmr_package (mm_of pr st H) = match st with BN.MainMissing => [pr] | _ => [] end.
Proof. destruct st; reflexivity. Qed.

(* §11.1/§19.1 the missing-main packages are exactly the MainMissing packages of packages s, in package order *)
Lemma missing_main_packages : map mmr_package (missing_main_refs pf) = filter is_missing (BN.PI.packages s).
Proof.
  unfold missing_main_refs. rewrite BN.map_flat_map.
  apply flat_map_match_filter. intro pr. rewrite mm_of_package. unfold is_missing.
  destruct (package_rule pf pr); reflexivity.
Qed.
(* §19.1 soundness: every retained missing-main ref carries the exact MainMissing decision of its package *)
Lemma missing_main_sound (mmr : MissingMainRef pf) : package_rule pf (mmr_package mmr) = BN.MainMissing.
Proof. exact (mmr_case mmr). Qed.
(* §19.1 a MainOne or MainMultiple package can never inhabit MissingMainRef: its exact decision is not MainMissing *)
Lemma no_missing_of_main_one (mmr : MissingMainRef pf) (e : BN.Est s) :
  package_rule pf (mmr_package mmr) = BN.MainOne e -> False.
Proof. intro H. rewrite (mmr_case mmr) in H. discriminate H. Qed.
Lemma no_missing_of_main_multiple (mmr : MissingMainRef pf) (a b : BN.Est s) (rest : list (BN.Est s)) :
  package_rule pf (mmr_package mmr) = BN.MainMultiple a b rest -> False.
Proof. intro H. rewrite (mmr_case mmr) in H. discriminate H. Qed.
(* §11.1/§19.1 completeness: a MainMissing package appears exactly once among the enumerated missing-main packages *)
Lemma missing_main_complete (pr : BN.PI.PackageRef s) :
  In pr (BN.PI.packages s) -> package_rule pf pr = BN.MainMissing -> In pr (map mmr_package (missing_main_refs pf)).
Proof.
  intros Hin Hmm. rewrite missing_main_packages. apply filter_In. split; [exact Hin | unfold is_missing; rewrite Hmm; reflexivity].
Qed.
(* §11.1/§19.1 no duplicate package among the missing-main refs *)
Lemma missing_main_nodup : NoDup (map mmr_package (missing_main_refs pf)).
Proof. rewrite missing_main_packages. apply nodup_filter. apply BN.packages_nodup. Qed.

(* §11.2/§19.2 a collision ref exists exactly when the exact retained preflight is a collision at that package+root *)
Lemma coll_of_none (d : FreshBuildDisposition s) (H : preflight pf = d) : coll_of d H = None <-> d = FreshOk.
Proof. destruct d; cbn; split; solve [ reflexivity | discriminate | intro; reflexivity ]. Qed.
Lemma collision_ref_none : collision_ref pf = None <-> preflight pf = FreshOk.
Proof. exact (coll_of_none (preflight pf) eq_refl). Qed.
(* §19.2 soundness: a collision ref carries the exact FreshCollision decision at its exact package and root *)
Lemma collision_case (cr : CollisionRef pf) : preflight pf = FreshCollision (cr_package cr) (cr_root cr).
Proof. exact (cr_case cr). Qed.
(* §19.2 a FreshCollision preflight yields a collision ref (not None) *)
Lemma collision_ref_of_fresh (pr : BN.PI.PackageRef s) (rr : BN.PI.RootEntryRef idx) :
  preflight pf = FreshCollision pr rr -> collision_ref pf <> None.
Proof. intros Hf Hn. apply collision_ref_none in Hn. rewrite Hf in Hn. discriminate Hn. Qed.
(* §19.2 the collision case is unique: any two collision refs name the same exact package and root *)
Lemma collision_unique (cr1 cr2 : CollisionRef pf) :
  cr_package cr1 = cr_package cr2 /\ cr_root cr1 = cr_root cr2.
Proof.
  pose proof (cr_case cr1) as H1. pose proof (cr_case cr2) as H2. rewrite H1 in H2. injection H2 as Hp Hr.
  split; [ exact Hp | exact Hr ].
Qed.

End PackageCaseLaws.
Arguments is_missing {p idx s bd bp} pf pr.

(* the one canonical analysis result over p; analyze builds it once, holding FactPhase and PackageFacts as fields *)
Record Result (p : Syntax.Program) : Type := mk_result {
  res_index     : Index.ProgramIndex p ;
  res_surface   : BN.PI.PackageSurface res_index ;
  res_bind_data : BN.PhaseData res_surface ;
  res_binds     : BN.BindingPhase res_surface res_bind_data ;
  res_facts     : FactPhase res_binds ;
  res_pkg       : PackageFacts res_binds
}.
Arguments mk_result {p} _ _ _ _ _ _.
Arguments res_index {p} _. Arguments res_surface {p} _.
Arguments res_bind_data {p} _. Arguments res_binds {p} _.
Arguments res_facts {p} _. Arguments res_pkg {p} _.

Definition analyze (p : Syntax.Program) : Result p :=
  let i := Index.index_program p in
  let s := BN.PI.package_surface i in
  let b := BN.bindings s in
  mk_result i s (BN.phase_data s) b (facts b) (package_facts b).

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

Section FactRow.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
        {bp : BN.BindingPhase s bd} (fp : FactPhase bp).

(* an exact retained fact-row identity: an ordinal into fact_list fp with the exact row retained at that ordinal *)
Record FactRowRef : Type := mk_frr {
  frr_ord : nat ;
  frr_row : OccFact bp ;
  frr_at  : nth_error (fact_list fp) frr_ord = Some frr_row
}.
Definition frr_site (ref : FactRowRef) : Index.NodeRef idx := fact_site (frr_row ref).
Definition frr_kind (ref : FactRowRef) : FactKind := fact_kind (frr_row ref).
Definition frr_family (ref : FactRowRef) : Family := fact_family (frr_row ref).

(* the exact row at ordinal k: retains the row and its membership proof; None ordinals yield no ref *)
Definition row_of (k : nat) (o : option (OccFact bp)) : nth_error (fact_list fp) k = o -> list FactRowRef :=
  match o with Some x => fun H => [mk_frr k x H] | None => fun _ => [] end.

(* canonical ordered row enumeration: exactly one retained row per valid ordinal of fact_list fp *)
Definition fact_rows : list FactRowRef :=
  flat_map (fun k => row_of k (nth_error (fact_list fp) k) eq_refl) (seq 0%nat (List.length (fact_list fp))).

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
Arguments FactRowRef {p idx s bd bp} fp.
Arguments mk_frr {p idx s bd bp fp} _ _ _.
Arguments frr_ord {p idx s bd bp fp} _. Arguments frr_row {p idx s bd bp fp} _. Arguments frr_at {p idx s bd bp fp} _.
Arguments frr_site {p idx s bd bp fp} _. Arguments frr_kind {p idx s bd bp fp} _. Arguments frr_family {p idx s bd bp fp} _.
Arguments row_of {p idx s bd bp fp} k o H.
Arguments fact_rows {p idx s bd bp} fp.
Arguments InvalidFactRef {p idx s bd bp} fp.
Arguments mk_ifr {p idx s bd bp fp} _ _ _.
Arguments ifr_rowref {p idx s bd bp fp} _. Arguments ifr_cause {p idx s bd bp fp} _. Arguments ifr_ok {p idx s bd bp fp} _.
Arguments ifr_fact {p idx s bd bp fp} _. Arguments ifr_ord {p idx s bd bp fp} _.
Arguments UnmetFactRef {p idx s bd bp} fp.
Arguments mk_ufr {p idx s bd bp fp} _ _ _.
Arguments ufr_rowref {p idx s bd bp fp} _. Arguments ufr_req {p idx s bd bp fp} _. Arguments ufr_ok {p idx s bd bp fp} _.
Arguments ufr_fact {p idx s bd bp fp} _. Arguments ufr_ord {p idx s bd bp fp} _.
Arguments DependentFactRef {p idx s bd bp} fp.
Arguments mk_dfr {p idx s bd bp fp} _ _ _.
Arguments dfr_rowref {p idx s bd bp fp} _. Arguments dfr_dep {p idx s bd bp fp} _. Arguments dfr_ok {p idx s bd bp fp} _.
Arguments dfr_fact {p idx s bd bp fp} _. Arguments dfr_ord {p idx s bd bp fp} _.

(* §10 canonical row enumeration laws: the enumeration IS exactly fact_list fp, once, in retained order *)
Section FactRowLaws.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
        {bp : BN.BindingPhase s bd} (fp : FactPhase bp).

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
Lemma row_of_row (k : nat) (o : option (OccFact bp)) (H : nth_error (fact_list fp) k = o) :
  map frr_row (row_of k o H) = match o with Some x => [x] | None => [] end.
Proof. destruct o; reflexivity. Qed.
Lemma row_of_ord (k : nat) (o : option (OccFact bp)) (H : nth_error (fact_list fp) k = o) :
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

(* §10 the retained rows project exactly to fact_list fp, in retained order; the ordinals are exactly seq 0 n *)
Lemma fact_rows_rows : map frr_row (fact_rows fp) = fact_list fp.
Proof.
  unfold fact_rows. rewrite map_flat_map_rows.
  rewrite (flat_map_ext_rows _ (fun k => match nth_error (fact_list fp) k with Some x => [x] | None => [] end))
    by (intro k; apply row_of_row).
  apply opt_flatmap_full.
Qed.
Lemma fact_rows_ords : map frr_ord (fact_rows fp) = seq 0 (List.length (fact_list fp)).
Proof.
  unfold fact_rows. rewrite map_flat_map_rows.
  rewrite (flat_map_ext_rows _ (fun k => match nth_error (fact_list fp) k with Some _ => [k] | None => [] end))
    by (intro k; apply row_of_ord).
  apply idx_flatmap_all. intros k Hk. apply in_seq in Hk. lia.
Qed.
(* §10 ordinal identity: the row ordinals are duplicate-free *)
Lemma fact_rows_ord_nodup : NoDup (map frr_ord (fact_rows fp)).
Proof. rewrite fact_rows_ords. apply seq_NoDup. Qed.
(* §10 completeness + positional uniqueness: every list member is enumerated at its exact position, retaining it *)
Lemma fact_rows_complete (k : nat) (row : OccFact bp) (Hk : nth_error (fact_list fp) k = Some row) :
  exists ref, nth_error (fact_rows fp) k = Some ref /\ frr_ord ref = k /\ frr_row ref = row.
Proof.
  assert (Hlt : (k < List.length (fact_list fp))%nat) by (apply nth_error_Some; rewrite Hk; discriminate).
  destruct (nth_error (fact_rows fp) k) as [ref|] eqn:E.
  2:{ exfalso. apply nth_error_None in E. rewrite <- (length_map frr_row), fact_rows_rows in E. lia. }
  exists ref. split; [reflexivity | split].
  - assert (Ho : nth_error (seq 0 (List.length (fact_list fp))) k = Some (frr_ord ref))
      by (rewrite <- fact_rows_ords, nth_error_map, E; reflexivity).
    rewrite (seq_nth_error_id (List.length (fact_list fp)) 0 k Hlt) in Ho. injection Ho as Ho. lia.
  - assert (Hr : nth_error (fact_list fp) k = Some (frr_row ref))
      by (rewrite <- fact_rows_rows, nth_error_map, E; reflexivity).
    rewrite Hk in Hr. injection Hr as Hr. symmetry. exact Hr.
Qed.

(* §11 the exact canonical key: an occurrence's exact site paired with its exact fact kind *)
Definition fact_key (o : OccFact bp) : Index.NodeRef idx * FactKind := (fact_site o, fact_kind o).
Definition frr_key (ref : FactRowRef fp) : Index.NodeRef idx * FactKind := fact_key (frr_row ref).

(* every fact occ_facts retains at a node carries that exact node as its site *)
Lemma occ_facts_site (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx) (o : OccFact bp) :
  In o (occ_facts bp ctab r) -> fact_site o = r.
Proof.
  intro Hin. unfold occ_facts in Hin. destruct (Index.node_view r) as [n|l|u| |[nt]|b|c|v|ts|d|st| |tp| ] eqn:E;
    try (rewrite (app_fact_app_at bp r E) in Hin); try (rewrite (type_fact_at bp r nt E) in Hin);
    try (destruct (stmt_fact_content bp r _ _ (Index.node_view r) eq_refl Hin) as [[os Hos] _]; subst o; reflexivity);
    cbn in Hin; repeat (destruct Hin as [Hin|Hin]); solve [ exfalso; exact Hin | subst o; reflexivity ].
Qed.
(* stmt_fact is a singleton or empty, so its site+kind keys are trivially duplicate-free *)
Lemma stmt_fact_key_nodup (r : Index.NodeRef idx)
  (sx : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr -> StmtOutcome bp r)
  (v : Index.Model.NodeView) (H : Index.node_view r = v) :
  NoDup (map fact_key (stmt_fact_body bp r sx v H)).
Proof.
  destruct v as [na|nl|nu| |nt|nb|nc|nvv|nts|nd|nst| |ntp| ]; try (cbn; apply NoDup_nil).
  destruct nst; cbn; try apply NoDup_nil.
  all: apply NoDup_cons; [ intro Hc; exact Hc | apply NoDup_nil ].
Qed.
(* the facts occ_facts retains at a node have duplicate-free keys: one per family, application's two kinds distinct *)
Lemma occ_facts_key_nodup (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx) :
  NoDup (map fact_key (occ_facts bp ctab r)).
Proof.
  unfold occ_facts. destruct (Index.node_view r) as [n|l|u| |[nt]|b|c|v|ts|d|st| |tp| ] eqn:E;
    try (rewrite (app_fact_app_at bp r E)); try (rewrite (type_fact_at bp r nt E));
    try (exact (stmt_fact_key_nodup r (expr_sx_own bp ctab r) (Index.node_view r) eq_refl));
    cbn [occ_facts map fact_key fact_site fact_kind app];
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
(* §11 the child-first builder projects the same rows the direct occ_facts traversal does (each node in its file) *)
Lemma flat_map_ext_in {A B : Type} (f g : A -> list B) (l : list A)
  (H : forall a, In a l -> f a = g a) : flat_map f l = flat_map g l.
Proof.
  induction l as [|x xs IH]; cbn; [reflexivity|].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity | intros a Ha; apply H; right; exact Ha].
Qed.
Lemma raw_facts_as_occ :
  raw_facts bp = flat_map (fun fr => flat_map (occ_facts bp (const_table bp fr)) (Index.file_nodes fr))
                          (flat_map BN.PI.pkg_members (BN.PI.packages s)).
Proof.
  unfold raw_facts; cbv zeta. apply flat_map_ext_rows. intro fr.
  apply flat_map_ext_in. intros r Hr. apply occ_facts_va_eq. exact (Index.file_nodes_file fr r Hr).
Qed.
(* §11 canonical-key soundness at the source: no two retained facts share a site+kind key across the whole program *)
Lemma raw_facts_key_nodup : NoDup (map fact_key (raw_facts bp)).
Proof.
  rewrite raw_facts_as_occ; rewrite map_flat_map.
  apply (BN.flat_map_nodup _ (fun sk => Index.nr_file (fst sk))).
  - apply files_nodup.
  - intros fr _. rewrite map_flat_map. apply (BN.flat_map_nodup _ (fun sk => fst sk)).
    + apply file_nodes_nodup.
    + intros r _. apply occ_facts_key_nodup.
    + intros r sk _ Hin. apply in_map_iff in Hin. destruct Hin as [o [Hk Ho]].
      subst sk. cbn. exact (occ_facts_site (const_table bp fr) r o Ho).
  - intros fr sk _ Hin. apply in_map_iff in Hin. destruct Hin as [o [Hk Ho]].
    apply in_flat_map in Ho. destruct Ho as [r [Hr Ho]].
    subst sk. cbn. rewrite (occ_facts_site (const_table bp fr) r o Ho). exact (Index.file_nodes_file fr r Hr).
Qed.
(* the retained fact list, and the row enumeration, inherit the duplicate-free site+kind key *)
Lemma fact_list_key_nodup : NoDup (map fact_key (fact_list fp)).
Proof. rewrite fact_once. apply raw_facts_key_nodup. Qed.
Lemma fact_rows_key_nodup : NoDup (map frr_key (fact_rows fp)).
Proof. unfold frr_key. rewrite <- map_map, fact_rows_rows. apply fact_list_key_nodup. Qed.
(* §24.2 row uniqueness: two retained rows with equal site and equal kind are the same exact row *)
Lemma fact_row_key_unique (r1 r2 : FactRowRef fp) :
  In r1 (fact_rows fp) -> In r2 (fact_rows fp) -> frr_site r1 = frr_site r2 -> frr_kind r1 = frr_kind r2 -> r1 = r2.
Proof.
  intros H1 H2 Hs Hk. apply (nodup_map_inj frr_key (fact_rows fp) fact_rows_key_nodup r1 r2 H1 H2).
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
Definition fact_row_for (site : Index.NodeRef idx) (kind : FactKind) : option (FactRowRef fp) :=
  find (fun ref => andb (BN.noderef_eqb (frr_site ref) site) (fact_kind_eqb (frr_kind ref) kind)) (fact_rows fp).

(* §24.2 soundness: a found row is a retained row with exactly the requested site and kind *)
Lemma fact_row_for_sound (site : Index.NodeRef idx) (kind : FactKind) (ref : FactRowRef fp) :
  fact_row_for site kind = Some ref -> In ref (fact_rows fp) /\ frr_site ref = site /\ frr_kind ref = kind.
Proof.
  intro H. apply find_some in H. destruct H as [Hin Hp]. apply andb_prop in Hp. destruct Hp as [Hs Hk].
  apply BN.noderef_eqb_spec in Hs. apply fact_kind_eqb_spec in Hk. split; [ exact Hin | split; [ exact Hs | exact Hk ] ].
Qed.
(* §24.2 completeness: any retained row with that site and kind is exactly the one the lookup returns *)
Lemma fact_row_for_complete (site : Index.NodeRef idx) (kind : FactKind) (ref : FactRowRef fp) :
  In ref (fact_rows fp) -> frr_site ref = site -> frr_kind ref = kind -> fact_row_for site kind = Some ref.
Proof.
  intros Hin Hs Hk. destruct (fact_row_for site kind) as [ref'|] eqn:E.
  - f_equal. apply fact_row_for_sound in E. destruct E as [Hin' [Hs' Hk']].
    apply (fact_row_key_unique ref' ref Hin' Hin); [ rewrite Hs', Hs; reflexivity | rewrite Hk', Hk; reflexivity ].
  - exfalso. unfold fact_row_for in E. pose proof (find_none _ _ E ref Hin) as Hno. cbv beta in Hno.
    rewrite Hs, Hk in Hno. rewrite (proj2 (BN.noderef_eqb_spec site site) eq_refl) in Hno.
    rewrite (proj2 (fact_kind_eqb_spec kind kind) eq_refl) in Hno. discriminate Hno.
Qed.
(* §24.2 None soundness: no retained row of that exact site and kind means the lookup is None *)
Lemma fact_row_for_none (site : Index.NodeRef idx) (kind : FactKind) :
  (forall ref, In ref (fact_rows fp) -> ~ (frr_site ref = site /\ frr_kind ref = kind)) -> fact_row_for site kind = None.
Proof.
  intro Hno. destruct (fact_row_for site kind) as [ref|] eqn:E; [ | reflexivity ].
  exfalso. apply fact_row_for_sound in E. destruct E as [Hin [Hs Hk]]. exact (Hno ref Hin (conj Hs Hk)).
Qed.
(* §24.2 None completeness: a None lookup means no retained row carries that exact site and kind *)
Lemma fact_row_for_none_inv (site : Index.NodeRef idx) (kind : FactKind) (ref : FactRowRef fp) :
  fact_row_for site kind = None -> In ref (fact_rows fp) -> ~ (frr_site ref = site /\ frr_kind ref = kind).
Proof.
  intros E Hin [Hs Hk]. pose proof (fact_row_for_complete site kind ref Hin Hs Hk) as Hc. rewrite E in Hc. discriminate.
Qed.
(* §24.2 non-conflation: an application site's Application-key and Value-key lookups return two distinct rows *)
Lemma fact_row_for_kind_distinct (site : Index.NodeRef idx) (r1 r2 : FactRowRef fp) :
  fact_row_for site ApplicationKind = Some r1 -> fact_row_for site ValueKind = Some r2 -> r1 <> r2.
Proof.
  intros H1 H2 Heq. apply fact_row_for_sound in H1. apply fact_row_for_sound in H2.
  destruct H1 as [_ [_ Hk1]]. destruct H2 as [_ [_ Hk2]]. subst r2. rewrite Hk1 in Hk2. discriminate.
Qed.

(* every retained fact decomposes to the exact package file and node whose occ_facts traversal produced it *)
Lemma raw_facts_node (o : OccFact bp) :
  In o (raw_facts bp) -> exists fr r, In r (Index.file_nodes fr) /\ In o (occ_facts bp (const_table bp fr) r).
Proof.
  rewrite raw_facts_as_occ. intro Hin. apply in_flat_map in Hin. destruct Hin as [fr [_ Hin]].
  apply in_flat_map in Hin. destruct Hin as [r [Hr Ho]]. exists fr, r. split; [ exact Hr | exact Ho ].
Qed.
(* §12 canonical-row truth: a retained row's exact outcome is the own_* result the canonical traversal selected *)
Lemma fact_row_is_own (ref : FactRowRef fp) :
  match frr_row ref with
  | OFValue r ov => ov = own_value bp (const_table bp (Index.nr_file r)) r
  | OFApp r oa => exists H : Index.node_view r = Index.Model.VApplication, oa = own_app bp (Index.Refs.mkAppRef r H)
  | OFStmt r os => In (OFStmt r os) (stmt_fact bp r (expr_sx_own bp (const_table bp (Index.nr_file r)) r))
  | OFType r ot => exists n (H : Index.node_view r = Index.Model.VTypeExpr (Syntax.NamedType n)),
      ot = own_type bp r n H
  end.
Proof.
  destruct ref as [k o Hat]; cbn [frr_row].
  assert (Hin : In o (raw_facts bp)) by (rewrite <- (fact_once bp fp); exact (nth_error_In _ _ Hat)).
  destruct (raw_facts_node o Hin) as [fr [r [Hr Ho]]]. pose proof (Index.file_nodes_file fr r Hr) as Hfile.
  unfold occ_facts in Ho. destruct (Index.node_view r) as [n|l|u| |[nt]|b|c|v|ts|d|st| |tp| ] eqn:E;
    try (rewrite (app_fact_app_at bp r E) in Ho); try (rewrite (type_fact_at bp r nt E) in Ho);
    try (destruct (stmt_fact_content bp r _ _ (Index.node_view r) eq_refl Ho) as [[os Hos] _]; subst o; rewrite Hfile; exact Ho);
    cbn in Ho; repeat (destruct Ho as [Ho|Ho]); try (exfalso; exact Ho);
    subst o; cbn; rewrite ?Hfile; try reflexivity.
  - exists E; reflexivity.
  - exists nt, E; reflexivity.
Qed.
(* §12 no false peer: the only retained fact at an exact site+kind is that one; no fabricated peer joins the list *)
Lemma no_false_row (o o' : OccFact bp) :
  In o (fact_list fp) -> In o' (fact_list fp) -> fact_site o' = fact_site o -> fact_kind o' = fact_kind o -> o' = o.
Proof.
  intros Ho Ho' Hs Hk. apply (nodup_map_inj fact_key (fact_list fp) fact_list_key_nodup o' o Ho' Ho).
  unfold fact_key. rewrite Hs, Hk. reflexivity.
Qed.
(* §24.3 a row with no retained cause admits no invalid-case ref: a success/nonconstant row is never invalid *)
Lemma no_invalid_of_no_cause (ref : FactRowRef fp) (ir : InvalidFactRef fp) :
  ifr_rowref ir = ref -> occ_cause (frr_row ref) = None -> False.
Proof. intros Href Hnone. subst ref. pose proof (ifr_ok ir) as Hok. rewrite Hnone in Hok. discriminate Hok. Qed.
(* §24.3 a row with no retained requirement admits no unmet-case ref: a success/nonconstant row is never unmet *)
Lemma no_unmet_of_no_req (ref : FactRowRef fp) (ur : UnmetFactRef fp) :
  ufr_rowref ur = ref -> occ_req (frr_row ref) = None -> False.
Proof. intros Href Hnone. subst ref. pose proof (ufr_ok ur) as Hok. rewrite Hnone in Hok. discriminate Hok. Qed.

(* §13 the exact negative case of a child row, projected from that exact row: invalid, unmet, or dependent *)
Inductive NegativeFactRef (child_row : FactRowRef fp) : Type :=
| ChildInvalid   : forall c : Cause bp (frr_site child_row) (frr_kind child_row),
    occ_cause (frr_row child_row) = Some c -> NegativeFactRef child_row
| ChildUnmet     : forall rq : Requirement bp (frr_site child_row) (frr_kind child_row),
    occ_req (frr_row child_row) = Some rq -> NegativeFactRef child_row
| ChildDependent : forall d : Dependency bp (frr_site child_row) (frr_kind child_row),
    occ_dep (frr_row child_row) = Some d -> NegativeFactRef child_row.
Arguments ChildInvalid {child_row} _ _. Arguments ChildUnmet {child_row} _ _. Arguments ChildDependent {child_row} _ _.
(* the exact negative class, a proof-insensitive descriptive projection *)
Definition nfr_class {child_row : FactRowRef fp} (n : NegativeFactRef child_row) : NegClass :=
  match n with ChildInvalid _ _ => NegInvalid | ChildUnmet _ _ => NegUnmet | ChildDependent _ _ => NegDependent end.
(* the exact negative case of a retained row, projected from its own outcome; none for a success/nonconstant row *)
Definition negative_case (child_row : FactRowRef fp) : option (NegativeFactRef child_row) :=
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
  cdfr_rowref : FactRowRef fp ;
  cdfr_site   : Index.NodeRef idx ;
  cdfr_edge   : ChildFactEdge cdfr_site StatementKind ;
  cdfr_ok     : frr_row cdfr_rowref = OFStmt cdfr_site (SDependent (DepChild cdfr_edge))
}.
Definition cdfr_edge_site (c : ChildDependentFactRef) : Index.NodeRef idx := cfe_child_site (cdfr_edge c).
Definition cdfr_edge_kind (c : ChildDependentFactRef) : FactKind := cfe_child_kind (cdfr_edge c).
(* a statement dependency can only be a DepChild, so its exact edge is a total projection *)
Definition dep_child_edge {site : Index.NodeRef idx} (d : Dependency bp site StatementKind) : ChildFactEdge site StatementKind :=
  match d in Dependency _ _ k return (match k with StatementKind => ChildFactEdge site StatementKind | _ => unit end) with
  | DepChild e => e | _ => tt end.
Lemma dep_child_eq {site : Index.NodeRef idx} (d : Dependency bp site StatementKind) : d = DepChild (dep_child_edge d).
Proof.
  refine (match d as d0 in Dependency _ _ k
    return (match k as k0 return Dependency bp site k0 -> Prop with
            | StatementKind => fun dd => dd = DepChild (dep_child_edge dd) | _ => fun _ => True end d0)
  with DepChild e => eq_refl | _ => I end).
Qed.
(* every child-dependent parent row is exactly a retained OFStmt at cdfr_site carrying the exact DepChild edge *)
Definition child_dep_of (row : FactRowRef fp) : option ChildDependentFactRef :=
  match frr_row row as o return frr_row row = o -> option ChildDependentFactRef with
  | OFStmt r (SDependent d) => fun Hr =>
      Some (mk_cdfr row r (dep_child_edge d) (eq_trans Hr (f_equal (fun x => OFStmt r (SDependent x)) (dep_child_eq d))))
  | _ => fun _ => None
  end eq_refl.

(* §15 the central relation: the parent's retained edge names the exact child fact_row_for finds, + its negative case *)
Record ChildPrerequisiteRef (cdfr : ChildDependentFactRef) : Type := mk_cpr {
  cpr_child_row : FactRowRef fp ;
  cpr_lookup    : fact_row_for (cdfr_edge_site cdfr) (cdfr_edge_kind cdfr) = Some cpr_child_row ;
  cpr_neg       : NegativeFactRef cpr_child_row
}.
(* §15 the one total builder from the exact parent child-dependency view: look up the exact child, retain its case *)
Definition child_prerequisite_body (cdfr : ChildDependentFactRef) (fr : option (FactRowRef fp))
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
    | None => [] end) (fact_rows fp).

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
               /\ In r (Index.file_nodes fr) /\ In o (occ_facts bp (const_table bp fr) r).
Proof.
  intro Hin. rewrite raw_facts_as_occ in Hin. apply in_flat_map in Hin. destruct Hin as [fr [Hfr Hin]].
  apply in_flat_map in Hin. destruct Hin as [r [Hr Ho]]. exists fr, r. split; [exact Hfr | split; [exact Hr | exact Ho]].
Qed.
(* a retained row's own file: its package membership, exact file, and the node whose occ_facts produced it *)
Lemma row_file (row : FactRowRef fp) :
  In row (fact_rows fp) ->
  exists fr, In fr (flat_map BN.PI.pkg_members (BN.PI.packages s))
             /\ Index.nr_file (frr_site row) = fr
             /\ In (frr_row row) (occ_facts bp (const_table bp fr) (frr_site row)).
Proof.
  intro Hin. assert (Hil : In (frr_row row) (fact_list fp))
    by (rewrite <- fact_rows_rows; apply in_map; exact Hin).
  rewrite fact_once in Hil. destruct (raw_facts_node_file (frr_row row) Hil) as [fr [r' [Hfr [Hr' Ho]]]].
  pose proof (occ_facts_site (const_table bp fr) r' (frr_row row) Ho) as Hsite.
  exists fr. unfold frr_site. rewrite Hsite. split; [exact Hfr | split].
  - exact (Index.file_nodes_file fr r' Hr').
  - exact Ho.
Qed.
(* a negative value child's exact value fact is retained in the same FactPhase, in its own file *)
Lemma value_fact_retained (fr : Index.FileRef idx)
  (Hfr : In fr (flat_map BN.PI.pkg_members (BN.PI.packages s)))
  (e : Index.NodeRef idx) (He : Index.nr_file e = fr)
  (Hneg : value_neg_b bp (own_value bp (const_table bp fr) e) = true) :
  In (OFValue e (own_value bp (const_table bp fr) e)) (fact_list fp).
Proof.
  rewrite fact_once, raw_facts_as_occ. apply in_flat_map. exists fr. split; [exact Hfr|].
  apply in_flat_map. exists e. split; [ exact (file_nodes_complete fr e He) | apply occ_value_mem; exact Hneg ].
Qed.
(* a negative application child's exact application fact is retained in the same FactPhase, in its own file *)
Lemma app_fact_retained (fr : Index.FileRef idx)
  (Hfr : In fr (flat_map BN.PI.pkg_members (BN.PI.packages s)))
  (e : Index.NodeRef idx) (He : Index.nr_file e = fr) (Hva : Index.node_view e = Index.Model.VApplication) :
  In (OFApp e (own_app bp (Index.Refs.mkAppRef e Hva))) (fact_list fp).
Proof.
  rewrite fact_once, raw_facts_as_occ. apply in_flat_map. exists fr. split; [exact Hfr|].
  apply in_flat_map. exists e. split; [ exact (file_nodes_complete fr e He) | apply occ_app_mem ].
Qed.
(* a retained SDependent statement fact came from the expr-statement arm: its outcome is the exact driver result *)
Lemma stmt_fact_dependent (r : Index.NodeRef idx)
  (sx : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr -> StmtOutcome bp r)
  (d : Dependency bp r StatementKind) :
  In (OFStmt r (SDependent d)) (stmt_fact bp r sx) ->
  exists (Hv : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr), SDependent d = sx Hv.
Proof.
  unfold stmt_fact.
  assert (Hgen : forall (v : Index.Model.NodeView) (H : Index.node_view r = v),
    In (OFStmt r (SDependent d)) (stmt_fact_body bp r sx v H) ->
    exists (Hv : Index.node_view r = Index.Model.VStmt Index.Model.SSExpr), SDependent d = sx Hv).
  { intros v H Hin. destruct v as [na|nl|nu| |nt|nb|nc|nvv|nts|nd0|nst| |ntp|];
      cbn [stmt_fact_body] in Hin; try (exfalso; exact Hin).
    destruct nst as [ | | sn sv ]; cbn [stmt_fact_body] in Hin.
    - destruct Hin as [Heq | []]. injection Heq as Heq'.
      apply (Eqdep_dec.inj_pair2_eq_dec _ noderef_eq_dec) in Heq'. exists H. symmetry; exact Heq'.
    - exfalso; exact Hin.
    - exfalso. destruct Hin as [Heq | []]. injection Heq as Heq'.
      apply (Eqdep_dec.inj_pair2_eq_dec _ noderef_eq_dec) in Heq'.
      exact (short_stmt_body_not_dep bp r sn sv H _ eq_refl d Heq'). }
  exact (Hgen (Index.node_view r) eq_refl).
Qed.
(* a negative value / application outcome makes one of the row's own cause/req/dep present *)
Lemma value_neg_disj (child_row : FactRowRef fp) (e : Index.NodeRef idx) (ov : ValueOutcome bp e)
  (Hrow : frr_row child_row = OFValue e ov) (Hneg : value_neg_b bp ov = true) :
  occ_cause (frr_row child_row) <> None \/ occ_req (frr_row child_row) <> None \/ occ_dep (frr_row child_row) <> None.
Proof.
  rewrite Hrow. destruct ov; cbn in Hneg |- *; try discriminate Hneg;
    first [ left; discriminate | right; left; discriminate | right; right; discriminate ].
Qed.
Lemma app_neg_disj (child_row : FactRowRef fp) (e : Index.NodeRef idx) (oa : AppOutcome bp e)
  (Hrow : frr_row child_row = OFApp e oa) (Hneg : app_neg_b bp oa = true) :
  occ_cause (frr_row child_row) <> None \/ occ_req (frr_row child_row) <> None \/ occ_dep (frr_row child_row) <> None.
Proof.
  rewrite Hrow. destruct oa; cbn in Hneg |- *; try discriminate Hneg;
    first [ left; discriminate | right; left; discriminate | right; right; discriminate ].
Qed.
(* §19.4/§19.5 a row with a present cause/req/dep has an exact negative case *)
Lemma negative_case_some (child_row : FactRowRef fp)
  (H : occ_cause (frr_row child_row) <> None \/ occ_req (frr_row child_row) <> None
       \/ occ_dep (frr_row child_row) <> None) :
  negative_case child_row <> None.
Proof.
  unfold negative_case.
  assert (Hg : forall
    (oc : option (Cause bp (fact_site (frr_row child_row)) (fact_kind (frr_row child_row))))
    (Hoc : occ_cause (frr_row child_row) = oc)
    (oq : option (Requirement bp (fact_site (frr_row child_row)) (fact_kind (frr_row child_row))))
    (Hoq : occ_req (frr_row child_row) = oq)
    (od : option (Dependency bp (fact_site (frr_row child_row)) (fact_kind (frr_row child_row))))
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
Lemma child_prerequisite_some (cdfr : ChildDependentFactRef) (child_row : FactRowRef fp)
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
Lemma fact_list_row (o : OccFact bp) : In o (fact_list fp) -> exists ref, In ref (fact_rows fp) /\ frr_row ref = o.
Proof.
  intro Hin. apply In_nth_error in Hin. destruct Hin as [k Hk].
  destruct (fact_rows_complete k o Hk) as [ref [Hnth [_ Hrow]]].
  exists ref. split; [ exact (nth_error_In _ _ Hnth) | exact Hrow ].
Qed.
(* §19.4 completeness: every child-dependent parent row has its exact negative child prerequisite, same FactPhase *)
Lemma child_prerequisite_complete (cdfr : ChildDependentFactRef) :
  In (cdfr_rowref cdfr) (fact_rows fp) -> child_prerequisite cdfr <> None.
Proof.
  intro Hin. pose proof (cdfr_ok cdfr) as Hok.
  destruct (row_file (cdfr_rowref cdfr) Hin) as [fr [Hfr [Hfile _]]].
  assert (Hsite : frr_site (cdfr_rowref cdfr) = cdfr_site cdfr) by (unfold frr_site; rewrite Hok; reflexivity).
  rewrite Hsite in Hfile.
  pose proof (fact_row_is_own (cdfr_rowref cdfr)) as Hown. rewrite Hok in Hown.
  destruct (stmt_fact_dependent (cdfr_site cdfr) _ (DepChild (cdfr_edge cdfr)) Hown) as [Hv Hsx].
  unfold expr_sx_own in Hsx.
  set (pr := Index.Refs.mkExprStmtRef (cdfr_site cdfr) Hv) in *.
  set (e0 := Index.Edges.ee_child (Index.Edges.exprstmt_expr pr)) in *.
  set (ctab := const_table bp (Index.nr_file (cdfr_site cdfr))) in *.
  symmetry in Hsx.
  destruct (own_stmt_expr_dep_inv pr _ _ (cdfr_edge cdfr) Hsx) as [Hcs Hcase].
  assert (Hes : cdfr_edge_site cdfr = e0) by (unfold cdfr_edge_site; exact Hcs).
  assert (Hfe : Index.nr_file e0 = fr)
    by (unfold e0, pr; rewrite (ee_child_file (cdfr_site cdfr) Hv); exact Hfile).
  assert (Hctab : ctab = const_table bp fr) by (unfold ctab; rewrite Hfile; reflexivity).
  destruct Hcase as [[Hk Hvn] | [Hk [_ [Han Hva]]]].
  - assert (Hret : In (OFValue e0 (own_value bp (const_table bp fr) e0)) (fact_list fp))
      by (apply (value_fact_retained fr Hfr e0 Hfe); rewrite <- Hctab; exact Hvn).
    assert (Hek : cdfr_edge_kind cdfr = ValueKind) by (unfold cdfr_edge_kind; exact Hk).
    destruct (fact_list_row _ Hret) as [child_row [Hcin Hcrow]].
    apply (child_prerequisite_some cdfr child_row).
    + rewrite Hes, Hek.
      apply (fact_row_for_complete e0 ValueKind child_row Hcin);
        [ unfold frr_site; rewrite Hcrow; reflexivity | unfold frr_kind; rewrite Hcrow; reflexivity ].
    + apply negative_case_some. apply (value_neg_disj child_row e0 (own_value bp (const_table bp fr) e0) Hcrow).
      rewrite <- Hctab; exact Hvn.
  - assert (Hret : In (OFApp e0 (own_app bp (Index.Refs.mkAppRef e0 Hva))) (fact_list fp))
      by (apply (app_fact_retained fr Hfr e0 Hfe Hva)).
    assert (Hek : cdfr_edge_kind cdfr = ApplicationKind) by (unfold cdfr_edge_kind; exact Hk).
    destruct (fact_list_row _ Hret) as [child_row [Hcin Hcrow]].
    apply (child_prerequisite_some cdfr child_row).
    + rewrite Hes, Hek.
      apply (fact_row_for_complete e0 ApplicationKind child_row Hcin);
        [ unfold frr_site; rewrite Hcrow; reflexivity | unfold frr_kind; rewrite Hcrow; reflexivity ].
    + apply negative_case_some. apply (app_neg_disj child_row e0 (own_app bp (Index.Refs.mkAppRef e0 Hva)) Hcrow).
      rewrite (app_neg_at_app bp e0 Hva) in Han; exact Han.
Qed.
(* §19.1 the retained parent row's site is exactly the edge's parent index *)
Lemma cdfr_parent_site (cdfr : ChildDependentFactRef) : frr_site (cdfr_rowref cdfr) = cdfr_site cdfr.
Proof. unfold frr_site; rewrite (cdfr_ok cdfr); reflexivity. Qed.
(* §19.1 the exact child fact's node is a real structural descendant: node_parent child = the parent statement *)
Lemma cdfr_child_parent (cdfr : ChildDependentFactRef) :
  Index.node_parent (cdfr_edge_site cdfr) = Some (cdfr_site cdfr).
Proof.
  unfold cdfr_edge_site. destruct (cdfr_edge cdfr) as [pr Hp | pr ar Hp Ha]; cbn [cfe_child_site];
    rewrite Hp; exact (Index.Child.ca_node_parent (Index.Edges.ee_at (Index.Edges.exprstmt_expr pr))).
Qed.
(* §19.1 the retained child kind is exactly value or application, never statement or type-use *)
Lemma cdfr_child_kind_va (cdfr : ChildDependentFactRef) :
  cdfr_edge_kind cdfr = ValueKind \/ cdfr_edge_kind cdfr = ApplicationKind.
Proof. unfold cdfr_edge_kind; destruct (cdfr_edge cdfr); [ left | right ]; reflexivity. Qed.
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
Lemma negative_case_none (child_row : FactRowRef fp) :
  occ_cause (frr_row child_row) = None -> occ_req (frr_row child_row) = None ->
  occ_dep (frr_row child_row) = None -> negative_case child_row = None.
Proof.
  intros Hc Hq Hd. unfold negative_case.
  assert (Hg : forall
    (oc : option (Cause bp (fact_site (frr_row child_row)) (fact_kind (frr_row child_row))))
    (Hoc : occ_cause (frr_row child_row) = oc)
    (oq : option (Requirement bp (fact_site (frr_row child_row)) (fact_kind (frr_row child_row))))
    (Hoq : occ_req (frr_row child_row) = oq)
    (od : option (Dependency bp (fact_site (frr_row child_row)) (fact_kind (frr_row child_row))))
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
Lemma nfr_class_invalid (child_row : FactRowRef fp) (n : NegativeFactRef child_row) :
  nfr_class n = NegInvalid <-> exists c H, n = ChildInvalid c H.
Proof.
  split; [ destruct n as [c Hc|rq Hq|d Hd]; cbn; try discriminate; intros _; exists c, Hc; reflexivity
         | intros [c [H ->]]; reflexivity ].
Qed.
(* §19.3 a value-negative child is selected first: the retained edge is the exact value-child edge *)
Lemma stmt_expr_value_first (pr : Index.Refs.ExprStmtRef idx) (an : bool) :
  own_stmt_expr bp pr true an = SDependent (DepChild (ExprStmtValueChild pr eq_refl)).
Proof. reflexivity. Qed.
(* §19.3 an application-negative child is selected only when the value child is nonnegative — the app-child edge *)
Lemma stmt_expr_app_second (pr : Index.Refs.ExprStmtRef idx)
  (He : Index.node_view (Index.Edges.ee_child (Index.Edges.exprstmt_expr pr)) = Index.Model.VApplication) :
  own_stmt_expr bp pr false true
  = SDependent (DepChild (ExprStmtApplicationChild pr (Index.Refs.mkAppRef _ He) eq_refl eq_refl)).
Proof.
  unfold own_stmt_expr.
  rewrite (convoy_at (Index.node_view (Index.Edges.ee_child (Index.Edges.exprstmt_expr pr)))
             (stmt_expr_body bp pr true) Index.Model.VApplication He).
  reflexivity.
Qed.
(* §19.3 no child dependency when both applicable child facts are nonnegative *)
Lemma stmt_expr_none (pr : Index.Refs.ExprStmtRef idx) (d : Dependency bp (Index.Refs.exs_node pr) StatementKind) :
  own_stmt_expr bp pr false false = SDependent d -> False.
Proof.
  intro H.
  destruct (own_stmt_expr_dep_inv pr false false (dep_child_edge d)
    (eq_trans H (f_equal (fun x => SDependent x) (dep_child_eq d)))) as [_ [[_ Hb]|[_ [_ [Hb _]]]]];
    discriminate Hb.
Qed.
End FactRowLaws.
Arguments fact_rows_rows {p idx s bd bp} fp. Arguments fact_rows_ords {p idx s bd bp} fp.
Arguments fact_rows_ord_nodup {p idx s bd bp} fp.
Arguments fact_key {p idx s bd bp} o. Arguments frr_key {p idx s bd bp fp} ref.
Arguments fact_row_for {p idx s bd bp} fp site kind.
Arguments nfr_class {p idx s bd bp fp child_row} _.
Arguments cdfr_site {p idx s bd bp fp} _. Arguments cdfr_edge_site {p idx s bd bp fp} _.
Arguments cdfr_edge_kind {p idx s bd bp fp} _. Arguments cpr_neg {p idx s bd bp fp cdfr} _.

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
Inductive IssueRoot {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) : Type :=
| RootNode : Index.NodeRef idx -> IssueRoot bp
| RootPackage : BN.PI.PackageRef s -> IssueRoot bp
| RootGroup : forall (n : Names.OrdinaryIdentifier), BN.RedeclRoot bp n -> IssueRoot bp.
Arguments RootNode {p idx s bd bp} _.
Arguments RootPackage {p idx s bd bp} _.
Arguments RootGroup {p idx s bd bp n} _.

(* the exact diagnostics, indexed by fp AND pf: a package invalidity is exactly its retained decision case ref *)
Inductive Diagnostic {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} (fp : FactPhase bp) (pf : PackageFacts bp) : Type :=
| DOcc : InvalidFactRef fp -> Diagnostic fp pf
| DMissingMain : MissingMainRef pf -> Diagnostic fp pf
| DOutputCollision : CollisionRef pf -> Diagnostic fp pf
| DRedeclaredGroup : forall (n : Names.OrdinaryIdentifier), BN.RedeclRoot bp n -> Diagnostic fp pf.
Arguments DOcc {p idx s bd bp fp pf} _.
Arguments DMissingMain {p idx s bd bp fp pf} _.
Arguments DOutputCollision {p idx s bd bp fp pf} _.
Arguments DRedeclaredGroup {p idx s bd bp fp pf n} _.

(* the exact boundaries: an occurrence-family unmet requirement is exactly its unmet fact-row ref, indexed by fp *)
Inductive Boundary {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} (fp : FactPhase bp) : Type :=
| BOcc : UnmetFactRef fp -> Boundary fp.
Arguments BOcc {p idx s bd bp fp} _.

(* the issue cause a reader projects from a diagnostic row, exactly as retained, never re-derived from a weaker site *)
Inductive IssueCause {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} (fp : FactPhase bp) (pf : PackageFacts bp) : Type :=
| OccCause : InvalidFactRef fp -> IssueCause fp pf
| MissingMainCause : MissingMainRef pf -> IssueCause fp pf
| OutputCollisionCause : CollisionRef pf -> IssueCause fp pf
| RedeclaredGroupCause : forall (n : Names.OrdinaryIdentifier), BN.RedeclRoot bp n -> IssueCause fp pf.
Arguments OccCause {p idx s bd bp fp pf} _.
Arguments MissingMainCause {p idx s bd bp fp pf} _.
Arguments OutputCollisionCause {p idx s bd bp fp pf} _.
Arguments RedeclaredGroupCause {p idx s bd bp fp pf n} _.

Section IssueProjections.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
        {bp : BN.BindingPhase s bd} {fp : FactPhase bp} {pf : PackageFacts bp}.

(* related nodes a cause carries: a complex mismatch's two components (all other causes carry none directly) *)
Definition cause_related {site : Index.NodeRef idx} {k : FactKind} (c : Cause bp site k) : list (Index.NodeRef idx) :=
  match c with ComplexMismatch _ a b => [a; b] | _ => [] end.
(* the cause a row retains: the exact invalid fact-row ref or exact package-decision case, projected exactly *)
Definition diag_cause (d : Diagnostic fp pf) : IssueCause fp pf :=
  match d with
  | DOcc ifr => OccCause ifr
  | DMissingMain mmr => MissingMainCause mmr
  | DOutputCollision cr => OutputCollisionCause cr
  | DRedeclaredGroup root => RedeclaredGroupCause root
  end.
Definition diag_family (d : Diagnostic fp pf) : option Family :=
  match d with DOcc ifr => Some (fact_family (ifr_fact ifr)) | _ => None end.
(* related nodes a row projects: the cause's components, or a group's exact members (use contexts via Report) *)
Definition diag_related (d : Diagnostic fp pf) : list (Index.NodeRef idx) :=
  match d with
  | DOcc ifr => cause_related (ifr_cause ifr)
  | DRedeclaredGroup root => map (fun m => BN.est_node (BN.es_est m)) (BN.bg_members (BN.rr_group (projT2 root)))
  | _ => []
  end.
Definition diag_root (d : Diagnostic fp pf) : IssueRoot bp :=
  match d with
  | DOcc ifr => RootNode (fact_site (ifr_fact ifr))
  | DMissingMain mmr => RootPackage (mmr_package mmr)
  | DOutputCollision cr => RootPackage (cr_package cr)
  | DRedeclaredGroup root => RootGroup root
  end.
Definition bound_req_ref (b : Boundary fp) : UnmetFactRef fp := match b with BOcc ufr => ufr end.
Definition bound_family (b : Boundary fp) : Family := match b with BOcc ufr => fact_family (ufr_fact ufr) end.
Definition bound_root (b : Boundary fp) : IssueRoot bp := match b with BOcc ufr => RootNode (fact_site (ufr_fact ufr)) end.

(* §18.3 occurrence-row projections are exact: cause/family/root of a DOcc project from its retained invalid fact *)
Lemma docc_cause (ifr : InvalidFactRef fp) : diag_cause (DOcc (pf:=pf) ifr) = OccCause ifr.
Proof. reflexivity. Qed.
Lemma docc_family (ifr : InvalidFactRef fp) : diag_family (DOcc (pf:=pf) ifr) = Some (fact_family (ifr_fact ifr)).
Proof. reflexivity. Qed.
Lemma docc_root (ifr : InvalidFactRef fp) : diag_root (DOcc (pf:=pf) ifr) = RootNode (fact_site (ifr_fact ifr)).
Proof. reflexivity. Qed.
(* §18.3 the invalid fact ref's exact cause is exactly the outcome payload its retained fact carries *)
Lemma ifr_cause_of_fact (ifr : InvalidFactRef fp) : occ_cause (ifr_fact ifr) = Some (ifr_cause ifr).
Proof. exact (ifr_ok ifr). Qed.
(* §18.3 boundary-row projections are exact: requirement/family/root of a BOcc project from its retained unmet fact *)
Lemma bocc_req (ufr : UnmetFactRef fp) : bound_req_ref (BOcc ufr) = ufr.
Proof. reflexivity. Qed.
Lemma bocc_family (ufr : UnmetFactRef fp) : bound_family (BOcc ufr) = fact_family (ufr_fact ufr).
Proof. reflexivity. Qed.
Lemma bocc_root (ufr : UnmetFactRef fp) : bound_root (BOcc ufr) = RootNode (fact_site (ufr_fact ufr)).
Proof. reflexivity. Qed.
Lemma ufr_req_of_fact (ufr : UnmetFactRef fp) : occ_req (ufr_fact ufr) = Some (ufr_req ufr).
Proof. exact (ufr_ok ufr). Qed.

End IssueProjections.

Section IssueTable.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} {bp : BN.BindingPhase s bd}
        (fp : FactPhase bp) (pf : PackageFacts bp).

(* one retained row yields one diagnostic iff its outcome is invalid: the exact invalid fact-row ref, no free fields *)
Definition occ_diag_rows (ref : FactRowRef fp) : list (Diagnostic fp pf) :=
  match occ_cause (frr_row ref) as oc return occ_cause (frr_row ref) = oc -> list (Diagnostic fp pf) with
  | Some c => fun H => [DOcc (mk_ifr ref c H)]
  | None => fun _ => []
  end eq_refl.
(* one exact retained row yields one boundary exactly when its outcome is unmet; invalid and unmet coexist (§6) *)
Definition occ_bound_rows (ref : FactRowRef fp) : list (Boundary fp) :=
  match occ_req (frr_row ref) as oq return occ_req (frr_row ref) = oq -> list (Boundary fp) with
  | Some q => fun H => [BOcc (mk_ufr ref q H)]
  | None => fun _ => []
  end eq_refl.

(* the sole selected package's default-output collision projects the exact retained preflight collision case *)
Definition collision_rows : list (Diagnostic fp pf) :=
  match collision_ref pf with Some cr => [DOutputCollision cr] | None => [] end.
(* one missing-executable-entry diagnostic per package whose exact canonical main decision IS MainMissing *)
Definition main_rows : list (Diagnostic fp pf) :=
  map DMissingMain (missing_main_refs pf).

(* every package-member name occurrence: the use sites a redeclared group can contextualize *)
Definition name_uses : list (Index.NodeRef idx) :=
  filter (fun r => match Index.node_view r with Index.Model.VName _ => true | _ => false end)
         (flat_map Index.file_nodes (flat_map BN.PI.pkg_members (BN.PI.packages s))).
(* one exact use context: a use of root's name resolving by exact-identity check to that exact root, with proof *)
Definition use_context_of {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot bp n0)
  (r : Index.NodeRef idx) : option (RedeclaredUseRef root) :=
  match Index.node_view r with
  | Index.Model.VName n =>
      match BN.ordinary_eq_dec n n0 with
      | left _ =>
          match BN.option_redeclroot_eq_dec (BN.resolution_redecl_root (BN.resolve bp r n0)) (Some root) with
          | left Hyields => Some (mk_redeclared_use r (BN.resolve bp r n0) Hyields)
          | right _ => None
          end
      | right _ => None
      end
  | _ => None
  end.
(* the exact use-site contexts of a redeclared root: uses of its name resolving, by exact identity, to it *)
Definition group_use_contexts {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot bp n0)
  : list (RedeclaredUseRef root) :=
  flat_map (fun r => match use_context_of root r with Some c => [c] | None => [] end) name_uses.

(* a returned use context's node is exactly the name occurrence it was built from *)
Lemma use_context_of_node {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot bp n0)
  (r : Index.NodeRef idx) (c : RedeclaredUseRef root) : use_context_of root r = Some c -> ruc_node c = r.
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
Definition context_qualifies {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot bp n0) (r : Index.NodeRef idx) : bool :=
  match use_context_of root r with Some _ => true | None => false end.
Lemma group_use_contexts_nodes {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot bp n0) :
  map ruc_node (group_use_contexts root) = filter (context_qualifies root) name_uses.
Proof. exact (flatmap_option_filter (use_context_of root) ruc_node (use_context_of_node root) name_uses). Qed.

(* the package name occurrences are duplicate-free: distinct positions within a file, distinct files across packages *)
Lemma name_uses_nodup : NoDup name_uses.
Proof.
  unfold name_uses. apply nodup_filter.
  apply (BN.flat_map_nodup_key _ Index.nr_file (fun fr => fr)).
  - rewrite map_id.
    apply (BN.flat_map_nodup_key _ (BN.PI.package_of_file s) (fun pr => pr)).
    + rewrite map_id. apply BN.packages_nodup.
    + intros pr _. apply BN.pkg_members_nodup.
    + intros pr fr _ Hin. exact (BN.PI.package_of_file_member s pr fr Hin).
  - intros fr _. apply file_nodes_nodup.
  - intros fr r _ Hin. exact (Index.file_nodes_file fr r Hin).
Qed.

(* §24.4 uniqueness / no-duplication: no name occurrence appears twice as a use context of a root *)
Lemma group_use_contexts_nodup {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot bp n0) :
  NoDup (map ruc_node (group_use_contexts root)).
Proof. rewrite group_use_contexts_nodes. apply nodup_filter. exact name_uses_nodup. Qed.

(* a name occurrence of the root's name resolving to that exact root does have a context *)
Lemma use_context_of_complete {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot bp n0) (r : Index.NodeRef idx) :
  Index.node_view r = Index.Model.VName n0 ->
  BN.resolution_redecl_root (BN.resolve bp r n0) = Some root ->
  exists c, use_context_of root r = Some c.
Proof.
  intros Hv Hres. unfold use_context_of. rewrite Hv.
  destruct (BN.ordinary_eq_dec n0 n0) as [_|Hne]; [| exfalso; apply Hne; reflexivity].
  destruct (BN.option_redeclroot_eq_dec (BN.resolution_redecl_root (BN.resolve bp r n0)) (Some root)) as [Hy|Hne];
    [ eexists; reflexivity | exfalso; apply Hne; exact Hres ].
Qed.

(* §24.4 completeness: every relevant use of the root's name resolving to it appears among its contexts *)
Lemma group_use_context_complete {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot bp n0) (r : Index.NodeRef idx) :
  In r name_uses -> Index.node_view r = Index.Model.VName n0 ->
  BN.resolution_redecl_root (BN.resolve bp r n0) = Some root ->
  In r (map ruc_node (group_use_contexts root)).
Proof.
  intros Hin Hv Hres. destruct (use_context_of_complete root r Hv Hres) as [c HE].
  rewrite <- (use_context_of_node root r c HE). apply in_map. unfold group_use_contexts.
  apply in_flat_map. exists r. split; [ exact Hin | rewrite HE; left; reflexivity ].
Qed.
(* one redeclared-group diagnostic per exact enumerated root; use contexts stay off the disposition path (on demand) *)
Definition group_rows : list (Diagnostic fp pf) :=
  map (fun rr => DRedeclaredGroup (projT2 rr)) (BN.redeclaration_roots bp).

(* §24.4 diagnostic enumeration: the group diagnostics are exactly one DRedeclaredGroup per exact enumerated root *)
Lemma group_rows_enumerated :
  group_rows = map (fun rr => DRedeclaredGroup (projT2 rr)) (BN.redeclaration_roots bp).
Proof. reflexivity. Qed.

(* occurrence diagnostics/boundaries derive FROM the exact retained rows (fact_rows fp), not from standalone facts *)
Definition occ_diags : list (Diagnostic fp pf) := flat_map occ_diag_rows (fact_rows fp).

(* the canonical order: output collision, package main, ordinary redeclaration, then occurrence in fact-row order *)
Definition diagnostics : list (Diagnostic fp pf) := collision_rows ++ main_rows ++ group_rows ++ occ_diags.
Definition boundaries : list (Boundary fp) := flat_map occ_bound_rows (fact_rows fp).

(* §19.3 the package diagnostic rows ARE the exact case-ref projections; neither re-tests the semantic condition *)
Lemma collision_rows_ref : collision_rows = match collision_ref pf with Some cr => [DOutputCollision cr] | None => [] end.
Proof. reflexivity. Qed.
Lemma main_rows_refs : main_rows = map DMissingMain (missing_main_refs pf).
Proof. reflexivity. Qed.
(* §19.3/§21 the collision-before-main-before-redeclaration-before-occurrence category order is unchanged *)
Lemma diagnostics_order : diagnostics = collision_rows ++ main_rows ++ group_rows ++ occ_diags.
Proof. reflexivity. Qed.

(* one row yields a diagnostic XOR a boundary; distinct-family facts of one subject still coexist across rows (§6) *)
Lemma occ_row_exclusive (ref : FactRowRef fp) : occ_diag_rows ref <> [] -> occ_bound_rows ref = [].
Proof.
  destruct ref as [o row Hat]; destruct row as [r ov | r oa | r os | r ot];
    [ destruct ov | destruct oa | destruct os | destruct ot ];
    cbn; intro H; solve [ reflexivity | exfalso; exact (H eq_refl) ].
Qed.

(* §18.1 the displayed family is exactly the total projection of the exact site and fact kind, never a stored field *)
Lemma fact_family_projection (o : OccFact bp) : fact_family o = displayed_family (fact_site o) (fact_kind o).
Proof. reflexivity. Qed.
(* §18.2 an occurrence fact's exact site and kind round-trip from the constructor that built it *)
Lemma occfact_roundtrip (r : Index.NodeRef idx) (ov : ValueOutcome bp r) (oa : AppOutcome bp r)
  (os : StmtOutcome bp r) (ot : TypeUseOutcome bp r) :
  (fact_site (OFValue r ov) = r /\ fact_kind (OFValue r ov) = ValueKind)
  /\ (fact_site (OFApp r oa) = r /\ fact_kind (OFApp r oa) = ApplicationKind)
  /\ (fact_site (OFStmt r os) = r /\ fact_kind (OFStmt r os) = StatementKind)
  /\ (fact_site (OFType r ot) = r /\ fact_kind (OFType r ot) = TypeUseKind).
Proof. repeat split; reflexivity. Qed.

(* §18.3 diagnostic completeness: an invalid row yields exactly one DOcc retaining that exact row *)
Lemma occ_diag_complete (ref : FactRowRef fp) (c : Cause bp (fact_site (frr_row ref)) (fact_kind (frr_row ref))) :
  occ_cause (frr_row ref) = Some c -> exists ifr, occ_diag_rows ref = [DOcc ifr] /\ ifr_rowref ifr = ref.
Proof.
  destruct ref as [o row Hat]; destruct row as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; intro H; try discriminate H; eexists; split; reflexivity.
Qed.
(* a row with no invalid outcome yields no diagnostic row *)
Lemma occ_diag_none (ref : FactRowRef fp) : occ_cause (frr_row ref) = None -> occ_diag_rows ref = [].
Proof.
  destruct ref as [o row Hat]; destruct row as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; intro H; solve [ reflexivity | discriminate H ].
Qed.
(* §18.3 diagnostic soundness: every occurrence diagnostic row is a DOcc of the exact retained row, no free fields *)
Lemma occ_diag_row_shape (ref : FactRowRef fp) (d : Diagnostic fp pf) :
  In d (occ_diag_rows ref) -> exists ifr, d = DOcc ifr /\ ifr_rowref ifr = ref.
Proof.
  destruct ref as [o row Hat]; destruct row as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; intro Hin; try (exfalso; exact Hin);
    destruct Hin as [Heq|[]]; subst d; eexists; split; reflexivity.
Qed.
(* §18.3 boundary completeness: an unmet row yields exactly one BOcc retaining that exact row *)
Lemma occ_bound_complete (ref : FactRowRef fp) (q : Requirement bp (fact_site (frr_row ref)) (fact_kind (frr_row ref))) :
  occ_req (frr_row ref) = Some q -> exists ufr, occ_bound_rows ref = [BOcc ufr] /\ ufr_rowref ufr = ref.
Proof.
  destruct ref as [o row Hat]; destruct row as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; intro H; try discriminate H; eexists; split; reflexivity.
Qed.
(* a row with no unmet outcome yields no boundary row *)
Lemma occ_bound_none (ref : FactRowRef fp) : occ_req (frr_row ref) = None -> occ_bound_rows ref = [].
Proof.
  destruct ref as [o row Hat]; destruct row as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; intro H; solve [ reflexivity | discriminate H ].
Qed.
(* §18.3 boundary soundness: every occurrence boundary row is a BOcc of the exact retained row, no free fields *)
Lemma occ_bound_row_shape (ref : FactRowRef fp) (b : Boundary fp) :
  In b (occ_bound_rows ref) -> exists ufr, b = BOcc ufr /\ ufr_rowref ufr = ref.
Proof.
  destruct ref as [o row Hat]; destruct row as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; intro Hin; try (exfalso; exact Hin);
    destruct Hin as [Heq|[]]; subst b; eexists; split; reflexivity.
Qed.
(* §18.3 at most one row of each class per retained row: the row lists are empty or a single exact row *)
Lemma occ_diag_rows_le1 (ref : FactRowRef fp) : occ_diag_rows ref = [] \/ exists d, occ_diag_rows ref = [d].
Proof.
  destruct ref as [o row Hat]; destruct row as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; solve [ left; reflexivity | right; eexists; reflexivity ].
Qed.
Lemma occ_bound_rows_le1 (ref : FactRowRef fp) : occ_bound_rows ref = [] \/ exists b, occ_bound_rows ref = [b].
Proof.
  destruct ref as [o row Hat]; destruct row as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; solve [ left; reflexivity | right; eexists; reflexivity ].
Qed.
(* §17.3/§18.3 a dependent outcome retains no cause or requirement, so its exact row yields no occurrence row *)
Lemma occ_dep_no_cause (o : OccFact bp) (d : Dependency bp (fact_site o) (fact_kind o)) :
  occ_dep o = Some d -> occ_cause o = None.
Proof.
  destruct o as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; intro H; solve [ reflexivity | discriminate H ].
Qed.
Lemma occ_dep_no_req (o : OccFact bp) (d : Dependency bp (fact_site o) (fact_kind o)) :
  occ_dep o = Some d -> occ_req o = None.
Proof.
  destruct o as [r ov|r oa|r os|r ot]; [destruct ov|destruct oa|destruct os|destruct ot];
    cbn; intro H; solve [ reflexivity | discriminate H ].
Qed.
Lemma dependent_fact_no_rows (dfr : DependentFactRef fp) :
  occ_diag_rows (dfr_rowref dfr) = [] /\ occ_bound_rows (dfr_rowref dfr) = [].
Proof.
  destruct dfr as [ref d Hok]; cbn; split;
    [ apply occ_diag_none; exact (occ_dep_no_cause (frr_row ref) d Hok)
    | apply occ_bound_none; exact (occ_dep_no_req (frr_row ref) d Hok) ].
Qed.

End IssueTable.

Arguments diagnostics {p idx s bd bp} fp pf.
Arguments boundaries {p idx s bd bp} fp.

Section IssueLaws.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
        {bp : BN.BindingPhase s bd} {fp : FactPhase bp} {pf : PackageFacts bp}.

(* the root algebra is total: every diagnostic roots at an exact node, package, or group, never a self-fallback *)
Lemma root_algebra_total (d : Diagnostic fp pf) :
  (exists r, diag_root d = RootNode r) \/ (exists pr, diag_root d = RootPackage pr)
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
  diag_root (DRedeclaredGroup root : Diagnostic fp pf) = RootGroup root.
Proof. reflexivity. Qed.

End IssueLaws.

(* §6 the complete disposition algebra + applicability before judgment *)
Inductive Disposition {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} (fp : FactPhase bp) (pf : PackageFacts bp) : Type :=
| DSucceeded : Disposition fp pf
| DAbsent : Disposition fp pf
| DInvalid : IssueCause fp pf -> list (IssueCause fp pf) -> Disposition fp pf
| DUnsupported : UnmetFactRef fp -> list (UnmetFactRef fp) -> Disposition fp pf
| DInvalidAndUnsupported : IssueCause fp pf -> list (IssueCause fp pf) -> UnmetFactRef fp -> list (UnmetFactRef fp) -> Disposition fp pf.
Arguments DSucceeded {p idx s bd bp fp pf}. Arguments DAbsent {p idx s bd bp fp pf}.
Arguments DInvalid {p idx s bd bp fp pf} _ _. Arguments DUnsupported {p idx s bd bp fp pf} _ _.
Arguments DInvalidAndUnsupported {p idx s bd bp fp pf} _ _ _ _.

Section DispositionAlgebra.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} {bp : BN.BindingPhase s bd}
        (fp : FactPhase bp) (pf : PackageFacts bp).

(* the whole-program disposition aggregates the one canonical issue table into the complete 5-way algebra *)
Definition program_disposition : Disposition fp pf :=
  match diagnostics fp pf, boundaries fp with
  | nil, nil => DSucceeded
  | d :: ds, nil => DInvalid (diag_cause d) (map diag_cause ds)
  | nil, b :: bs => DUnsupported (bound_req_ref b) (map bound_req_ref bs)
  | d :: ds, b :: bs => DInvalidAndUnsupported (diag_cause d) (map diag_cause ds)
                                               (bound_req_ref b) (map bound_req_ref bs)
  end.

(* success is exactly empty reports; a rejected program with simultaneous boundaries is InvalidAndUnsupported *)
Lemma program_disposition_succeeded :
  program_disposition = DSucceeded <-> diagnostics fp pf = nil /\ boundaries fp = nil.
Proof.
  unfold program_disposition; destruct (diagnostics fp pf) as [|d ds], (boundaries fp) as [|b bs]; cbn.
  - split; intros _; [ split; reflexivity | reflexivity ].
  - split; [ discriminate | intros [_ H2]; discriminate H2 ].
  - split; [ discriminate | intros [H1 _]; discriminate H1 ].
  - split; [ discriminate | intros [H1 _]; discriminate H1 ].
Qed.

Lemma program_disposition_both :
  (exists d ds b bs c1 c2 q1 q2, diagnostics fp pf = d :: ds /\ boundaries fp = b :: bs
     /\ program_disposition = DInvalidAndUnsupported c1 c2 q1 q2) \/
  program_disposition = DSucceeded \/
  (exists c cs, program_disposition = DInvalid c cs) \/
  (exists q qs, program_disposition = DUnsupported q qs).
Proof.
  unfold program_disposition; destruct (diagnostics fp pf) as [|d ds] eqn:Ed, (boundaries fp) as [|b bs] eqn:Eb.
  - right; left; reflexivity.
  - right; right; right; eexists; eexists; reflexivity.
  - right; right; left; eexists; eexists; reflexivity.
  - left; do 8 eexists; repeat split; reflexivity.
Qed.

End DispositionAlgebra.

(* §11 structural progress + cost: every construction is structural recursion over finite maps, no fuel or budget *)
Section Cost.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} (bp : BN.BindingPhase s bd).

(* one structural pass: each node contributes the facts of its applicable families via a single flat_map, no fuel *)
Lemma fact_phase_one_pass : fact_list (facts bp) = raw_facts bp.
Proof. unfold fact_list, facts; cbn [proj1_sig]. reflexivity. Qed.

End Cost.

(* the canonical issue lists and 5-way summary as projections of the one retained result, indexed by its exact fp *)
Definition result_diagnostics {p} (r : Result p) : list (Diagnostic (res_facts r) (res_pkg r)) :=
  diagnostics (res_facts r) (res_pkg r).
Definition result_boundaries {p} (r : Result p) : list (Boundary (res_facts r)) :=
  boundaries (res_facts r).
Definition result_disposition {p} (r : Result p) : Disposition (res_facts r) (res_pkg r) :=
  program_disposition (res_facts r) (res_pkg r).
(* §17 the child prerequisites of the one retained result, a narrow projection from its exact res_facts *)
Definition result_child_prerequisites {p} (r : Result p)
  : list { cdfr : ChildDependentFactRef (res_facts r) & ChildPrerequisiteRef (res_facts r) cdfr } :=
  child_prerequisite_refs (res_facts r).

(* an issue is a diagnostic or a boundary; the two classes partition the one canonical sequence *)
Inductive IssueClass : Type := ClassDiagnostic | ClassBoundary.

Inductive Issue {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} (fp : FactPhase bp) (pf : PackageFacts bp) : Type :=
| IDiag  : Diagnostic fp pf -> Issue fp pf
| IBound : Boundary fp -> Issue fp pf.
Arguments IDiag {p idx s bd bp fp pf} _.
Arguments IBound {p idx s bd bp fp pf} _.

(* the one canonical issue sequence: every diagnostic then every boundary, each kept in its own source order *)
Definition result_issues {p} (r : Result p) : list (Issue (res_facts r) (res_pkg r)) :=
  map IDiag (result_diagnostics r) ++ map IBound (result_boundaries r).

Section IssueIdentity.
Context {p : Syntax.Program}.

(* an issue's class, root, family, subject, and cause-or-requirement, projected from whichever row it is *)
Definition issue_class {r : Result p} (i : Issue (res_facts r) (res_pkg r)) : IssueClass :=
  match i with IDiag _ => ClassDiagnostic | IBound _ => ClassBoundary end.
Definition issue_root {r : Result p} (i : Issue (res_facts r) (res_pkg r)) : IssueRoot (res_binds r) :=
  match i with IDiag d => diag_root d | IBound b => bound_root b end.
Definition issue_family {r : Result p} (i : Issue (res_facts r) (res_pkg r)) : option Family :=
  match i with IDiag d => diag_family d | IBound b => Some (bound_family b) end.
Definition issue_cause_or_req {r : Result p} (i : Issue (res_facts r) (res_pkg r))
  : IssueCause (res_facts r) (res_pkg r) + UnmetFactRef (res_facts r) :=
  match i with IDiag d => inl (diag_cause d) | IBound b => inr (bound_req_ref b) end.
Definition issue_related {r : Result p} (i : Issue (res_facts r) (res_pkg r)) : list (Index.NodeRef (res_index r)) :=
  match i with IDiag d => diag_related d | IBound _ => [] end.

(* an issue identity: an exact ordinal into result_issues, retaining the exact row it indexes there *)
Record IssueRef (r : Result p) : Type := mkIssueRef {
  ir_ord : nat ;
  ir_row : Issue (res_facts r) (res_pkg r) ;
  ir_at  : nth_error (result_issues r) ir_ord = Some ir_row
}.
Arguments mkIssueRef {r} _ _ _.
Arguments ir_ord {r} _.
Arguments ir_row {r} _.
Arguments ir_at {r} _.

(* Diagnostic and Boundary are projections of an issue ref: exactly the row it references, never a synthesis *)
Definition iref_diagnostic {r : Result p} (ref : IssueRef r) : option (Diagnostic (res_facts r) (res_pkg r)) :=
  match ir_row ref with IDiag d => Some d | IBound _ => None end.
Definition iref_boundary {r : Result p} (ref : IssueRef r) : option (Boundary (res_facts r)) :=
  match ir_row ref with IBound b => Some b | IDiag _ => None end.

(* bidirectional membership: a ref is exactly a position that indexes an issue in the one sequence *)
Lemma issue_ref_sound (r : Result p) (ref : IssueRef r) :
  nth_error (result_issues r) (ir_ord ref) = Some (ir_row ref).
Proof. exact (ir_at ref). Qed.
Lemma issue_ref_complete (r : Result p) (n : nat) (i : Issue (res_facts r) (res_pkg r)) :
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
Lemma idiag_in (r : Result p) (n : nat) (d : Diagnostic (res_facts r) (res_pkg r)) :
  nth_error (result_issues r) n = Some (IDiag d) -> In d (result_diagnostics r).
Proof.
  intro H. apply nth_error_In in H. unfold result_issues in H. apply in_app_or in H.
  destruct H as [Hd|Hb].
  - apply in_map_iff in Hd. destruct Hd as [d' [Heq Hin]]. injection Heq as Heq. subst d'. exact Hin.
  - apply in_map_iff in Hb. destruct Hb as [b' [Heq _]]. discriminate Heq.
Qed.
Lemma ibound_in (r : Result p) (n : nat) (b : Boundary (res_facts r)) :
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
Lemma issue_diag_at (r : Result p) (n : nat) (d : Diagnostic (res_facts r) (res_pkg r)) :
  nth_error (result_diagnostics r) n = Some d -> nth_error (result_issues r) n = Some (IDiag d).
Proof.
  intro H. unfold result_issues.
  rewrite nth_error_app1 by (rewrite <- nth_error_Some; rewrite (map_nth_error _ _ _ H); discriminate).
  exact (map_nth_error _ _ _ H).
Qed.
Lemma issue_bound_at (r : Result p) (n : nat) (b : Boundary (res_facts r)) :
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
