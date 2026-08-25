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
| DepChild : forall (k : FactKind), Index.NodeRef idx -> Dependency bp site k.
Arguments DepRedeclaredNameV {p idx s bd bp site n} _ _ _.
Arguments DepRedeclaredNameA {p idx s bd bp site n} _ _ _.
Arguments DepRedeclaredNameT {p idx s bd bp site n} _ _ _.
Arguments DepUnboundNameV {p idx s bd bp site n} _ _ _.
Arguments DepUnboundNameA {p idx s bd bp site n} _ _ _.
Arguments DepInvalidId {p idx s bd bp site n} _ _ _. Arguments DepChild {p idx s bd bp site} k _.

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

Definition own_value (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx) : ValueOutcome bp r :=
  match Index.node_view r as v return Index.node_view r = v -> ValueOutcome bp r with
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
  end eq_refl.

Definition own_app (r : Index.NodeRef idx) : AppOutcome bp r :=
  match Index.node_view r as v return Index.node_view r = v -> AppOutcome bp r with
  | Index.Model.VApplication => fun Hv =>
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
      end
  | _ => fun _ => ADependent (DepChild ApplicationKind r)
  end eq_refl.

(* the dependency when a statement's expr already owns an invalidity, unmet requirement, or a dependent non-result *)
Definition expr_dependency (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (site e : Index.NodeRef idx)
  : option (Dependency bp site StatementKind) :=
  match own_value ctab e with
  | VInvalid _ | VUnmet _ | VDependent _ => Some (DepChild StatementKind e)
  | _ => match Index.node_view e with
         | Index.Model.VApplication => match own_app e with AInvalid _ | AUnmet _ | ADependent _ => Some (DepChild StatementKind e) | _ => None end
         | _ => None
         end
  end.

(* an expr-statement defers to an expr that owns an issue; otherwise it is a legal call statement or an illegal one *)
Definition own_stmt (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx) : StmtOutcome bp r :=
  match Index.node_view r as v return Index.node_view r = v -> StmtOutcome bp r with
  | Index.Model.VStmt Index.Model.SSExpr => fun Hv =>
      let e := Index.Edges.ee_child (Index.Edges.exprstmt_expr (Index.Refs.mkExprStmtRef r Hv)) in
      match expr_dependency ctab r e with
      | Some d => SDependent d
      | None =>
          match Index.node_view e as ve return Index.node_view e = ve -> StmtOutcome bp r with
          | Index.Model.VApplication => fun He =>
              match Index.node_view (Index.Edges.ah_child (Index.Edges.app_head (Index.Refs.mkAppRef e He))) with
              | Index.Model.VName h =>
                  match BN.resolution_object_view (BN.resolve bp r h) with
                  | Some o =>
                      match o with
                      | BN.PredeclaredObject Names.PPrintln => SOK
                      | BN.SourceObject _ => SOK
                      | _ => SInvalid (IllegalStatement Hv)
                      end
                  | None => SInvalid (IllegalStatement Hv)
                  end
              | _ => SInvalid (IllegalStatement Hv)
              end
          | _ => fun _ => SInvalid (IllegalStatement Hv)
          end eq_refl
      end
  | Index.Model.VStmt (Index.Model.SSShort nn nv) => fun Hv =>
      (* short declaration: retain the exact short event and canonical duplicate decision naming the repeated left *)
      let se := BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv) in
      match BN.short_dup_decision_name (BN.short_duplicate_decision se)
        as nm return BN.short_dup_decision_name (BN.short_duplicate_decision se) = nm -> StmtOutcome bp r with
      | Some n => fun Hn => SInvalid (ShortDuplicate (BN.short_duplicate_decision se) n eq_refl Hn eq_refl)
      | None => fun _ => SUnmet (ReqDeclMeaningS (Index.Refs.mkShortStmtRef r nn nv Hv) eq_refl)
      end eq_refl
  | _ => fun _ => SDependent (DepChild StatementKind r)
  end eq_refl.

(* the represented but unmodelled predeclared types: real Go types with no current C4 TypeForm *)
Definition is_unmodeled_type (pn : Names.PredeclaredName) : bool :=
  match pn with Names.PUintptr | Names.PAny | Names.PComparable | Names.PError => true | _ => false end.

(* a type use resolves its name: modelled type is its form, unmodelled real type a boundary, else invalid *)
Definition own_type (r : Index.NodeRef idx) : TypeUseOutcome bp r :=
  match Index.node_view r with
  | Index.Model.VTypeExpr (Syntax.NamedType n) =>
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
      end eq_refl
  | _ => TDependent (DepChild TypeUseKind r)
  end.

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

Section Retain.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} (bp : BN.BindingPhase s bd).

(* exactly the facts of the families that apply to a node, in family order; an inapplicable family yields none *)
Definition occ_facts (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx) : list (OccFact bp) :=
  match Index.node_view r with
  | Index.Model.VName _ | Index.Model.VLiteral _ | Index.Model.VUnary _ => [OFValue r (own_value bp ctab r)]
  | Index.Model.VApplication => [OFApp r (own_app bp r); OFValue r (own_value bp ctab r)]
  | Index.Model.VStmt Index.Model.SSExpr => [OFStmt r (own_stmt bp ctab r)]
  | Index.Model.VStmt (Index.Model.SSShort _ _) => [OFStmt r (own_stmt bp ctab r)]
  | Index.Model.VTypeExpr _ => [OFType r (own_type bp r)]
  | Index.Model.VConstSpec _ | Index.Model.VVarSpec _ | Index.Model.VTypeSpec _ => [OFValue r (own_value bp ctab r)]
  | _ => []
  end.

(* §16.5 same-site multi-family: an application node owns both its OFApp and OFValue facts at one identical site r *)
Lemma app_site_two_families (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx) :
  Index.node_view r = Index.Model.VApplication ->
  occ_facts ctab r = [OFApp r (own_app bp r); OFValue r (own_value bp ctab r)].
Proof. intro H. unfold occ_facts. rewrite H. reflexivity. Qed.

(* nonapplicability: occ_facts retains an application fact only at an application role, never elsewhere *)
Lemma no_app_fact_off_application (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r r' : Index.NodeRef idx) (o : AppOutcome bp r') :
  In (OFApp r' o) (occ_facts ctab r) -> Index.node_view r = Index.Model.VApplication.
Proof.
  intro Hin. unfold occ_facts in Hin. destruct (Index.node_view r); cbn in Hin;
    try (match type of Hin with context [match ?x with _ => _ end] => destruct x end; cbn in Hin);
    solve [ reflexivity | exfalso; intuition discriminate ].
Qed.
(* nonapplicability: occ_facts retains a statement fact only at a statement role *)
Lemma no_stmt_fact_off_statement (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r r' : Index.NodeRef idx) (o : StmtOutcome bp r') :
  In (OFStmt r' o) (occ_facts ctab r) -> exists st, Index.node_view r = Index.Model.VStmt st.
Proof.
  intro Hin. unfold occ_facts in Hin. destruct (Index.node_view r); cbn in Hin;
    try (match type of Hin with context [match ?x with _ => _ end] => destruct x end; cbn in Hin);
    solve [ eexists; reflexivity | exfalso; intuition discriminate ].
Qed.
(* nonapplicability: occ_facts retains a type-use fact only at a type-use role *)
Lemma no_type_fact_off_typeuse (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r r' : Index.NodeRef idx) (o : TypeUseOutcome bp r') :
  In (OFType r' o) (occ_facts ctab r) -> exists t, Index.node_view r = Index.Model.VTypeExpr t.
Proof.
  intro Hin. unfold occ_facts in Hin. destruct (Index.node_view r); cbn in Hin;
    try (match type of Hin with context [match ?x with _ => _ end] => destruct x end; cbn in Hin);
    solve [ eexists; reflexivity | exfalso; intuition discriminate ].
Qed.

(* one const table per file, built once and shared across that file's per-node facts (children stay in-file) *)
Definition raw_facts : list (OccFact bp) :=
  flat_map (fun fr => let ctab := const_table bp fr in flat_map (occ_facts ctab) (Index.file_nodes fr))
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
Arguments mm_of {p idx s bd bp} pf pr st H.
Arguments missing_main_refs {p idx s bd bp} pf.
Arguments coll_of {p idx s bd bp} pf d H.
Arguments collision_ref {p idx s bd bp} pf.

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
  unfold occ_facts. destruct (Index.node_view r) as [n|l|u| |t|b|c|v|ts|d|st| |tp| ]; try (destruct st);
    intro Hin; cbn in Hin; repeat (destruct Hin as [Hin|Hin]); solve [ exfalso; exact Hin | subst o; reflexivity ].
Qed.
(* the facts occ_facts retains at a node have duplicate-free keys: one per family, application's two kinds distinct *)
Lemma occ_facts_key_nodup (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx) :
  NoDup (map fact_key (occ_facts bp ctab r)).
Proof.
  unfold occ_facts. destruct (Index.node_view r) as [n|l|u| |t|b|c|v|ts|d|st| |tp| ]; try (destruct st);
    cbn [occ_facts map fact_key fact_site fact_kind];
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
  unfold raw_facts; cbv zeta; rewrite map_flat_map.
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
  unfold raw_facts. intro Hin. apply in_flat_map in Hin. destruct Hin as [fr [_ Hin]].
  cbv zeta in Hin. apply in_flat_map in Hin. destruct Hin as [r [Hr Ho]]. exists fr, r. split; [ exact Hr | exact Ho ].
Qed.
(* §12 canonical-row truth: a retained row's exact outcome is the own_* result the canonical traversal selected *)
Lemma fact_row_is_own (ref : FactRowRef fp) :
  match frr_row ref with
  | OFValue r ov => ov = own_value bp (const_table bp (Index.nr_file r)) r
  | OFApp r oa => oa = own_app bp r
  | OFStmt r os => os = own_stmt bp (const_table bp (Index.nr_file r)) r
  | OFType r ot => ot = own_type bp r
  end.
Proof.
  destruct ref as [k o Hat]; cbn [frr_row].
  assert (Hin : In o (raw_facts bp)) by (rewrite <- (fact_once bp fp); exact (nth_error_In _ _ Hat)).
  destruct (raw_facts_node o Hin) as [fr [r [Hr Ho]]]. pose proof (Index.file_nodes_file fr r Hr) as Hfile.
  unfold occ_facts in Ho. destruct (Index.node_view r) as [n|l|u| |t|b|c|v|ts|d|st| |tp| ]; try (destruct st);
    cbn in Ho; repeat (destruct Ho as [Ho|Ho]); try (exfalso; exact Ho);
    subst o; cbn; rewrite ?Hfile; reflexivity.
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

End FactRowLaws.
Arguments fact_rows_rows {p idx s bd bp} fp. Arguments fact_rows_ords {p idx s bd bp} fp.
Arguments fact_rows_ord_nodup {p idx s bd bp} fp.
Arguments fact_key {p idx s bd bp} o. Arguments frr_key {p idx s bd bp fp} ref.
Arguments fact_row_for {p idx s bd bp} fp site kind.

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

(* the exact diagnostics, indexed by fp: an occurrence invalidity is exactly its invalid fact-row ref, no free fields *)
Inductive Diagnostic {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} (fp : FactPhase bp) : Type :=
| DOcc : InvalidFactRef fp -> Diagnostic fp
| DMissingMain : BN.PI.PackageRef s -> Diagnostic fp
| DOutputCollision : BN.PI.PackageRef s -> BN.PI.RootEntryRef idx -> Diagnostic fp
| DRedeclaredGroup : forall (n : Names.OrdinaryIdentifier), BN.RedeclRoot bp n -> Diagnostic fp.
Arguments DOcc {p idx s bd bp fp} _.
Arguments DMissingMain {p idx s bd bp fp} _.
Arguments DOutputCollision {p idx s bd bp fp} _ _.
Arguments DRedeclaredGroup {p idx s bd bp fp n} _.

(* the exact boundaries: an occurrence-family unmet requirement is exactly its unmet fact-row ref, indexed by fp *)
Inductive Boundary {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} (fp : FactPhase bp) : Type :=
| BOcc : UnmetFactRef fp -> Boundary fp.
Arguments BOcc {p idx s bd bp fp} _.

(* the issue cause a reader projects from a diagnostic row, exactly as retained, never re-derived from a weaker site *)
Inductive IssueCause {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} (fp : FactPhase bp) : Type :=
| OccCause : InvalidFactRef fp -> IssueCause fp
| MissingMainCause : BN.PI.PackageRef s -> IssueCause fp
| OutputCollisionCause : BN.PI.PackageRef s -> BN.PI.RootEntryRef idx -> IssueCause fp
| RedeclaredGroupCause : forall (n : Names.OrdinaryIdentifier), BN.RedeclRoot bp n -> IssueCause fp.
Arguments OccCause {p idx s bd bp fp} _.
Arguments MissingMainCause {p idx s bd bp fp} _.
Arguments OutputCollisionCause {p idx s bd bp fp} _ _.
Arguments RedeclaredGroupCause {p idx s bd bp fp n} _.

Section IssueProjections.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
        {bp : BN.BindingPhase s bd} {fp : FactPhase bp}.

(* related nodes a cause carries: a complex mismatch's two components (all other causes carry none directly) *)
Definition cause_related {site : Index.NodeRef idx} {k : FactKind} (c : Cause bp site k) : list (Index.NodeRef idx) :=
  match c with ComplexMismatch _ a b => [a; b] | _ => [] end.
(* the cause a row retains: the exact invalid fact-row ref, projected exactly, never re-derived from a weaker site *)
Definition diag_cause (d : Diagnostic fp) : IssueCause fp :=
  match d with
  | DOcc ifr => OccCause ifr
  | DMissingMain pr => MissingMainCause pr
  | DOutputCollision pr rr => OutputCollisionCause pr rr
  | DRedeclaredGroup root => RedeclaredGroupCause root
  end.
Definition diag_family (d : Diagnostic fp) : option Family :=
  match d with DOcc ifr => Some (fact_family (ifr_fact ifr)) | _ => None end.
(* related nodes a row projects: the cause's components, or a group's exact members (use contexts via Report) *)
Definition diag_related (d : Diagnostic fp) : list (Index.NodeRef idx) :=
  match d with
  | DOcc ifr => cause_related (ifr_cause ifr)
  | DRedeclaredGroup root => map (fun m => BN.est_node (BN.es_est m)) (BN.bg_members (BN.rr_group (projT2 root)))
  | _ => []
  end.
Definition diag_root (d : Diagnostic fp) : IssueRoot bp :=
  match d with
  | DOcc ifr => RootNode (fact_site (ifr_fact ifr))
  | DMissingMain pr => RootPackage pr
  | DOutputCollision pr _ => RootPackage pr
  | DRedeclaredGroup root => RootGroup root
  end.
Definition bound_req_ref (b : Boundary fp) : UnmetFactRef fp := match b with BOcc ufr => ufr end.
Definition bound_family (b : Boundary fp) : Family := match b with BOcc ufr => fact_family (ufr_fact ufr) end.
Definition bound_root (b : Boundary fp) : IssueRoot bp := match b with BOcc ufr => RootNode (fact_site (ufr_fact ufr)) end.

(* §18.3 occurrence-row projections are exact: cause/family/root of a DOcc project from its retained invalid fact *)
Lemma docc_cause (ifr : InvalidFactRef fp) : diag_cause (DOcc ifr) = OccCause ifr.
Proof. reflexivity. Qed.
Lemma docc_family (ifr : InvalidFactRef fp) : diag_family (DOcc ifr) = Some (fact_family (ifr_fact ifr)).
Proof. reflexivity. Qed.
Lemma docc_root (ifr : InvalidFactRef fp) : diag_root (DOcc ifr) = RootNode (fact_site (ifr_fact ifr)).
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
Definition occ_diag_rows (ref : FactRowRef fp) : list (Diagnostic fp) :=
  match occ_cause (frr_row ref) as oc return occ_cause (frr_row ref) = oc -> list (Diagnostic fp) with
  | Some c => fun H => [DOcc (mk_ifr ref c H)]
  | None => fun _ => []
  end eq_refl.
(* one exact retained row yields one boundary exactly when its outcome is unmet; invalid and unmet coexist (§6) *)
Definition occ_bound_rows (ref : FactRowRef fp) : list (Boundary fp) :=
  match occ_req (frr_row ref) as oq return occ_req (frr_row ref) = oq -> list (Boundary fp) with
  | Some q => fun H => [BOcc (mk_ufr ref q H)]
  | None => fun _ => []
  end eq_refl.

(* the sole selected package's default-output collision, retaining the exact colliding root entry *)
Definition collision_rows : list (Diagnostic fp) :=
  match preflight pf with FreshOk => [] | FreshCollision pr rr => [DOutputCollision pr rr] end.
(* a package with no fixed main is a missing-executable-entry diagnostic; multiple mains are a group redeclaration *)
Definition main_rows : list (Diagnostic fp) :=
  flat_map (fun pr => match BN.package_main bp pr with BN.MainMissing => [DMissingMain pr] | _ => [] end) (BN.PI.packages s).

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
Definition group_rows : list (Diagnostic fp) :=
  map (fun rr => DRedeclaredGroup (projT2 rr)) (BN.redeclaration_roots bp).

(* §24.4 diagnostic enumeration: the group diagnostics are exactly one DRedeclaredGroup per exact enumerated root *)
Lemma group_rows_enumerated :
  group_rows = map (fun rr => DRedeclaredGroup (projT2 rr)) (BN.redeclaration_roots bp).
Proof. reflexivity. Qed.

(* occurrence diagnostics/boundaries derive FROM the exact retained rows (fact_rows fp), not from standalone facts *)
Definition occ_diags : list (Diagnostic fp) := flat_map occ_diag_rows (fact_rows fp).

(* the canonical order: output collision, package main, ordinary redeclaration, then occurrence in fact-row order *)
Definition diagnostics : list (Diagnostic fp) := collision_rows ++ main_rows ++ group_rows ++ occ_diags.
Definition boundaries : list (Boundary fp) := flat_map occ_bound_rows (fact_rows fp).

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
Lemma occ_diag_row_shape (ref : FactRowRef fp) (d : Diagnostic fp) :
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
        {bp : BN.BindingPhase s bd} {fp : FactPhase bp}.

(* the root algebra is total: every diagnostic roots at an exact node, package, or group, never a self-fallback *)
Lemma root_algebra_total (d : Diagnostic fp) :
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
  diag_root (DRedeclaredGroup root : Diagnostic fp) = RootGroup root.
Proof. reflexivity. Qed.

End IssueLaws.

(* §6 the complete disposition algebra + applicability before judgment *)
Inductive Disposition {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} (fp : FactPhase bp) : Type :=
| DSucceeded : Disposition fp
| DAbsent : Disposition fp
| DInvalid : IssueCause fp -> list (IssueCause fp) -> Disposition fp
| DUnsupported : UnmetFactRef fp -> list (UnmetFactRef fp) -> Disposition fp
| DInvalidAndUnsupported : IssueCause fp -> list (IssueCause fp) -> UnmetFactRef fp -> list (UnmetFactRef fp) -> Disposition fp.
Arguments DSucceeded {p idx s bd bp fp}. Arguments DAbsent {p idx s bd bp fp}.
Arguments DInvalid {p idx s bd bp fp} _ _. Arguments DUnsupported {p idx s bd bp fp} _ _.
Arguments DInvalidAndUnsupported {p idx s bd bp fp} _ _ _ _.

Section DispositionAlgebra.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} {bp : BN.BindingPhase s bd}
        (fp : FactPhase bp) (pf : PackageFacts bp).

(* the whole-program disposition aggregates the one canonical issue table into the complete 5-way algebra *)
Definition program_disposition : Disposition fp :=
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
Definition result_diagnostics {p} (r : Result p) : list (Diagnostic (res_facts r)) :=
  diagnostics (res_facts r) (res_pkg r).
Definition result_boundaries {p} (r : Result p) : list (Boundary (res_facts r)) :=
  boundaries (res_facts r).
Definition result_disposition {p} (r : Result p) : Disposition (res_facts r) :=
  program_disposition (res_facts r) (res_pkg r).

(* an issue is a diagnostic or a boundary; the two classes partition the one canonical sequence *)
Inductive IssueClass : Type := ClassDiagnostic | ClassBoundary.

Inductive Issue {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} (fp : FactPhase bp) : Type :=
| IDiag  : Diagnostic fp -> Issue fp
| IBound : Boundary fp -> Issue fp.
Arguments IDiag {p idx s bd bp fp} _.
Arguments IBound {p idx s bd bp fp} _.

(* the one canonical issue sequence: every diagnostic then every boundary, each kept in its own source order *)
Definition result_issues {p} (r : Result p) : list (Issue (res_facts r)) :=
  map IDiag (result_diagnostics r) ++ map IBound (result_boundaries r).

Section IssueIdentity.
Context {p : Syntax.Program}.

(* an issue's class, root, family, subject, and cause-or-requirement, projected from whichever row it is *)
Definition issue_class {r : Result p} (i : Issue (res_facts r)) : IssueClass :=
  match i with IDiag _ => ClassDiagnostic | IBound _ => ClassBoundary end.
Definition issue_root {r : Result p} (i : Issue (res_facts r)) : IssueRoot (res_binds r) :=
  match i with IDiag d => diag_root d | IBound b => bound_root b end.
Definition issue_family {r : Result p} (i : Issue (res_facts r)) : option Family :=
  match i with IDiag d => diag_family d | IBound b => Some (bound_family b) end.
Definition issue_cause_or_req {r : Result p} (i : Issue (res_facts r))
  : IssueCause (res_facts r) + UnmetFactRef (res_facts r) :=
  match i with IDiag d => inl (diag_cause d) | IBound b => inr (bound_req_ref b) end.
Definition issue_related {r : Result p} (i : Issue (res_facts r)) : list (Index.NodeRef (res_index r)) :=
  match i with IDiag d => diag_related d | IBound _ => [] end.

(* an issue identity: an exact ordinal into result_issues, retaining the exact row it indexes there *)
Record IssueRef (r : Result p) : Type := mkIssueRef {
  ir_ord : nat ;
  ir_row : Issue (res_facts r) ;
  ir_at  : nth_error (result_issues r) ir_ord = Some ir_row
}.
Arguments mkIssueRef {r} _ _ _.
Arguments ir_ord {r} _.
Arguments ir_row {r} _.
Arguments ir_at {r} _.

(* Diagnostic and Boundary are projections of an issue ref: exactly the row it references, never a synthesis *)
Definition iref_diagnostic {r : Result p} (ref : IssueRef r) : option (Diagnostic (res_facts r)) :=
  match ir_row ref with IDiag d => Some d | IBound _ => None end.
Definition iref_boundary {r : Result p} (ref : IssueRef r) : option (Boundary (res_facts r)) :=
  match ir_row ref with IBound b => Some b | IDiag _ => None end.

(* bidirectional membership: a ref is exactly a position that indexes an issue in the one sequence *)
Lemma issue_ref_sound (r : Result p) (ref : IssueRef r) :
  nth_error (result_issues r) (ir_ord ref) = Some (ir_row ref).
Proof. exact (ir_at ref). Qed.
Lemma issue_ref_complete (r : Result p) (n : nat) (i : Issue (res_facts r)) :
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
Lemma idiag_in (r : Result p) (n : nat) (d : Diagnostic (res_facts r)) :
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
Lemma issue_diag_at (r : Result p) (n : nat) (d : Diagnostic (res_facts r)) :
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
