(* Bindings — binders, blocks, objects, scopes, ordinary-name resolution, and package-scope function declarations. *)

From Stdlib Require Import String List Bool Arith PeanoNat Lia Eqdep_dec PArith NArith.
From Fido Require Import Syntax Names Index Compilable.PackageIdentity.
Import ListNotations.

Module PI := Compilable.PackageIdentity.

(* a declaration binder role: a const/var/type spec name; a short-left is NOT a declaration binder *)
Definition is_binder_role (r : Index.Model.Role) : bool :=
  match r with Index.Model.RSpecName _ => true | _ => false end.

Record BinderRef {p} (idx : Index.Core.ProgramIndex p) : Type := binder_ref {
  binder_node : Index.Core.NodeRef idx ;
  binder_ok   : is_binder_role (Index.Core.node_role binder_node) = true
}.
Arguments binder_ref {p idx} _ _.
Arguments binder_node {p idx} _.
Arguments binder_ok {p idx} _.

Lemma binderref_positional {p} {idx : Index.Core.ProgramIndex p} (a b : BinderRef idx) :
  binder_node a = binder_node b -> a = b.
Proof. destruct a as [na Ha], b as [nb Hb]; cbn; intro E; subst nb; f_equal; apply (UIP_dec Bool.bool_dec). Qed.

(* a package-scope function declaration reference; the fixed main is its only current inhabitant (C9 adds funcs) *)
Inductive FunctionDeclRef {p} (idx : Index.Core.ProgramIndex p) : Type :=
| FixedMainFunction : Index.Refs.MainOccurrenceRef idx -> FunctionDeclRef idx.
Arguments FixedMainFunction {p idx} _.

Definition function_occ {p} {idx : Index.Core.ProgramIndex p} (f : FunctionDeclRef idx) : Index.Refs.MainOccurrenceRef idx :=
  match f with FixedMainFunction mo => mo end.
Definition function_node {p} {idx : Index.Core.ProgramIndex p} (f : FunctionDeclRef idx) : Index.Core.NodeRef idx :=
  Index.Refs.mo_node (function_occ f).

(* the exact function signature profile; the fixed main's profile is exactly zero parameters and zero results *)
Record FunctionProfile {p} (idx : Index.Core.ProgramIndex p) : Type := mk_profile {
  fpr_params  : list (Index.Core.NodeRef idx) ;
  fpr_results : list (Index.Core.NodeRef idx)
}.
Arguments mk_profile {p idx} _ _.
Arguments fpr_params {p idx} _.
Arguments fpr_results {p idx} _.
Definition function_profile {p} {idx : Index.Core.ProgramIndex p} (f : FunctionDeclRef idx) : FunctionProfile idx :=
  match f with FixedMainFunction _ => mk_profile [] [] end.
Lemma fixed_main_profile {p} {idx : Index.Core.ProgramIndex p} (f : FunctionDeclRef idx) :
  fpr_params (function_profile f) = [] /\ fpr_results (function_profile f) = [].
Proof. destruct f; split; reflexivity. Qed.

(* a short-origin establishment's exact source identity: the statement, the left index, and its exact edge *)
Record ShortNewRef {p} (idx : Index.Core.ProgramIndex p) : Type := mk_short_new {
  snr_stmt : Index.Refs.ShortStmtRef idx ;
  snr_ix   : nat ;
  snr_edge : Index.Edges.ShortLhsEdge snr_stmt snr_ix
}.
Arguments mk_short_new {p idx} _ _ _.
Arguments snr_stmt {p idx} _.
Arguments snr_ix {p idx} _.
Arguments snr_edge {p idx} _.

(* a declaration origin: a declaration binder, a package-scope function declaration, or an exact ShortNew *)
Inductive DeclOrigin {p} (idx : Index.Core.ProgramIndex p) : Type :=
| DOBinder : BinderRef idx -> DeclOrigin idx
| DOFunc   : FunctionDeclRef idx -> DeclOrigin idx
| DOShort  : ShortNewRef idx -> DeclOrigin idx.
Arguments DOBinder {p idx} _.
Arguments DOFunc {p idx} _.
Arguments DOShort {p idx} _.

(* the establishing source occurrence of a declaration origin: binder token, function declaration, or left *)
Definition do_node {p} {idx : Index.Core.ProgramIndex p} (o : DeclOrigin idx) : Index.Core.NodeRef idx :=
  match o with
  | DOBinder b => binder_node b
  | DOFunc f => function_node f
  | DOShort sn => Index.Edges.sl_child (snr_edge sn)
  end.

(* an object a name resolves to: a predeclared identity, or a source declaration (a binder or a function) *)
Inductive ObjectRef {p} (idx : Index.Core.ProgramIndex p) : Type :=
| PredeclaredObject : Names.PredeclaredName -> ObjectRef idx
| SourceObject      : DeclOrigin idx -> ObjectRef idx.
Arguments PredeclaredObject {p idx} _.
Arguments SourceObject {p idx} _.

Inductive ScopeId {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
| PackageScope : PI.PackageRef s -> ScopeId s
| BlockScope   : Index.Refs.BlockRef idx -> ScopeId s.
Arguments PackageScope {p idx s} _.
Arguments BlockScope {p idx s} _.

(* a block binder's visibility start: type at its position, else its enclosing spec/statement parent's extent *)
Definition vis_start {p} {idx : Index.Core.ProgramIndex p} (b : Index.Core.NodeRef idx) : nat :=
  match Index.Core.node_role b with
  | Index.Model.RSpecName Index.Model.TypeSpecF => Index.Core.nr_pos b
  | Index.Model.RSpecName _ => match Index.Core.node_parent b with Some par => Index.Core.node_extent par | None => Index.Core.nr_pos b end
  | Index.Model.RShortLhs   => match Index.Core.node_parent b with Some par => Index.Core.node_extent par | None => Index.Core.nr_pos b end
  | _ => Index.Core.nr_pos b
  end.

Definition binder_ident {p} {idx : Index.Core.ProgramIndex p} (b : Index.Core.NodeRef idx) : option Names.OrdinaryIdentifier :=
  match Index.Core.node_view b with Index.Model.VBindingName (Syntax.BNamed n) => Some n | _ => None end.

Lemma spec_binder {p} {idx : Index.Core.ProgramIndex p} (b : Index.Core.NodeRef idx) (fl : Index.Model.SpecFlavor) :
  Index.Core.node_role b = Index.Model.RSpecName fl -> is_binder_role (Index.Core.node_role b) = true.
Proof. intro H; rewrite H; reflexivity. Qed.

(* whether a binder node spells a given name *)
Definition binder_name_matches {p} {idx : Index.Core.ProgramIndex p}
  (n : Names.OrdinaryIdentifier) (b : Index.Core.NodeRef idx) : bool :=
  match binder_ident b with Some m => Names.ordinary_equalb m n | None => false end.

(* the source identifier "main"; the fixed package-scope main function establishes under this ordinary name *)
Definition main_ident : Names.OrdinaryIdentifier :=
  Names.MakeOrdinary (Names.MakeIdentifier "main"%string eq_refl) eq_refl.

Record Est {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx) : Type := mk_est {
  est_origin : DeclOrigin idx ;
  est_name   : Names.OrdinaryIdentifier ;
  est_scope  : ScopeId s ;
  est_vstart : nat
}.
Arguments mk_est {p idx s} _ _ _ _.
Arguments est_origin {p idx s} _.
Arguments est_name {p idx s} _.
Arguments est_scope {p idx s} _.
Arguments est_vstart {p idx s} _.

(* the establishing source occurrence of an establishment: its binder token or its function declaration *)
Definition est_node {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx} (e : Est s) : Index.Core.NodeRef idx :=
  do_node (est_origin e).

(* a declaration binder establishes its name at the given scope; only an exact spec-name edge establishes here *)
Definition spec_name_est {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {fl : Index.Model.SpecFlavor} {sp : Index.Refs.SpecRef idx fl} {i : nat}
  (sc : ScopeId s) (ne : Index.Edges.SpecNameEdge sp i) : option (Est s) :=
  match binder_ident (Index.Edges.sn_child ne) with
  | Some n => Some (mk_est (DOBinder (binder_ref (Index.Edges.sn_child ne) (spec_binder _ fl (Index.Edges.sn_role ne))))
                          n sc (vis_start (Index.Edges.sn_child ne)))
  | None => None
  end.

(* one spec's establishments at its scope: every named binder among its exact name edges, in name order *)
Definition spec_ests {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {fl : Index.Model.SpecFlavor} (sc : ScopeId s) (sp : Index.Refs.SpecRef idx fl) : list (Est s) :=
  flat_map (fun x => match spec_name_est sc (projT2 x) with Some e => [e] | None => [] end)
           (Index.Edges.spec_name_edges sp).

(* the spec emission of one occurrence, factored over its view so laws can invert it exactly *)
Definition spec_emit {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (r : Index.Core.NodeRef idx) (v : Index.Model.NodeView) (Hv : Index.Core.node_view r = v) : list (Est s) :=
  match v as v0 return Index.Core.node_view r = v0 -> list (Est s) with
  | Index.Model.VConstSpec sh => fun Hv0 => spec_ests sc (Index.Refs.mkSpecRef (fl := Index.Model.ConstSpecF) r sh Hv0)
  | Index.Model.VVarSpec sh => fun Hv0 => spec_ests sc (Index.Refs.mkSpecRef (fl := Index.Model.VarSpecF) r sh Hv0)
  | Index.Model.VTypeSpec sh => fun Hv0 => spec_ests sc (Index.Refs.mkSpecRef (fl := Index.Model.TypeSpecF) r sh Hv0)
  | _ => fun _ => []
  end Hv.

(* one declaration's establishments: each child spec's named binders, in spec order *)
Definition decl_ests {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (d : Index.Core.NodeRef idx) : list (Est s) :=
  flat_map (fun x => spec_emit sc (Index.Child.ca_child (projT2 x)) (Index.Core.node_view (Index.Child.ca_child (projT2 x))) eq_refl)
           (Index.Child.all_children d).

(* a declaration statement's or top-level declaration's establishments: its one declaration child's specs *)
Definition stmt_decl_ests {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (t : Index.Core.NodeRef idx) : list (Est s) :=
  match Index.Child.child_at_opt t 0 with
  | Some e => decl_ests sc (Index.Child.ca_child e)
  | None => []
  end.

(* one spec's binder nodes, one per exact name edge in name order — blank and named alike *)
Definition spec_binder_nodes {p} {idx : Index.Core.ProgramIndex p}
  {fl : Index.Model.SpecFlavor} (sp : Index.Refs.SpecRef idx fl) : list (Index.Core.NodeRef idx) :=
  map (fun x => Index.Edges.sn_child (projT2 x)) (Index.Edges.spec_name_edges sp).

(* the binder nodes of one spec occurrence, factored over its view *)
Definition spec_binders_view {p} {idx : Index.Core.ProgramIndex p}
  (r : Index.Core.NodeRef idx) (v : Index.Model.NodeView) (Hv : Index.Core.node_view r = v) : list (Index.Core.NodeRef idx) :=
  match v as v0 return Index.Core.node_view r = v0 -> list (Index.Core.NodeRef idx) with
  | Index.Model.VConstSpec sh => fun Hv0 => spec_binder_nodes (Index.Refs.mkSpecRef (fl := Index.Model.ConstSpecF) r sh Hv0)
  | Index.Model.VVarSpec sh => fun Hv0 => spec_binder_nodes (Index.Refs.mkSpecRef (fl := Index.Model.VarSpecF) r sh Hv0)
  | Index.Model.VTypeSpec sh => fun Hv0 => spec_binder_nodes (Index.Refs.mkSpecRef (fl := Index.Model.TypeSpecF) r sh Hv0)
  | _ => fun _ => []
  end Hv.

(* one declaration's binder nodes: each child spec's binders, in spec order *)
Definition decl_binder_nodes {p} {idx : Index.Core.ProgramIndex p} (d : Index.Core.NodeRef idx) : list (Index.Core.NodeRef idx) :=
  flat_map (fun x => spec_binders_view (Index.Child.ca_child (projT2 x))
                       (Index.Core.node_view (Index.Child.ca_child (projT2 x))) eq_refl)
           (Index.Child.all_children d).

(* a declaration statement's or top declaration's flat binder sequence, in source order *)
Definition decl_binders {p} {idx : Index.Core.ProgramIndex p} (t : Index.Core.NodeRef idx) : list (Index.Core.NodeRef idx) :=
  match Index.Child.child_at_opt t 0 with
  | Some e => decl_binder_nodes (Index.Child.ca_child e)
  | None => []
  end.

(* a package-scope function declaration: the fixed main establishes the name main at package scope *)
Definition make_main_est {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (b : Index.Core.NodeRef idx) : option (Est s) :=
  (match Index.Core.is_main_view (Index.Core.node_view b) as m
     return Index.Core.is_main_view (Index.Core.node_view b) = m -> option (Est s) with
   | true => fun H => Some (mk_est (DOFunc (FixedMainFunction (Index.Refs.mkMainOccurrenceRef b H))) main_ident (PackageScope pr) (Index.Core.nr_pos b))
   | false => fun _ => None
   end) eq_refl.

(* the package-scope establishments of one occurrence: a fixed main, or a top-level declaration's binders *)
Inductive MainStatus {p} {idx : Index.Core.ProgramIndex p}
  (s : PI.PackageSurface idx) (pr : PI.PackageRef s) : Type :=
| MainMissing : MainStatus s pr
| MainOne : Est s -> MainStatus s pr
| MainMultiple : Est s -> Est s -> list (Est s) -> MainStatus s pr.
Arguments MainMissing {p idx s pr}.
Arguments MainOne {p idx s pr} _.
Arguments MainMultiple {p idx s pr} _ _ _.

Definition main_status_ests {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx} {pr : PI.PackageRef s}
  (st : MainStatus s pr) : list (Est s) :=
  match st with
  | MainMissing => []
  | MainOne m => [m]
  | MainMultiple m1 m2 rest => m1 :: m2 :: rest
  end.

(* a function-declaration establishment (DOFunc); the fixed main is its only current inhabitant *)
Definition is_func_est {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx} (e : Est s) : bool :=
  match est_origin e with DOFunc _ => true | _ => false end.

(* the package-scope function declarations named main in one package, in establishment order *)
Definition main_ests_of {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (ests : list (Est s)) (pr : PI.PackageRef s) : list (Est s) :=
  filter (fun e => andb (is_func_est e)
                        (andb (Names.ordinary_equalb (est_name e) main_ident)
                              (match est_scope e with PackageScope q => PI.packageref_eqb q pr | _ => false end)))
         ests.

Definition main_status_of {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (ests : list (Est s)) (pr : PI.PackageRef s) : MainStatus s pr :=
  match main_ests_of ests pr with
  | [] => MainMissing
  | m :: nil => MainOne m
  | m1 :: m2 :: rest => MainMultiple m1 m2 rest
  end.

Lemma main_status_ests_of {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (ests : list (Est s)) (pr : PI.PackageRef s) :
  main_status_ests (main_status_of ests pr) = main_ests_of ests pr.
Proof. unfold main_status_of; destruct (main_ests_of ests pr) as [|m1 [|m2 rest]]; reflexivity. Qed.

(* declaration groups: the establishments sharing one exact scope and spelling *)

Definition noderef_eqb {p} {idx : Index.Core.ProgramIndex p} (a b : Index.Core.NodeRef idx) : bool :=
  andb (Index.Edges.fileref_eqb (Index.Core.nr_file a) (Index.Core.nr_file b)) (Nat.eqb (Index.Core.nr_pos a) (Index.Core.nr_pos b)).

Lemma noderef_eqb_spec {p} {idx : Index.Core.ProgramIndex p} (a b : Index.Core.NodeRef idx) :
  noderef_eqb a b = true <-> a = b.
Proof.
  unfold noderef_eqb; split.
  - intro H; apply andb_true_iff in H as [Hf Hp].
    apply Index.Edges.fileref_eqb_spec in Hf. apply Nat.eqb_eq in Hp. apply Index.Core.noderef_positional; assumption.
  - intro H; subst b. rewrite (proj2 (Index.Edges.fileref_eqb_spec _ _) eq_refl), Nat.eqb_refl; reflexivity.
Qed.

Definition scope_eqb {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx} (a b : ScopeId s) : bool :=
  match a, b with
  | PackageScope pa, PackageScope pb => PI.packageref_eqb pa pb
  | BlockScope ba, BlockScope bb => noderef_eqb (Index.Refs.bl_node ba) (Index.Refs.bl_node bb)
  | _, _ => false
  end.

Lemma scope_eqb_spec {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx} (a b : ScopeId s) :
  scope_eqb a b = true <-> a = b.
Proof.
  destruct a as [pa|ba], b as [pb|bb]; cbn; split; try discriminate.
  - intro H; apply PI.packageref_eqb_spec in H; subst; reflexivity.
  - intro H; injection H as <-; apply (proj2 (PI.packageref_eqb_spec _ _) eq_refl).
  - intro H; apply noderef_eqb_spec in H; apply Index.Refs.blockref_positional in H; subst; reflexivity.
  - intro H; injection H as <-; apply (proj2 (noderef_eqb_spec _ _) eq_refl).
Qed.

(* two establishments belong to the same declaration group iff they share an exact scope and spelling *)
Definition same_group {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx} (a b : Est s) : bool :=
  andb (scope_eqb (est_scope a) (est_scope b)) (Names.ordinary_equalb (est_name a) (est_name b)).

(* two establishments are the same establishment iff they share their exact source occurrence *)
Definition est_eqb {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx} (a b : Est s) : bool :=
  noderef_eqb (est_node a) (est_node b).

(* the ordered members of e's group over an establishment list: shared exact scope and spelling, list order *)
Definition is_block_scoped {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx} (e : Est s) : bool :=
  match est_scope e with BlockScope _ => true | PackageScope _ => false end.

(* a binder introduces a variable object exactly when it is a short-lhs or var-spec name *)
Definition is_variable_binder {p} {idx : Index.Core.ProgramIndex p} (b : Index.Core.NodeRef idx) : bool :=
  match Index.Core.node_role b with Index.Model.RShortLhs | Index.Model.RSpecName Index.Model.VarSpecF => true | _ => false end.

Definition is_explicit_const_spec {p} {idx : Index.Core.ProgramIndex p} (c : Index.Core.NodeRef idx) : bool :=
  match Index.Core.node_view c with Index.Model.VConstSpec (Index.Model.CSExplicit _ _ _) => true | _ => false end.

(* a const spec is explicit exactly when its retained shape is; the ref's shape is the one authority *)
Definition cs_explicit {p} {idx : Index.Core.ProgramIndex p} (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF) : bool :=
  match Index.Refs.sp_shape cs with Index.Model.CSExplicit _ _ _ => true | Index.Model.CSInherited _ => false end.

(* the first earlier left edge of the same exact statement repeating this name, with its exact index *)
Fixpoint find_dup {p} {idx : Index.Core.ProgramIndex p} {st : Index.Refs.ShortStmtRef idx}
  (i : nat) (n : Names.OrdinaryIdentifier) (l : list { j : nat & Index.Edges.ShortLhsEdge st j }) {struct l}
  : option { j : nat & (Index.Edges.ShortLhsEdge st j * (j < i))%type } :=
  match l with
  | [] => None
  | existT _ j e :: rest =>
      match lt_dec j i with
      | left Hj =>
          if match binder_ident (Index.Edges.sl_child e) with
             | Some m => Names.ordinary_equalb m n | None => false end
          then Some (existT _ j (e, Hj)) else find_dup i n rest
      | right _ => find_dup i n rest
      end
  end.

(* the exact first-in-group evidence: the spec is a file root or sits at ordinal zero under its parent *)
Inductive ConstFirst {p} {idx : Index.Core.ProgramIndex p} (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF) : Type :=
| CFRoot : Index.Core.node_parent (Index.Refs.sp_node cs) = None -> ConstFirst cs
| CFOrd0 : forall se : Index.Edges.SelfEdge (Index.Refs.sp_node cs), Index.Edges.se_ord se = 0 -> ConstFirst cs.
Arguments CFRoot {p idx cs} _.
Arguments CFOrd0 {p idx cs} _ _.

(* the exact immediate predecessor: the canonical edges of predecessor and spec at adjacent ordinals *)
Record ConstAdjacency {p} {idx : Index.Core.ProgramIndex p}
  (cs pred : Index.Refs.SpecRef idx Index.Model.ConstSpecF) : Type := mk_const_adj {
  cad_parent  : Index.Core.NodeRef idx ;
  cad_ord     : nat ;
  cad_pred_at : Index.Child.ChildAt cad_parent cad_ord ;
  cad_pred_eq : Index.Refs.sp_node pred = Index.Child.ca_child cad_pred_at ;
  cad_self_at : Index.Child.ChildAt cad_parent (S cad_ord) ;
  cad_self_eq : Index.Refs.sp_node cs = Index.Child.ca_child cad_self_at
}.
Arguments mk_const_adj {p idx cs pred} _ _ _ _ _ _.
Arguments cad_parent {p idx cs pred} _.
Arguments cad_ord {p idx cs pred} _.
Arguments cad_pred_at {p idx cs pred} _.
Arguments cad_pred_eq {p idx cs pred} _.
Arguments cad_self_at {p idx cs pred} _.
Arguments cad_self_eq {p idx cs pred} _.

(* the exact const-spec judgment: explicit, first inherited, or inherited with its exact predecessor chain *)
Inductive ConstJudgment {p} {idx : Index.Core.ProgramIndex p} : Index.Refs.SpecRef idx Index.Model.ConstSpecF -> Type :=
| CJExplicit : forall cs, cs_explicit cs = true -> ConstJudgment cs
| CJFirstInherited : forall cs, cs_explicit cs = false -> ConstFirst cs -> ConstJudgment cs
| CJInherited : forall cs pred, cs_explicit cs = false -> ConstAdjacency cs pred ->
                ConstJudgment pred -> ConstJudgment cs.

(* the effective explicit origin, projected through the exact retained predecessor chain *)
Fixpoint const_origin {p} {idx : Index.Core.ProgramIndex p} {cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF}
  (j : ConstJudgment cs) : option { o : Index.Refs.SpecRef idx Index.Model.ConstSpecF & cs_explicit o = true } :=
  match j with
  | CJExplicit c He => Some (existT _ c He)
  | CJFirstInherited _ _ _ => None
  | CJInherited _ _ _ _ jp => const_origin jp
  end.

(* the exact immediate predecessor a judgment retains, when it has one *)
Definition const_pred {p} {idx : Index.Core.ProgramIndex p} {cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF}
  (j : ConstJudgment cs) : option (Index.Refs.SpecRef idx Index.Model.ConstSpecF) :=
  match j with
  | CJExplicit _ _ => None
  | CJFirstInherited _ _ _ => None
  | CJInherited _ pred _ _ _ => Some pred
  end.

(* judge the const spec at ordinal k under its declaration, chaining structurally on the ordinal *)
Fixpoint const_judge {p} {idx : Index.Core.ProgramIndex p} (par : Index.Core.NodeRef idx)
  (Hd : Index.Core.node_view par = Index.Model.VDecl Index.Model.ConstSpecF) (k : nat) {struct k}
  : forall (e : Index.Child.ChildAt par k) (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF),
    Index.Refs.sp_node cs = Index.Child.ca_child e -> ConstJudgment cs :=
  match k with
  | O => fun e cs Hnode =>
      match Bool.bool_dec (cs_explicit cs) true with
      | left He => CJExplicit cs He
      | right Hne =>
          CJFirstInherited cs (Bool.not_true_is_false _ Hne)
            (CFOrd0 (Index.Edges.mkSelfEdge par 0 e (eq_sym Hnode)) eq_refl)
      end
  | S k' => fun e cs Hnode =>
      match Bool.bool_dec (cs_explicit cs) true with
      | left He => CJExplicit cs He
      | right Hne =>
          let pca := Index.Child.child_at_lt par k' (Index.Edges.ca_pred_lt e) in
          let pred := Index.Edges.spec_child_at par k' Hd pca in
          CJInherited cs (proj1_sig pred) (Bool.not_true_is_false _ Hne)
            (mk_const_adj par k' pca (proj2_sig pred) e Hnode)
            (const_judge par Hd k' pca (proj1_sig pred) (proj2_sig pred))
      end
  end.

(* a const spec that sits under a parent sits under its const declaration *)
Lemma self_parent_decl {p} {idx : Index.Core.ProgramIndex p} (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF)
  (se : Index.Edges.SelfEdge (Index.Refs.sp_node cs)) :
  Index.Core.node_view (Index.Edges.se_parent se) = Index.Model.VDecl Index.Model.ConstSpecF.
Proof.
  pose proof (Index.Child.ca_at (Index.Edges.se_at se)) as Hat.
  rewrite (Index.Edges.se_child_eq se) in Hat.
  destruct (Index.Core.node_child_const_parent (Index.Edges.se_parent se) (Index.Refs.sp_node cs)
              (Index.Edges.se_ord se) (Index.Refs.sp_shape cs) Hat (Index.Refs.sp_ok cs)) as [fl Hfl].
  destruct fl; [ exact Hfl | | ];
    (pose proof (Index.Core.node_child_decl_spec (Index.Edges.se_parent se) (Index.Refs.sp_node cs) _
                   (Index.Edges.se_ord se) Hfl Hat) as Hclass;
     rewrite (Index.Refs.sp_ok cs) in Hclass; cbn in Hclass; destruct Hclass).
Qed.

(* the one canonical judgment of a const spec, decided at its exact canonical position *)
Definition const_judgment_of {p} {idx : Index.Core.ProgramIndex p}
  (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF) : ConstJudgment cs :=
  (match Index.Core.node_parent (Index.Refs.sp_node cs) as o
         return Index.Core.node_parent (Index.Refs.sp_node cs) = o -> ConstJudgment cs with
   | Some par => fun Hp =>
       let se := Index.Edges.self_edge_of (Index.Refs.sp_node cs) par Hp in
       const_judge (Index.Edges.se_parent se) (self_parent_decl cs se) (Index.Edges.se_ord se)
         (Index.Edges.se_at se) cs (eq_sym (Index.Edges.se_child_eq se))
   | None => fun Hp =>
       match Bool.bool_dec (cs_explicit cs) true with
       | left He => CJExplicit cs He
       | right Hne => CJFirstInherited cs (Bool.not_true_is_false _ Hne) (CFRoot Hp)
       end
   end) eq_refl.

(* the const-spec emission of one occurrence, factored over its view so laws can invert it exactly *)
Definition const_ref_emit {p} {idx : Index.Core.ProgramIndex p} (r : Index.Core.NodeRef idx)
  (v : Index.Model.NodeView) (Hv : Index.Core.node_view r = v) : list (Index.Refs.SpecRef idx Index.Model.ConstSpecF) :=
  match v as v0 return Index.Core.node_view r = v0 -> _ with
  | Index.Model.VConstSpec sh => fun Hv0 => [Index.Refs.mkSpecRef (fl := Index.Model.ConstSpecF) r sh Hv0]
  | _ => fun _ => []
  end Hv.

Lemma const_ref_emit_cover {p} {idx : Index.Core.ProgramIndex p} (r : Index.Core.NodeRef idx)
  (v : Index.Model.NodeView) (Hv : Index.Core.node_view r = v) (sh : Index.Model.ConstShape) :
  v = Index.Model.VConstSpec sh ->
  exists cs', In cs' (const_ref_emit r v Hv) /\ Index.Refs.sp_node cs' = r.
Proof.
  intro E. revert Hv. subst v. intro Hv. cbn.
  eexists. split; [ left; reflexivity | reflexivity ].
Qed.

(* every represented const spec of the surface, in exact source order: file order, then position order *)
Definition const_specs_of_file {p} {idx : Index.Core.ProgramIndex p} (fr : Index.Core.FileRef idx)
  : list (Index.Refs.SpecRef idx Index.Model.ConstSpecF) :=
  flat_map (fun pos => match Index.Core.mk_noderef fr (Pos.of_succ_nat pos) with
                       | Some r => const_ref_emit r (Index.Core.node_view r) eq_refl
                       | None => []
                       end)
           (seq 0 (Index.Core.occ_count fr)).
Definition const_subjects {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx)
  : list (Index.Refs.SpecRef idx Index.Model.ConstSpecF) :=
  flat_map (fun pr => flat_map const_specs_of_file (PI.pkg_members pr)) (PI.packages s).

(* the one canonical const-judgment table of the surface *)
Definition const_table {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx)
  : list { cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF & ConstJudgment cs } :=
  map (fun cs => existT _ cs (const_judgment_of cs)) (const_subjects s).

(* the first member satisfying a predicate, with its exact ordinal *)
Fixpoint find_ord {A} (f : A -> bool) (k : nat) (l : list A) : option (nat * A) :=
  match l with
  | [] => None
  | x :: t => if f x then Some (k, x) else find_ord f (S k) t
  end.

Lemma find_ord_none {A} (f : A -> bool) :
  forall l k, find_ord f k l = None -> forall x, In x l -> f x = false.
Proof.
  induction l as [|x t IH]; intros k Hf y Hin; [ destruct Hin |].
  cbn in Hf. destruct (f x) eqn:Hx; [ discriminate Hf |].
  destruct Hin as [<-|Hin]; [ exact Hx | exact (IH (S k) Hf y Hin) ].
Qed.

Lemma find_ord_found {A} (f : A -> bool) :
  forall l k j x, find_ord f k l = Some (j, x) ->
  k <= j /\ nth_error l (j - k) = Some x /\ f x = true
  /\ (forall j2 y, j2 < j - k -> nth_error l j2 = Some y -> f y = false).
Proof.
  induction l as [|a t IH]; intros k j x Hf; [ discriminate Hf |].
  cbn in Hf. destruct (f a) eqn:Ha.
  - injection Hf as <- <-. rewrite Nat.sub_diag. cbn.
    split; [ lia | split; [ reflexivity | split; [ exact Ha |] ] ].
    intros j2 y Hj2 _. lia.
  - destruct (IH (S k) j x Hf) as [Hle [Hnth [Hfx Hbefore]]].
    split; [ lia |]. split.
    + replace (j - k) with (S (j - S k)) by lia. exact Hnth.
    + split; [ exact Hfx |].
      intros j2 y Hj2 Hny. destruct j2 as [|j2'].
      * cbn in Hny. injection Hny as <-. exact Ha.
      * cbn in Hny. apply (Hbefore j2' y); [ lia | exact Hny ].
Qed.

(* the first two ordinals at which a predicate holds, if there are at least two — the exact ambiguity witnesses *)
Fixpoint find_two_ord {A} (f : A -> bool) (k : nat) (l : list A) : option (nat * nat) :=
  match l with
  | [] => None
  | x :: t => if f x
              then match find_ord f (S k) t with Some (j, _) => Some (k, j) | None => None end
              else find_two_ord f (S k) t
  end.

(* two distinct in-range matches when find_two_ord finds a pair — the exact ambiguity witnesses *)
Lemma find_two_ord_found {A} (f : A -> bool) :
  forall l k j0 j1, find_two_ord f k l = Some (j0, j1) ->
  k <= j0 /\ j0 < j1
  /\ (exists x0, nth_error l (j0 - k) = Some x0 /\ f x0 = true)
  /\ (exists x1, nth_error l (j1 - k) = Some x1 /\ f x1 = true).
Proof.
  induction l as [|x t IH]; intros k j0 j1 H; cbn in H; [ discriminate H |].
  destruct (f x) eqn:Hx.
  - destruct (find_ord f (S k) t) as [[j m]|] eqn:Ho; [| discriminate H ].
    injection H as <- <-.
    destruct (find_ord_found f t (S k) j m Ho) as [Hle [Hnth [Hf _]]].
    split; [ lia | split; [ lia |]].
    split.
    + exists x. rewrite Nat.sub_diag. split; [ reflexivity | exact Hx ].
    + exists m. replace (j - k) with (S (j - S k)) by lia. cbn.
      split; [ exact Hnth | exact Hf ].
  - destruct (IH (S k) j0 j1 H) as [Hle [Hlt [[x0 [Hn0 Hf0]] [x1 [Hn1 Hf1]]]]].
    split; [ lia | split; [ exact Hlt |]].
    split.
    + exists x0. replace (j0 - k) with (S (j0 - S k)) by lia. cbn. split; [ exact Hn0 | exact Hf0 ].
    + exists x1. replace (j1 - k) with (S (j1 - S k)) by lia. cbn. split; [ exact Hn1 | exact Hf1 ].
Qed.

(* the same-block occupancy test: a block-scoped member spelling this exact name; short origins included *)
Definition same_block_cand {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (n : Names.OrdinaryIdentifier) (e : Est s) : bool :=
  andb (is_block_scoped e) (Names.ordinary_equalb (est_name e) n).

(* the exact new establishment a ShortNew left creates: its origin ties the statement, index, and edge *)
Definition new_est {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.Refs.BlockRef idx) {st : Index.Refs.ShortStmtRef idx} {i : nat}
  (e : Index.Edges.ShortLhsEdge st i) (n : Names.OrdinaryIdentifier) : Est s :=
  mk_est (DOShort (mk_short_new st i e)) n (BlockScope br) (vis_start (Index.Edges.sl_child e)).

(* the canonical short-left decision as cheap descriptive data, retained in the event, authoritative only as a row *)
Inductive ShortLeftDecisionData : Type :=
| ShortBlankData
| ShortDuplicateData (earlier : nat)
| ShortNewData (n : Names.OrdinaryIdentifier)
| ShortExistingVariableData (member : nat)
| ShortExistingNonVariableData (member : nat)
| ShortAmbiguousData (first second : nat).

(* the one canonical decision per left, in fixed precedence: blank, earliest duplicate, ambiguous, existing, new *)
Definition short_left_decide {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) {st : Index.Refs.ShortStmtRef idx} {i : nat} (e : Index.Edges.ShortLhsEdge st i)
  : ShortLeftDecisionData :=
  match binder_ident (Index.Edges.sl_child e) with
  | None => ShortBlankData
  | Some n =>
      match find_dup i n (Index.Edges.short_lhs_edges st) with
      | Some (existT _ j _) => ShortDuplicateData j
      | None =>
          match find_two_ord (same_block_cand n) 0 env with
          | Some (j, k) => ShortAmbiguousData j k
          | None =>
              match find_ord (same_block_cand n) 0 env with
              | Some (j, m) => if is_variable_binder (est_node m)
                               then ShortExistingVariableData j else ShortExistingNonVariableData j
              | None => ShortNewData n
              end
          end
      end
  end.

(* one retained decision row per exact left, in source order *)
Definition short_decide_rows {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) (st : Index.Refs.ShortStmtRef idx) : list ShortLeftDecisionData :=
  map (fun x => match x with existT _ i e => short_left_decide env e end) (Index.Edges.short_lhs_edges st).

(* the one canonical per-edge addition body: a New row's establishment, or nothing *)
Definition short_add_at {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.Refs.BlockRef idx) {st : Index.Refs.ShortStmtRef idx} (rows : list ShortLeftDecisionData)
  (x : {i : nat & Index.Edges.ShortLhsEdge st i}) : list (Est s) :=
  match x with existT _ i e =>
    match nth_error rows i with Some (ShortNewData n) => [new_est br e n] | _ => [] end end.

(* event additions as the ordered projection of the retained New rows — the one and only source of short additions *)
Definition short_rows_adds {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.Refs.BlockRef idx) (st : Index.Refs.ShortStmtRef idx) (rows : list ShortLeftDecisionData) : list (Est s) :=
  flat_map (short_add_at br rows) (Index.Edges.short_lhs_edges st).
Lemma short_rows_adds_scope {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.Refs.BlockRef idx) (st : Index.Refs.ShortStmtRef idx) (rows : list ShortLeftDecisionData) (e : Est s) :
  In e (short_rows_adds br st rows) -> est_scope e = BlockScope br.
Proof.
  unfold short_rows_adds, short_add_at. intro Hin. apply in_flat_map in Hin. destruct Hin as [x [_ Hin]].
  destruct x as [i ed]. destruct (nth_error rows i) as [row|]; try (exact (match Hin with end)).
  destruct row; try (exact (match Hin with end)).
  destruct Hin as [<-|F]; [ reflexivity | destruct F ].
Qed.

(* a declaration establishment rebuilt from its binder node alone, equal to the spec-edge establishment *)
Definition node_binder_est {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (bd : Index.Core.NodeRef idx) : option (Est s) :=
  match binder_ident bd with
  | Some n =>
      match Bool.bool_dec (is_binder_role (Index.Core.node_role bd)) true with
      | left Hr => Some (mk_est (DOBinder (binder_ref bd Hr)) n sc (vis_start bd))
      | right _ => None
      end
  | None => None
  end.

(* the canonical decl-binder decision as cheap descriptive data, retained in the event, authoritative as a row *)
Inductive DeclBinderDecisionData : Type :=
| DeclBlankData
| DeclDuplicateEarlierData (earlier : nat)
| DeclFreshData
| DeclRedeclaredPriorData (member : nat)
| DeclAlreadyAmbiguousData (first second : nat).

(* one canonical decision per binder: blank, earliest same-event dup, already-ambiguous, unique prior, fresh *)
Definition decl_binder_decide {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) (t : Index.Core.NodeRef idx) (i : nat) (bd : Index.Core.NodeRef idx) : DeclBinderDecisionData :=
  match binder_ident bd with
  | None => DeclBlankData
  | Some n =>
      match find_ord (binder_name_matches n) 0 (firstn i (decl_binders t)) with
      | Some (j, _) => DeclDuplicateEarlierData j
      | None =>
          match find_two_ord (same_block_cand n) 0 env with
          | Some (j0, j1) => DeclAlreadyAmbiguousData j0 j1
          | None =>
              match find_ord (same_block_cand n) 0 env with
              | Some (j, _) => DeclRedeclaredPriorData j
              | None => DeclFreshData
              end
          end
      end
  end.

(* one retained decision row per exact binder, in source order *)
Definition decl_decide_rows {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) (t : Index.Core.NodeRef idx) : list DeclBinderDecisionData :=
  map (fun ib => decl_binder_decide env t (fst ib) (snd ib))
      (combine (seq 0 (length (decl_binders t))) (decl_binders t)).

(* the one canonical per-binder addition body: a nonblank binder's establishment, or nothing *)
Definition decl_add_at {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (rb : DeclBinderDecisionData * Index.Core.NodeRef idx) : list (Est s) :=
  match rb with
  | (DeclBlankData, _) => []
  | (_, bd) => match node_binder_est sc bd with Some e => [e] | None => [] end
  end.

(* decl additions as the ordered projection of the retained nonblank rows — the one source of decl additions *)
Definition decl_rows_adds {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (t : Index.Core.NodeRef idx) (rows : list DeclBinderDecisionData) : list (Est s) :=
  flat_map (decl_add_at sc) (combine rows (decl_binders t)).

Lemma node_binder_est_scope {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (bd : Index.Core.NodeRef idx) (e : Est s) :
  node_binder_est sc bd = Some e -> est_scope e = sc.
Proof.
  unfold node_binder_est. destruct (binder_ident bd) as [n|]; [| discriminate].
  destruct (Bool.bool_dec (is_binder_role (Index.Core.node_role bd)) true) as [Hr|_]; intro H;
    [ injection H as <-; reflexivity | discriminate H ].
Qed.

(* a spec's binder nodes are exactly its name-edge children, which carry a binder role *)
Lemma spec_binder_nodes_role {p} {idx : Index.Core.ProgramIndex p} {fl : Index.Model.SpecFlavor}
  (sp : Index.Refs.SpecRef idx fl) (bd : Index.Core.NodeRef idx) :
  In bd (spec_binder_nodes sp) -> is_binder_role (Index.Core.node_role bd) = true.
Proof.
  unfold spec_binder_nodes. intro Hin. apply in_map_iff in Hin. destruct Hin as [x [Heq _]].
  subst bd. rewrite (Index.Edges.sn_role (projT2 x)). reflexivity.
Qed.
Lemma spec_binders_view_role {p} {idx : Index.Core.ProgramIndex p}
  (r : Index.Core.NodeRef idx) (v : Index.Model.NodeView) (Hv : Index.Core.node_view r = v) (bd : Index.Core.NodeRef idx) :
  In bd (spec_binders_view r v Hv) -> is_binder_role (Index.Core.node_role bd) = true.
Proof.
  destruct v; cbn [spec_binders_view]; intro Hin;
    first [ apply spec_binder_nodes_role in Hin; exact Hin | cbn in Hin; contradiction ].
Qed.

(* every declaration binder node carries a binder role: they are exactly spec name-edge children *)
Lemma decl_binder_role {p} {idx : Index.Core.ProgramIndex p} (t bd : Index.Core.NodeRef idx) :
  In bd (decl_binders t) -> is_binder_role (Index.Core.node_role bd) = true.
Proof.
  unfold decl_binders. destruct (Index.Child.child_at_opt t 0) as [e|]; [| intro H; destruct H].
  unfold decl_binder_nodes. intro Hin. apply in_flat_map in Hin. destruct Hin as [x [_ Hin]].
  exact (spec_binders_view_role _ _ _ bd Hin).
Qed.

(* a nonblank declaration binder always yields an establishment: its role and name are both present *)
Definition decl_binder_est_some {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (t bd : Index.Core.NodeRef idx) (n : Names.OrdinaryIdentifier) :
  In bd (decl_binders t) -> binder_ident bd = Some n -> { e : Est s | node_binder_est sc bd = Some e }.
Proof.
  intros Hin Hid. unfold node_binder_est. rewrite Hid.
  destruct (Bool.bool_dec (is_binder_role (Index.Core.node_role bd)) true) as [Hr|Hr].
  - exists (mk_est (DOBinder (binder_ref bd Hr)) n sc (vis_start bd)). reflexivity.
  - exfalso. apply Hr. exact (decl_binder_role t bd Hin).
Defined.

Lemma decl_rows_adds_scope {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (t : Index.Core.NodeRef idx) (rows : list DeclBinderDecisionData) (e : Est s) :
  In e (decl_rows_adds sc t rows) -> est_scope e = sc.
Proof.
  unfold decl_rows_adds, decl_add_at. intro Hin. apply in_flat_map in Hin. destruct Hin as [rb [_ Hin]].
  assert (Hgen : forall bd, In e (match node_binder_est sc bd with Some e0 => [e0] | None => [] end)
                            -> est_scope e = sc).
  { intros bd H. destruct (node_binder_est sc bd) as [e0|] eqn:Hn; [| destruct H].
    destruct H as [<-|F]; [ exact (node_binder_est_scope sc bd e0 Hn) | destruct F ]. }
  destruct rb as [row bd]. destruct row;
    [ destruct Hin | exact (Hgen bd Hin) | exact (Hgen bd Hin) | exact (Hgen bd Hin) | exact (Hgen bd Hin) ].
Qed.

Lemma stmt_has_parent {p} {idx : Index.Core.ProgramIndex p} (st : Index.Refs.ShortStmtRef idx) :
  Index.Core.node_parent (Index.Refs.sh_node st) = None -> False.
Proof.
  intro Hp. pose proof (Index.Core.parentless_view_file (Index.Refs.sh_node st) Hp) as Hv.
  rewrite (Index.Refs.sh_ok st) in Hv. discriminate Hv.
Qed.

Lemma stmt_parent_block {p} {idx : Index.Core.ProgramIndex p} (st : Index.Refs.ShortStmtRef idx)
  (par : Index.Core.NodeRef idx) :
  Index.Core.node_parent (Index.Refs.sh_node st) = Some par -> Index.Core.node_view par = Index.Model.VBlock.
Proof.
  intro Hp.
  destruct (Index.Edges.all_children_of_parent (Index.Refs.sh_node st) par Hp) as [k [e [Hrow Hc]]].
  apply (Index.Child.child_at_stmt_block e (Index.Model.SSShort (Index.Refs.sh_names st) (Index.Refs.sh_values st))).
  rewrite Hc. exact (Index.Refs.sh_ok st).
Qed.

Lemma stmt_parent_not_block {p} {idx : Index.Core.ProgramIndex p} (st : Index.Refs.ShortStmtRef idx)
  (par : Index.Core.NodeRef idx) :
  Index.Core.node_parent (Index.Refs.sh_node st) = Some par ->
  Index.Core.is_block_view (Index.Core.node_view par) = false -> False.
Proof. intros Hp Hb. rewrite (stmt_parent_block st par Hp) in Hb. discriminate Hb. Qed.


(* one retained block event: expr statement, judged declaration, or judged short — no raw predecessor env stored *)
Inductive BlockEv {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
| BEvExpr : Index.Core.NodeRef idx -> BlockEv s
| BEvDecl : forall (sc : ScopeId s) (t : Index.Core.NodeRef idx), list DeclBinderDecisionData -> BlockEv s
| BEvShort : forall (st : Index.Refs.ShortStmtRef idx), list ShortLeftDecisionData -> BlockEv s.
Arguments BEvExpr {p idx s} _.
Arguments BEvDecl {p idx s} _ _ _.
Arguments BEvShort {p idx s} _ _.

Definition bev_node {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (ev : BlockEv s) : Index.Core.NodeRef idx :=
  match ev with
  | BEvExpr r => r
  | BEvDecl _ t _ => t
  | BEvShort st _ => Index.Refs.sh_node st
  end.

(* the exact ordered additions of one event; a short's News need its exact block for their scope *)
Definition bev_adds {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.Refs.BlockRef idx) (ev : BlockEv s) : list (Est s) :=
  match ev with
  | BEvExpr _ => []
  | BEvDecl sc t rows => decl_rows_adds sc t rows
  | BEvShort st rows => short_rows_adds br st rows
  end.

(* one package event: the exact top occurrence and its exact ordered additions *)
Definition PkgEv {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
  (Index.Core.NodeRef idx * list (Est s))%type.

(* one block trace row: the exact block, its package position, and its events in statement order *)
Definition TraceRow {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
  (Index.Refs.BlockRef idx * nat * list (BlockEv s))%type.
Definition trow_block {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (t : TraceRow s) : Index.Refs.BlockRef idx := fst (fst t).
Definition trow_pkg {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (t : TraceRow s) : nat := snd (fst t).
Definition trow_evs {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (t : TraceRow s) : list (BlockEv s) := snd t.

(* the retained phase graph: the package ledgers, the block traces, and the const judgment table *)
Definition PhaseData {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
  (list (list (PkgEv s)) * list (TraceRow s)
   * list { cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF & ConstJudgment cs })%type.

(* the one canonical builder; Internal is plumbing under the phase pin, never a client authority *)
Section Build.
Context {p : Syntax.Program} {idx : Index.Core.ProgramIndex p}.
Variable s : PI.PackageSurface idx.

Definition pkg_event_at (pr : PI.PackageRef s) (r : Index.Core.NodeRef idx) : option (PkgEv s) :=
  match Index.Core.node_view r with
  | Index.Model.VTop Index.Model.TSMain =>
      match make_main_est pr r with Some e0 => Some (r, [e0]) | None => None end
  | Index.Model.VTop Index.Model.TSTopDecl => Some (r, stmt_decl_ests (PackageScope pr) r)
  | _ => None
  end.

Definition ledger_of (pr : PI.PackageRef s) : list (PkgEv s) :=
  flat_map (fun fr =>
    flat_map (fun pos => match Index.Core.mk_noderef fr (Pos.of_succ_nat pos) with
                         | Some r => match pkg_event_at pr r with Some ev => [ev] | None => [] end
                         | None => [] end)
             (seq 0 (Index.Core.occ_count fr)))
    (PI.pkg_members pr).

Definition pkg_env_of (pr : PI.PackageRef s) : list (Est s) :=
  flat_map snd (ledger_of pr).

Definition block_event (br : Index.Refs.BlockRef idx) (env : list (Est s)) (c : Index.Core.NodeRef idx)
  (v : Index.Model.NodeView) (Hv : Index.Core.node_view c = v) : BlockEv s :=
  match v as v0 return Index.Core.node_view c = v0 -> BlockEv s with
  | Index.Model.VStmt Index.Model.SSDecl => fun _ =>
      BEvDecl (BlockScope br) c (decl_decide_rows env c)
  | Index.Model.VStmt (Index.Model.SSShort nn nv) => fun Hv0 =>
      BEvShort (Index.Refs.mkShortStmtRef c nn nv Hv0)
        (short_decide_rows env (Index.Refs.mkShortStmtRef c nn nv Hv0))
  | _ => fun _ => BEvExpr c
  end Hv.

Fixpoint block_fold (br : Index.Refs.BlockRef idx)
  (l : list { o : nat & Index.Child.ChildAt (Index.Refs.bl_node br) o }) (env : list (Est s)) {struct l}
  : list (BlockEv s) :=
  match l with
  | [] => []
  | x :: t =>
      let ev := block_event br env (Index.Child.ca_child (projT2 x))
                  (Index.Core.node_view (Index.Child.ca_child (projT2 x))) eq_refl in
      ev :: block_fold br t (env ++ bev_adds br ev)
  end.

Definition traces_of_pkg (pr : PI.PackageRef s) : list (TraceRow s) :=
  let pe := pkg_env_of pr in
  flat_map (fun fr =>
    flat_map (fun pos =>
      match Index.Core.mk_noderef fr (Pos.of_succ_nat pos) with
      | Some r =>
          (match Index.Core.is_block_view (Index.Core.node_view r) as bv
                 return Index.Core.is_block_view (Index.Core.node_view r) = bv -> list (TraceRow s) with
           | true => fun Hb =>
               [ (Index.Refs.mkBlockRef r Hb, PI.pr_pos pr,
                  block_fold (Index.Refs.mkBlockRef r Hb)
                    (Index.Child.all_children (Index.Refs.bl_node (Index.Refs.mkBlockRef r Hb))) pe) ]
           | false => fun _ => []
           end) eq_refl
      | None => [] end)
      (seq 0 (Index.Core.occ_count fr)))
    (PI.pkg_members pr).

Definition phase_data : PhaseData s :=
  (map ledger_of (PI.packages s),
   flat_map traces_of_pkg (PI.packages s),
   const_table s).

End Build.

(* PhaseData is transparent, inspectable, carries no authority; the sealed certificate below is the sole authority *)
Module Type PHASE_CERT.
  Parameter Certified : forall {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx),
    PhaseData s -> Prop.
  Parameter canonical : forall {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx),
    Certified s (phase_data s).
  Parameter certified_canonical : forall {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx)
    (d : PhaseData s), Certified s d -> d = phase_data s.
End PHASE_CERT.
Module PhaseCert : PHASE_CERT.
  Definition Certified {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx)
    (d : PhaseData s) : Prop := d = phase_data s.
  Definition canonical {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx)
    : Certified s (phase_data s) := eq_refl.
  Definition certified_canonical {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx)
    (d : PhaseData s) (c : Certified s d) : d = phase_data s := c.
End PhaseCert.

(* the phase authority: an abstract certificate that exact data d is the canonical phase; unforgeable *)
Definition BindingPhase {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx)
  (d : PhaseData s) : Prop := PhaseCert.Certified s d.
Definition bindings {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx)
  : BindingPhase s (phase_data s) := PhaseCert.canonical s.
(* the certificate's data is the canonical computation — the authority-to-canonicity bridge the laws consume *)
Definition bp_canonical {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : d = phase_data s := PhaseCert.certified_canonical s d bp.

Definition bp_ledgers {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : list (list (PkgEv s)) := fst (fst d).
Definition bp_traces {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : list (TraceRow s) := snd (fst d).
Definition bp_consts {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : list { cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF & ConstJudgment cs } :=
  snd d.
Lemma in_seq_intro : forall i n, i < n -> In i (seq 0 n).
Proof. intros i n H. apply in_seq. lia. Qed.


Definition dec_of_eqb {A} (eqb : A -> A -> bool) (spec : forall a b, eqb a b = true <-> a = b)
  (a b : A) : {a = b} + {a <> b} :=
  match Bool.bool_dec (eqb a b) true with
  | left H => left (proj1 (spec a b) H)
  | right H => right (fun E => H (proj2 (spec a b) E))
  end.

Lemma literal_eq_dec : forall a b : Syntax.Literal, {a = b} + {a <> b}.
Proof.
  decide equality.
  - apply N.eq_dec.
  - apply (dec_of_eqb Float.nnd_equalb Float.nnd_equalb_spec).
  - apply string_dec.
Qed.

Lemma nodeview_eq_dec : forall a b : Index.Model.NodeView, {a = b} + {a <> b}.
Proof.
  decide equality.
  - apply (dec_of_eqb Names.ordinary_equalb Names.ordinary_equalb_spec).
  - apply literal_eq_dec.
  - decide equality.
  - decide equality. apply (dec_of_eqb Names.ordinary_equalb Names.ordinary_equalb_spec).
  - decide equality. apply (dec_of_eqb Names.ordinary_equalb Names.ordinary_equalb_spec).
  - decide equality; first [ apply Nat.eq_dec | apply Bool.bool_dec ].
  - decide equality; first [ apply Nat.eq_dec | apply Bool.bool_dec ].
  - decide equality.
  - decide equality.
  - decide equality; apply Nat.eq_dec.
  - decide equality.
Qed.

(* a spec ref is identified by its node: the shape and the view proof are forced *)
Lemma specref_positional {p} {idx : Index.Core.ProgramIndex p} {fl : Index.Model.SpecFlavor}
  (a b : Index.Refs.SpecRef idx fl) : Index.Refs.sp_node a = Index.Refs.sp_node b -> a = b.
Proof.
  destruct a as [na sha Ha], b as [nb shb Hb]; cbn; intro E; subst nb.
  assert (Hv : Index.Refs.spec_view_of fl sha = Index.Refs.spec_view_of fl shb)
    by (rewrite <- Ha, <- Hb; reflexivity).
  assert (Hsh : sha = shb) by (destruct fl; cbn in Hv; injection Hv as Hv; exact Hv).
  subst shb. f_equal. apply (UIP_dec nodeview_eq_dec).
Qed.

(* a short-statement ref is identified by its node: the counts and the view proof are forced *)
Lemma shortstmtref_positional {p} {idx : Index.Core.ProgramIndex p}
  (a b : Index.Refs.ShortStmtRef idx) : Index.Refs.sh_node a = Index.Refs.sh_node b -> a = b.
Proof.
  destruct a as [na nna nva Ha], b as [nb nnb nvb Hb]; cbn; intro E; subst nb.
  assert (Hv : Index.Model.VStmt (Index.Model.SSShort nna nva) = Index.Model.VStmt (Index.Model.SSShort nnb nvb))
    by (rewrite <- Ha, <- Hb; reflexivity).
  injection Hv as Hnn Hnv. subst nnb nvb.
  f_equal. apply (UIP_dec nodeview_eq_dec).
Qed.

(* every node's position is in range on its own file *)
Lemma nr_pos_lt {p} {idx : Index.Core.ProgramIndex p} (r : Index.Core.NodeRef idx) :
  Index.Core.nr_pos r < Index.Core.occ_count (Index.Core.nr_file r).
Proof.
  destruct (Index.Core.occ_in_number_file r) as [f [Hin Hcount]].
  destruct (Index.BuildLaws.number_file_positions f) as [n Hpos].
  assert (Hinp : In (Index.Core.nr_pos r) (map fst (Index.Build.number_file f)))
    by (apply in_map_iff; exists (Index.Core.nr_pos r, Index.Core.occ_at r); split; [ reflexivity | exact Hin ]).
  rewrite Hpos in Hinp. apply in_seq in Hinp.
  assert (Hlen : length (Index.Build.number_file f) = n).
  { apply (f_equal (@length nat)) in Hpos.
    rewrite length_map, length_seq in Hpos. exact Hpos. }
  lia.
Qed.

(* the subjects enumeration covers every const spec: some entry shares its exact node *)
Lemma const_subjects_cover {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx)
  (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF) :
  exists cs', In cs' (const_subjects s) /\ Index.Refs.sp_node cs' = Index.Refs.sp_node cs.
Proof.
  set (r := Index.Refs.sp_node cs).
  assert (Hfile : In (Index.Core.nr_file r) (PI.pkg_members (PI.package_of_file s (Index.Core.nr_file r))))
    by apply PI.pkg_members_of_file.
  assert (Hentry : exists cs', In cs' (const_specs_of_file (Index.Core.nr_file r))
                               /\ Index.Refs.sp_node cs' = r).
  { unfold const_specs_of_file.
    assert (Hmk : Index.Core.mk_noderef (Index.Core.nr_file r) (Pos.of_succ_nat (Index.Core.nr_pos r)) = Some r)
      by (rewrite <- Index.Core.nr_key_pos; apply Index.Core.mk_noderef_self).
    assert (Hin : exists cs', In cs' (const_ref_emit r (Index.Core.node_view r) eq_refl)
                  /\ Index.Refs.sp_node cs' = r).
    { exact (const_ref_emit_cover r (Index.Core.node_view r) eq_refl (Index.Refs.sp_shape cs) (Index.Refs.sp_ok cs)). }
    destruct Hin as [cs' [Hin' Hnode']].
    exists cs'. split; [| exact Hnode' ].
    apply in_flat_map. exists (Index.Core.nr_pos r). split.
    - apply in_seq. pose proof (nr_pos_lt r). lia.
    - rewrite Hmk. exact Hin'. }
  destruct Hentry as [cs' [Hin' Hnode']].
  exists cs'. split; [| exact Hnode' ].
  unfold const_subjects. apply in_flat_map.
  exists (PI.package_of_file s (Index.Core.nr_file r)). split; [ apply PI.packages_complete |].
  apply in_flat_map. exists (Index.Core.nr_file r). split; [ exact Hfile | exact Hin' ].
Qed.

Record ConstSpecJudgmentRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF) : Type := mk_cjr {
  cjr_ord : nat ;
  cjr_row : { c : Index.Refs.SpecRef idx Index.Model.ConstSpecF & ConstJudgment c } ;
  cjr_at  : nth_error (bp_consts bp) cjr_ord = Some cjr_row ;
  cjr_subject : projT1 cjr_row = cs
}.
Arguments mk_cjr {p idx s d bp cs} _ _ _ _.
Arguments cjr_ord {p idx s d bp cs} _.
Arguments cjr_row {p idx s d bp cs} _.
Arguments cjr_at {p idx s d bp cs} _.
Arguments cjr_subject {p idx s d bp cs} _.

Lemma specref_of_nodes {p} {idx : Index.Core.ProgramIndex p} {fl : Index.Model.SpecFlavor}
  (a b : Index.Refs.SpecRef idx fl) : noderef_eqb (Index.Refs.sp_node a) (Index.Refs.sp_node b) = true -> a = b.
Proof. intro H. apply specref_positional. apply noderef_eqb_spec. exact H. Qed.

Fixpoint cjr_scan {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF) (k : nat)
  (l : list { c : Index.Refs.SpecRef idx Index.Model.ConstSpecF & ConstJudgment c }) {struct l}
  : l = skipn k (bp_consts bp) -> option (ConstSpecJudgmentRef bp cs) :=
  match l with
  | [] => fun _ => None
  | row :: rest => fun E =>
      match Bool.bool_dec (noderef_eqb (Index.Refs.sp_node (projT1 row)) (Index.Refs.sp_node cs)) true with
      | left Hb => Some (mk_cjr k row (Index.Child.skipn_head_at (bp_consts bp) rest k row E)
                                (specref_of_nodes (projT1 row) cs Hb))
      | right _ => cjr_scan bp cs (S k) rest (Index.Child.skipn_tail_at (bp_consts bp) rest k row E)
      end
  end.

Lemma cjr_scan_finds {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF) :
  forall l k (E : l = skipn k (bp_consts bp)),
  (exists row, In row l /\ Index.Refs.sp_node (projT1 row) = Index.Refs.sp_node cs) ->
  cjr_scan bp cs k l E <> None.
Proof.
  induction l as [|row rest IH]; intros k E [row0 [Hin Hnode]]; [ destruct Hin |].
  cbn. destruct (Bool.bool_dec (noderef_eqb (Index.Refs.sp_node (projT1 row)) (Index.Refs.sp_node cs)) true)
    as [|Hne]; [ discriminate |].
  destruct Hin as [Hhead|Hin].
  - exfalso. apply Hne. subst row0. apply noderef_eqb_spec. exact Hnode.
  - apply (IH (S k) (Index.Child.skipn_tail_at (bp_consts bp) rest k row E)).
    exists row0. split; [ exact Hin | exact Hnode ].
Qed.

(* the retained const table's subjects are exactly the canonical enumeration *)
Lemma bp_consts_subjects {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) :
  map (fun row => projT1 row) (bp_consts bp) = const_subjects s.
Proof.
  unfold bp_consts. rewrite (bp_canonical bp). cbn [phase_data snd].
  unfold const_table. rewrite map_map.
  etransitivity; [ apply map_ext; intro cs; reflexivity | apply map_id ].
Qed.

Lemma bp_consts_cover {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF) :
  exists row, In row (bp_consts bp) /\ Index.Refs.sp_node (projT1 row) = Index.Refs.sp_node cs.
Proof.
  destruct (const_subjects_cover s cs) as [cs' [Hin Hnode]].
  assert (Hin' : In cs' (map (fun row => projT1 row) (bp_consts bp)))
    by (rewrite bp_consts_subjects; exact Hin).
  apply in_map_iff in Hin'. destruct Hin' as [row [Hproj Hrow]].
  exists row. split; [ exact Hrow | rewrite Hproj; exact Hnode ].
Qed.

(* the sole ordinary const-judgment lookup: total, returning the exact retained phase row *)
Definition const_spec_judgment {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF) : ConstSpecJudgmentRef bp cs :=
  (match cjr_scan bp cs 0 (bp_consts bp) eq_refl as o
         return cjr_scan bp cs 0 (bp_consts bp) eq_refl = o -> ConstSpecJudgmentRef bp cs with
   | Some r => fun _ => r
   | None => fun E =>
       False_rect _ (cjr_scan_finds bp cs (bp_consts bp) 0 eq_refl (bp_consts_cover bp cs) E)
   end) eq_refl.


(* the exact retained event count at one ledger or trace ordinal; absent ordinals hold no events *)
Definition pkg_event_count {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pix : nat) : nat :=
  match nth_error (bp_ledgers bp) pix with Some l => length l | None => 0 end.
Definition trace_event_count {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix : nat) : nat :=
  match nth_error (bp_traces bp) tix with Some tr => length (trow_evs tr) | None => 0 end.

(* the exact retained package event at a valid ordinal: total, no option — the bound forces the ledger present *)
Definition pkg_row {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pix eix : nat) (H : eix < pkg_event_count bp pix) : PkgEv s :=
  (match nth_error (bp_ledgers bp) pix as o
         return eix < (match o with Some l => length l | None => 0 end) -> PkgEv s with
   | Some l => fun H' => Index.Model.nth_lt l eix H'
   | None => fun H' => False_rect _ (Nat.nlt_0_r eix H')
   end) H.
Definition trace_row_at {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix : nat) (H : nth_error (bp_traces bp) tix <> None) : TraceRow s :=
  (match nth_error (bp_traces bp) tix as o return o <> None -> TraceRow s with
   | Some tr => fun _ => tr
   | None => fun H' => False_rect _ (H' eq_refl)
   end) H.
Definition blk_ev_row {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix eix : nat) (H : eix < trace_event_count bp tix) : BlockEv s :=
  (match nth_error (bp_traces bp) tix as o
         return eix < (match o with Some tr => length (trow_evs tr) | None => 0 end) -> BlockEv s with
   | Some tr => fun H' => Index.Model.nth_lt (trow_evs tr) eix H'
   | None => fun H' => False_rect _ (Nat.nlt_0_r eix H')
   end) H.
Definition blk_ev_block {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix eix : nat) (H : eix < trace_event_count bp tix) : Index.Refs.BlockRef idx :=
  (match nth_error (bp_traces bp) tix as o
         return eix < (match o with Some tr => length (trow_evs tr) | None => 0 end) -> Index.Refs.BlockRef idx with
   | Some tr => fun _ => trow_block tr
   | None => fun H' => False_rect _ (Nat.nlt_0_r eix H')
   end) H.

(* one exact VALID event site: ledger/trace + in-range ordinal; invalid coordinates unrepresentable, lookups total *)
Inductive EvSite {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : Type :=
| PkgEventAt : forall (pix eix : nat), eix < pkg_event_count bp pix -> EvSite bp
| BlockEventAt : forall (tix eix : nat), eix < trace_event_count bp tix -> EvSite bp.
Arguments PkgEventAt {p idx s d bp} _ _ _.
Arguments BlockEventAt {p idx s d bp} _ _ _.

(* the exact retained additions of the event at a valid site — total *)
Definition event_adds {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) : list (Est s) :=
  match site with
  | PkgEventAt pix eix H => snd (pkg_row bp pix eix H)
  | BlockEventAt tix eix H => bev_adds (blk_ev_block bp tix eix H) (blk_ev_row bp tix eix H)
  end.

(* one exact in-range addition of an event, pinned to its retained payload; its site and index are TYPE indices *)
Record EventAdditionRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (site : EvSite bp) (ix : nat) : Type := mk_event_addition {
  ea_est : Est s ;
  ea_at  : nth_error (event_adds site) ix = Some ea_est
}.
Arguments mk_event_addition {p idx s d bp site ix} _ _.
Arguments ea_est {p idx s d bp site ix} _.
Arguments ea_at {p idx s d bp site ix} _.

(* the exact phase-owned establishment identity: its creating event and its exact in-range addition there *)
Record EstablishmentRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : Type := mk_establishment {
  es_site : EvSite bp ;
  es_ix   : nat ;
  es_add  : EventAdditionRef bp es_site es_ix
}.
Arguments mk_establishment {p idx s d bp} _ _ _.
Arguments es_site {p idx s d bp} _.
Arguments es_ix {p idx s d bp} _.
Arguments es_add {p idx s d bp} _.

Definition es_est {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (er : EstablishmentRef bp) : Est s :=
  ea_est (es_add er).

(* a total in-range witness from a successful positional lookup *)
Lemma nth_error_lt {A} (l : list A) (k : nat) (e : A) : nth_error l k = Some e -> k < length l.
Proof. intro H. apply nth_error_Some. rewrite H. discriminate. Qed.

(* the addition of an establishment sits at an intrinsically in-range index of its event *)
Definition es_lt {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (er : EstablishmentRef bp)
  : es_ix er < length (event_adds (es_site er)) :=
  nth_error_lt (event_adds (es_site er)) (es_ix er) (es_est er) (ea_at (es_add er)).

(* the exact establishment refs of one event: one per retained addition, positionally enumerated, no invalid index *)
Fixpoint refs_scan {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) (k : nat) (l : list (Est s)) {struct l}
  : l = skipn k (event_adds site) -> list (EstablishmentRef bp) :=
  match l with
  | [] => fun _ => []
  | e0 :: rest => fun E =>
      mk_establishment site k
        (mk_event_addition e0 (Index.Child.skipn_head_at (event_adds site) rest k e0 E))
      :: refs_scan site (S k) rest (Index.Child.skipn_tail_at (event_adds site) rest k e0 E)
  end.
Definition refs_of_event {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) : list (EstablishmentRef bp) :=
  refs_scan site 0 (event_adds site) (eq_sym (skipn_O _)).

(* the establishment refs of the package event at one ordinal — the event's additions when in range, else none *)
Definition pkg_ev_refs {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pix eix : nat) : list (EstablishmentRef bp) :=
  match lt_dec eix (pkg_event_count bp pix) with
  | left H => refs_of_event (PkgEventAt pix eix H)
  | right _ => []
  end.
Definition block_ev_refs {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix eix : nat) : list (EstablishmentRef bp) :=
  match lt_dec eix (trace_event_count bp tix) with
  | left H => refs_of_event (BlockEventAt tix eix H)
  | right _ => []
  end.

(* every ledger's / trace's events in order; every actual establishment of the phase *)
Definition ledger_refs {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pix : nat) : list (EstablishmentRef bp) :=
  flat_map (pkg_ev_refs bp pix) (seq 0 (pkg_event_count bp pix)).
Definition trace_refs {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix : nat) : list (EstablishmentRef bp) :=
  flat_map (block_ev_refs bp tix) (seq 0 (trace_event_count bp tix)).
Definition all_establishment_refs {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : list (EstablishmentRef bp) :=
  flat_map (ledger_refs bp) (seq 0 (length (bp_ledgers bp)))
  ++ flat_map (trace_refs bp) (seq 0 (length (bp_traces bp))).

(* the exact final package environment: the package's own event additions, as retained refs *)
Definition package_env_refs {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pr : PI.PackageRef s) : list (EstablishmentRef bp) :=
  ledger_refs bp (PI.pr_pos pr).

(* the exact members at one causal cut: the package seed then the additions of strictly-earlier block events *)
Definition state_refs {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix : nat) (cut : nat) : list (EstablishmentRef bp) :=
  match nth_error (bp_traces bp) tix with
  | Some tr =>
      ledger_refs bp (trow_pkg tr)
      ++ flat_map (block_ev_refs bp tix) (seq 0 cut)
  | None => []
  end.

(* the exact package ledger reference *)
Record PackageLedgerRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pr : PI.PackageRef s) : Type := mk_package_ledger {
  plr_evs : list (PkgEv s) ;
  plr_at  : nth_error (bp_ledgers bp) (PI.pr_pos pr) = Some plr_evs
}.
Arguments mk_package_ledger {p idx s d bp pr} _ _.
Arguments plr_evs {p idx s d bp pr} _.
Arguments plr_at {p idx s d bp pr} _.

Record PackageEventRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {pr : PI.PackageRef s} (l : PackageLedgerRef bp pr)
  (i : nat) : Type := mk_package_event {
  per_lt  : i < length (plr_evs l)
}.
Arguments mk_package_event {p idx s d bp pr l i} _.
Arguments per_lt {p idx s d bp pr l i} _.

Record PackageMemberRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (pr : PI.PackageRef s) : Type := mk_package_member {
  pm_ord : nat ;
  pm_ref : EstablishmentRef bp ;
  pm_at  : nth_error (package_env_refs bp pr) pm_ord = Some pm_ref
}.
Arguments mk_package_member {p idx s d bp pr} _ _ _.
Arguments pm_ord {p idx s d bp pr} _.
Arguments pm_ref {p idx s d bp pr} _.
Arguments pm_at {p idx s d bp pr} _.

(* the exact block trace reference *)
Record BlockTraceRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (b : Index.Core.NodeRef idx) : Type := mk_block_trace {
  btr_ord : nat ;
  btr_row : TraceRow s ;
  btr_at  : nth_error (bp_traces bp) btr_ord = Some btr_row ;
  btr_subject : Index.Refs.bl_node (trow_block btr_row) = b
}.
Arguments mk_block_trace {p idx s d bp b} _ _ _ _.
Arguments btr_ord {p idx s d bp b} _.
Arguments btr_row {p idx s d bp b} _.
Arguments btr_at {p idx s d bp b} _.
Arguments btr_subject {p idx s d bp b} _.

(* the exact finite causal cut: an ordinal at most the event count; an n-event trace has exactly cuts 0..n *)
Record BlockCutRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} (tr : BlockTraceRef bp b) : Type
  := mk_block_cut {
  bc_ord : nat ;
  bc_le  : bc_ord <= length (trow_evs (btr_row tr))
}.
Arguments mk_block_cut {p idx s d bp b tr} _ _.
Arguments bc_ord {p idx s d bp b tr} _.
Arguments bc_le {p idx s d bp b tr} _.

(* the exact causal state at one finite cut: its identity is the phase, trace, and cut, never its contents *)
Record BlockStateRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  (c : BlockCutRef tr) : Type := mk_block_state {
  bs_members : list (EstablishmentRef bp) ;
  bs_ok : bs_members = state_refs bp (btr_ord tr) (bc_ord c)
}.
Arguments mk_block_state {p idx s d bp b tr c} _ _.
Arguments bs_members {p idx s d bp b tr c} _.
Arguments bs_ok {p idx s d bp b tr c} _.

Definition block_state {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  (c : BlockCutRef tr) : BlockStateRef c := mk_block_state (state_refs bp (btr_ord tr) (bc_ord c)) eq_refl.

Record BlockMemberRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (st : BlockStateRef c) : Type := mk_block_member {
  bm_ord : nat ;
  bm_ref : EstablishmentRef bp ;
  bm_at  : nth_error (bs_members st) bm_ord = Some bm_ref
}.
Arguments mk_block_member {p idx s d bp b tr c st} _ _ _.
Arguments bm_ord {p idx s d bp b tr c st} _.
Arguments bm_ref {p idx s d bp b tr c st} _.
Arguments bm_at {p idx s d bp b tr c st} _.

(* the exact block event reference at an intrinsically in-range ordinal, with its exact causal pre/post cuts *)
Record BlockEventRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} (tr : BlockTraceRef bp b) : Type
  := mk_block_event {
  ber_ix : nat ;
  ber_lt : ber_ix < length (trow_evs (btr_row tr))
}.
Arguments mk_block_event {p idx s d bp b tr} _ _.
Arguments ber_ix {p idx s d bp b tr} _.
Arguments ber_lt {p idx s d bp b tr} _.

Definition ber_row {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  (e : BlockEventRef tr) : BlockEv s := Index.Model.nth_lt (trow_evs (btr_row tr)) (ber_ix e) (ber_lt e).

(* the exact predecessor cut (the event's ordinal) and successor cut (its ordinal + 1), both in range *)
Definition ber_pre {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  (e : BlockEventRef tr) : BlockCutRef tr := mk_block_cut (ber_ix e) (Nat.lt_le_incl _ _ (ber_lt e)).
Definition ber_post {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  (e : BlockEventRef tr) : BlockCutRef tr := mk_block_cut (S (ber_ix e)) (ber_lt e).

(* the canonical occupancy group: one identity per exact phase, scope, and spelling *)
Definition scope_name_matches {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (sc : ScopeId s) (n : Names.OrdinaryIdentifier)
  (er : EstablishmentRef bp) : bool :=
  andb (scope_eqb (est_scope (es_est er)) sc) (Names.ordinary_equalb (est_name (es_est er)) n).

Definition group_refs {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (sc : ScopeId s) (n : Names.OrdinaryIdentifier)
  : list (EstablishmentRef bp) :=
  filter (scope_name_matches sc n) (all_establishment_refs bp).

Record BindingGroupRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (sc : ScopeId s) (n : Names.OrdinaryIdentifier) : Type
  := mk_binding_group {
  bg_members : list (EstablishmentRef bp) ;
  bg_ok : bg_members = group_refs bp sc n
}.
Arguments mk_binding_group {p idx s d bp sc n} _ _.
Arguments bg_members {p idx s d bp sc n} _.
Arguments bg_ok {p idx s d bp sc n} _.

Definition binding_group {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (sc : ScopeId s) (n : Names.OrdinaryIdentifier)
  : BindingGroupRef bp sc n := mk_binding_group (group_refs bp sc n) eq_refl.

(* the exact redeclaration root: the canonical group with its exact first two conflicting members *)
Record RedeclarationRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (sc : ScopeId s) (n : Names.OrdinaryIdentifier) : Type
  := mk_redeclaration {
  rr_group : BindingGroupRef bp sc n ;
  rr_two   : 2 <= length (bg_members rr_group)
}.
Arguments mk_redeclaration {p idx s d bp sc n} _ _.
Arguments rr_group {p idx s d bp sc n} _.
Arguments rr_two {p idx s d bp sc n} _.

(* the first-conflict event: the exact creating event of the group's second member *)
Definition rr_conflict_site {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {sc : ScopeId s} {n : Names.OrdinaryIdentifier}
  (rr : RedeclarationRef bp sc n) : option (EvSite bp) :=
  match bg_members (rr_group rr) with
  | _ :: m2 :: _ => Some (es_site m2)
  | _ => None
  end.

(* the visible occupancy group at one exact causal state *)
Record GroupAtStateRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  (c : BlockCutRef tr) (n : Names.OrdinaryIdentifier) : Type := mk_group_at_state {
  gs_members : list (EstablishmentRef bp) ;
  gs_ok : gs_members
          = filter (fun er => andb (is_block_scoped (es_est er))
                                   (Names.ordinary_equalb (est_name (es_est er)) n))
                   (state_refs bp (btr_ord tr) (bc_ord c))
}.
Arguments mk_group_at_state {p idx s d bp b tr c n} _ _.
Arguments gs_members {p idx s d bp b tr c n} _.
Arguments gs_ok {p idx s d bp b tr c n} _.

Definition group_at_state {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  (c : BlockCutRef tr) (n : Names.OrdinaryIdentifier) : GroupAtStateRef c n := mk_group_at_state _ eq_refl.
Lemma binder_ident_view {p} {idx : Index.Core.ProgramIndex p} (b : Index.Core.NodeRef idx)
  (n : Names.OrdinaryIdentifier) :
  binder_ident b = Some n -> Index.Core.node_view b = Index.Model.VBindingName (Syntax.BNamed n).
Proof.
  unfold binder_ident. destruct (Index.Core.node_view b) as [| | | | |bn| | | | | | | |]; try discriminate.
  destruct bn; [| discriminate ]. intro H. injection H as <-. reflexivity.
Qed.

Lemma make_main_est_none {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (b : Index.Core.NodeRef idx) :
  Index.Core.is_main_view (Index.Core.node_view b) = false -> make_main_est pr b = None.
Proof.
  intro Hf. unfold make_main_est.
  generalize (@eq_refl bool (Index.Core.is_main_view (Index.Core.node_view b))).
  destruct (Index.Core.is_main_view (Index.Core.node_view b)) at 2 3; intro e;
    [ exfalso; pose proof (eq_trans (eq_sym e) Hf) as Ht; discriminate Ht | reflexivity ].
Qed.

Lemma find_dup_sound {p} {idx : Index.Core.ProgramIndex p} {st : Index.Refs.ShortStmtRef idx}
  (i : nat) (n : Names.OrdinaryIdentifier) :
  forall (l : list { j0 : nat & Index.Edges.ShortLhsEdge st j0 }) (j : nat)
         (w : (Index.Edges.ShortLhsEdge st j * (j < i))%type),
  find_dup i n l = Some (existT _ j w) ->
  In (existT _ j (fst w)) l
  /\ match binder_ident (Index.Edges.sl_child (fst w)) with
     | Some m => Names.ordinary_equalb m n | None => false end = true.
Proof.
  induction l as [|[k ek] rest IH]; intros j w Hf; [ discriminate Hf |].
  cbn in Hf. destruct (lt_dec k i) as [Hk|Hk].
  - destruct (match binder_ident (Index.Edges.sl_child ek) with
              | Some m => Names.ordinary_equalb m n | None => false end) eqn:Ht.
    + injection Hf as He H2. subst j.
      apply Eqdep_dec.inj_pair2_eq_dec in H2; [| exact Nat.eq_dec ]. subst w.
      split; [ left; reflexivity | exact Ht ].
    + destruct (IH j w Hf) as [Hin Hm]. split; [ right; exact Hin | exact Hm ].
  - destruct (IH j w Hf) as [Hin Hm]. split; [ right; exact Hin | exact Hm ].
Qed.

Lemma find_dup_earliest {p} {idx : Index.Core.ProgramIndex p} {st : Index.Refs.ShortStmtRef idx}
  (i : nat) (n : Names.OrdinaryIdentifier) :
  forall (l : list { j0 : nat & Index.Edges.ShortLhsEdge st j0 }) (a m : nat),
  map (@projT1 _ _) l = seq a m ->
  forall (j : nat) (w : (Index.Edges.ShortLhsEdge st j * (j < i))%type),
  find_dup i n l = Some (existT _ j w) ->
  forall (k : nat) (ek : Index.Edges.ShortLhsEdge st k),
  In (existT _ k ek) l -> k < j -> k < i ->
  match binder_ident (Index.Edges.sl_child ek) with
  | Some m0 => Names.ordinary_equalb m0 n | None => false end = false.
Proof.
  induction l as [|[k0 e0] rest IH]; intros a m Hords j w Hf k ek Hin Hkj Hki; [ destruct Hin |].
  cbn in Hords. destruct m as [|m']; [ discriminate Hords |].
  injection Hords as Hk0 Hrest. subst k0.
  cbn in Hf. destruct (lt_dec a i) as [Ha|Ha].
  - destruct (match binder_ident (Index.Edges.sl_child e0) with
              | Some m0 => Names.ordinary_equalb m0 n | None => false end) eqn:Ht.
    + injection Hf as He H2. subst j.
      destruct Hin as [Hhead|Hin].
      * injection Hhead as Hke. lia.
      * exfalso.
        assert (Hkin : In k (map (@projT1 _ _) rest))
          by (apply in_map_iff; exists (existT _ k ek); split; [ reflexivity | exact Hin ]).
        rewrite Hrest in Hkin. apply in_seq in Hkin. lia.
    + destruct Hin as [Hhead|Hin].
      * injection Hhead as Hke He. subst k.
        apply Eqdep_dec.inj_pair2_eq_dec in He; [| exact Nat.eq_dec ]. subst ek. exact Ht.
      * exact (IH (S a) m' Hrest j w Hf k ek Hin Hkj Hki).
  - destruct Hin as [Hhead|Hin].
    + injection Hhead as Hke He. subst k. lia.
    + exact (IH (S a) m' Hrest j w Hf k ek Hin Hkj Hki).
Qed.

Lemma option_noderef_eq_dec {p} {idx : Index.Core.ProgramIndex p} :
  forall a b : option (Index.Core.NodeRef idx), {a = b} + {a <> b}.
Proof. decide equality. apply (dec_of_eqb noderef_eqb noderef_eqb_spec). Qed.

(* one canonical edge inhabitant per parent and ordinal *)
Lemma childat_unique {p} {idx : Index.Core.ProgramIndex p} {par : Index.Core.NodeRef idx} {k : nat}
  (a b : Index.Child.ChildAt par k) : a = b.
Proof.
  destruct a as [ca Ha], b as [cb Hb].
  assert (E : ca = cb) by (rewrite Ha in Hb; injection Hb as Hb; exact Hb).
  subst cb. f_equal. apply (UIP_dec option_noderef_eq_dec).
Qed.

Lemma shortlhsedge_unique {p} {idx : Index.Core.ProgramIndex p} {st : Index.Refs.ShortStmtRef idx} {i : nat}
  (a b : Index.Edges.ShortLhsEdge st i) : a = b.
Proof.
  destruct a as [ea la], b as [eb lb].
  assert (E : ea = eb) by apply childat_unique. subst eb.
  f_equal. apply Index.Model.lt_unique.
Qed.

(* a self edge names the exact parent the parent relation retains *)
Lemma selfedge_parent {p} {idx : Index.Core.ProgramIndex p} {r : Index.Core.NodeRef idx}
  (se : Index.Edges.SelfEdge r) : Index.Core.node_parent r = Some (Index.Edges.se_parent se).
Proof.
  pose proof (Index.Child.ca_node_parent (Index.Edges.se_at se)) as H.
  rewrite (Index.Edges.se_child_eq se) in H. exact H.
Qed.

Lemma selfedge_ord_unique {p} {idx : Index.Core.ProgramIndex p} {r : Index.Core.NodeRef idx}
  (se1 se2 : Index.Edges.SelfEdge r) : Index.Edges.se_ord se1 = Index.Edges.se_ord se2.
Proof.
  pose proof (selfedge_parent se1) as H1. pose proof (selfedge_parent se2) as H2.
  rewrite H1 in H2. injection H2 as E.
  destruct se2 as [par2 o2 at2 eq2]; cbn in *.
  revert at2 eq2. rewrite <- E. intros at2 eq2.
  apply (Index.Child.ca_ord_unique (Index.Edges.se_at se1) at2).
  rewrite (Index.Edges.se_child_eq se1), eq2. reflexivity.
Qed.

(* the first and adjacent cases are exact and disjoint *)
Lemma const_first_not_adjacent {p} {idx : Index.Core.ProgramIndex p}
  (cs pred : Index.Refs.SpecRef idx Index.Model.ConstSpecF)
  (cf : ConstFirst cs) (adj : ConstAdjacency cs pred) : False.
Proof.
  pose (se' := Index.Edges.mkSelfEdge (cad_parent adj) (S (cad_ord adj)) (cad_self_at adj)
                 (eq_sym (cad_self_eq adj))).
  destruct cf as [Hp|se H0].
  - pose proof (selfedge_parent se') as Hsp. rewrite Hp in Hsp. discriminate Hsp.
  - pose proof (selfedge_ord_unique se se') as He. rewrite H0 in He. cbn in He. discriminate He.
Qed.

(* the immediate predecessor is unique *)
Lemma const_pred_exact {p} {idx : Index.Core.ProgramIndex p}
  (cs pred1 pred2 : Index.Refs.SpecRef idx Index.Model.ConstSpecF)
  (a1 : ConstAdjacency cs pred1) (a2 : ConstAdjacency cs pred2) : pred1 = pred2.
Proof.
  pose proof (selfedge_parent (Index.Edges.mkSelfEdge (cad_parent a1) (S (cad_ord a1)) (cad_self_at a1)
                (eq_sym (cad_self_eq a1)))) as H1.
  pose proof (selfedge_parent (Index.Edges.mkSelfEdge (cad_parent a2) (S (cad_ord a2)) (cad_self_at a2)
                (eq_sym (cad_self_eq a2)))) as H2.
  pose proof (selfedge_ord_unique
                (Index.Edges.mkSelfEdge (cad_parent a1) (S (cad_ord a1)) (cad_self_at a1)
                   (eq_sym (cad_self_eq a1)))
                (Index.Edges.mkSelfEdge (cad_parent a2) (S (cad_ord a2)) (cad_self_at a2)
                   (eq_sym (cad_self_eq a2)))) as Eord.
  cbn in H1, H2, Eord. rewrite H1 in H2. injection H2 as Epar. injection Eord as Eord.
  destruct a1 as [par1 o1 pat1 peq1 sat1 seq1], a2 as [par2 o2 pat2 peq2 sat2 seq2]; cbn in *.
  subst par2 o2.
  apply specref_positional.
  rewrite peq1, peq2. f_equal. apply childat_unique.
Qed.

(* the origin projection follows the exact retained chain, one constructor at a time *)
Lemma const_origin_explicit {p} {idx : Index.Core.ProgramIndex p}
  (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF) (He : cs_explicit cs = true) :
  const_origin (CJExplicit cs He) = Some (existT _ cs He).
Proof. reflexivity. Qed.
Lemma const_origin_first {p} {idx : Index.Core.ProgramIndex p}
  (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF) (Hne : cs_explicit cs = false) (cf : ConstFirst cs) :
  const_origin (CJFirstInherited cs Hne cf) = None.
Proof. reflexivity. Qed.
Lemma const_origin_inherited {p} {idx : Index.Core.ProgramIndex p}
  (cs pred : Index.Refs.SpecRef idx Index.Model.ConstSpecF) (Hne : cs_explicit cs = false)
  (adj : ConstAdjacency cs pred) (jp : ConstJudgment pred) :
  const_origin (CJInherited cs pred Hne adj jp) = const_origin jp.
Proof. reflexivity. Qed.

(* the judgment constructor is forced by the exact source shape *)
Lemma const_judgment_forms {p} {idx : Index.Core.ProgramIndex p}
  (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF) (j : ConstJudgment cs) :
  match j with CJExplicit _ _ => cs_explicit cs = true | _ => cs_explicit cs = false end.
Proof. destruct j as [c He|c Hne cf|c pred Hne adj jp]; assumption. Qed.

(* no alternative predecessor decision can inhabit the same spec *)
Lemma const_pred_unique {p} {idx : Index.Core.ProgramIndex p}
  (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF) (j1 j2 : ConstJudgment cs) :
  const_pred j1 = const_pred j2.
Proof.
  pose proof (const_judgment_forms cs j1) as F1. pose proof (const_judgment_forms cs j2) as F2.
  destruct j1 as [c1 He1|c1 Hne1 cf1|c1 pred1 Hne1 adj1 jp1];
    destruct j2 as [c2 He2|c2 Hne2 cf2|c2 pred2 Hne2 adj2 jp2];
    cbn; try reflexivity; try congruence.
  - exact (match const_first_not_adjacent _ _ cf1 adj2 with end).
  - exact (match const_first_not_adjacent _ _ cf2 adj1 with end).
  - f_equal. exact (const_pred_exact _ _ _ adj1 adj2).
Qed.

Lemma mk_noderef_key {p} {idx : Index.Core.ProgramIndex p} (fr : Index.Core.FileRef idx) (k : positive)
  (r : Index.Core.NodeRef idx) : Index.Core.mk_noderef fr k = Some r -> Index.Core.nr_key r = k.
Proof.
  unfold Index.Core.mk_noderef.
  generalize (@eq_refl bool (Collections.NodeMap.mem k (Index.Core.cell_map fr))).
  destruct (Collections.NodeMap.mem k (Index.Core.cell_map fr)) at 2 3; intro e;
    [ intro H; injection H as <-; reflexivity | discriminate ].
Qed.

Lemma app_nodup_disjoint {A} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> In x l2 -> False) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [|x t IH]; intros H1 H2 Hdisj; [ exact H2 |].
  apply NoDup_cons_iff in H1. destruct H1 as [Hnx H1'].
  cbn [app]. constructor.
  - intro Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin];
      [ exact (Hnx Hin) | exact (Hdisj x (or_introl eq_refl) Hin) ].
  - apply IH; [ exact H1' | exact H2 | intros y Hy1 Hy2; exact (Hdisj y (or_intror Hy1) Hy2) ].
Qed.

(* a disjoint tagged flat_map of per-item duplicate-free blocks is duplicate-free *)
Lemma flat_map_nodup {A B} (f : A -> list B) (tag : B -> A) (l : list A) :
  NoDup l -> (forall a, In a l -> NoDup (f a)) ->
  (forall a b, In a l -> In b (f a) -> tag b = a) ->
  NoDup (flat_map f l).
Proof.
  induction l as [|a0 rest IH]; intros Hnd Hblocks Htags; [ constructor |].
  cbn [flat_map]. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd'].
  apply app_nodup_disjoint.
  - apply Hblocks. left. reflexivity.
  - apply IH; [ exact Hnd' | intros a Ha; apply Hblocks; right; exact Ha
              | intros a b Ha Hb; apply Htags; [ right; exact Ha | exact Hb ] ].
  - intros b Hb0 Hbr.
    apply in_flat_map in Hbr. destruct Hbr as [a [Ha Hbin]].
    apply Hnotin.
    rewrite <- (Htags a0 b (or_introl eq_refl) Hb0).
    rewrite (Htags a b (or_intror Ha) Hbin). exact Ha.
Qed.

(* the file enumeration is duplicate-free: one file per retained path key *)
Lemma files_emit_paths_nodup {p} {idx : Index.Core.ProgramIndex p} :
  forall l : list (FilePath.T * Index.Build.FileInfo),
  NoDup (map fst l) ->
  NoDup (map Index.Core.fr_path
           (flat_map (fun kv => match Index.Edges.mk_fileref idx (fst kv) with
                                | Some fr => [fr] | None => [] end) l)).
Proof.
  induction l as [|kv rest IH]; intro Hk; [ constructor |].
  cbn [map] in Hk. apply NoDup_cons_iff in Hk. destruct Hk as [Hnotin Hk'].
  specialize (IH Hk'). cbn [flat_map].
  destruct (Index.Edges.mk_fileref idx (fst kv)) as [fr|] eqn:Hmk; [| cbn [app]; exact IH ].
  cbn [app map]. constructor; [| exact IH ].
  intro Hin. apply Hnotin.
  rewrite (Index.Edges.mk_fileref_path idx (fst kv) fr Hmk) in Hin.
  clear -Hin. induction rest as [|kv' rest' IH']; [ destruct Hin |].
  cbn [flat_map] in Hin. cbn [map].
  destruct (Index.Edges.mk_fileref idx (fst kv')) as [fr'|] eqn:Hmk'.
  - cbn [app map] in Hin. destruct Hin as [He|Hin];
      [ left; rewrite <- (Index.Edges.mk_fileref_path idx (fst kv') fr' Hmk'); exact He
      | right; exact (IH' Hin) ].
  - cbn [app] in Hin. right. exact (IH' Hin).
Qed.

Lemma all_files_paths_nodup {p} {idx : Index.Core.ProgramIndex p} :
  NoDup (map Index.Core.fr_path (Index.Edges.all_files idx)).
Proof.
  exact (files_emit_paths_nodup (Collections.FileMap.elements (Index.Core.prog_map idx))
           (Collections.file_map_elements_keys_nodup (Index.Core.prog_map idx))).
Qed.

Lemma all_files_nodup {p} {idx : Index.Core.ProgramIndex p} : NoDup (Index.Edges.all_files idx).
Proof. exact (NoDup_map_inv _ _ all_files_paths_nodup). Qed.

Lemma pkg_members_nodup {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) : NoDup (PI.pkg_members pr).
Proof. unfold PI.pkg_members. apply NoDup_filter. apply all_files_nodup. Qed.

Lemma mk_packageref_pos {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (n : nat) (pr : PI.PackageRef s) : PI.mk_packageref s n = Some pr -> PI.pr_pos pr = n.
Proof.
  unfold PI.mk_packageref. destruct (lt_dec n (PI.package_count s));
    [ intro H; injection H as <-; reflexivity | discriminate ].
Qed.

Lemma packages_nodup {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx) :
  NoDup (PI.packages s).
Proof.
  unfold PI.packages.
  apply (flat_map_nodup _ PI.pr_pos); [ apply seq_NoDup | |].
  - intros n _. destruct (PI.mk_packageref s n); [ apply NoDup_cons; [ intro F; destruct F | constructor ] | constructor ].
  - intros n pr _ Hin. destruct (PI.mk_packageref s n) as [pr0|] eqn:Hmk; [| destruct Hin ].
    destruct Hin as [He|F]; [| destruct F ]. subst pr0.
    exact (mk_packageref_pos n pr Hmk).
Qed.

(* every emitted const ref names its own occurrence *)
Lemma const_ref_emit_node {p} {idx : Index.Core.ProgramIndex p} (r : Index.Core.NodeRef idx)
  (v : Index.Model.NodeView) (Hv : Index.Core.node_view r = v) (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF) :
  In cs (const_ref_emit r v Hv) -> Index.Refs.sp_node cs = r.
Proof.
  destruct v; cbn; try (intros F; exact (match F with end)).
  intros [He|F]; [ rewrite <- He; reflexivity | destruct F ].
Qed.


Lemma const_ref_emit_nodup {p} {idx : Index.Core.ProgramIndex p} (r : Index.Core.NodeRef idx)
  (v : Index.Model.NodeView) (Hv : Index.Core.node_view r = v) : NoDup (const_ref_emit r v Hv).
Proof. destruct v; cbn; repeat constructor; intros F; destruct F. Qed.


Lemma noderef_pos_of_key {p} {idx : Index.Core.ProgramIndex p} (r : Index.Core.NodeRef idx) (pos : nat) :
  Index.Core.nr_key r = Pos.of_succ_nat pos -> Index.Core.nr_pos r = pos.
Proof.
  intro H. pose proof (Index.Core.nr_key_pos r) as Hk. rewrite H in Hk.
  apply (f_equal Pos.to_nat) in Hk. rewrite !SuccNat2Pos.id_succ in Hk. lia.
Qed.

(* the const subjects are duplicate-free: one exact subject per source occurrence *)
Lemma const_subjects_nodup {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx) :
  NoDup (const_subjects s).
Proof.
  unfold const_subjects.
  apply (flat_map_nodup _ (fun cs => PI.package_of_file s (Index.Core.nr_file (Index.Refs.sp_node cs))));
    [ apply packages_nodup | |].
  - intros pr _.
    apply (flat_map_nodup _ (fun cs => Index.Core.nr_file (Index.Refs.sp_node cs)));
      [ apply pkg_members_nodup | |].
    + intros fr _. unfold const_specs_of_file.
      apply (flat_map_nodup _ (fun cs => Index.Core.nr_pos (Index.Refs.sp_node cs)));
        [ apply seq_NoDup | |].
      * intros pos _. destruct (Index.Core.mk_noderef fr (Pos.of_succ_nat pos)) as [r|]; [| constructor ].
        apply const_ref_emit_nodup.
      * intros pos cs _ Hin.
        destruct (Index.Core.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
        rewrite (const_ref_emit_node r _ _ cs Hin).
        exact (noderef_pos_of_key r pos (mk_noderef_key fr _ r Hmk)).
    + intros fr cs _ Hin.
      unfold const_specs_of_file in Hin. apply in_flat_map in Hin.
      destruct Hin as [pos [_ Hin]].
      destruct (Index.Core.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
      rewrite (const_ref_emit_node r _ _ cs Hin).
      exact (Index.Core.mk_noderef_file _ _ _ Hmk).
  - intros pr cs Hpr Hin.
    apply in_flat_map in Hin. destruct Hin as [fr [Hfr Hin]].
    unfold const_specs_of_file in Hin. apply in_flat_map in Hin.
    destruct Hin as [pos [_ Hin]].
    destruct (Index.Core.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
    rewrite (const_ref_emit_node r _ _ cs Hin).
    rewrite (Index.Core.mk_noderef_file _ _ _ Hmk).
    exact (PI.package_of_file_member s pr fr Hfr).
Qed.

(* a map distributes into a flat_map, block by block *)
Lemma map_flat_map {A B C} (f : B -> C) (g : A -> list B) (l : list A) :
  map f (flat_map g l) = flat_map (fun x => map f (g x)) l.
Proof. induction l as [|a t IH]; [ reflexivity | cbn; rewrite map_app, IH; reflexivity ]. Qed.

Lemma bp_consts_exactly_once {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (o1 o2 : nat)
  (row1 row2 : { c : Index.Refs.SpecRef idx Index.Model.ConstSpecF & ConstJudgment c }) :
  nth_error (bp_consts bp) o1 = Some row1 -> nth_error (bp_consts bp) o2 = Some row2 ->
  projT1 row1 = projT1 row2 -> o1 = o2.
Proof.
  intros H1 H2 He.
  assert (Hnd : NoDup (map (fun row => projT1 row) (bp_consts bp)))
    by (rewrite bp_consts_subjects; apply const_subjects_nodup).
  assert (Hm1 : nth_error (map (fun row => projT1 row) (bp_consts bp)) o1 = Some (projT1 row1))
    by (exact (map_nth_error _ o1 _ H1)).
  assert (Hm2 : nth_error (map (fun row => projT1 row) (bp_consts bp)) o2 = Some (projT1 row2))
    by (exact (map_nth_error _ o2 _ H2)).
  apply (proj1 (NoDup_nth_error _) Hnd o1 o2).
  - apply nth_error_Some. rewrite Hm1. discriminate.
  - rewrite Hm1, Hm2, He. reflexivity.
Qed.

Lemma flat_map_nodup_key {A B K} (f : A -> list B) (key : B -> K) (akey : A -> K) (l : list A) :
  NoDup (map akey l) -> (forall a, In a l -> NoDup (f a)) ->
  (forall a b, In a l -> In b (f a) -> key b = akey a) ->
  NoDup (flat_map f l).
Proof.
  induction l as [|a0 rest IH]; intros Hnd Hblocks Htags; [ constructor |].
  cbn [map] in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd'].
  cbn [flat_map]. apply app_nodup_disjoint.
  - apply Hblocks. left. reflexivity.
  - apply IH; [ exact Hnd' | intros a Ha; apply Hblocks; right; exact Ha
              | intros a b Ha Hb; apply Htags; [ right; exact Ha | exact Hb ] ].
  - intros b Hb0 Hbr.
    apply in_flat_map in Hbr. destruct Hbr as [a [Ha Hbin]].
    apply Hnotin.
    rewrite <- (Htags a0 b (or_introl eq_refl) Hb0).
    rewrite (Htags a b (or_intror Ha) Hbin).
    apply in_map. exact Ha.
Qed.

(* a strictly monotone image of an ordinal-sequenced list is duplicate-free *)
Lemma seq_map_nodup {A} (g f : A -> nat) (l : list A) :
  forall a m, map g l = seq a m ->
  (forall x y, In x l -> In y l -> g x < g y -> f x < f y) ->
  NoDup (map f l).
Proof.
  induction l as [|x t IH]; intros a m Hg Hmono; [ constructor |].
  cbn [map] in Hg |- *. destruct m as [|m']; [ discriminate Hg |].
  cbn [seq] in Hg. injection Hg as Hx Ht.
  constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Hf Hy]].
    assert (Hgy : In (g y) (seq (S a) m'))
      by (rewrite <- Ht; apply in_map; exact Hy).
    apply in_seq in Hgy.
    assert (Hlt : f x < f y)
      by (apply Hmono; [ left; reflexivity | right; exact Hy | lia ]).
    lia.
  - apply (IH (S a) m' Ht). intros x0 y0 Hx0 Hy0. apply Hmono; right; assumption.
Qed.

(* the fixed-main emission: the exact function establishment on the exact occurrence *)
Lemma make_main_est_some {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (b : Index.Core.NodeRef idx) (e : Est s) :
  make_main_est pr b = Some e ->
  (exists f, est_origin e = DOFunc f) /\ est_node e = b /\ est_scope e = PackageScope pr
  /\ est_name e = main_ident /\ est_vstart e = Index.Core.nr_pos b.
Proof.
  unfold make_main_est.
  generalize (@eq_refl bool (Index.Core.is_main_view (Index.Core.node_view b))).
  destruct (Index.Core.is_main_view (Index.Core.node_view b)) at 2 3; intro Hm; [| discriminate ].
  intro He. injection He as <-. cbn.
  split; [ eexists; reflexivity |]. split; [ reflexivity |].
  split; [ reflexivity |]. split; reflexivity.
Qed.

Lemma make_main_est_fires {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (b : Index.Core.NodeRef idx) :
  Index.Core.is_main_view (Index.Core.node_view b) = true -> make_main_est pr b <> None.
Proof.
  intro Hv. unfold make_main_est.
  generalize (@eq_refl bool (Index.Core.is_main_view (Index.Core.node_view b))).
  destruct (Index.Core.is_main_view (Index.Core.node_view b)) at 2 3; intro Hm;
    [ discriminate | exfalso; rewrite Hv in Hm; discriminate Hm ].
Qed.

(* the spec-name emission: the exact declaration-binder establishment on the exact name edge *)
Lemma spec_name_est_fields {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {fl : Index.Model.SpecFlavor} {sp : Index.Refs.SpecRef idx fl} {i : nat}
  (sc : ScopeId s) (ne : Index.Edges.SpecNameEdge sp i) (e : Est s) :
  spec_name_est sc ne = Some e ->
  est_scope e = sc /\ est_node e = Index.Edges.sn_child ne
  /\ binder_ident (Index.Edges.sn_child ne) = Some (est_name e)
  /\ est_vstart e = vis_start (Index.Edges.sn_child ne)
  /\ (exists b, est_origin e = DOBinder b).
Proof.
  unfold spec_name_est.
  destruct (binder_ident (Index.Edges.sn_child ne)) as [n|] eqn:Hb; [| discriminate ].
  intro He. injection He as <-. cbn.
  split; [ reflexivity |]. split; [ reflexivity |].
  split; [ reflexivity |]. split; [ reflexivity |]. eexists; reflexivity.
Qed.

Lemma spec_ests_member {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {fl : Index.Model.SpecFlavor} (sc : ScopeId s) (sp : Index.Refs.SpecRef idx fl) (e : Est s) :
  In e (spec_ests sc sp) ->
  exists i (ne : Index.Edges.SpecNameEdge sp i), spec_name_est sc ne = Some e.
Proof.
  intro Hin. unfold spec_ests in Hin. apply in_flat_map in Hin.
  destruct Hin as [x [_ Hin]].
  destruct (spec_name_est sc (projT2 x)) as [e0|] eqn:He; [| destruct Hin ].
  destruct Hin as [He0|F]; [| destruct F ].
  exists (projT1 x), (projT2 x). rewrite He, He0. reflexivity.
Qed.

(* the spec emission at an occurrence: members are its own name children's establishments *)
Lemma spec_emit_member {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (r : Index.Core.NodeRef idx) (v : Index.Model.NodeView) (Hv : Index.Core.node_view r = v)
  (e : Est s) :
  In e (spec_emit sc r v Hv) ->
  est_scope e = sc
  /\ Index.Core.node_parent (est_node e) = Some r
  /\ (exists b, est_origin e = DOBinder b)
  /\ binder_ident (est_node e) = Some (est_name e).
Proof.
  destruct v; cbv beta iota delta [spec_emit]; try (intros F; exact (match F with end)); intro Hin;
    (destruct (spec_ests_member _ _ _ Hin) as [i [ne He]];
     destruct (spec_name_est_fields _ ne _ He) as [Hsc [Hnode [Hb [_ Hor]]]];
     split; [ exact Hsc |];
     split; [ rewrite Hnode; exact (Index.Edges.sn_parent ne) |];
     split; [ exact Hor | rewrite Hnode; exact Hb ]).
Qed.

(* one declaration statement's establishments: scope exact, nodes exactly two parent hops below *)
Lemma stmt_decl_ests_member {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (t : Index.Core.NodeRef idx) (e : Est s) :
  In e (stmt_decl_ests sc t) ->
  est_scope e = sc
  /\ (exists b, est_origin e = DOBinder b)
  /\ binder_ident (est_node e) = Some (est_name e)
  /\ (exists sp d, Index.Core.node_parent (est_node e) = Some sp
                   /\ Index.Core.node_parent sp = Some d /\ Index.Core.node_parent d = Some t).
Proof.
  unfold stmt_decl_ests.
  destruct (Index.Child.child_at_opt t 0) as [e0|] eqn:H0; [| intros F; exact (match F with end) ].
  intro Hin. unfold decl_ests in Hin. apply in_flat_map in Hin.
  destruct Hin as [[k ce] [_ Hin]].
  destruct (spec_emit_member _ _ _ _ _ Hin) as [Hsc [Hpar [Hor Hbn]]].
  split; [ exact Hsc |]. split; [ exact Hor |]. split; [ exact Hbn |].
  exists (Index.Child.ca_child ce), (Index.Child.ca_child e0).
  split; [ exact Hpar |].
  split; [ exact (Index.Child.ca_node_parent ce) | exact (Index.Child.ca_node_parent e0) ].
Qed.

Definition est_site {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (e : Est s) : option (Index.Core.NodeRef idx) :=
  match est_origin e with
  | DOFunc _ => Some (est_node e)
  | DOShort _ => Index.Core.node_parent (est_node e)
  | DOBinder _ =>
      match Index.Core.node_parent (est_node e) with
      | Some sp => match Index.Core.node_parent sp with
                   | Some d => Index.Core.node_parent d
                   | None => None
                   end
      | None => None
      end
  end.

Lemma stmt_decl_ests_site {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (t : Index.Core.NodeRef idx) (e : Est s) :
  In e (stmt_decl_ests sc t) -> est_site e = Some t.
Proof.
  intro Hin. destruct (stmt_decl_ests_member sc t e Hin)
    as [_ [[b Hor] [_ [sp [d [H1 [H2 H3]]]]]]].
  unfold est_site. rewrite Hor, H1, H2. exact H3.
Qed.
Lemma spec_ests_nodup {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {fl : Index.Model.SpecFlavor} (sc : ScopeId s) (sp : Index.Refs.SpecRef idx fl) :
  NoDup (spec_ests sc sp).
Proof.
  unfold spec_ests.
  apply (flat_map_nodup_key _ (fun e => Index.Core.nr_pos (est_node e))
           (fun x => Index.Core.nr_pos (Index.Edges.sn_child (projT2 x)))).
  - apply (seq_map_nodup (@projT1 _ _) _ _ 0 (Index.Refs.shape_names fl (Index.Refs.sp_shape sp)));
      [ apply Index.Edges.spec_name_edges_ords |].
    intros x y _ _ Hlt. unfold Index.Edges.sn_child. apply Index.Child.ca_pos_lt. exact Hlt.
  - intros x _. destruct (spec_name_est sc (projT2 x)); repeat constructor; intros F; destruct F.
  - intros x e _ Hin.
    destruct (spec_name_est sc (projT2 x)) as [e0|] eqn:He; [| destruct Hin ].
    destruct Hin as [He0|F]; [| destruct F ]. subst e0.
    destruct (spec_name_est_fields sc (projT2 x) e He) as [_ [Hnode _]].
    rewrite Hnode. reflexivity.
Qed.

Lemma spec_emit_nodup {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (r : Index.Core.NodeRef idx) (v : Index.Model.NodeView) (Hv : Index.Core.node_view r = v) :
  NoDup (spec_emit sc r v Hv).
Proof.
  destruct v; cbv beta iota delta [spec_emit]; first [ apply spec_ests_nodup | constructor ].
Qed.

Lemma decl_ests_nodup {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (d : Index.Core.NodeRef idx) : NoDup (decl_ests sc d).
Proof.
  unfold decl_ests.
  apply (flat_map_nodup_key _
           (fun e => match Index.Core.node_parent (est_node e) with
                     | Some x => Index.Core.nr_pos x | None => 0 end)
           (fun x => Index.Core.nr_pos (Index.Child.ca_child (projT2 x)))).
  - eapply (seq_map_nodup (@projT1 _ _)); [ apply Index.Child.all_children_ords |].
    intros x y _ _ Hlt. apply Index.Child.ca_pos_lt. exact Hlt.
  - intros x _. apply spec_emit_nodup.
  - intros x e _ Hin.
    destruct (spec_emit_member _ _ _ _ _ Hin) as [_ [Hpar _]].
    rewrite Hpar. reflexivity.
Qed.

Lemma stmt_decl_ests_nodup {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (t : Index.Core.NodeRef idx) : NoDup (stmt_decl_ests sc t).
Proof.
  unfold stmt_decl_ests. destruct (Index.Child.child_at_opt t 0); [ apply decl_ests_nodup | constructor ].
Qed.
Lemma shortstmtref_eq_dec {p} {idx : Index.Core.ProgramIndex p} :
  forall a b : Index.Refs.ShortStmtRef idx, {a = b} + {a <> b}.
Proof.
  intros a b.
  destruct (Bool.bool_dec (noderef_eqb (Index.Refs.sh_node a) (Index.Refs.sh_node b)) true) as [H|H].
  - left. apply shortstmtref_positional. apply noderef_eqb_spec. exact H.
  - right. intro E. apply H. subst b. apply noderef_eqb_spec. reflexivity.
Qed.

Lemma spec_emit_eval {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {fl : Index.Model.SpecFlavor} (sc : ScopeId s) (r : Index.Core.NodeRef idx) (v : Index.Model.NodeView)
  (Hv : Index.Core.node_view r = v) (sh : Index.Refs.SpecShape fl) :
  v = Index.Refs.spec_view_of fl sh ->
  exists Hv0 : Index.Core.node_view r = Index.Refs.spec_view_of fl sh,
    spec_emit sc r v Hv = spec_ests sc (Index.Refs.mkSpecRef (fl := fl) r sh Hv0).
Proof.
  intro E. revert Hv. subst v. intro Hv. exists Hv.
  destruct fl; reflexivity.
Qed.

Lemma spec_ests_cover {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {fl : Index.Model.SpecFlavor} (sc : ScopeId s) (sp : Index.Refs.SpecRef idx fl) (i : nat)
  (ne : Index.Edges.SpecNameEdge sp i) (n : Names.OrdinaryIdentifier) :
  binder_ident (Index.Edges.sn_child ne) = Some n ->
  exists e, In e (spec_ests sc sp) /\ est_node e = Index.Edges.sn_child ne.
Proof.
  intro Hb.
  assert (Hin : In i (map (@projT1 _ _) (Index.Edges.spec_name_edges sp)))
    by (rewrite (Index.Edges.spec_name_edges_ords sp); apply in_seq_intro; exact (Index.Edges.sn_lt ne)).
  apply in_map_iff in Hin. destruct Hin as [x [Hx Hrow]].
  destruct x as [i' ne']. cbn [projT1] in Hx. subst i'.
  assert (Hc : Index.Edges.sn_child ne' = Index.Edges.sn_child ne)
    by (exact (Index.Child.ca_det (Index.Edges.sn_at ne') (Index.Edges.sn_at ne))).
  assert (Hb' : binder_ident (Index.Edges.sn_child ne') = Some n) by (rewrite Hc; exact Hb).
  unfold spec_ests.
  destruct (spec_name_est sc ne') as [e0|] eqn:He.
  - exists e0. split.
    + apply in_flat_map. exists (existT _ i ne'). split; [ exact Hrow |].
      cbn [projT1 projT2]. rewrite He. left. reflexivity.
    + destruct (spec_name_est_fields sc ne' e0 He) as [_ [Hnode _]].
      rewrite Hnode. exact Hc.
  - exfalso. unfold spec_name_est in He. rewrite Hb' in He. discriminate He.
Qed.

(* one declaration's establishments cover each child spec's named binders *)
Lemma decl_ests_cover {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (d : Index.Core.NodeRef idx) {fl : Index.Model.SpecFlavor}
  (spref : Index.Refs.SpecRef idx fl) (i : nat) (ne : Index.Edges.SpecNameEdge spref i)
  (n : Names.OrdinaryIdentifier) :
  Index.Core.node_parent (Index.Refs.sp_node spref) = Some d ->
  binder_ident (Index.Edges.sn_child ne) = Some n ->
  exists e, In e (decl_ests sc d) /\ est_node e = Index.Edges.sn_child ne.
Proof.
  intros Hp Hb.
  destruct (Index.Edges.all_children_of_parent (Index.Refs.sp_node spref) d Hp) as [k [ed [Hrow Hc]]].
  destruct (spec_emit_eval (fl := fl) sc (Index.Child.ca_child ed) (Index.Core.node_view (Index.Child.ca_child ed))
              eq_refl (Index.Refs.sp_shape spref))
    as [Hv0 Hemit]; [ rewrite Hc; exact (Index.Refs.sp_ok spref) |].
  assert (Hsp : Index.Refs.mkSpecRef (fl := fl) (Index.Child.ca_child ed) (Index.Refs.sp_shape spref) Hv0 = spref)
    by (apply specref_positional; exact Hc).
  destruct (spec_ests_cover sc spref i ne n Hb) as [e0 [Hin Hnode]].
  exists e0. split; [| exact Hnode ].
  unfold decl_ests. apply in_flat_map. exists (existT _ k ed). split; [ exact Hrow |].
  cbn [projT1 projT2]. rewrite Hemit, Hsp. exact Hin.
Qed.

Lemma stmt_decl_ests_cover {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (t : Index.Core.NodeRef idx) (et : Index.Child.ChildAt t 0)
  {fl : Index.Model.SpecFlavor} (spref : Index.Refs.SpecRef idx fl) (i : nat)
  (ne : Index.Edges.SpecNameEdge spref i) (n : Names.OrdinaryIdentifier) :
  Index.Core.node_parent (Index.Refs.sp_node spref) = Some (Index.Child.ca_child et) ->
  binder_ident (Index.Edges.sn_child ne) = Some n ->
  exists e, In e (stmt_decl_ests sc t) /\ est_node e = Index.Edges.sn_child ne.
Proof.
  intros Hp Hb. unfold stmt_decl_ests.
  destruct (Index.Child.child_at_opt t 0) as [e0|] eqn:H0;
    [| exact (match Index.Child.child_at_opt_some _ _ et H0 with end) ].
  assert (Hde : Index.Child.ca_child e0 = Index.Child.ca_child et) by (exact (Index.Child.ca_det e0 et)).
  rewrite Hde.
  exact (decl_ests_cover sc (Index.Child.ca_child et) spref i ne n Hp Hb).
Qed.

(* a spec-name edge exists at every spec-name-roled child ordinal: the role decodes the bound *)
Lemma specname_ordinal_lt {p} {idx : Index.Core.ProgramIndex p} {fl : Index.Model.SpecFlavor}
  (sp : Index.Refs.SpecRef idx fl) (i : nat) (eb : Index.Child.ChildAt (Index.Refs.sp_node sp) i) :
  Index.Core.node_role (Index.Child.ca_child eb) = Index.Model.RSpecName fl ->
  i < Index.Refs.shape_names fl (Index.Refs.sp_shape sp).
Proof.
  intro Hr. pose proof (Index.Child.ca_role eb) as Hrole.
  rewrite Hr, (Index.Refs.sp_ok sp) in Hrole.
  pose proof (Index.Child.child_at_count_lt eb) as Hcount.
  destruct fl.
  - destruct (Index.Refs.sp_shape sp) as [ht nn nv|nn] eqn:Hsh;
      cbn [Index.Refs.spec_view_of Index.Core.layout_role Index.Refs.shape_names] in Hrole |- *.
    + destruct (i <? nn) eqn:Hlt; [ apply Nat.ltb_lt; exact Hlt |].
      destruct (andb ht (i =? nn)); discriminate Hrole.
    + assert (Hlc : Index.Core.layout_count (Index.Core.node_view (Index.Refs.sp_node sp)) = Some nn)
        by (rewrite (Index.Refs.sp_ok sp), Hsh; reflexivity).
      exact (Hcount nn Hlc).
  - destruct (Index.Refs.sp_shape sp) as [nn|ht nn nv] eqn:Hsh;
      cbn [Index.Refs.spec_view_of Index.Core.layout_role Index.Refs.shape_names] in Hrole |- *.
    + destruct (i <? nn) eqn:Hlt; [ apply Nat.ltb_lt; exact Hlt | discriminate Hrole ].
    + destruct (i <? nn) eqn:Hlt; [ apply Nat.ltb_lt; exact Hlt |].
      destruct (andb ht (i =? nn)); discriminate Hrole.
  - destruct (Index.Refs.sp_shape sp) eqn:Hsh;
      cbn [Index.Refs.spec_view_of Index.Core.layout_role Index.Refs.shape_names] in Hrole |- *;
      destruct i; [ lia | discriminate Hrole | lia | discriminate Hrole ].
Qed.

Lemma pre_nth_post {A} (l1 l2 : list A) (j : nat) (x : A) :
  nth_error l1 j = Some x -> nth_error (l1 ++ l2) j = Some x.
Proof.
  intro H. rewrite nth_error_app1; [ exact H |].
  apply nth_error_Some. rewrite H. discriminate.
Qed.

Lemma post_nth {A} (l1 l2 : list A) (k : nat) (x : A) :
  nth_error l2 k = Some x -> nth_error (l1 ++ l2) (length l1 + k) = Some x.
Proof.
  intro H. rewrite nth_error_app2; [| lia ].
  rewrite (Nat.add_comm (length l1) k), Nat.add_sub. exact H.
Qed.

Lemma flat_map_nil_all {A B} (f : A -> list B) (l : list A) :
  (forall x, In x l -> f x = []) -> flat_map f l = [].
Proof.
  induction l as [|a t IH]; intro H; [ reflexivity |].
  cbn. rewrite (H a (or_introl eq_refl)). apply IH. intros x Hx. exact (H x (or_intror Hx)).
Qed.

Lemma filter_all_false {A} (f : A -> bool) (l : list A) :
  (forall x, In x l -> f x = false) -> filter f l = [].
Proof.
  induction l as [|a t IH]; intro H; [ reflexivity |].
  cbn. rewrite (H a (or_introl eq_refl)). apply IH. intros x Hx. exact (H x (or_intror Hx)).
Qed.

Lemma filter_impl_le {A} (f g : A -> bool) (l : list A) :
  (forall x, In x l -> f x = true -> g x = true) ->
  length (filter f l) <= length (filter g l).
Proof.
  induction l as [|a t IH]; intro H; [ cbn; lia |].
  cbn. destruct (f a) eqn:Hf.
  - rewrite (H a (or_introl eq_refl) Hf). cbn.
    assert (IH' : length (filter f t) <= length (filter g t))
      by (apply IH; intros x Hx; exact (H x (or_intror Hx))). lia.
  - assert (IH' : length (filter f t) <= length (filter g t))
      by (apply IH; intros x Hx; exact (H x (or_intror Hx))).
    destruct (g a); cbn; lia.
Qed.

Lemma flat_map_length_le {A B C} (f : A -> list B) (g : A -> list C) (l : list A) :
  (forall x, In x l -> length (f x) <= length (g x)) ->
  length (flat_map f l) <= length (flat_map g l).
Proof.
  induction l as [|a t IH]; intro H; [ cbn; lia |].
  cbn. rewrite !length_app.
  assert (IH' : length (flat_map f t) <= length (flat_map g t))
    by (apply IH; intros x Hx; exact (H x (or_intror Hx))).
  pose proof (H a (or_introl eq_refl)). lia.
Qed.

Lemma filter_filter {A} (f g : A -> bool) (l : list A) :
  filter f (filter g l) = filter (fun x => andb (g x) (f x)) l.
Proof.
  induction l as [|a t IH]; [ reflexivity |].
  cbn. destruct (g a) eqn:Hg; cbn; destruct (f a); cbn; rewrite IH; reflexivity.
Qed.

Lemma map_nth_error_inv {A B} (f : A -> B) (l : list A) (n : nat) (y : B) :
  nth_error (map f l) n = Some y -> exists x, nth_error l n = Some x /\ y = f x.
Proof.
  revert n; induction l as [|a t IH]; intros [|n'] H; try discriminate H.
  - injection H as <-. exists a. split; reflexivity.
  - cbn in H. exact (IH n' H).
Qed.

Lemma nodup_map_nth {A B} (f : A -> B) (l : list A) (i j : nat) (x y : A) :
  NoDup (map f l) -> nth_error l i = Some x -> nth_error l j = Some y ->
  f x = f y -> i = j.
Proof.
  intros Hnd Hi Hj Hf.
  assert (Hi' : nth_error (map f l) i = Some (f x)) by (apply map_nth_error; exact Hi).
  assert (Hj' : nth_error (map f l) j = Some (f y)) by (apply map_nth_error; exact Hj).
  rewrite Hf in Hi'.
  apply (NoDup_nth_error (map f l)); [ exact Hnd | | congruence ].
  apply nth_error_Some. rewrite Hi'. discriminate.
Qed.

(* a total singleton emitter enumerates positionally: position k of the image is the image of position k *)
Lemma flatmap_singleton_nth {A B} (f : A -> option B) (l : list A) :
  (forall x, In x l -> f x <> None) ->
  forall k x, nth_error l k = Some x ->
  exists y, nth_error (flat_map (fun a => match f a with Some b => [b] | None => [] end) l) k = Some y
            /\ f x = Some y.
Proof.
  induction l as [|a t IH]; intros Htot k x Hk; [ destruct k; discriminate Hk |].
  destruct (f a) as [b|] eqn:Hf;
    [| exfalso; exact (Htot a (or_introl eq_refl) Hf) ].
  destruct k as [|k'].
  - injection Hk as <-. exists b. cbn. rewrite Hf. cbn.
    split; reflexivity.
  - cbn in Hk. cbn. rewrite Hf. cbn.
    apply (IH (fun x Hx => Htot x (or_intror Hx)) k' x Hk).
Qed.

(* the retained package roster is positional: each package sits at its exact position *)
Lemma packages_nth {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx)
  (pr : PI.PackageRef s) :
  nth_error (PI.packages s) (PI.pr_pos pr) = Some pr.
Proof.
  assert (Hseq : nth_error (seq 0 (PI.package_count s)) (PI.pr_pos pr) = Some (PI.pr_pos pr)).
  { rewrite (nth_error_nth' (seq 0 (PI.package_count s)) 0);
      [| rewrite length_seq; exact (PI.pr_lt pr) ].
    rewrite seq_nth; [ reflexivity | exact (PI.pr_lt pr) ]. }
  assert (Htot : forall n, In n (seq 0 (PI.package_count s)) -> PI.mk_packageref s n <> None).
  { intros n Hn. apply in_seq in Hn. unfold PI.mk_packageref.
    destruct (lt_dec n (PI.package_count s)); [ discriminate | lia ]. }
  destruct (flatmap_singleton_nth (PI.mk_packageref s) (seq 0 (PI.package_count s)) Htot
              (PI.pr_pos pr) (PI.pr_pos pr) Hseq) as [y [Hy Hmk]].
  unfold PI.packages. rewrite Hy. f_equal.
  unfold PI.mk_packageref in Hmk.
  destruct (lt_dec (PI.pr_pos pr) (PI.package_count s)); [| discriminate Hmk ].
  injection Hmk as <-. apply PI.pkgref_positional. reflexivity.
Qed.

(* every ref an event emits carries that exact site *)
Lemma refs_scan_site {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) (er : EstablishmentRef bp) :
  forall l k (E : l = skipn k (event_adds site)),
  In er (refs_scan site k l E) -> es_site er = site.
Proof.
  induction l as [|e0 rest IH]; intros k E Hin; [ destruct Hin |].
  destruct Hin as [<-|Hin]; [ reflexivity | exact (IH _ _ Hin) ].
Qed.

Lemma refs_of_event_site {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) (er : EstablishmentRef bp) :
  In er (refs_of_event site) -> es_site er = site.
Proof. apply refs_scan_site. Qed.

(* the emitted refs project the event's exact additions, in order *)
Lemma refs_scan_ests {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) :
  forall l k (E : l = skipn k (event_adds site)),
  map es_est (refs_scan site k l E) = l.
Proof.
  induction l as [|e0 rest IH]; intros k E; [ reflexivity |].
  cbn [refs_scan map]. f_equal. exact (IH (S k) _).
Qed.

Lemma refs_of_event_adds {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) :
  map es_est (refs_of_event site) = event_adds site.
Proof. apply refs_scan_ests. Qed.

(* every ref an event emits projects an exact retained addition of that event *)
Lemma refs_of_event_est_in {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) (er : EstablishmentRef bp) :
  In er (refs_of_event site) -> In (es_est er) (event_adds site).
Proof.
  intro Hin. rewrite <- refs_of_event_adds. apply in_map. exact Hin.
Qed.

Lemma refs_of_event_empty {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) :
  event_adds site = [] -> refs_of_event site = [].
Proof.
  intro H. pose proof (refs_of_event_adds site) as Hm. rewrite H in Hm.
  destruct (refs_of_event site); [ reflexivity | discriminate Hm ].
Qed.

(* the exact additions of one block event: total, no option — the eix-th event's ordered additions *)
Lemma blk_ev_row_eq {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix eix : nat) (H : eix < trace_event_count bp tix)
  (tr : TraceRow s) (ev : BlockEv s) :
  nth_error (bp_traces bp) tix = Some tr -> nth_error (trow_evs tr) eix = Some ev ->
  blk_ev_row bp tix eix H = ev.
Proof.
  intros Htr Hev. unfold blk_ev_row.
  set (o := nth_error (bp_traces bp) tix) in *.
  change (trace_event_count bp tix)
    with (match o with Some tr0 => length (trow_evs tr0) | None => 0 end) in H.
  clearbody o. destruct o as [tr0|]; [| discriminate Htr ].
  injection Htr as ->.
  assert (Heq : Some (Index.Model.nth_lt (trow_evs tr) eix H) = Some ev)
    by (rewrite <- (Index.Model.nth_lt_nth_error (trow_evs tr) eix H); exact Hev).
  injection Heq as Heq. exact Heq.
Qed.
Lemma blk_ev_block_eq {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix eix : nat) (H : eix < trace_event_count bp tix)
  (tr : TraceRow s) :
  nth_error (bp_traces bp) tix = Some tr -> blk_ev_block bp tix eix H = trow_block tr.
Proof.
  intro Htr. unfold blk_ev_block.
  set (o := nth_error (bp_traces bp) tix) in *.
  change (trace_event_count bp tix)
    with (match o with Some tr0 => length (trow_evs tr0) | None => 0 end) in H.
  clearbody o. destruct o as [tr0|]; [| discriminate Htr ].
  injection Htr as ->. reflexivity.
Qed.
Lemma event_adds_block {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix eix : nat) (H : eix < trace_event_count bp tix)
  (tr : TraceRow s) (ev : BlockEv s) :
  nth_error (bp_traces bp) tix = Some tr -> nth_error (trow_evs tr) eix = Some ev ->
  event_adds (BlockEventAt tix eix H) = bev_adds (trow_block tr) ev.
Proof.
  intros Htr Hev. cbn [event_adds].
  rewrite (blk_ev_block_eq bp tix eix H tr Htr).
  rewrite (blk_ev_row_eq bp tix eix H tr ev Htr Hev). reflexivity.
Qed.

(* the exact additions of one package event: total, the eix-th ledger event's additions *)
Lemma pkg_row_eq {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pix eix : nat) (H : eix < pkg_event_count bp pix)
  (l : list (PkgEv s)) (row : PkgEv s) :
  nth_error (bp_ledgers bp) pix = Some l -> nth_error l eix = Some row ->
  pkg_row bp pix eix H = row.
Proof.
  intros Hl Hrow. unfold pkg_row.
  set (o := nth_error (bp_ledgers bp) pix) in *.
  change (pkg_event_count bp pix)
    with (match o with Some l0 => length l0 | None => 0 end) in H.
  clearbody o. destruct o as [l0|]; [| discriminate Hl ].
  injection Hl as ->.
  assert (Heq : Some (Index.Model.nth_lt l eix H) = Some row)
    by (rewrite <- (Index.Model.nth_lt_nth_error l eix H); exact Hrow).
  injection Heq as Heq. exact Heq.
Qed.
Lemma event_adds_pkg {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pix eix : nat) (H : eix < pkg_event_count bp pix)
  (l : list (PkgEv s)) (row : PkgEv s) :
  nth_error (bp_ledgers bp) pix = Some l -> nth_error l eix = Some row ->
  event_adds (PkgEventAt pix eix H) = snd row.
Proof.
  intros Hl Hrow. cbn [event_adds]. rewrite (pkg_row_eq bp pix eix H l row Hl Hrow). reflexivity.
Qed.

Lemma spec_ests_scope {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {fl : Index.Model.SpecFlavor} (sc : ScopeId s) (sp : Index.Refs.SpecRef idx fl) (e : Est s) :
  In e (spec_ests sc sp) -> est_scope e = sc.
Proof.
  unfold spec_ests. intro Hin. apply in_flat_map in Hin. destruct Hin as [x [_ Hin]].
  destruct (spec_name_est sc (projT2 x)) as [e0|] eqn:He0; [| destruct Hin ].
  destruct Hin as [<-|F]; [| destruct F ].
  exact (proj1 (spec_name_est_fields sc (projT2 x) e0 He0)).
Qed.

Lemma spec_emit_scope {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (r : Index.Core.NodeRef idx) (v : Index.Model.NodeView) (Hv : Index.Core.node_view r = v)
  (e : Est s) :
  In e (spec_emit sc r v Hv) -> est_scope e = sc.
Proof.
  destruct v; cbv beta iota delta [spec_emit];
    try (intro F; destruct F); apply spec_ests_scope.
Qed.

Lemma decl_ests_scope {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (d : Index.Core.NodeRef idx) (e : Est s) :
  In e (decl_ests sc d) -> est_scope e = sc.
Proof.
  unfold decl_ests. intro Hin. apply in_flat_map in Hin. destruct Hin as [x [_ Hin]].
  exact (spec_emit_scope sc _ _ eq_refl e Hin).
Qed.

Lemma stmt_decl_ests_scope {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (t : Index.Core.NodeRef idx) (e : Est s) :
  In e (stmt_decl_ests sc t) -> est_scope e = sc.
Proof.
  unfold stmt_decl_ests. destruct (Index.Child.child_at_opt t 0) as [ce|];
    [ apply decl_ests_scope | intro F; destruct F ].
Qed.

(* dependent boolean convoys reduce under a known scrutinee value *)
Lemma bool_convoy_true {T : Type} (X : bool) (f : X = true -> T) (g : X = false -> T) (H : X = true) :
  (match X as b return X = b -> T with true => f | false => g end) eq_refl = f H.
Proof.
  destruct X; [| discriminate H ].
  rewrite (UIP_dec Bool.bool_dec H eq_refl). reflexivity.
Qed.

Lemma bool_convoy_false {T : Type} (X : bool) (f : X = true -> T) (g : X = false -> T) (H : X = false) :
  (match X as b return X = b -> T with true => f | false => g end) eq_refl = g H.
Proof.
  destruct X; [ discriminate H |].
  rewrite (UIP_dec Bool.bool_dec H eq_refl). reflexivity.
Qed.

Lemma flat_map_map {A B C} (f : B -> list C) (g : A -> B) (l : list A) :
  flat_map f (map g l) = flat_map (fun x => f (g x)) l.
Proof. induction l as [|a t IH]; [ reflexivity | cbn; rewrite IH; reflexivity ]. Qed.

Lemma flat_map_flat_map {A B C} (g : B -> list C) (f : A -> list B) (l : list A) :
  flat_map g (flat_map f l) = flat_map (fun x => flat_map g (f x)) l.
Proof.
  induction l as [|a t IH]; [ reflexivity |].
  cbn. rewrite flat_map_app, IH. reflexivity.
Qed.

(* a positional emitter over an exact index range enumerates the underlying rows *)
Lemma flat_map_nth_gen {A B} (l : list A) (g : A -> list B) (F : nat -> list B) :
  (forall k x, nth_error l k = Some x -> F k = g x) ->
  forall t k, t = skipn k l -> flat_map F (seq k (length t)) = flat_map g t.
Proof.
  intros Hpt. induction t as [|x t' IH]; intros k Ht; [ reflexivity |].
  cbn [length seq flat_map].
  rewrite (Hpt k x (Index.Child.skipn_head_at l t' k x Ht)).
  rewrite (IH (S k) (Index.Child.skipn_tail_at l t' k x Ht)). reflexivity.
Qed.

Lemma firstn_nth_error {A} (l : list A) :
  forall n k x, nth_error (firstn n l) k = Some x -> nth_error l k = Some x.
Proof.
  induction l as [|a t IH]; intros [|n'] [|k'] x H; try discriminate H;
    [ exact H | exact (IH n' k' x H) ].
Qed.

(* the retained graph is exactly the one canonical construction: the phase pin names the builder *)
Lemma bp_ledgers_form {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : bp_ledgers bp = map (ledger_of s) (PI.packages s).
Proof. unfold bp_ledgers. rewrite (bp_canonical bp). reflexivity. Qed.

Lemma bp_traces_form {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : bp_traces bp = flat_map (traces_of_pkg s) (PI.packages s).
Proof. unfold bp_traces. rewrite (bp_canonical bp). reflexivity. Qed.

Lemma bp_consts_form {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : bp_consts bp = const_table s.
Proof. unfold bp_consts. rewrite (bp_canonical bp). reflexivity. Qed.

(* exactly one ledger per exact package, at the package's exact position *)
Lemma bp_ledgers_at {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pr : PI.PackageRef s) :
  nth_error (bp_ledgers bp) (PI.pr_pos pr) = Some (ledger_of s pr).
Proof.
  rewrite bp_ledgers_form. exact (map_nth_error _ _ _ (packages_nth s pr)).
Qed.

Lemma bp_ledgers_len {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : length (bp_ledgers bp) = length (PI.packages s).
Proof. rewrite bp_ledgers_form. apply length_map. Qed.

Lemma bp_ledgers_row {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pix : nat) (l : list (PkgEv s)) :
  nth_error (bp_ledgers bp) pix = Some l ->
  exists pr, nth_error (PI.packages s) pix = Some pr /\ l = ledger_of s pr.
Proof. rewrite bp_ledgers_form. apply map_nth_error_inv. Qed.

(* every retained ledger row is one exact canonical package event, and every such event is retained *)
Lemma ledger_row {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (row : PkgEv s) :
  In row (ledger_of s pr) ->
  exists r, In (Index.Core.nr_file r) (PI.pkg_members pr) /\ pkg_event_at s pr r = Some row.
Proof.
  unfold ledger_of. intro Hin.
  apply in_flat_map in Hin. destruct Hin as [fr [Hfr Hin]].
  apply in_flat_map in Hin. destruct Hin as [pos [_ Hin]].
  destruct (Index.Core.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
  destruct (pkg_event_at s pr r) as [row0|] eqn:Hev; [| destruct Hin ].
  destruct Hin as [<-|F]; [| destruct F ].
  exists r. rewrite (Index.Core.mk_noderef_file fr _ r Hmk). split; [ exact Hfr | exact Hev ].
Qed.

Lemma ledger_covers {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.Core.NodeRef idx) (row : PkgEv s) :
  In (Index.Core.nr_file r) (PI.pkg_members pr) ->
  pkg_event_at s pr r = Some row ->
  In row (ledger_of s pr).
Proof.
  intros Hfr Hev. unfold ledger_of.
  apply in_flat_map. exists (Index.Core.nr_file r). split; [ exact Hfr |].
  apply in_flat_map. exists (Index.Core.nr_pos r).
  split; [ apply in_seq; pose proof (nr_pos_lt r); lia |].
  rewrite <- Index.Core.nr_key_pos, Index.Core.mk_noderef_self. cbv beta iota.
  rewrite Hev. left; reflexivity.
Qed.

(* a canonical package event carries its exact top occurrence as its site *)
Lemma pkg_event_at_fst {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.Core.NodeRef idx) (row : PkgEv s) :
  pkg_event_at s pr r = Some row -> fst row = r.
Proof.
  unfold pkg_event_at. destruct (Index.Core.node_view r) as [| | | | | | | | | | | |ts|]; try discriminate.
  destruct ts.
  - intro H. injection H as <-. reflexivity.
  - destruct (make_main_est pr r); intro H; [ injection H as <-; reflexivity | discriminate H ].
Qed.

(* every addition of a canonical package event establishes at exactly that package's scope *)
Lemma pkg_event_at_scope {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.Core.NodeRef idx) (row : PkgEv s) (e : Est s) :
  pkg_event_at s pr r = Some row -> In e (snd row) ->
  est_scope e = PackageScope pr.
Proof.
  unfold pkg_event_at. destruct (Index.Core.node_view r) as [| | | | | | | | | | | |ts|]; try discriminate.
  destruct ts.
  - intro H. injection H as <-. cbn. apply stmt_decl_ests_scope.
  - destruct (make_main_est pr r) as [e0|] eqn:Hm; intro H; [| discriminate H ].
    injection H as <-. cbn. intros [<-|F]; [| destruct F ].
    exact (proj1 (proj2 (proj2 (make_main_est_some pr r e0 Hm)))).
Qed.

(* every addition of a canonical package event sites at exactly its top occurrence *)
Lemma pkg_event_at_site {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.Core.NodeRef idx) (row : PkgEv s) (e : Est s) :
  pkg_event_at s pr r = Some row -> In e (snd row) ->
  est_site e = Some r.
Proof.
  unfold pkg_event_at. destruct (Index.Core.node_view r) as [| | | | | | | | | | | |ts|]; try discriminate.
  destruct ts.
  - intro H. injection H as <-. cbn. apply stmt_decl_ests_site.
  - destruct (make_main_est pr r) as [e0|] eqn:Hm; intro H; [| discriminate H ].
    injection H as <-. cbn. intros [<-|F]; [| destruct F ].
    destruct (make_main_est_some pr r e0 Hm) as [[f Hf] [Hnode _]].
    unfold est_site. rewrite Hf, Hnode. reflexivity.
Qed.

(* the refs of a package event establish at exactly that package's scope *)
Lemma ledger_add_scope {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pix eix : nat) (pr : PI.PackageRef s) (er : EstablishmentRef bp) :
  nth_error (PI.packages s) pix = Some pr ->
  In er (pkg_ev_refs bp pix eix) ->
  est_scope (es_est er) = PackageScope pr.
Proof.
  intros Hpr Hin. unfold pkg_ev_refs in Hin. revert Hin.
  destruct (lt_dec eix (pkg_event_count bp pix)) as [H|]; intro Hin; [| destruct Hin ].
  pose proof (refs_of_event_est_in (PkgEventAt pix eix H) er Hin) as Hest.
  assert (Hl : nth_error (bp_ledgers bp) pix = Some (ledger_of s pr))
    by (rewrite bp_ledgers_form; exact (map_nth_error _ _ _ Hpr)).
  assert (Heix : eix < length (ledger_of s pr)).
  { pose proof H as H'. unfold pkg_event_count in H'. rewrite Hl in H'. exact H'. }
  set (row := Index.Model.nth_lt (ledger_of s pr) eix Heix).
  assert (Hrow : nth_error (ledger_of s pr) eix = Some row) by (apply Index.Model.nth_lt_nth_error).
  rewrite (event_adds_pkg bp pix eix H (ledger_of s pr) row Hl Hrow) in Hest.
  destruct (ledger_row pr row (nth_error_In _ _ Hrow)) as [r [_ Hev]].
  exact (pkg_event_at_scope pr r row (es_est er) Hev Hest).
Qed.

(* every retained trace row is the canonical fold of its exact block over its package's final environment *)
Lemma bp_traces_row {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tr : TraceRow s) :
  In tr (bp_traces bp) ->
  exists (pr : PI.PackageRef s) (r : Index.Core.NodeRef idx)
         (Hb : Index.Core.is_block_view (Index.Core.node_view r) = true),
    In pr (PI.packages s) /\ In (Index.Core.nr_file r) (PI.pkg_members pr)
    /\ tr = (Index.Refs.mkBlockRef r Hb, PI.pr_pos pr,
             block_fold s (Index.Refs.mkBlockRef r Hb) (Index.Child.all_children r)
               (pkg_env_of s pr)).
Proof.
  rewrite bp_traces_form. intro Hin.
  apply in_flat_map in Hin. destruct Hin as [pr [Hpr Hin]].
  unfold traces_of_pkg in Hin. cbv zeta in Hin.
  apply in_flat_map in Hin. destruct Hin as [fr [Hfr Hin]].
  apply in_flat_map in Hin. destruct Hin as [pos [_ Hin]].
  destruct (Index.Core.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
  destruct (Bool.bool_dec (Index.Core.is_block_view (Index.Core.node_view r)) true) as [Hb|Hneq].
  - rewrite (bool_convoy_true _ _ _ Hb) in Hin.
    destruct Hin as [He|F]; [| destruct F ].
    exists pr, r, Hb.
    rewrite <- (Index.Core.mk_noderef_file fr _ r Hmk) in Hfr.
    split; [ exact Hpr |]. split; [ exact Hfr |]. exact (eq_sym He).
  - rewrite (bool_convoy_false _ _ _ (Bool.not_true_is_false _ Hneq)) in Hin. destruct Hin.
Qed.

(* the trace of every represented block exists in the phase *)
Lemma traces_cover {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (r : Index.Core.NodeRef idx) (Hb : Index.Core.is_block_view (Index.Core.node_view r) = true) :
  In (Index.Refs.mkBlockRef r Hb, PI.pr_pos (PI.package_of_file s (Index.Core.nr_file r)),
      block_fold s (Index.Refs.mkBlockRef r Hb) (Index.Child.all_children r)
        (pkg_env_of s (PI.package_of_file s (Index.Core.nr_file r))))
     (bp_traces bp).
Proof.
  rewrite bp_traces_form.
  set (pr := PI.package_of_file s (Index.Core.nr_file r)).
  apply in_flat_map. exists pr. split; [ apply PI.packages_complete |].
  unfold traces_of_pkg. cbv zeta.
  apply in_flat_map. exists (Index.Core.nr_file r). split; [ apply PI.pkg_members_of_file |].
  apply in_flat_map. exists (Index.Core.nr_pos r).
  split; [ apply in_seq; pose proof (nr_pos_lt r); lia |].
  rewrite <- Index.Core.nr_key_pos, Index.Core.mk_noderef_self. cbv beta iota.
  rewrite (bool_convoy_true _ _ _ Hb). left; reflexivity.
Qed.

(* one event per direct statement: the canonical fold maps the block's children one to one *)
Lemma block_fold_length {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.Refs.BlockRef idx) :
  forall (l : list { o : nat & Index.Child.ChildAt (Index.Refs.bl_node br) o }) (env : list (Est s)),
  length (block_fold s br l env) = length l.
Proof.
  induction l as [|x t IH]; intro env; [ reflexivity |].
  cbn. rewrite IH. reflexivity.
Qed.

Lemma block_fold_nth {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.Refs.BlockRef idx) :
  forall (l : list { o : nat & Index.Child.ChildAt (Index.Refs.bl_node br) o }) (env : list (Est s)) (j : nat)
         (x : { o : nat & Index.Child.ChildAt (Index.Refs.bl_node br) o }),
  nth_error l j = Some x ->
  exists env',
    nth_error (block_fold s br l env) j
    = Some (block_event s br env' (Index.Child.ca_child (projT2 x))
              (Index.Core.node_view (Index.Child.ca_child (projT2 x))) eq_refl).
Proof.
  induction l as [|x0 t IH]; intros env j x Hj; [ destruct j; discriminate Hj |].
  destruct j as [|j'].
  - injection Hj as <-. eexists. reflexivity.
  - cbn in Hj. cbn. exact (IH _ j' x Hj).
Qed.

(* the exact inverse: the j-th event is the canonical event of the j-th child over the exact threaded environment *)
Lemma block_fold_nth_env {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.Refs.BlockRef idx) :
  forall (l : list { o : nat & Index.Child.ChildAt (Index.Refs.bl_node br) o }) (env : list (Est s)) (j : nat)
         (ev : BlockEv s),
  nth_error (block_fold s br l env) j = Some ev ->
  exists x,
    nth_error l j = Some x
    /\ ev = block_event s br
              (env ++ flat_map (bev_adds br) (firstn j (block_fold s br l env)))
              (Index.Child.ca_child (projT2 x)) (Index.Core.node_view (Index.Child.ca_child (projT2 x))) eq_refl.
Proof.
  induction l as [|x0 t IH]; intros env j ev Hj; [ destruct j; discriminate Hj |].
  destruct j as [|j'].
  - injection Hj as <-. exists x0. split; [ reflexivity |].
    cbn [firstn flat_map]. rewrite app_nil_r. reflexivity.
  - cbn in Hj. destruct (IH _ j' ev Hj) as [x [Hx He]].
    exists x. split; [ exact Hx |].
    rewrite He. cbn [block_fold firstn flat_map].
    rewrite app_assoc. reflexivity.
Qed.

(* the exact occurrence an event names, uniform over its kinds *)
Lemma block_event_node {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.Refs.BlockRef idx) (env : list (Est s)) (c : Index.Core.NodeRef idx)
  (v : Index.Model.NodeView) (Hv : Index.Core.node_view c = v) :
  bev_node (block_event s br env c v Hv) = c.
Proof.
  destruct v; cbn; try reflexivity.
  match goal with sh0 : Index.Model.StmtShape |- _ => destruct sh0; reflexivity end.
Qed.

(* the canonical short event of a short statement, evaluated at its exact known view *)
Lemma block_event_short_eval {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.Refs.BlockRef idx) (env : list (Est s)) (c : Index.Core.NodeRef idx)
  (v : Index.Model.NodeView) (Hv : Index.Core.node_view c = v) (nn nv : nat) :
  v = Index.Model.VStmt (Index.Model.SSShort nn nv) ->
  exists Hv0 : Index.Core.node_view c = Index.Model.VStmt (Index.Model.SSShort nn nv),
    block_event s br env c v Hv
    = BEvShort (Index.Refs.mkShortStmtRef c nn nv Hv0)
        (short_decide_rows env (Index.Refs.mkShortStmtRef c nn nv Hv0)).
Proof. intro E. revert Hv. subst v. intro Hv. exists Hv. reflexivity. Qed.

Lemma block_event_decl_eval {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.Refs.BlockRef idx) (env : list (Est s)) (c : Index.Core.NodeRef idx)
  (v : Index.Model.NodeView) (Hv : Index.Core.node_view c = v) :
  v = Index.Model.VStmt Index.Model.SSDecl ->
  block_event s br env c v Hv = BEvDecl (BlockScope br) c (decl_decide_rows env c).
Proof. intro E. revert Hv. subst v. intro Hv. reflexivity. Qed.

Lemma block_event_decl_view {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.Refs.BlockRef idx) (env : list (Est s)) (c : Index.Core.NodeRef idx)
  (v : Index.Model.NodeView) (Hv : Index.Core.node_view c = v) (sc : ScopeId s) (t : Index.Core.NodeRef idx)
  (rows : list DeclBinderDecisionData) :
  block_event s br env c v Hv = BEvDecl sc t rows -> v = Index.Model.VStmt Index.Model.SSDecl.
Proof.
  intro H. destruct v; try discriminate H.
  match goal with sh : Index.Model.StmtShape |- _ => destruct sh end; try discriminate H. reflexivity.
Qed.

(* every addition of a canonical block event establishes at its exact block scope *)
Lemma block_event_adds_scope {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (br br' : Index.Refs.BlockRef idx) (env : list (Est s)) (c : Index.Core.NodeRef idx)
  (v : Index.Model.NodeView) (Hv : Index.Core.node_view c = v) (e : Est s) :
  In e (bev_adds br' (block_event s br env c v Hv)) ->
  est_scope e = BlockScope br \/ est_scope e = BlockScope br'.
Proof.
  destruct v; cbn; try (intro F; destruct F).
  match goal with sh0 : Index.Model.StmtShape |- _ => destruct sh0 as [| |nn nv] end; cbn.
  - intro F; destruct F.
  - intro Hin. left.
    exact (decl_rows_adds_scope (BlockScope br) c _ e Hin).
  - intro Hin. right.
    exact (short_rows_adds_scope br' _ _ e Hin).
Qed.

(* the refs of a block event establish at exactly that trace's block scope *)
Lemma trace_add_scope {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix eix : nat) (tr : TraceRow s) (er : EstablishmentRef bp) :
  nth_error (bp_traces bp) tix = Some tr ->
  In er (block_ev_refs bp tix eix) ->
  est_scope (es_est er) = BlockScope (trow_block tr).
Proof.
  intros Htr Hin. unfold block_ev_refs in Hin. revert Hin.
  destruct (lt_dec eix (trace_event_count bp tix)) as [Hlt|]; intro Hin; [| destruct Hin ].
  pose proof (refs_of_event_est_in (BlockEventAt tix eix Hlt) er Hin) as Hest.
  assert (Heix : eix < length (trow_evs tr)).
  { pose proof Hlt as Hlt'. unfold trace_event_count in Hlt'. rewrite Htr in Hlt'. exact Hlt'. }
  remember (Index.Model.nth_lt (trow_evs tr) eix Heix) as ev eqn:Hevdef.
  assert (Hev : nth_error (trow_evs tr) eix = Some ev) by (rewrite Hevdef; apply Index.Model.nth_lt_nth_error).
  rewrite (event_adds_block bp tix eix Hlt tr ev Htr Hev) in Hest.
  destruct (bp_traces_row bp tr (nth_error_In _ _ Htr)) as [pr [r [Hb [_ [_ Hform]]]]].
  assert (Hevs : trow_evs tr = block_fold s (Index.Refs.mkBlockRef r Hb) (Index.Child.all_children r)
                                 (pkg_env_of s pr)) by (rewrite Hform; reflexivity).
  assert (Hblk : trow_block tr = Index.Refs.mkBlockRef r Hb) by (rewrite Hform; reflexivity).
  rewrite Hevs in Hev.
  destruct (block_fold_nth_env _ _ _ _ _ Hev) as [x [_ He]].
  rewrite He in Hest. rewrite Hblk in Hest.
  destruct (block_event_adds_scope _ _ _ _ _ _ _ Hest) as [Hsc|Hsc]; rewrite Hblk; exact Hsc.
Qed.

(* the final package environment is exactly the ledger's additions, with retained provenance *)
Lemma package_env_ests {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pr : PI.PackageRef s) :
  map es_est (package_env_refs bp pr) = pkg_env_of s pr.
Proof.
  unfold package_env_refs, ledger_refs, pkg_env_of.
  assert (Hl : nth_error (bp_ledgers bp) (PI.pr_pos pr) = Some (ledger_of s pr)) by (apply bp_ledgers_at).
  assert (Hcount : pkg_event_count bp (PI.pr_pos pr) = length (ledger_of s pr))
    by (unfold pkg_event_count; rewrite Hl; reflexivity).
  rewrite Hcount, map_flat_map.
  assert (Hpt : forall k row, nth_error (ledger_of s pr) k = Some row ->
            map es_est (pkg_ev_refs bp (PI.pr_pos pr) k) = snd row).
  { intros k row Hk.
    unfold pkg_ev_refs. destruct (lt_dec k (pkg_event_count bp (PI.pr_pos pr))) as [H|Hno].
    - rewrite refs_of_event_adds. exact (event_adds_pkg bp (PI.pr_pos pr) k H (ledger_of s pr) row Hl Hk).
    - exfalso. apply Hno. rewrite Hcount. exact (nth_error_lt _ _ _ Hk). }
  exact (flat_map_nth_gen (ledger_of s pr) (fun row => snd row) _ Hpt
           (ledger_of s pr) 0 (eq_sym (skipn_O _))).
Qed.

(* the initial state is exactly the package seed; each successor adds exactly its event's refs *)
Lemma state_refs_zero {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix : nat) (tr : TraceRow s) :
  nth_error (bp_traces bp) tix = Some tr ->
  state_refs bp tix 0 = ledger_refs bp (trow_pkg tr).
Proof.
  intro H. unfold state_refs. rewrite H. cbn [seq flat_map]. apply app_nil_r.
Qed.

Lemma state_refs_succ {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix i : nat) (tr : TraceRow s) :
  nth_error (bp_traces bp) tix = Some tr ->
  state_refs bp tix (S i) = state_refs bp tix i ++ block_ev_refs bp tix i.
Proof.
  intro H. unfold state_refs. rewrite H.
  rewrite seq_S. cbn [Nat.add]. rewrite flat_map_app.
  cbn [flat_map]. rewrite app_nil_r. apply app_assoc.
Qed.

(* cuts beyond the statement count add nothing: the trace has exactly statement_count + 1 states *)
Lemma state_refs_saturates {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix cut : nat) (tr : TraceRow s) :
  nth_error (bp_traces bp) tix = Some tr ->
  length (trow_evs tr) <= cut ->
  state_refs bp tix cut = state_refs bp tix (length (trow_evs tr)).
Proof.
  intros H Hle. unfold state_refs. rewrite H.
  replace (seq 0 cut)
    with (seq 0 (length (trow_evs tr)) ++ seq (length (trow_evs tr)) (cut - length (trow_evs tr)))
    by (rewrite <- seq_app; f_equal; lia).
  rewrite flat_map_app.
  rewrite (flat_map_nil_all _ (seq (length (trow_evs tr)) (cut - length (trow_evs tr))));
    [ rewrite app_nil_r; reflexivity |].
  intros eix Hin. apply in_seq in Hin.
  unfold block_ev_refs. destruct (lt_dec eix (trace_event_count bp tix)) as [Hlt|]; [| reflexivity ].
  exfalso. revert Hlt. unfold trace_event_count. rewrite H. lia.
Qed.

(* a state member is a package-seed ref or the ref of an exactly earlier event; nothing future leaks in *)
Lemma state_member_site {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix cut : nat) (er : EstablishmentRef bp) :
  In er (state_refs bp tix cut) ->
  (exists pix eix (H : eix < pkg_event_count bp pix), es_site er = PkgEventAt pix eix H)
  \/ (exists eix (H : eix < trace_event_count bp tix), es_site er = BlockEventAt tix eix H /\ eix < cut).
Proof.
  unfold state_refs.
  destruct (nth_error (bp_traces bp) tix) as [tr|]; [| intro F; destruct F ].
  intro Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - left. unfold ledger_refs in Hin. apply in_flat_map in Hin. destruct Hin as [eix [_ Hin]].
    unfold pkg_ev_refs in Hin. revert Hin.
    destruct (lt_dec eix (pkg_event_count bp (trow_pkg tr))) as [Hpk|]; intro Hin; [| destruct Hin ].
    exists (trow_pkg tr), eix, Hpk. exact (refs_of_event_site _ er Hin).
  - right. apply in_flat_map in Hin. destruct Hin as [eix [Hseq Hin]]. apply in_seq in Hseq.
    unfold block_ev_refs in Hin. revert Hin.
    destruct (lt_dec eix (trace_event_count bp tix)) as [Hbk|]; intro Hin; [| destruct Hin ].
    exists eix, Hbk. split; [ exact (refs_of_event_site _ er Hin) | lia ].
Qed.

Lemma state_covers {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix cut eix : nat) (tr : TraceRow s) (er : EstablishmentRef bp) :
  nth_error (bp_traces bp) tix = Some tr -> eix < cut ->
  In er (block_ev_refs bp tix eix) ->
  In er (state_refs bp tix cut).
Proof.
  intros Htr Hlt Hin. unfold state_refs. rewrite Htr.
  apply in_or_app. right.
  apply in_flat_map. exists eix. split; [ apply in_seq; lia | exact Hin ].
Qed.

(* the est projection of a state: the exact final package environment, then the earlier additions in order *)
Lemma state_ests {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix cut : nat) (tr : TraceRow s) :
  nth_error (bp_traces bp) tix = Some tr ->
  cut <= length (trow_evs tr) ->
  map es_est (state_refs bp tix cut)
  = map es_est (ledger_refs bp (trow_pkg tr))
    ++ flat_map (bev_adds (trow_block tr)) (firstn cut (trow_evs tr)).
Proof.
  intros Htr Hle. unfold state_refs. rewrite Htr.
  rewrite map_app. f_equal.
  rewrite map_flat_map.
  replace (seq 0 cut) with (seq 0 (length (firstn cut (trow_evs tr))))
    by (rewrite length_firstn; f_equal; lia).
  assert (Hpt : forall k ev, nth_error (firstn cut (trow_evs tr)) k = Some ev ->
            map es_est (block_ev_refs bp tix k) = bev_adds (trow_block tr) ev).
  { intros k ev Hk.
    pose proof (firstn_nth_error _ _ _ _ Hk) as Hk'.
    unfold block_ev_refs. destruct (lt_dec k (trace_event_count bp tix)) as [Hlt|Hno].
    - rewrite refs_of_event_adds. exact (event_adds_block bp tix k Hlt tr ev Htr Hk').
    - exfalso. apply Hno. unfold trace_event_count. rewrite Htr. exact (nth_error_lt _ _ _ Hk'). }
  exact (flat_map_nth_gen (firstn cut (trow_evs tr)) (bev_adds (trow_block tr)) _ Hpt
           (firstn cut (trow_evs tr)) 0 (eq_sym (skipn_O _))).
Qed.

(* a no-binding event moves the cut but adds nothing: distinct identities, equal member projections *)
Lemma state_refs_expr_step {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix i : nat) (tr : TraceRow s) (r : Index.Core.NodeRef idx) :
  nth_error (bp_traces bp) tix = Some tr ->
  nth_error (trow_evs tr) i = Some (BEvExpr r) ->
  state_refs bp tix (S i) = state_refs bp tix i.
Proof.
  intros Htr Hev.
  rewrite (state_refs_succ bp tix i tr Htr).
  assert (Hlt : i < trace_event_count bp tix)
    by (unfold trace_event_count; rewrite Htr; apply (nth_error_lt _ _ _ Hev)).
  assert (Hempty : block_ev_refs bp tix i = []).
  { unfold block_ev_refs. destruct (lt_dec i (trace_event_count bp tix)) as [Hlt'|]; [| reflexivity ].
    apply refs_of_event_empty.
    rewrite (event_adds_block bp tix i Hlt' tr (BEvExpr r) Htr Hev). reflexivity. }
  rewrite Hempty. apply app_nil_r.
Qed.

Lemma nodup_map_inj {A B} (f : A -> B) (l : list A) :
  (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros Hinj Hnd. induction Hnd as [|x t Hx Hnd IH]; [ constructor |].
  cbn. constructor; [| exact IH ].
  intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Hy Hin]].
  apply Hinj in Hy. subst y. exact (Hx Hin).
Qed.

Lemma nodup_map_impl {A B C} (f : A -> B) (g : A -> C) (l : list A) :
  (forall x y, In x l -> In y l -> f x = f y -> g x = g y) ->
  NoDup (map g l) -> NoDup (map f l).
Proof.
  induction l as [|a t IH]; intros Himpl Hnd; [ constructor |].
  cbn in Hnd |- *. inversion Hnd as [|? ? Hga Hnd']; subst.
  constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Hy Hin]].
    apply Hga. apply in_map_iff. exists y. split; [| exact Hin ].
    symmetry. apply (Himpl a y (or_introl eq_refl) (or_intror Hin)). symmetry. exact Hy.
  - apply IH; [| exact Hnd' ].
    intros x y Hx Hy. exact (Himpl x y (or_intror Hx) (or_intror Hy)).
Qed.

Lemma nodup_app_disjoint {A} (a b : list A) :
  NoDup a -> NoDup b -> (forall x, In x a -> In x b -> False) -> NoDup (a ++ b).
Proof.
  induction a as [|x t IH]; intros Ha Hb Hdis; [ exact Hb |].
  inversion Ha as [|? ? Hx Ha']; subst. cbn. constructor.
  - intro Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin];
      [ exact (Hx Hin) | exact (Hdis x (or_introl eq_refl) Hin) ].
  - apply IH; [ exact Ha' | exact Hb |].
    intros y Hy Hyb. exact (Hdis y (or_intror Hy) Hyb).
Qed.

(* a canonical package event's additions are duplicate-free *)
Lemma pkg_event_at_nodup {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.Core.NodeRef idx) (row : PkgEv s) :
  pkg_event_at s pr r = Some row -> NoDup (snd row).
Proof.
  unfold pkg_event_at. destruct (Index.Core.node_view r) as [| | | | | | | | | | | |ts|]; try discriminate.
  destruct ts.
  - intro H. injection H as <-. apply stmt_decl_ests_nodup.
  - destruct (make_main_est pr r) as [e0|]; intro H; [| discriminate H ].
    injection H as <-. cbn. repeat constructor. intro F; destruct F.
Qed.

(* each package ledger names each top occurrence at most once *)
Lemma ledger_nodes_nodup {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) : NoDup (map fst (ledger_of s pr)).
Proof.
  unfold ledger_of. rewrite map_flat_map.
  apply (flat_map_nodup_key _ Index.Core.nr_file (fun fr => fr));
    [ rewrite map_id; apply pkg_members_nodup | |].
  - intros fr _. rewrite map_flat_map.
    apply (flat_map_nodup_key _ Index.Core.nr_pos (fun pos => pos));
      [ rewrite map_id; apply seq_NoDup | |].
    + intros pos _.
      destruct (Index.Core.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| constructor ].
      destruct (pkg_event_at s pr r) as [row|]; cbn; repeat constructor. intro F; destruct F.
    + intros pos rn _ Hin.
      destruct (Index.Core.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
      destruct (pkg_event_at s pr r) as [row|] eqn:Hev; [| destruct Hin ].
      destruct Hin as [<-|F]; [| destruct F ].
      rewrite (pkg_event_at_fst pr r row Hev).
      exact (noderef_pos_of_key r pos (mk_noderef_key fr _ r Hmk)).
  - intros fr rn _ Hin. rewrite map_flat_map in Hin.
    apply in_flat_map in Hin. destruct Hin as [pos [_ Hin]].
    destruct (Index.Core.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
    destruct (pkg_event_at s pr r) as [row|] eqn:Hev; [| destruct Hin ].
    destruct Hin as [<-|F]; [| destruct F ].
    rewrite (pkg_event_at_fst pr r row Hev).
    exact (Index.Core.mk_noderef_file fr _ r Hmk).
Qed.

(* the final package environment is duplicate-free: one establishment per exact source site *)
Lemma pkg_env_nodup {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) : NoDup (pkg_env_of s pr).
Proof.
  unfold pkg_env_of.
  apply (flat_map_nodup_key _ est_site (fun row => Some (fst row))).
  - apply (nodup_map_impl _ (fun row => fst row));
      [ intros x y _ _ H; injection H as H; exact H | apply ledger_nodes_nodup ].
  - intros row Hin.
    destruct (ledger_row pr row Hin) as [r [_ Hev]].
    exact (pkg_event_at_nodup pr r row Hev).
  - intros row e Hin He.
    destruct (ledger_row pr row Hin) as [r [_ Hev]].
    rewrite (pkg_event_at_site pr r row e Hev He).
    rewrite (pkg_event_at_fst pr r row Hev). reflexivity.
Qed.

(* exactly one block trace per exact block *)
Lemma traces_nodes_nodup {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) :
  NoDup (map (fun tr => Index.Refs.bl_node (trow_block tr)) (bp_traces bp)).
Proof.
  rewrite bp_traces_form, map_flat_map.
  apply (flat_map_nodup_key _ (fun r => PI.package_of_file s (Index.Core.nr_file r)) (fun pr => pr));
    [ rewrite map_id; apply packages_nodup | |].
  - intros pr _. unfold traces_of_pkg. cbv zeta. rewrite map_flat_map.
    apply (flat_map_nodup_key _ Index.Core.nr_file (fun fr => fr));
      [ rewrite map_id; apply pkg_members_nodup | |].
    + intros fr _. rewrite map_flat_map.
      apply (flat_map_nodup_key _ Index.Core.nr_pos (fun pos => pos));
        [ rewrite map_id; apply seq_NoDup | |].
      * intros pos _.
        destruct (Index.Core.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| constructor ].
        destruct (Bool.bool_dec (Index.Core.is_block_view (Index.Core.node_view r)) true) as [Hb|Hneq];
          [ rewrite (bool_convoy_true _ _ _ Hb)
          | rewrite (bool_convoy_false _ _ _ (Bool.not_true_is_false _ Hneq)) ];
          cbn; repeat constructor. intro F; destruct F.
      * intros pos rn _ Hin.
        destruct (Index.Core.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
        destruct (Bool.bool_dec (Index.Core.is_block_view (Index.Core.node_view r)) true) as [Hb|Hneq];
          [ rewrite (bool_convoy_true _ _ _ Hb) in Hin
          | rewrite (bool_convoy_false _ _ _ (Bool.not_true_is_false _ Hneq)) in Hin; destruct Hin ].
        destruct Hin as [<-|F]; [| destruct F ].
        exact (noderef_pos_of_key r pos (mk_noderef_key fr _ r Hmk)).
    + intros fr rn _ Hin. rewrite map_flat_map in Hin.
      apply in_flat_map in Hin. destruct Hin as [pos [_ Hin]].
      destruct (Index.Core.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
      destruct (Bool.bool_dec (Index.Core.is_block_view (Index.Core.node_view r)) true) as [Hb|Hneq];
        [ rewrite (bool_convoy_true _ _ _ Hb) in Hin
        | rewrite (bool_convoy_false _ _ _ (Bool.not_true_is_false _ Hneq)) in Hin; destruct Hin ].
      destruct Hin as [<-|F]; [| destruct F ].
      exact (Index.Core.mk_noderef_file fr _ r Hmk).
  - intros pr rn Hpr Hin.
    apply in_map_iff in Hin. destruct Hin as [tr [Hnode Hin]].
    unfold traces_of_pkg in Hin. cbv zeta in Hin.
    apply in_flat_map in Hin. destruct Hin as [fr [Hfr Hin]].
    apply in_flat_map in Hin. destruct Hin as [pos [_ Hin]].
    destruct (Index.Core.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
    destruct (Bool.bool_dec (Index.Core.is_block_view (Index.Core.node_view r)) true) as [Hb|Hneq];
      [ rewrite (bool_convoy_true _ _ _ Hb) in Hin
      | rewrite (bool_convoy_false _ _ _ (Bool.not_true_is_false _ Hneq)) in Hin; destruct Hin ].
    destruct Hin as [<-|F]; [| destruct F ].
    cbn in Hnode. subst rn.
    rewrite (Index.Core.mk_noderef_file fr _ r Hmk).
    exact (PI.package_of_file_member s pr fr Hfr).
Qed.

Lemma trace_at_unique {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (i j : nat) (tri trj : TraceRow s) :
  nth_error (bp_traces bp) i = Some tri -> nth_error (bp_traces bp) j = Some trj ->
  Index.Refs.bl_node (trow_block tri) = Index.Refs.bl_node (trow_block trj) -> i = j.
Proof.
  intros Hi Hj He.
  exact (nodup_map_nth _ _ i j tri trj (traces_nodes_nodup bp) Hi Hj He).
Qed.

(* one located trace: the exact ordinal, row, and retention pin of the first row satisfying a test *)
Record TraceHit {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pred : TraceRow s -> bool) : Type := mk_trace_hit {
  th_ord : nat ;
  th_row : TraceRow s ;
  th_at  : nth_error (bp_traces bp) th_ord = Some th_row ;
  th_ok  : pred th_row = true
}.
Arguments mk_trace_hit {p idx s d bp pred} _ _ _ _.
Arguments th_ord {p idx s d bp pred} _.
Arguments th_row {p idx s d bp pred} _.
Arguments th_at {p idx s d bp pred} _.
Arguments th_ok {p idx s d bp pred} _.

Fixpoint trace_scan {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pred : TraceRow s -> bool) (k : nat) (l : list (TraceRow s)) {struct l}
  : l = skipn k (bp_traces bp) -> option (TraceHit bp pred) :=
  match l with
  | [] => fun _ => None
  | tr :: rest => fun E =>
      match Bool.bool_dec (pred tr) true with
      | left Hp => Some (mk_trace_hit k tr (Index.Child.skipn_head_at (bp_traces bp) rest k tr E) Hp)
      | right _ => trace_scan bp pred (S k) rest (Index.Child.skipn_tail_at (bp_traces bp) rest k tr E)
      end
  end.

Lemma trace_scan_finds {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pred : TraceRow s -> bool) :
  forall l k (E : l = skipn k (bp_traces bp)),
  (exists tr, In tr l /\ pred tr = true) ->
  trace_scan bp pred k l E <> None.
Proof.
  induction l as [|tr rest IH]; intros k E [tr0 [Hin Hp]]; [ destruct Hin |].
  cbn. destruct (Bool.bool_dec (pred tr) true) as [|Hne]; [ discriminate |].
  destruct Hin as [<-|Hin]; [ exact (False_ind _ (Hne Hp)) |].
  apply (IH (S k) (Index.Child.skipn_tail_at (bp_traces bp) rest k tr E)).
  exists tr0. split; [ exact Hin | exact Hp ].
Qed.

(* the total exact block lookup: every represented block has exactly one retained trace *)
Definition block_trace {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (br : Index.Refs.BlockRef idx) : TraceHit bp
    (fun tr => noderef_eqb (Index.Refs.bl_node (trow_block tr)) (Index.Refs.bl_node br)) :=
  (match trace_scan bp _ 0 (bp_traces bp) (eq_sym (skipn_O _)) as o
         return trace_scan bp _ 0 (bp_traces bp) (eq_sym (skipn_O _)) = o -> _ with
   | Some h => fun _ => h
   | None => fun E =>
       False_rect _
         (trace_scan_finds bp _ (bp_traces bp) 0 (eq_sym (skipn_O _))
            (ex_intro _ _
               (conj (traces_cover bp (Index.Refs.bl_node br) (Index.Refs.bl_ok br))
                     (proj2 (noderef_eqb_spec _ _) eq_refl)))
            E)
   end) eq_refl.

Lemma block_trace_subject {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (br : Index.Refs.BlockRef idx) :
  Index.Refs.bl_node (trow_block (th_row (block_trace bp br))) = Index.Refs.bl_node br.
Proof.
  apply noderef_eqb_spec. exact (th_ok (block_trace bp br)).
Qed.

(* the retained trace of a block, as the exact typed trace ref *)
Definition trace_of_block {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (br : Index.Refs.BlockRef idx) : BlockTraceRef bp (Index.Refs.bl_node br) :=
  mk_block_trace (th_ord (block_trace bp br)) (th_row (block_trace bp br))
    (th_at (block_trace bp br)) (block_trace_subject bp br).

(* the enclosing block of a short statement, total by the accepted statement topology *)
Definition stmt_block {p} {idx : Index.Core.ProgramIndex p} (st : Index.Refs.ShortStmtRef idx)
  : Index.Refs.BlockRef idx :=
  (match Index.Core.node_parent (Index.Refs.sh_node st) as o
         return Index.Core.node_parent (Index.Refs.sh_node st) = o -> Index.Refs.BlockRef idx with
   | Some par => fun E => Index.Refs.mkBlockRef par (f_equal Index.Core.is_block_view (stmt_parent_block st par E))
   | None => fun E => False_rect _ (stmt_has_parent st E)
   end) eq_refl.

Definition noderef_eq_dec {p} {idx : Index.Core.ProgramIndex p} (a b : Index.Core.NodeRef idx)
  : {a = b} + {a <> b} := dec_of_eqb noderef_eqb noderef_eqb_spec a b.

(* dependent option convoys reduce under a known scrutinee value over a decidable base *)
Lemma option_convoy_some {A T : Type} (Adec : forall a b : A, {a = b} + {a <> b})
  (X : option A) (f : forall a, X = Some a -> T) (g : X = None -> T) (a : A) (H : X = Some a) :
  (match X as o return X = o -> T with Some a' => f a' | None => g end) eq_refl = f a H.
Proof.
  assert (Odec : forall x y : option A, {x = y} + {x <> y}) by (decide equality).
  destruct X as [a0|]; [| discriminate H ].
  assert (Ha : a0 = a) by (injection H as Ha; exact Ha). subst a0.
  rewrite (UIP_dec Odec H eq_refl). reflexivity.
Qed.

(* the enclosing statement of a short statement points back through the retained parent relation *)
Lemma stmt_block_parent {p} {idx : Index.Core.ProgramIndex p} (st : Index.Refs.ShortStmtRef idx) :
  Index.Core.node_parent (Index.Refs.sh_node st) = Some (Index.Refs.bl_node (stmt_block st)).
Proof.
  assert (Hex : exists par, Index.Core.node_parent (Index.Refs.sh_node st) = Some par).
  { destruct (Index.Core.node_parent (Index.Refs.sh_node st)) as [par|] eqn:Hp;
      [ exists par; reflexivity | exact (False_ind _ (stmt_has_parent st Hp)) ]. }
  destruct Hex as [par Hp].
  unfold stmt_block.
  rewrite (option_convoy_some noderef_eq_dec _ _ _ par Hp).
  exact Hp.
Qed.

(* the exact short event of every short statement exists at its statement ordinal in its block's trace *)
Lemma short_event_cover {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (st : Index.Refs.ShortStmtRef idx) (par : Index.Core.NodeRef idx) (tr : TraceRow s) :
  Index.Core.node_parent (Index.Refs.sh_node st) = Some par ->
  In tr (bp_traces bp) -> Index.Refs.bl_node (trow_block tr) = par ->
  exists eix (st'' : Index.Refs.ShortStmtRef idx) (rows : list ShortLeftDecisionData),
    nth_error (trow_evs tr) eix = Some (BEvShort st'' rows)
    /\ Index.Refs.sh_node st'' = Index.Refs.sh_node st.
Proof.
  intros Hp Hin Hnode.
  destruct (bp_traces_row bp tr Hin) as [pr [r [Hb [_ [_ Hform]]]]].
  assert (Hr : r = par)
    by (rewrite Hform in Hnode; cbn in Hnode; exact Hnode).
  subst r.
  destruct (Index.Edges.all_children_of_parent (Index.Refs.sh_node st) par Hp) as [j [e [_ Hc]]].
  destruct (Index.Edges.all_children_nth par j e) as [e' Hrow].
  assert (Hevs : trow_evs tr = block_fold s (Index.Refs.mkBlockRef par Hb) (Index.Child.all_children par)
                                 (pkg_env_of s pr)) by (rewrite Hform; reflexivity).
  destruct (block_fold_nth (Index.Refs.mkBlockRef par Hb) (Index.Child.all_children par)
              (pkg_env_of s pr) j (existT _ j e') Hrow) as [env' Hnth].
  cbn [projT2] in Hnth.
  assert (Hcc : Index.Child.ca_child e' = Index.Refs.sh_node st)
    by exact (eq_trans (Index.Child.ca_det e' e) Hc).
  assert (Hview : Index.Core.node_view (Index.Child.ca_child e')
                  = Index.Model.VStmt (Index.Model.SSShort (Index.Refs.sh_names st) (Index.Refs.sh_values st)))
    by (rewrite Hcc; exact (Index.Refs.sh_ok st)).
  destruct (block_event_short_eval (Index.Refs.mkBlockRef par Hb) env' (Index.Child.ca_child e')
              _ eq_refl (Index.Refs.sh_names st) (Index.Refs.sh_values st) Hview) as [Hv0 Hev].
  pose proof (eq_trans Hnth (f_equal Some Hev)) as Hnth2.
  exists j. do 2 eexists.
  split; [ rewrite Hevs; exact Hnth2 |].
  cbn [Index.Refs.sh_node]. exact Hcc.
Qed.

(* one retained short event ref: the exact trace, statement ordinal, and judged event, pinned *)
Record ShortEventRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (st : Index.Refs.ShortStmtRef idx) : Type := mk_short_event {
  se_block : Index.Refs.BlockRef idx ;
  se_trace : BlockTraceRef bp (Index.Refs.bl_node se_block) ;
  se_ord   : nat ;
  se_stmt  : Index.Refs.ShortStmtRef idx ;
  se_rows  : list ShortLeftDecisionData ;
  se_at : nth_error (trow_evs (btr_row se_trace)) se_ord = Some (BEvShort se_stmt se_rows) ;
  se_subject : Index.Refs.sh_node se_stmt = Index.Refs.sh_node st
}.
Arguments mk_short_event {p idx s d bp st} _ _ _ _ _ _ _.
Arguments se_block {p idx s d bp st} _.
Arguments se_trace {p idx s d bp st} _.
Arguments se_ord {p idx s d bp st} _.
Arguments se_stmt {p idx s d bp st} _.
Arguments se_rows {p idx s d bp st} _.
Arguments se_at {p idx s d bp st} _.
Arguments se_subject {p idx s d bp st} _.

Definition is_short_match {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (st : Index.Refs.ShortStmtRef idx) (ev : BlockEv s) : bool :=
  match ev with
  | BEvShort st' _ => noderef_eqb (Index.Refs.sh_node st') (Index.Refs.sh_node st)
  | _ => false
  end.

Fixpoint short_scan {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (br : Index.Refs.BlockRef idx) (tr0 : BlockTraceRef bp (Index.Refs.bl_node br))
  (st : Index.Refs.ShortStmtRef idx) (k : nat) (l : list (BlockEv s)) {struct l}
  : l = skipn k (trow_evs (btr_row tr0)) -> option (ShortEventRef bp st) :=
  match l with
  | [] => fun _ => None
  | BEvShort st' sj :: rest => fun E =>
      match Bool.bool_dec (noderef_eqb (Index.Refs.sh_node st') (Index.Refs.sh_node st)) true with
      | left Hn =>
          Some (mk_short_event br tr0 k st' sj
                  (Index.Child.skipn_head_at (trow_evs (btr_row tr0)) rest k (BEvShort st' sj) E)
                  (proj1 (noderef_eqb_spec _ _) Hn))
      | right _ =>
          short_scan br tr0 st (S k) rest
            (Index.Child.skipn_tail_at (trow_evs (btr_row tr0)) rest k (BEvShort st' sj) E)
      end
  | ev :: rest => fun E =>
      short_scan br tr0 st (S k) rest
        (Index.Child.skipn_tail_at (trow_evs (btr_row tr0)) rest k ev E)
  end.

Lemma short_scan_finds {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (br : Index.Refs.BlockRef idx) (tr0 : BlockTraceRef bp (Index.Refs.bl_node br))
  (st : Index.Refs.ShortStmtRef idx) :
  forall l k (E : l = skipn k (trow_evs (btr_row tr0))),
  (exists ev, In ev l /\ is_short_match st ev = true) ->
  short_scan br tr0 st k l E <> None.
Proof.
  induction l as [|ev rest IH]; intros k E [ev0 [Hin Hm]]; [ destruct Hin |].
  destruct ev as [r|sc t dj|st' sj]; cbn.
  - destruct Hin as [He|Hin];
      [ rewrite <- He in Hm; discriminate Hm
      | apply IH; exists ev0; split; [ exact Hin | exact Hm ] ].
  - destruct Hin as [He|Hin];
      [ rewrite <- He in Hm; discriminate Hm
      | apply IH; exists ev0; split; [ exact Hin | exact Hm ] ].
  - destruct (Bool.bool_dec (noderef_eqb (Index.Refs.sh_node st') (Index.Refs.sh_node st)) true)
      as [|Hne]; [ discriminate |].
    destruct Hin as [He|Hin].
    + rewrite <- He in Hm. cbn in Hm. exact (False_ind _ (Hne Hm)).
    + apply IH. exists ev0. split; [ exact Hin | exact Hm ].
Qed.

Lemma short_event_present {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (st : Index.Refs.ShortStmtRef idx) :
  exists ev, In ev (trow_evs (btr_row (trace_of_block bp (stmt_block st))))
             /\ is_short_match st ev = true.
Proof.
  set (tr0 := trace_of_block bp (stmt_block st)).
  destruct (short_event_cover bp st (Index.Refs.bl_node (stmt_block st)) (btr_row tr0)
              (stmt_block_parent st) (nth_error_In _ _ (btr_at tr0)) (btr_subject tr0))
    as [eix [st'' [sj [Hnth Hsn]]]].
  exists (BEvShort st'' sj). split; [ exact (nth_error_In _ _ Hnth) |].
  cbn. apply noderef_eqb_spec. exact Hsn.
Qed.

(* the total exact short lookup: every short statement's retained event, judgment included *)
Definition short_event {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (st : Index.Refs.ShortStmtRef idx) : ShortEventRef bp st :=
  (match short_scan (stmt_block st) (trace_of_block bp (stmt_block st)) st 0
           (trow_evs (btr_row (trace_of_block bp (stmt_block st)))) (eq_sym (skipn_O _)) as o
         return short_scan (stmt_block st) (trace_of_block bp (stmt_block st)) st 0
                  (trow_evs (btr_row (trace_of_block bp (stmt_block st)))) (eq_sym (skipn_O _)) = o
                -> ShortEventRef bp st with
   | Some se => fun _ => se
   | None => fun E =>
       False_rect _
         (short_scan_finds (stmt_block st) (trace_of_block bp (stmt_block st)) st
            (trow_evs (btr_row (trace_of_block bp (stmt_block st)))) 0 (eq_sym (skipn_O _))
            (short_event_present bp st) E)
   end) eq_refl.

(* the retained event ref and its exact causal states, projected from the short event *)
Definition se_event {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  : BlockEventRef (se_trace se) :=
  mk_block_event (se_ord se) (nth_error_lt _ _ _ (se_at se)).

Definition short_state_before {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  : BlockStateRef (ber_pre (se_event se)) := block_state (ber_pre (se_event se)).

Definition short_state_after {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  : BlockStateRef (ber_post (se_event se)) := block_state (ber_post (se_event se)).

(* the retained short rows are exactly the canonical decision over the exact predecessor state's members *)
Lemma se_rows_decide {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st) :
  se_rows se = short_decide_rows (map es_est (bs_members (short_state_before se))) (se_stmt se).
Proof.
  pose proof (se_at se) as Hat.
  set (tr := btr_row (se_trace se)) in *.
  destruct (bp_traces_row bp tr (nth_error_In _ _ (btr_at (se_trace se)))) as [pr [r [Hb [_ [_ Hform]]]]].
  assert (Hevs : trow_evs tr = block_fold s (Index.Refs.mkBlockRef r Hb) (Index.Child.all_children r) (pkg_env_of s pr))
    by (rewrite Hform; reflexivity).
  pose proof Hat as Hat2. rewrite Hevs in Hat2.
  destruct (block_fold_nth_env (Index.Refs.mkBlockRef r Hb) (Index.Child.all_children r) (pkg_env_of s pr)
              (se_ord se) _ Hat2) as [x [_ He]].
  set (c := Index.Child.ca_child (projT2 x)) in *.
  assert (Hcc : Index.Refs.sh_node (se_stmt se) = c).
  { pose proof (f_equal bev_node He) as Hn. cbn [bev_node] in Hn.
    rewrite block_event_node in Hn. exact Hn. }
  assert (Hview : Index.Core.node_view c
                  = Index.Model.VStmt (Index.Model.SSShort (Index.Refs.sh_names (se_stmt se)) (Index.Refs.sh_values (se_stmt se))))
    by (rewrite <- Hcc; exact (Index.Refs.sh_ok (se_stmt se))).
  destruct (block_event_short_eval (Index.Refs.mkBlockRef r Hb)
              (pkg_env_of s pr ++ flat_map (bev_adds (Index.Refs.mkBlockRef r Hb))
                 (firstn (se_ord se) (block_fold s (Index.Refs.mkBlockRef r Hb) (Index.Child.all_children r)
                    (pkg_env_of s pr)))) c _ eq_refl
              (Index.Refs.sh_names (se_stmt se)) (Index.Refs.sh_values (se_stmt se)) Hview) as [Hv0 Heval].
  rewrite Heval in He.
  set (st'' := Index.Refs.mkShortStmtRef c (Index.Refs.sh_names (se_stmt se)) (Index.Refs.sh_values (se_stmt se)) Hv0) in *.
  assert (Hst : se_stmt se = st'') by (apply shortstmtref_positional; cbn [Index.Refs.sh_node]; exact Hcc).
  injection He as _ He2.
  rewrite <- Hst in He2.
  rewrite He2. f_equal.
  assert (Hbs : bs_members (short_state_before se) = state_refs bp (btr_ord (se_trace se)) (se_ord se))
    by reflexivity.
  rewrite Hbs.
  rewrite (state_ests bp (btr_ord (se_trace se)) (se_ord se) tr (btr_at (se_trace se))
             (Nat.lt_le_incl _ _ (nth_error_lt _ _ _ Hat))).
  assert (Hpkg : map es_est (ledger_refs bp (trow_pkg tr)) = pkg_env_of s pr).
  { replace (trow_pkg tr) with (PI.pr_pos pr) by (rewrite Hform; reflexivity).
    exact (package_env_ests bp pr). }
  rewrite Hpkg.
  replace (trow_block tr) with (Index.Refs.mkBlockRef r Hb) by (rewrite Hform; reflexivity).
  rewrite Hevs. reflexivity.
Qed.

(* an exact predecessor-state member ref from a positional match over the state's projected members *)
Definition state_member_ref {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (st : BlockStateRef c) (j : nat) (m : Est s)
  (H : nth_error (map es_est (bs_members st)) j = Some m)
  : { mr : BlockMemberRef st | es_est (bm_ref mr) = m /\ bm_ord mr = j }.
Proof.
  rewrite nth_error_map in H.
  destruct (nth_error (bs_members st) j) as [er|] eqn:Her; [| discriminate H].
  cbn in H. injection H as <-.
  exists (mk_block_member j er Her). split; reflexivity.
Defined.

(* the exact state-level occupancy group: the same-name members visible in a block state, in source order *)
Definition local_group_refs {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (st : BlockStateRef c) (nm : Names.OrdinaryIdentifier) : list (EstablishmentRef bp) :=
  filter (fun er => same_block_cand nm (es_est er)) (bs_members st).
Record LocalGroupRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (st : BlockStateRef c) (nm : Names.OrdinaryIdentifier) : Type := mk_local_group {
  lg_members : list (EstablishmentRef bp) ;
  lg_ok : lg_members = local_group_refs st nm
}.
Arguments mk_local_group {p idx s d bp b tr c st nm} _ _.
Arguments lg_members {p idx s d bp b tr c st nm} _.
Arguments lg_ok {p idx s d bp b tr c st nm} _.
Definition local_group {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (st : BlockStateRef c) (nm : Names.OrdinaryIdentifier) : LocalGroupRef st nm :=
  mk_local_group (local_group_refs st nm) eq_refl.

(* the exact short-left fact, INDEXED by the retained decision row: for a given row exactly one case inhabits *)
Inductive ShortLhsFact {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (pre : BlockStateRef c) {st : Index.Refs.ShortStmtRef idx} {i : nat}
  (e : Index.Edges.ShortLhsEdge st i) : ShortLeftDecisionData -> Type :=
| ShortBlankFact : binder_ident (Index.Edges.sl_child e) = None -> ShortLhsFact pre e ShortBlankData
| ShortDuplicateFact : forall (n : Names.OrdinaryIdentifier) (j : nat) (ej : Index.Edges.ShortLhsEdge st j)
    (Hj : j < i),
    binder_ident (Index.Edges.sl_child e) = Some n -> binder_ident (Index.Edges.sl_child ej) = Some n ->
    find_dup i n (Index.Edges.short_lhs_edges st) = Some (existT _ j (ej, Hj)) ->
    ShortLhsFact pre e (ShortDuplicateData j)
| ShortNewFact : forall (n : Names.OrdinaryIdentifier),
    binder_ident (Index.Edges.sl_child e) = Some n ->
    find_dup i n (Index.Edges.short_lhs_edges st) = None ->
    (forall mr : BlockMemberRef pre, same_block_cand n (es_est (bm_ref mr)) = false) ->
    ShortLhsFact pre e (ShortNewData n)
| ShortExistingVariableFact : forall (n : Names.OrdinaryIdentifier) (mr : BlockMemberRef pre),
    binder_ident (Index.Edges.sl_child e) = Some n ->
    find_dup i n (Index.Edges.short_lhs_edges st) = None ->
    find_two_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = None ->
    find_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = Some (bm_ord mr, es_est (bm_ref mr)) ->
    is_variable_binder (est_node (es_est (bm_ref mr))) = true ->
    ShortLhsFact pre e (ShortExistingVariableData (bm_ord mr))
| ShortExistingNonVariableFact : forall (n : Names.OrdinaryIdentifier) (mr : BlockMemberRef pre),
    binder_ident (Index.Edges.sl_child e) = Some n ->
    find_dup i n (Index.Edges.short_lhs_edges st) = None ->
    find_two_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = None ->
    find_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = Some (bm_ord mr, es_est (bm_ref mr)) ->
    is_variable_binder (est_node (es_est (bm_ref mr))) = false ->
    ShortLhsFact pre e (ShortExistingNonVariableData (bm_ord mr))
| ShortAmbiguousFact : forall (n : Names.OrdinaryIdentifier) (grp : LocalGroupRef pre n)
    (mr1 mr2 : BlockMemberRef pre),
    binder_ident (Index.Edges.sl_child e) = Some n ->
    find_dup i n (Index.Edges.short_lhs_edges st) = None ->
    find_two_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = Some (bm_ord mr1, bm_ord mr2) ->
    lg_members grp = local_group_refs pre n ->
    same_block_cand n (es_est (bm_ref mr1)) = true ->
    same_block_cand n (es_est (bm_ref mr2)) = true ->
    ShortLhsFact pre e (ShortAmbiguousData (bm_ord mr1) (bm_ord mr2)).
Arguments ShortBlankFact {p idx s d bp b tr c pre st i e} _.
Arguments ShortDuplicateFact {p idx s d bp b tr c pre st i e} _ _ _ _ _ _ _.
Arguments ShortNewFact {p idx s d bp b tr c pre st i e} _ _ _ _.
Arguments ShortExistingVariableFact {p idx s d bp b tr c pre st i e} _ _ _ _ _ _ _.
Arguments ShortExistingNonVariableFact {p idx s d bp b tr c pre st i e} _ _ _ _ _ _ _.
Arguments ShortAmbiguousFact {p idx s d bp b tr c pre st i e} _ _ _ _ _ _ _ _ _.

(* the one canonical short fact for a left edge, indexed by its canonical decision over the exact state *)
Definition short_lhs_fact {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (pre : BlockStateRef c) {st : Index.Refs.ShortStmtRef idx} {i : nat}
  (e : Index.Edges.ShortLhsEdge st i)
  : ShortLhsFact pre e (short_left_decide (map es_est (bs_members pre)) e).
Proof.
  unfold short_left_decide.
  destruct (binder_ident (Index.Edges.sl_child e)) as [n|] eqn:Hb; [| exact (ShortBlankFact Hb) ].
  destruct (find_dup i n (Index.Edges.short_lhs_edges st)) as [[j [ej Hj]]|] eqn:Hd.
  { destruct (find_dup_sound i n (Index.Edges.short_lhs_edges st) j (ej, Hj) Hd) as [_ Hm]. cbn in Hm.
    destruct (binder_ident (Index.Edges.sl_child ej)) as [m|] eqn:Hbej; [| discriminate Hm].
    apply Names.ordinary_equalb_spec in Hm. subst m.
    exact (ShortDuplicateFact n j ej Hj Hb Hbej Hd). }
  destruct (find_two_ord (same_block_cand n) 0 (map es_est (bs_members pre))) as [[j0 j1]|] eqn:Hft.
  { destruct (find_two_ord_found (same_block_cand n) (map es_est (bs_members pre)) 0 j0 j1 Hft)
      as [_ [Hlt [Hex0 Hex1]]].
    destruct (nth_error (map es_est (bs_members pre)) j0) as [m0|] eqn:Hm0;
      [| exfalso; destruct Hex0 as [x0 [Hnx _]]; rewrite Nat.sub_0_r, Hm0 in Hnx; discriminate ].
    destruct (nth_error (map es_est (bs_members pre)) j1) as [m1|] eqn:Hm1;
      [| exfalso; destruct Hex1 as [x1 [Hnx _]]; rewrite Nat.sub_0_r, Hm1 in Hnx; discriminate ].
    destruct (state_member_ref pre j0 m0 Hm0) as [mr0 [He0 Ho0]].
    destruct (state_member_ref pre j1 m1 Hm1) as [mr1 [He1 Ho1]].
    rewrite <- Ho0, <- Ho1.
    apply (ShortAmbiguousFact n (local_group pre n) mr0 mr1 Hb Hd).
    - rewrite Ho0, Ho1. exact Hft.
    - exact (lg_ok (local_group pre n)).
    - rewrite He0. destruct Hex0 as [x0 [Hnx Hfx]]. rewrite Nat.sub_0_r, Hm0 in Hnx.
      injection Hnx as <-. exact Hfx.
    - rewrite He1. destruct Hex1 as [x1 [Hnx Hfx]]. rewrite Nat.sub_0_r, Hm1 in Hnx.
      injection Hnx as <-. exact Hfx. }
  destruct (find_ord (same_block_cand n) 0 (map es_est (bs_members pre))) as [[j m]|] eqn:Ho.
  { destruct (find_ord_found (same_block_cand n) (map es_est (bs_members pre)) 0 j m Ho)
      as [_ [Hn' [Hf _]]].
    rewrite Nat.sub_0_r in Hn'.
    destruct (state_member_ref pre j m Hn') as [mr [He Hoo]].
    destruct (is_variable_binder (est_node m)) eqn:Hvar.
    - rewrite <- Hoo.
      apply (ShortExistingVariableFact n mr Hb Hd Hft).
      + rewrite Hoo, He. exact Ho.
      + rewrite He. exact Hvar.
    - rewrite <- Hoo.
      apply (ShortExistingNonVariableFact n mr Hb Hd Hft).
      + rewrite Hoo, He. exact Ho.
      + rewrite He. exact Hvar. }
  { apply (ShortNewFact n Hb Hd). intro mr.
    apply (find_ord_none (same_block_cand n) (map es_est (bs_members pre)) 0 Ho).
    apply (nth_error_In _ (bm_ord mr)). rewrite nth_error_map, (bm_at mr). reflexivity. }
Defined.

(* the canonical left edge at an exact index: the ordinal-aligned member of the statement's edge list *)
Lemma short_lhs_edge_at {p} {idx : Index.Core.ProgramIndex p} (st : Index.Refs.ShortStmtRef idx) (i : nat) :
  i < Index.Refs.sh_names st ->
  { e : Index.Edges.ShortLhsEdge st i | nth_error (Index.Edges.short_lhs_edges st) i = Some (existT _ i e) }.
Proof.
  intro Hi.
  assert (Hlen : length (Index.Edges.short_lhs_edges st) = Index.Refs.sh_names st).
  { pose proof (Index.Edges.short_lhs_edges_ords st) as Ho.
    apply (f_equal (@length _)) in Ho. rewrite length_map, length_seq in Ho. exact Ho. }
  destruct (nth_error (Index.Edges.short_lhs_edges st) i) as [x|] eqn:Hx;
    [| exfalso; apply nth_error_None in Hx; lia ].
  assert (Hj : projT1 x = i).
  { pose proof (Index.Edges.short_lhs_edges_ords st) as Ho.
    apply (f_equal (fun l => nth_error l i)) in Ho.
    rewrite nth_error_map, Hx in Ho. cbn in Ho.
    rewrite (nth_error_nth' (seq 0 (Index.Refs.sh_names st)) 0) in Ho;
      [| rewrite length_seq; exact Hi ].
    rewrite seq_nth in Ho; [| exact Hi ]. cbn in Ho. injection Ho as Ho. exact Ho. }
  destruct x as [j e]. cbn in Hj. subst j. exists e. reflexivity.
Qed.

(* a short left edge is positionally unique: any two edges at the same index are equal (ChildAt is unique) *)
Lemma shortlhsedge_positional {p} {idx : Index.Core.ProgramIndex p} {st : Index.Refs.ShortStmtRef idx} {i : nat}
  (a b : Index.Edges.ShortLhsEdge st i) : a = b.
Proof.
  destruct a as [aa Ha], b as [ba Hb]. f_equal; [ apply childat_unique | apply le_unique ].
Qed.

(* decidable equality on the establishment key types: a decidable key plus an hProp proof, the basis for ref UIP *)
Definition ordinary_eq_dec (a b : Names.OrdinaryIdentifier) : {a = b} + {a <> b} :=
  dec_of_eqb Names.ordinary_equalb Names.ordinary_equalb_spec a b.
Definition scope_eq_dec {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx} (a b : ScopeId s)
  : {a = b} + {a <> b} := dec_of_eqb scope_eqb scope_eqb_spec a b.
Definition binderref_eq_dec {p} {idx : Index.Core.ProgramIndex p} (a b : BinderRef idx) : {a = b} + {a <> b}.
Proof.
  destruct (noderef_eq_dec (binder_node a) (binder_node b)) as [E|E];
    [ left; apply binderref_positional; exact E | right; intro H; apply E; exact (f_equal binder_node H) ].
Defined.
Definition mainocc_eq_dec {p} {idx : Index.Core.ProgramIndex p} (a b : Index.Refs.MainOccurrenceRef idx)
  : {a = b} + {a <> b}.
Proof.
  destruct (noderef_eq_dec (Index.Refs.mo_node a) (Index.Refs.mo_node b)) as [E|E];
    [ left; apply Index.Refs.mainocc_positional; exact E | right; intro H; apply E; exact (f_equal Index.Refs.mo_node H) ].
Defined.
Definition functiondeclref_eq_dec {p} {idx : Index.Core.ProgramIndex p} (a b : FunctionDeclRef idx)
  : {a = b} + {a <> b}.
Proof.
  destruct a as [ma], b as [mb]. destruct (mainocc_eq_dec ma mb) as [E|E];
    [ left; f_equal; exact E | right; intro H; apply E; injection H as H; exact H ].
Defined.
Definition shortnewref_eq_dec {p} {idx : Index.Core.ProgramIndex p} (a b : ShortNewRef idx) : {a = b} + {a <> b}.
Proof.
  destruct a as [sta ia ea], b as [stb ib eb].
  destruct (shortstmtref_eq_dec sta stb) as [Es|Es]; [| right; intro H; apply Es; exact (f_equal snr_stmt H) ].
  subst stb. destruct (Nat.eq_dec ia ib) as [Ei|Ei]; [| right; intro H; apply Ei; exact (f_equal snr_ix H) ].
  subst ib. left. f_equal. apply shortlhsedge_positional.
Defined.
Definition declorigin_eq_dec {p} {idx : Index.Core.ProgramIndex p} (a b : DeclOrigin idx) : {a = b} + {a <> b}.
Proof.
  destruct a as [ba|fa|sa], b as [bb|fb|sb]; try (right; discriminate).
  - destruct (binderref_eq_dec ba bb) as [E|E]; [ left; f_equal; exact E | right; intro H; apply E; injection H as H; exact H ].
  - destruct (functiondeclref_eq_dec fa fb) as [E|E]; [ left; f_equal; exact E | right; intro H; apply E; injection H as H; exact H ].
  - destruct (shortnewref_eq_dec sa sb) as [E|E]; [ left; f_equal; exact E | right; intro H; apply E; injection H as H; exact H ].
Defined.
Definition est_eq_dec {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx} (a b : Est s)
  : {a = b} + {a <> b}.
Proof.
  destruct a as [oa na sca va], b as [ob nb scb vb].
  destruct (declorigin_eq_dec oa ob) as [Eo|Eo]; [| right; intro H; apply Eo; exact (f_equal est_origin H) ].
  destruct (ordinary_eq_dec na nb) as [En|En]; [| right; intro H; apply En; exact (f_equal est_name H) ].
  destruct (scope_eq_dec sca scb) as [Es|Es]; [| right; intro H; apply Es; exact (f_equal est_scope H) ].
  destruct (Nat.eq_dec va vb) as [Ev|Ev]; [| right; intro H; apply Ev; exact (f_equal est_vstart H) ].
  subst; left; reflexivity.
Defined.

Definition option_est_eq_dec {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (a b : option (Est s)) : {a = b} + {a <> b}.
Proof.
  destruct a as [x|], b as [y|]; try (right; discriminate); try (left; reflexivity).
  destruct (est_eq_dec x y) as [E|E]; [ left; f_equal; exact E | right; intro H; apply E; injection H as H; exact H ].
Defined.

(* exact addition refs are positionally unique: same site and index force the same ref (Est is an hSet) *)
Lemma eventadditionref_positional {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {site : EvSite bp} {ix : nat}
  (a b : EventAdditionRef bp site ix) : a = b.
Proof.
  destruct a as [ea pa], b as [eb pb].
  assert (Hest : ea = eb) by (pose proof (eq_trans (eq_sym pa) pb) as E; injection E as E; exact E).
  subst eb. f_equal. apply (UIP_dec option_est_eq_dec).
Qed.

(* the exact per-left short decision-row ref: transparent row + edge, Prop-pinned to the retained event *)
Record ShortDecisionRowRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (i : nat) : Type := mk_short_row {
  sdr_row  : ShortLeftDecisionData ;
  sdr_edge : Index.Edges.ShortLhsEdge (se_stmt se) i ;
  sdr_at   : nth_error (se_rows se) i = Some sdr_row
}.
Arguments mk_short_row {p idx s d bp st se i} _ _ _.
Arguments sdr_row {p idx s d bp st se i} _.
Arguments sdr_edge {p idx s d bp st se i} _.
Arguments sdr_at {p idx s d bp st se i} _.

(* transparent, proof-insensitive projections a live consumer reads without normalizing any pin *)
Definition row_decision {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} {se : ShortEventRef bp st} {i}
  (r : ShortDecisionRowRef se i) : ShortLeftDecisionData := sdr_row r.
Definition row_subject {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} {se : ShortEventRef bp st} {i}
  (r : ShortDecisionRowRef se i) : Index.Edges.ShortLhsEdge (se_stmt se) i := sdr_edge r.

(* the length of the retained short rows is exactly the statement's left count *)
Lemma se_rows_length {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st) :
  length (se_rows se) = Index.Refs.sh_names (se_stmt se).
Proof.
  rewrite se_rows_decide. unfold short_decide_rows. rewrite length_map.
  pose proof (Index.Edges.short_lhs_edges_ords (se_stmt se)) as Ho.
  apply (f_equal (@length _)) in Ho. rewrite length_map, length_seq in Ho. exact Ho.
Qed.

(* the one canonical per-left decision-row ref, built cheaply from the source edge: only the row is looked up *)
Definition short_decision_row {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (i : nat) (e : Index.Edges.ShortLhsEdge (se_stmt se) i) : ShortDecisionRowRef se i.
Proof.
  destruct (nth_error (se_rows se) i) as [row|] eqn:Hrow.
  - exact (mk_short_row row e Hrow).
  - exfalso. apply nth_error_None in Hrow. rewrite se_rows_length in Hrow.
    pose proof (Index.Edges.sl_lt e). lia.
Defined.

(* the source edge of a row ref is exactly the statement's left at that index (derived; ChildAt-unique) *)
Lemma short_row_edge_at {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (i : nat) (r : ShortDecisionRowRef se i) :
  nth_error (Index.Edges.short_lhs_edges (se_stmt se)) i = Some (existT _ i (sdr_edge r)).
Proof.
  destruct (short_lhs_edge_at (se_stmt se) i (Index.Edges.sl_lt (sdr_edge r))) as [e0 He0].
  rewrite (shortlhsedge_positional (sdr_edge r) e0). exact He0.
Qed.

(* the derived proof-bearing case fact for a row ref: authority for the laws, off every live computation path *)
Definition short_row_fact {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (i : nat) (r : ShortDecisionRowRef se i)
  : ShortLhsFact (short_state_before se) (sdr_edge r) (sdr_row r).
Proof.
  assert (Hcanon : sdr_row r = short_left_decide (map es_est (bs_members (short_state_before se))) (sdr_edge r)).
  { pose proof (sdr_at r) as Ha. rewrite se_rows_decide in Ha. unfold short_decide_rows in Ha.
    rewrite nth_error_map, (short_row_edge_at se i r) in Ha. cbn in Ha. injection Ha as Ha. exact (eq_sym Ha). }
  rewrite Hcanon. exact (short_lhs_fact (short_state_before se) (sdr_edge r)).
Defined.

(* the exact state-indexed short judgment: a view giving each left's canonical decision-row ref, never a table *)
Definition ShortJudgmentRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st) : Type :=
  forall i, i < Index.Refs.sh_names (se_stmt se) -> ShortDecisionRowRef se i.

(* the one canonical exact short judgment: every left's exact decision-row ref against the predecessor state *)
Definition short_judgment_ref {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  : ShortJudgmentRef se := fun i Hi => short_decision_row se i (proj1_sig (short_lhs_edge_at (se_stmt se) i Hi)).

(* the source edge at a position carries exactly that position as its ordinal (edges are ordinal-aligned) *)
Lemma short_edge_projT1 {p} {idx : Index.Core.ProgramIndex p} (st : Index.Refs.ShortStmtRef idx) (j : nat)
  (x : {i : nat & Index.Edges.ShortLhsEdge st i}) :
  nth_error (Index.Edges.short_lhs_edges st) j = Some x -> projT1 x = j.
Proof.
  intro Hx. pose proof (Index.Edges.short_lhs_edges_ords st) as Ho.
  assert (Hlen : length (Index.Edges.short_lhs_edges st) = Index.Refs.sh_names st)
    by (apply (f_equal (@length _)) in Ho; rewrite length_map, length_seq in Ho; exact Ho).
  assert (Hlt : j < Index.Refs.sh_names st) by (rewrite <- Hlen; apply nth_error_Some; rewrite Hx; discriminate).
  apply (f_equal (fun l => nth_error l j)) in Ho. rewrite nth_error_map, Hx in Ho. cbn in Ho.
  rewrite (nth_error_nth' (seq 0 _) 0) in Ho; [| rewrite length_seq; exact Hlt].
  rewrite seq_nth in Ho; [| exact Hlt]. cbn in Ho. injection Ho as Ho. exact Ho.
Qed.

(* the one live transparent short-duplicate decision: the first duplicate's exact row, index, and name, or none *)
Inductive ShortDuplicateDecision {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st) : Type :=
| ShortNoDup
| ShortDup (i : nat) (r : ShortDecisionRowRef se i) (earlier : nat) (n : Names.OrdinaryIdentifier).
Arguments ShortNoDup {p idx s d bp st se}.
Arguments ShortDup {p idx s d bp st se} _ _ _ _.

(* the per-edge fold step, carrying the canonical exact row ref: the leftmost named duplicate wins *)
Definition dup_fold_body {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (x : {i : nat & Index.Edges.ShortLhsEdge (se_stmt se) i}) (acc : ShortDuplicateDecision se)
  : ShortDuplicateDecision se :=
  match x with existT _ i e =>
    match row_decision (short_decision_row se i e) with
    | ShortDuplicateData earlier =>
        match binder_ident (Index.Edges.sl_child (row_subject (short_decision_row se i e))) with
        | Some n => ShortDup i (short_decision_row se i e) earlier n | None => acc end
    | _ => acc end end.

(* the canonical row builder keeps its input edge as the exact subject, and carries the retained row *)
Lemma short_decision_row_row {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (i : nat) (e : Index.Edges.ShortLhsEdge (se_stmt se) i) (row : ShortLeftDecisionData) :
  nth_error (se_rows se) i = Some row -> row_decision (short_decision_row se i e) = row.
Proof.
  intro Hn. pose proof (sdr_at (short_decision_row se i e)) as Hat.
  unfold row_decision. rewrite Hn in Hat. injection Hat as Hat. exact (eq_sym Hat).
Qed.
Lemma short_decision_row_sdr_edge {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (i : nat) (e : Index.Edges.ShortLhsEdge (se_stmt se) i) : sdr_edge (short_decision_row se i e) = e.
Proof. apply shortlhsedge_positional. Qed.

(* whether a source edge is a named duplicate: exactly the edges the fold step contributes, read directly *)
Definition dup_contributes {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (x : {i : nat & Index.Edges.ShortLhsEdge (se_stmt se) i}) : bool :=
  match x with existT _ i e =>
    match nth_error (se_rows se) i with
    | Some (ShortDuplicateData _) =>
        match binder_ident (Index.Edges.sl_child e) with Some _ => true | None => false end
    | _ => false end end.

(* the canonical duplicate decision, folded left-to-right over the exact rows: the leftmost duplicate wins *)
Definition short_duplicate_decision {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  : ShortDuplicateDecision se :=
  fold_right (dup_fold_body se) ShortNoDup (Index.Edges.short_lhs_edges (se_stmt se)).

(* the duplicate name a live consumer reads one-way from the exact decision, retained with the row it names *)
Definition short_dup_decision_name {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} {se : ShortEventRef bp st}
  (dd : ShortDuplicateDecision se) : option Names.OrdinaryIdentifier :=
  match dd with ShortNoDup => None | ShortDup _ _ _ n => Some n end.

(* the fold step as equations, so the single nth_error elimination is done off any dependent outer match *)
Lemma dup_step_nc {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (i : nat) (e : Index.Edges.ShortLhsEdge (se_stmt se) i) (acc : ShortDuplicateDecision se) :
  dup_contributes se (existT _ i e) = false -> dup_fold_body se (existT _ i e) acc = acc.
Proof.
  intro Hc. unfold dup_fold_body.
  destruct (nth_error (se_rows se) i) as [row|] eqn:Hn.
  2:{ exfalso. apply nth_error_None in Hn. rewrite se_rows_length in Hn. pose proof (Index.Edges.sl_lt e). lia. }
  rewrite (short_decision_row_row se i e row Hn).
  destruct row as [|earlier|n0|m1|m2|f1 f2]; try reflexivity.
  unfold row_subject. rewrite (short_decision_row_sdr_edge se i e).
  destruct (binder_ident (Index.Edges.sl_child e)) as [n|] eqn:Hbi; [| reflexivity ].
  exfalso. unfold dup_contributes in Hc. rewrite Hn, Hbi in Hc. discriminate Hc.
Qed.
Lemma dup_step_c {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (i : nat) (e : Index.Edges.ShortLhsEdge (se_stmt se) i) (acc : ShortDuplicateDecision se) :
  dup_contributes se (existT _ i e) = true ->
  exists (r : ShortDecisionRowRef se i) (earlier : nat) (n : Names.OrdinaryIdentifier),
    dup_fold_body se (existT _ i e) acc = ShortDup i r earlier n
    /\ sdr_edge r = e /\ row_decision r = ShortDuplicateData earlier
    /\ binder_ident (Index.Edges.sl_child (row_subject r)) = Some n.
Proof.
  intro Hc. unfold dup_contributes in Hc. unfold dup_fold_body.
  destruct (nth_error (se_rows se) i) as [row|] eqn:Hn; [| discriminate Hc ].
  destruct row as [|earlier|n0|m1|m2|f1 f2]; try discriminate Hc.
  pose proof (short_decision_row_row se i e _ Hn) as Hrd.
  pose proof (short_decision_row_sdr_edge se i e) as Hse.
  rewrite Hrd. unfold row_subject. rewrite Hse.
  destruct (binder_ident (Index.Edges.sl_child e)) as [n|] eqn:Hbi; [| discriminate Hc ].
  exists (short_decision_row se i e), earlier, n.
  split; [ reflexivity | split; [ exact Hse | split; [ exact Hrd |] ] ].
  unfold row_subject; rewrite Hse; exact Hbi.
Qed.

(* the fold certificate indexed by the decision: first contributing edge in source order; pre/post are fields *)
Inductive DupCert {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (l : list {i : nat & Index.Edges.ShortLhsEdge (se_stmt se) i}) : ShortDuplicateDecision se -> Prop :=
| DCNone : (forall x, In x l -> dup_contributes se x = false) -> DupCert se l ShortNoDup
| DCSome : forall (i : nat) (r : ShortDecisionRowRef se i) (earlier : nat) (n : Names.OrdinaryIdentifier)
             (pre post : list {i : nat & Index.Edges.ShortLhsEdge (se_stmt se) i}),
    l = pre ++ existT _ i (sdr_edge r) :: post ->
    (forall x, In x pre -> dup_contributes se x = false) ->
    row_decision r = ShortDuplicateData earlier ->
    binder_ident (Index.Edges.sl_child (row_subject r)) = Some n ->
    DupCert se l (ShortDup i r earlier n).

(* the fold produces its own certificate: casing on the read-direct bool, the step lemmas absorb the convoy *)
Lemma dup_cert {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (l : list {i : nat & Index.Edges.ShortLhsEdge (se_stmt se) i}) :
  DupCert se l (fold_right (dup_fold_body se) ShortNoDup l).
Proof.
  induction l as [| x xs IH].
  - apply DCNone. intros y Hy. destruct Hy.
  - destruct x as [i e]. cbn [fold_right].
    destruct (dup_contributes se (existT _ i e)) eqn:Hc.
    + destruct (dup_step_c se i e (fold_right (dup_fold_body se) ShortNoDup xs) Hc)
        as (r & earlier & n & Hfold & Hse & Hrd & Hbi).
      rewrite Hfold. apply (DCSome se _ i r earlier n [] xs).
      * cbn. rewrite Hse. reflexivity.
      * intros y Hy. destruct Hy.
      * exact Hrd.
      * exact Hbi.
    + rewrite (dup_step_nc se i e (fold_right (dup_fold_body se) ShortNoDup xs) Hc).
      destruct IH as [Hnone | i' r' earlier' n' pre' post' Heq' Hpre' Hrd' Hbi'].
      * apply DCNone. intros y [Hy | Hy]; [ subst y; exact Hc | exact (Hnone y Hy) ].
      * apply (DCSome se _ i' r' earlier' n' (existT _ i e :: pre') post').
        -- cbn. rewrite Heq'. reflexivity.
        -- intros y [Hy | Hy]; [ subst y; exact Hc | exact (Hpre' y Hy) ].
        -- exact Hrd'.
        -- exact Hbi'.
Qed.

(* the certificate the contract asks for: indexed by the exact transparent decision, off every live path *)
Definition ShortDuplicateStatus {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (dec : ShortDuplicateDecision se) : Prop :=
  DupCert se (Index.Edges.short_lhs_edges (se_stmt se)) dec.
Definition short_duplicate_status {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  : ShortDuplicateStatus se (short_duplicate_decision se) :=
  dup_cert se (Index.Edges.short_lhs_edges (se_stmt se)).

(* the exact finite event site of a short event, derived from its retained trace/ordinal membership *)
Lemma short_event_site_lt {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st) :
  se_ord se < trace_event_count bp (btr_ord (se_trace se)).
Proof.
  unfold trace_event_count. rewrite (btr_at (se_trace se)). exact (nth_error_lt _ _ _ (se_at se)).
Qed.
Definition short_event_site {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  : EvSite bp := BlockEventAt (btr_ord (se_trace se)) (se_ord se) (short_event_site_lt se).

(* the additions observed at a short event's exact site are exactly its projected New establishments *)
Lemma short_event_adds {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st) :
  event_adds (short_event_site se) = short_rows_adds (se_block se) (se_stmt se) (se_rows se).
Proof.
  unfold short_event_site.
  rewrite (event_adds_block bp (btr_ord (se_trace se)) (se_ord se) (short_event_site_lt se)
             (btr_row (se_trace se)) (BEvShort (se_stmt se) (se_rows se)) (btr_at (se_trace se)) (se_at se)).
  cbn [bev_adds].
  rewrite (Index.Refs.blockref_positional (trow_block (btr_row (se_trace se))) (se_block se)
             (btr_subject (se_trace se))).
  reflexivity.
Qed.

(* whether a retained short row is New *)
Definition is_new_row (r : ShortLeftDecisionData) : bool :=
  match r with ShortNewData _ => true | _ => false end.

(* the canonical addition ordinal of a short row: the count of New rows strictly before its exact left index *)
Definition short_new_rank {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (i : nat) : nat := length (filter is_new_row (firstn i (se_rows se))).

(* the count of contributing (nonempty-output) elements among the first k of a list *)
Definition adds_before {A B : Type} (f : A -> list B) (l : list A) (k : nat) : nat :=
  length (filter (fun x => match f x with [] => false | _ => true end) (firstn k l)).

(* a flat_map of empty-or-singleton outputs: the k-th contributor's value sits at the count of prior contributors *)
Lemma flat_map_opt_nth {A B : Type} (f : A -> list B) :
  (forall x, f x = [] \/ exists b, f x = [b]) ->
  forall (l : list A) (k : nat) (a : A) (b : B),
  nth_error l k = Some a -> f a = [b] ->
  nth_error (flat_map f l) (adds_before f l k) = Some b.
Proof.
  intro Hf. unfold adds_before. induction l as [|x xs IH]; intros k a b Hk Ha; [ destruct k; discriminate |].
  destruct k as [|k']; cbn [firstn].
  - cbn in Hk. injection Hk as <-. cbn [flat_map]. rewrite Ha. reflexivity.
  - cbn in Hk. cbn [filter flat_map]. destruct (Hf x) as [Hfx | [y Hfx]]; rewrite Hfx; cbn [app length].
    + exact (IH k' a b Hk Ha).
    + cbn [nth_error]. exact (IH k' a b Hk Ha).
Qed.

(* the informative inverse: flat_map element k is the singleton output of the (k+1)-th contributor, index recovered *)
Definition flat_map_opt_source {A B : Type} (f : A -> list B)
  (Hf : forall x, (f x = []) + { b : B | f x = [b] }) :
  forall (l : list A) (k : nat) (b : B),
  nth_error (flat_map f l) k = Some b ->
  { j : nat & { a : A | nth_error l j = Some a /\ f a = [b] /\ adds_before f l j = k } }.
Proof.
  unfold adds_before. induction l as [|x xs IH]; intros k b Hk; [ destruct k; discriminate Hk |].
  cbn [flat_map] in Hk. destruct (Hf x) as [Hfx | [y Hfx]]; rewrite Hfx in Hk.
  - cbn [app] in Hk. destruct (IH k b Hk) as [j [a [Hj [Ha Hcnt]]]].
    exists (S j), a. cbn [firstn filter]. rewrite Hfx.
    split; [ exact Hj | split; [ exact Ha | exact Hcnt ] ].
  - destruct k as [|k']; cbn [app nth_error] in Hk.
    + injection Hk as <-. exists 0, x. cbn [firstn filter length].
      split; [ reflexivity | split; [ exact Hfx | reflexivity ] ].
    + destruct (IH k' b Hk) as [j [a [Hj [Ha Hcnt]]]].
      exists (S j), a. cbn [firstn filter]. rewrite Hfx. cbn [length].
      split; [ exact Hj | split; [ exact Ha | rewrite Hcnt; reflexivity ] ].
Defined.

(* two same-length lists with position-wise agreeing predicates have equal filtered-prefix counts *)
Lemma filter_firstn_len_eq {A B : Type} (p : A -> bool) (q : B -> bool) :
  forall (l1 : list A) (l2 : list B), length l1 = length l2 ->
  (forall k x y, nth_error l1 k = Some x -> nth_error l2 k = Some y -> p x = q y) ->
  forall i, length (filter p (firstn i l1)) = length (filter q (firstn i l2)).
Proof.
  induction l1 as [|x xs IH]; intros [|y ys] Hlen Hp i; try discriminate Hlen.
  - destruct i; reflexivity.
  - destruct i as [|i']; [ reflexivity |]. cbn [firstn filter].
    assert (Hxy : p x = q y) by exact (Hp 0 x y eq_refl eq_refl).
    assert (Hrest : length (filter p (firstn i' xs)) = length (filter q (firstn i' ys))).
    { apply (IH ys); [ cbn in Hlen; lia | intros k a b Ha Hb; exact (Hp (S k) a b Ha Hb) ]. }
    rewrite Hxy. destruct (q y); cbn [length]; rewrite Hrest; reflexivity.
Qed.

(* a positional prefix extends by exactly the element at that index *)
Lemma firstn_S_nth {A : Type} (l : list A) (i : nat) (a : A) :
  nth_error l i = Some a -> firstn (S i) l = firstn i l ++ [a].
Proof.
  revert i; induction l as [|x xs IH]; intros [|i'] H; cbn in H; try discriminate.
  - injection H as <-. reflexivity.
  - cbn [firstn]. rewrite <- app_comm_cons. f_equal. apply IH; exact H.
Qed.

(* the contributor count of a filtered prefix is monotone and jumps by one at a contributing index *)
Lemma filter_firstn_le {A : Type} (g : A -> bool) (m : list A) (i : nat) :
  length (filter g (firstn i m)) <= length (filter g m).
Proof. rewrite <- (firstn_skipn i m) at 2. rewrite filter_app, length_app. lia. Qed.
Lemma adds_before_contrib_S {A B : Type} (f : A -> list B) (l : list A) (i : nat) (a : A) (b : B) :
  nth_error l i = Some a -> f a = [b] -> adds_before f l (S i) = S (adds_before f l i).
Proof.
  intros Hi Ha. unfold adds_before. rewrite (firstn_S_nth l i a Hi), filter_app, length_app.
  cbn [filter]. rewrite Ha. cbn [length]. lia.
Qed.
Lemma adds_before_mono {A B : Type} (f : A -> list B) (l : list A) (i j : nat) :
  i <= j -> adds_before f l i <= adds_before f l j.
Proof.
  intro Hij. unfold adds_before.
  replace (firstn i l) with (firstn i (firstn j l)) by (rewrite firstn_firstn, Nat.min_l; [ reflexivity | exact Hij ]).
  apply filter_firstn_le.
Qed.

(* a contributing index is determined by its contributor count: adds_before is injective on contributors *)
Lemma adds_before_inj {A B : Type} (f : A -> list B) (l : list A) (i j : nat) (ai aj : A) (bi bj : B) :
  nth_error l i = Some ai -> f ai = [bi] -> nth_error l j = Some aj -> f aj = [bj] ->
  adds_before f l i = adds_before f l j -> i = j.
Proof.
  intros Hi Hai Hj Haj Heq. destruct (Nat.lt_trichotomy i j) as [Hlt|[He|Hgt]]; [| exact He |].
  - exfalso. pose proof (adds_before_contrib_S f l i ai bi Hi Hai) as Hc.
    pose proof (adds_before_mono f l (S i) j Hlt) as Hm. lia.
  - exfalso. pose proof (adds_before_contrib_S f l j aj bj Hj Haj) as Hc.
    pose proof (adds_before_mono f l (S j) i Hgt) as Hm. lia.
Qed.

(* the per-edge addition body yields nothing or exactly the one New establishment *)
Lemma short_add_at_single {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.Refs.BlockRef idx) {st : Index.Refs.ShortStmtRef idx} (rows : list ShortLeftDecisionData) :
  forall x : {i : nat & Index.Edges.ShortLhsEdge st i},
    short_add_at (s:=s) br rows x = [] \/ exists b, short_add_at (s:=s) br rows x = [b].
Proof.
  intros [i e]. cbn [short_add_at]. destruct (nth_error rows i) as [row|]; [| left; reflexivity].
  destruct row; try (left; reflexivity). right. eexists. reflexivity.
Qed.

(* the informative form of the same fact, so the exact source element can be recovered computationally *)
Definition short_add_at_single_sig {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.Refs.BlockRef idx) {st : Index.Refs.ShortStmtRef idx} (rows : list ShortLeftDecisionData) :
  forall x : {i : nat & Index.Edges.ShortLhsEdge st i},
    (short_add_at (s:=s) br rows x = []) + { b : Est s | short_add_at (s:=s) br rows x = [b] }.
Proof.
  intros [i e]. cbn [short_add_at]. destruct (nth_error rows i) as [row|]; [| left; reflexivity].
  destruct row; try (left; reflexivity). right. exists (new_est br e n). reflexivity.
Defined.

(* the canonical New rank equals the flat_map's own contributor count over the source edges *)
Lemma short_new_rank_adds_eq {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st) (i : nat) :
  short_new_rank se i
    = adds_before (short_add_at (s:=s) (se_block se) (se_rows se)) (Index.Edges.short_lhs_edges (se_stmt se)) i.
Proof.
  unfold short_new_rank, adds_before. symmetry.
  apply (filter_firstn_len_eq
           (fun x => match short_add_at (s:=s) (se_block se) (se_rows se) x with [] => false | _ => true end)
           is_new_row (Index.Edges.short_lhs_edges (se_stmt se)) (se_rows se)).
  - rewrite se_rows_length. pose proof (Index.Edges.short_lhs_edges_ords (se_stmt se)) as Ho.
    apply (f_equal (@length _)) in Ho. rewrite length_map, length_seq in Ho. exact Ho.
  - intros k x y Hx Hy.
    assert (Hk : projT1 x = k).
    { pose proof (Index.Edges.short_lhs_edges_ords (se_stmt se)) as Ho.
      apply (f_equal (fun l => nth_error l k)) in Ho. rewrite nth_error_map, Hx in Ho. cbn in Ho.
      assert (Hlt : k < Index.Refs.sh_names (se_stmt se)).
      { rewrite <- se_rows_length. apply nth_error_Some. rewrite Hy. discriminate. }
      rewrite (nth_error_nth' (seq 0 _) 0) in Ho; [| rewrite length_seq; exact Hlt].
      rewrite seq_nth in Ho; [| exact Hlt]. cbn in Ho. injection Ho as Ho. exact Ho. }
    destruct x as [j e]. cbn in Hk. subst j. cbn [short_add_at]. rewrite Hy. destruct y; reflexivity.
Qed.

(* forward: a New row's establishment is the exact addition at its canonical rank at the event site *)
Lemma short_new_addition_at {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st) (i : nat)
  (r : ShortDecisionRowRef se i) (n : Names.OrdinaryIdentifier) (H : row_decision r = ShortNewData n) :
  nth_error (event_adds (short_event_site se)) (short_new_rank se i)
    = Some (new_est (se_block se) (row_subject r) n).
Proof.
  rewrite short_event_adds. unfold short_rows_adds. rewrite short_new_rank_adds_eq.
  apply (flat_map_opt_nth (short_add_at (s:=s) (se_block se) (se_rows se))
           (short_add_at_single (se_block se) (se_rows se))
           (Index.Edges.short_lhs_edges (se_stmt se)) i (existT _ i (row_subject r))
           (new_est (se_block se) (row_subject r) n)).
  - exact (short_row_edge_at se i r).
  - cbn [short_add_at]. rewrite (sdr_at r). unfold row_decision in H. rewrite H. reflexivity.
Qed.

(* decidable equality on retained short decision data, and hence on the option that a row pin lives in *)
Definition sld_eq_dec (a b : ShortLeftDecisionData) : {a = b} + {a <> b}.
Proof. decide equality; (apply Nat.eq_dec || apply ordinary_eq_dec). Defined.
Definition option_sld_eq_dec (a b : option ShortLeftDecisionData) : {a = b} + {a <> b}.
Proof. decide equality. apply sld_eq_dec. Defined.

(* the exact short decision-row ref is positionally unique: same event and index force the same ref *)
Lemma shortdecisionrowref_positional {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} {se : ShortEventRef bp st} {i : nat}
  (a b : ShortDecisionRowRef se i) : a = b.
Proof.
  destruct a as [ra ea Ha], b as [rb eb Hb].
  assert (Hr : ra = rb) by (pose proof (eq_trans (eq_sym Ha) Hb) as E; injection E as E; exact E).
  subst rb. rewrite (shortlhsedge_positional ea eb) in *. f_equal. apply (UIP_dec option_sld_eq_dec).
Qed.

(* the exact consequence of one short decision row: the New establishment addition, or exact no-addition *)
Inductive ShortRowConsequence {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (i : nat) (r : ShortDecisionRowRef se i) : Type :=
| ShortNoAddition (Hnn : is_new_row (row_decision r) = false)
| ShortNewAddition (n : Names.OrdinaryIdentifier) (Hnew : row_decision r = ShortNewData n)
    (add : EventAdditionRef bp (short_event_site se) (short_new_rank se i)).
Arguments ShortNoAddition {p idx s d bp st se i r} _.
Arguments ShortNewAddition {p idx s d bp st se i r} _ _ _.

(* the one exact event addition of a New row, at the canonical rank: the term the consequence carries *)
Definition short_row_addition {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st) (i : nat)
  (r : ShortDecisionRowRef se i) (n : Names.OrdinaryIdentifier) (H : row_decision r = ShortNewData n)
  : EventAdditionRef bp (short_event_site se) (short_new_rank se i) :=
  mk_event_addition (new_est (se_block se) (row_subject r) n) (short_new_addition_at se i r n H).

(* the one canonical consequence of a row, dispatched on its retained tag: New adds, everything else does not *)
Definition short_row_consequence {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (i : nat) (r : ShortDecisionRowRef se i) : ShortRowConsequence se i r.
Proof.
  destruct (row_decision r) as [|earlier|n|m|m|f2 sc] eqn:Hd;
    try (apply ShortNoAddition; rewrite Hd; reflexivity).
  exact (ShortNewAddition n Hd (short_row_addition se i r n Hd)).
Defined.

(* the exact addition a consequence carries: the New establishment, or none for a non-adding row *)
Definition short_consequence_addition {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} {se : ShortEventRef bp st}
  {i : nat} {r : ShortDecisionRowRef se i} (c : ShortRowConsequence se i r)
  : option (EventAdditionRef bp (short_event_site se) (short_new_rank se i)) :=
  match c with ShortNoAddition _ => None | ShortNewAddition _ _ add => Some add end.

(* the canonical consequence of a New row carries exactly that row's one addition *)
Lemma short_consequence_addition_new {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (i : nat) (r : ShortDecisionRowRef se i) (n : Names.OrdinaryIdentifier) (H : row_decision r = ShortNewData n) :
  short_consequence_addition (short_row_consequence se i r) = Some (short_row_addition se i r n H).
Proof.
  destruct (short_row_consequence se i r) as [Hnn | n0 Hnew add].
  - exfalso. rewrite H in Hnn. discriminate Hnn.
  - cbn. f_equal. apply eventadditionref_positional.
Qed.

(* the canonical consequence of a non-New row carries no addition *)
Lemma short_consequence_addition_nonnew {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (i : nat) (r : ShortDecisionRowRef se i) :
  is_new_row (row_decision r) = false -> short_consequence_addition (short_row_consequence se i r) = None.
Proof.
  intro Hnn. destruct (short_row_consequence se i r) as [Hnn2 | n0 Hnew add].
  - reflexivity.
  - rewrite Hnew in Hnn. discriminate Hnn.
Qed.

(* the exact establishment of a New row's addition, at the canonical event site and rank *)
Definition short_new_establishment {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st) (i : nat)
  (add : EventAdditionRef bp (short_event_site se) (short_new_rank se i)) : EstablishmentRef bp :=
  mk_establishment (short_event_site se) (short_new_rank se i) add.

(* the exact source of a short event addition: the unique New decision row at the canonical rank *)
Record ShortAdditionSourceRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (k : nat) (ea : EventAdditionRef bp (short_event_site se) k) : Type := mk_short_source {
  sas_index : nat ;
  sas_row   : ShortDecisionRowRef se sas_index ;
  sas_name  : Names.OrdinaryIdentifier ;
  sas_new   : row_decision sas_row = ShortNewData sas_name ;
  sas_rank  : short_new_rank se sas_index = k
}.
Arguments mk_short_source {p idx s d bp st se k ea} _ _ _ _ _.
Arguments sas_index {p idx s d bp st se k ea} _.
Arguments sas_row {p idx s d bp st se k ea} _.
Arguments sas_name {p idx s d bp st se k ea} _.
Arguments sas_new {p idx s d bp st se k ea} _.
Arguments sas_rank {p idx s d bp st se k ea} _.

(* every short event addition is sourced by exactly its one exact New decision row at the canonical rank *)
Definition short_addition_source {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (k : nat) (ea : EventAdditionRef bp (short_event_site se) k) : ShortAdditionSourceRef se k ea.
Proof.
  pose proof (ea_at ea) as Hat. rewrite short_event_adds in Hat. unfold short_rows_adds in Hat.
  destruct (flat_map_opt_source (short_add_at (s:=s) (se_block se) (se_rows se))
              (short_add_at_single_sig (se_block se) (se_rows se)) _ k (ea_est ea) Hat)
    as [j [a [Hj [Ha Hcnt]]]].
  pose proof (short_edge_projT1 (se_stmt se) j a Hj) as Hje.
  destruct a as [j' e]. cbn in Hje. subst j'.
  cbn [short_add_at] in Ha. destruct (nth_error (se_rows se) j) as [row|] eqn:Hrow; [| discriminate Ha].
  destruct row; try discriminate Ha.
  refine (mk_short_source j (mk_short_row (ShortNewData n) e Hrow) n eq_refl _).
  rewrite short_new_rank_adds_eq. exact Hcnt.
Defined.

(* the canonical New rank is injective across New rows: equal rank forces the same left index *)
Lemma short_new_rank_inj {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (i i' : nat) (r : ShortDecisionRowRef se i) (r' : ShortDecisionRowRef se i')
  (n n' : Names.OrdinaryIdentifier)
  (H : row_decision r = ShortNewData n) (H' : row_decision r' = ShortNewData n') :
  short_new_rank se i = short_new_rank se i' -> i = i'.
Proof.
  intro Heq. rewrite !short_new_rank_adds_eq in Heq.
  apply (adds_before_inj (short_add_at (s:=s) (se_block se) (se_rows se))
           (Index.Edges.short_lhs_edges (se_stmt se)) i i'
           (existT _ i (row_subject r)) (existT _ i' (row_subject r'))
           (new_est (se_block se) (row_subject r) n) (new_est (se_block se) (row_subject r') n')).
  - exact (short_row_edge_at se i r).
  - cbn [short_add_at]. rewrite (sdr_at r). unfold row_decision in H. rewrite H. reflexivity.
  - exact (short_row_edge_at se i' r').
  - cbn [short_add_at]. rewrite (sdr_at r'). unfold row_decision in H'. rewrite H'. reflexivity.
  - exact Heq.
Qed.

(* round trip: a New row's consequence addition sources back to the exact same row index and ref *)
Lemma short_row_roundtrip {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (i : nat) (r : ShortDecisionRowRef se i) (n : Names.OrdinaryIdentifier) (H : row_decision r = ShortNewData n) :
  sas_index (short_addition_source se (short_new_rank se i) (short_row_addition se i r n H)) = i.
Proof.
  set (src := short_addition_source se (short_new_rank se i) (short_row_addition se i r n H)).
  apply (short_new_rank_inj se (sas_index src) i (sas_row src) r (sas_name src) n (sas_new src) H).
  exact (sas_rank src).
Qed.
Lemma short_row_roundtrip_ref {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (i : nat) (r : ShortDecisionRowRef se i) (n : Names.OrdinaryIdentifier) (H : row_decision r = ShortNewData n) :
  eq_rect _ (fun k => ShortDecisionRowRef se k)
    (sas_row (short_addition_source se (short_new_rank se i) (short_row_addition se i r n H)))
    i (short_row_roundtrip se i r n H) = r.
Proof. apply shortdecisionrowref_positional. Qed.

(* round trip: any addition sources to a New row whose consequence addition is that exact same addition *)
Lemma short_addition_roundtrip {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.Refs.ShortStmtRef idx} (se : ShortEventRef bp st)
  (k : nat) (ea : EventAdditionRef bp (short_event_site se) k) :
  eq_rect _ (fun m => EventAdditionRef bp (short_event_site se) m)
    (short_row_addition se (sas_index (short_addition_source se k ea)) (sas_row (short_addition_source se k ea))
       (sas_name (short_addition_source se k ea)) (sas_new (short_addition_source se k ea)))
    k (sas_rank (short_addition_source se k ea)) = ea.
Proof. apply eventadditionref_positional. Qed.

(* the retained judgment is about the exact queried statement *)
Lemma short_event_subject {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (st : Index.Refs.ShortStmtRef idx) :
  se_stmt (short_event bp st) = st.
Proof. apply shortstmtref_positional. exact (se_subject (short_event bp st)). Qed.

(* a positional hit inside a prefix is an in-range hit of the whole list *)
Lemma nth_error_firstn_some {A} (l : list A) (i j : nat) (x : A) :
  nth_error (firstn i l) j = Some x -> j < i /\ nth_error l j = Some x.
Proof.
  revert i j x. induction l as [|a l IH]; intros i j x H.
  - destruct i; cbn in H; destruct j; discriminate.
  - destruct i as [|i']; cbn in H; [ destruct j; discriminate |].
    destruct j as [|j']; cbn in H.
    + injection H as <-. split; [ lia | reflexivity ].
    + destruct (IH i' j' x H) as [Hlt Hnth]. split; [ lia | exact Hnth ].
Qed.

(* the exact declaration event ref: the exact trace, ordinal, scope, and retained decision rows, pinned *)
Record DeclEventRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (t : Index.Core.NodeRef idx) : Type := mk_decl_event {
  de_block : Index.Refs.BlockRef idx ;
  de_trace : BlockTraceRef bp (Index.Refs.bl_node de_block) ;
  de_ord   : nat ;
  de_sc    : ScopeId s ;
  de_rows  : list DeclBinderDecisionData ;
  de_at : nth_error (trow_evs (btr_row de_trace)) de_ord = Some (BEvDecl de_sc t de_rows)
}.
Arguments mk_decl_event {p idx s d bp t} _ _ _ _ _ _.
Arguments de_block {p idx s d bp t} _.
Arguments de_trace {p idx s d bp t} _.
Arguments de_ord {p idx s d bp t} _.
Arguments de_sc {p idx s d bp t} _.
Arguments de_rows {p idx s d bp t} _.
Arguments de_at {p idx s d bp t} _.

Definition de_event {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t)
  : BlockEventRef (de_trace de) := mk_block_event (de_ord de) (nth_error_lt _ _ _ (de_at de)).

Definition decl_state_before {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t)
  : BlockStateRef (ber_pre (de_event de)) := block_state (ber_pre (de_event de)).

(* the retained decl rows are exactly the canonical decision over the exact predecessor state's members *)
Lemma de_rows_decide {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t) :
  de_rows de = decl_decide_rows (map es_est (bs_members (decl_state_before de))) t.
Proof.
  pose proof (de_at de) as Hat.
  set (tr := btr_row (de_trace de)) in *.
  destruct (bp_traces_row bp tr (nth_error_In _ _ (btr_at (de_trace de)))) as [pr [r [Hb [_ [_ Hform]]]]].
  assert (Hevs : trow_evs tr = block_fold s (Index.Refs.mkBlockRef r Hb) (Index.Child.all_children r) (pkg_env_of s pr))
    by (rewrite Hform; reflexivity).
  pose proof Hat as Hat2. rewrite Hevs in Hat2.
  destruct (block_fold_nth_env (Index.Refs.mkBlockRef r Hb) (Index.Child.all_children r) (pkg_env_of s pr)
              (de_ord de) _ Hat2) as [x [_ He]].
  set (c := Index.Child.ca_child (projT2 x)) in *.
  assert (Hview : Index.Core.node_view c = Index.Model.VStmt Index.Model.SSDecl)
    by exact (block_event_decl_view _ _ _ _ _ _ _ _ (eq_sym He)).
  rewrite (block_event_decl_eval (Index.Refs.mkBlockRef r Hb)
             (pkg_env_of s pr ++ flat_map (bev_adds (Index.Refs.mkBlockRef r Hb))
                (firstn (de_ord de) (block_fold s (Index.Refs.mkBlockRef r Hb) (Index.Child.all_children r)
                   (pkg_env_of s pr)))) c _ eq_refl Hview) in He.
  injection He as _ Ht Herows.
  rewrite <- Ht in Herows. rewrite Herows.
  f_equal.
  assert (Hbs : bs_members (decl_state_before de) = state_refs bp (btr_ord (de_trace de)) (de_ord de))
    by reflexivity.
  rewrite Hbs.
  rewrite (state_ests bp (btr_ord (de_trace de)) (de_ord de) tr (btr_at (de_trace de))
             (Nat.lt_le_incl _ _ (nth_error_lt _ _ _ Hat))).
  assert (Hpkg : map es_est (ledger_refs bp (trow_pkg tr)) = pkg_env_of s pr).
  { replace (trow_pkg tr) with (PI.pr_pos pr) by (rewrite Hform; reflexivity).
    exact (package_env_ests bp pr). }
  rewrite Hpkg.
  replace (trow_block tr) with (Index.Refs.mkBlockRef r Hb) by (rewrite Hform; reflexivity).
  rewrite Hevs. reflexivity.
Qed.

(* one indexed row of a map over combine (seq 0 len) l projects the element and its index *)
Lemma combine_seq_nth {A : Type} (l : list A) (start i : nat) (a : A) :
  nth_error l i = Some a -> nth_error (combine (seq start (length l)) l) i = Some (start + i, a).
Proof.
  revert start i. induction l as [|x xs IH]; intros start i H; [ destruct i; discriminate H |].
  destruct i as [|i']; cbn in H |- *.
  - injection H as <-. rewrite Nat.add_0_r. reflexivity.
  - rewrite (IH (S start) i' H). rewrite <- plus_n_Sm. reflexivity.
Qed.

(* the retained decl row at an exact binder index is the canonical decision over that binder *)
Lemma decl_decide_rows_nth {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) (t : Index.Core.NodeRef idx) (i : nat) (bd : Index.Core.NodeRef idx) :
  nth_error (decl_binders t) i = Some bd ->
  nth_error (decl_decide_rows env t) i = Some (decl_binder_decide env t i bd).
Proof.
  intro H. unfold decl_decide_rows. rewrite nth_error_map.
  rewrite (combine_seq_nth (decl_binders t) 0 i bd H). reflexivity.
Qed.

(* the exact decl-binder fact, INDEXED by the retained decision row: for a given row exactly one case inhabits *)
Inductive DeclBinderFact {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b0 : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b0}
  {c : BlockCutRef tr} (pre : BlockStateRef c) (t : Index.Core.NodeRef idx) (i : nat) (bd : Index.Core.NodeRef idx)
  : DeclBinderDecisionData -> Type :=
| DeclBlankFact : binder_ident bd = None -> DeclBinderFact pre t i bd DeclBlankData
| DeclDuplicateFact : forall (n : Names.OrdinaryIdentifier) (j : nat) (bj : Index.Core.NodeRef idx),
    binder_ident bd = Some n -> j < i -> nth_error (decl_binders t) j = Some bj -> binder_ident bj = Some n ->
    find_ord (binder_name_matches n) 0 (firstn i (decl_binders t)) = Some (j, bj) ->
    DeclBinderFact pre t i bd (DeclDuplicateEarlierData j)
| DeclFreshFact : forall (n : Names.OrdinaryIdentifier),
    binder_ident bd = Some n ->
    find_ord (binder_name_matches n) 0 (firstn i (decl_binders t)) = None ->
    (forall mr : BlockMemberRef pre, same_block_cand n (es_est (bm_ref mr)) = false) ->
    DeclBinderFact pre t i bd DeclFreshData
| DeclRedeclaredFact : forall (n : Names.OrdinaryIdentifier) (mr : BlockMemberRef pre),
    binder_ident bd = Some n ->
    find_ord (binder_name_matches n) 0 (firstn i (decl_binders t)) = None ->
    find_two_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = None ->
    find_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = Some (bm_ord mr, es_est (bm_ref mr)) ->
    DeclBinderFact pre t i bd (DeclRedeclaredPriorData (bm_ord mr))
| DeclAmbiguousFact : forall (n : Names.OrdinaryIdentifier) (grp : LocalGroupRef pre n)
    (mr1 mr2 : BlockMemberRef pre),
    binder_ident bd = Some n ->
    find_ord (binder_name_matches n) 0 (firstn i (decl_binders t)) = None ->
    find_two_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = Some (bm_ord mr1, bm_ord mr2) ->
    lg_members grp = local_group_refs pre n ->
    same_block_cand n (es_est (bm_ref mr1)) = true -> same_block_cand n (es_est (bm_ref mr2)) = true ->
    DeclBinderFact pre t i bd (DeclAlreadyAmbiguousData (bm_ord mr1) (bm_ord mr2)).
Arguments DeclBlankFact {p idx s d bp b0 tr c pre t i bd} _.
Arguments DeclDuplicateFact {p idx s d bp b0 tr c pre t i bd} _ _ _ _ _ _ _ _.
Arguments DeclFreshFact {p idx s d bp b0 tr c pre t i bd} _ _ _ _.
Arguments DeclRedeclaredFact {p idx s d bp b0 tr c pre t i bd} _ _ _ _ _ _.
Arguments DeclAmbiguousFact {p idx s d bp b0 tr c pre t i bd} _ _ _ _ _ _ _ _ _.

(* the one canonical decl-binder fact, indexed by its canonical decision over the exact state *)
Definition decl_binder_fact {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b0 : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b0}
  {c : BlockCutRef tr} (pre : BlockStateRef c) (t : Index.Core.NodeRef idx) (i : nat) (bd : Index.Core.NodeRef idx)
  : DeclBinderFact pre t i bd (decl_binder_decide (map es_est (bs_members pre)) t i bd).
Proof.
  unfold decl_binder_decide.
  destruct (binder_ident bd) as [n|] eqn:Hb; [| exact (DeclBlankFact Hb) ].
  destruct (find_ord (binder_name_matches n) 0 (firstn i (decl_binders t))) as [[j bj]|] eqn:Hdup.
  { destruct (find_ord_found (binder_name_matches n) (firstn i (decl_binders t)) 0 j bj Hdup)
      as [_ [Hnth [Hbm _]]].
    rewrite Nat.sub_0_r in Hnth.
    destruct (nth_error_firstn_some (decl_binders t) i j bj Hnth) as [Hlt Hjn].
    unfold binder_name_matches in Hbm.
    destruct (binder_ident bj) as [m|] eqn:Hbj; [| discriminate Hbm].
    apply Names.ordinary_equalb_spec in Hbm. subst m.
    exact (DeclDuplicateFact n j bj Hb Hlt Hjn Hbj Hdup). }
  destruct (find_two_ord (same_block_cand n) 0 (map es_est (bs_members pre))) as [[j0 j1]|] eqn:Hft.
  { destruct (find_two_ord_found (same_block_cand n) (map es_est (bs_members pre)) 0 j0 j1 Hft)
      as [_ [Hlt [Hex0 Hex1]]].
    destruct (nth_error (map es_est (bs_members pre)) j0) as [m0|] eqn:Hm0;
      [| exfalso; destruct Hex0 as [x0 [Hnx _]]; rewrite Nat.sub_0_r, Hm0 in Hnx; discriminate ].
    destruct (nth_error (map es_est (bs_members pre)) j1) as [m1|] eqn:Hm1;
      [| exfalso; destruct Hex1 as [x1 [Hnx _]]; rewrite Nat.sub_0_r, Hm1 in Hnx; discriminate ].
    destruct (state_member_ref pre j0 m0 Hm0) as [mr0 [He0 Ho0]].
    destruct (state_member_ref pre j1 m1 Hm1) as [mr1 [He1 Ho1]].
    rewrite <- Ho0, <- Ho1.
    apply (DeclAmbiguousFact n (local_group pre n) mr0 mr1 Hb Hdup).
    - rewrite Ho0, Ho1. exact Hft.
    - exact (lg_ok (local_group pre n)).
    - rewrite He0. destruct Hex0 as [x0 [Hnx Hfx]]. rewrite Nat.sub_0_r, Hm0 in Hnx.
      injection Hnx as <-. exact Hfx.
    - rewrite He1. destruct Hex1 as [x1 [Hnx Hfx]]. rewrite Nat.sub_0_r, Hm1 in Hnx.
      injection Hnx as <-. exact Hfx. }
  destruct (find_ord (same_block_cand n) 0 (map es_est (bs_members pre))) as [[j m]|] eqn:Ho.
  { destruct (find_ord_found (same_block_cand n) (map es_est (bs_members pre)) 0 j m Ho)
      as [_ [Hn' [Hf _]]].
    rewrite Nat.sub_0_r in Hn'.
    destruct (state_member_ref pre j m Hn') as [mr [He Hoo]].
    rewrite <- Hoo.
    apply (DeclRedeclaredFact n mr Hb Hdup Hft).
    rewrite Hoo, He. exact Ho. }
  { apply (DeclFreshFact n Hb Hdup). intro mr.
    apply (find_ord_none (same_block_cand n) (map es_est (bs_members pre)) 0 Ho).
    apply (nth_error_In _ (bm_ord mr)). rewrite nth_error_map, (bm_at mr). reflexivity. }
Defined.

(* the length of the retained decl rows is exactly the binder count *)
Lemma de_rows_length {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t) :
  length (de_rows de) = length (decl_binders t).
Proof.
  rewrite de_rows_decide. unfold decl_decide_rows. rewrite length_map, combine_length, length_seq. lia.
Qed.

(* the exact declaration binder occurrence: the node is PINNED to the source at index i, never supplied free *)
Record DeclBinderAt {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t)
  (i : nat) : Type := mk_decl_binder_at {
  dba_node : Index.Core.NodeRef idx ;
  dba_at   : nth_error (decl_binders t) i = Some dba_node
}.
Arguments mk_decl_binder_at {p idx s d bp t de i} _ _.
Arguments dba_node {p idx s d bp t de i} _.
Arguments dba_at {p idx s d bp t de i} _.

(* the exact per-binder decl decision-row ref: the exact binder occurrence + transparent retained row, Prop-pinned *)
Record DeclDecisionRowRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t)
  (i : nat) : Type := mk_decl_row {
  ddr_binder : DeclBinderAt de i ;
  ddr_row    : DeclBinderDecisionData ;
  ddr_at     : nth_error (de_rows de) i = Some ddr_row
}.
Arguments mk_decl_row {p idx s d bp t de i} _ _ _.
Arguments ddr_binder {p idx s d bp t de i} _.
Arguments ddr_row {p idx s d bp t de i} _.
Arguments ddr_at {p idx s d bp t de i} _.

(* transparent, proof-insensitive projections a live consumer reads *)
Definition decl_row_subject {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} {de : DeclEventRef bp t} {i}
  (r : DeclDecisionRowRef de i) : Index.Core.NodeRef idx := dba_node (ddr_binder r).
Definition decl_row_decision {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} {de : DeclEventRef bp t} {i}
  (r : DeclDecisionRowRef de i) : DeclBinderDecisionData := ddr_row r.

(* the one canonical per-binder decision-row ref, built cheaply: the exact occurrence + retained row lookup *)
Definition decl_decision_row {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t)
  (i : nat) (bd : Index.Core.NodeRef idx) (H : nth_error (decl_binders t) i = Some bd)
  : DeclDecisionRowRef de i.
Proof.
  destruct (nth_error (de_rows de) i) as [row|] eqn:Hrow.
  - exact (mk_decl_row (mk_decl_binder_at bd H) row Hrow).
  - exfalso. apply nth_error_None in Hrow. rewrite de_rows_length in Hrow.
    assert (Hlt : i < length (decl_binders t)) by (apply nth_error_Some; rewrite H; discriminate).
    lia.
Defined.

(* the derived proof-bearing case fact for a decl row ref: authority for the laws, off every live path *)
Definition decl_row_fact {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t)
  (i : nat) (r : DeclDecisionRowRef de i)
  : DeclBinderFact (decl_state_before de) t i (dba_node (ddr_binder r)) (ddr_row r).
Proof.
  assert (Hcanon : ddr_row r
    = decl_binder_decide (map es_est (bs_members (decl_state_before de))) t i (dba_node (ddr_binder r))).
  { pose proof (ddr_at r) as Ha. rewrite de_rows_decide in Ha.
    rewrite (decl_decide_rows_nth _ t i (dba_node (ddr_binder r)) (dba_at (ddr_binder r))) in Ha.
    injection Ha as Ha. exact (eq_sym Ha). }
  rewrite Hcanon. exact (decl_binder_fact (decl_state_before de) t i (dba_node (ddr_binder r))).
Defined.

(* the exact declaration judgment: a view giving each binder's canonical decision-row ref, never a table *)
Definition DeclJudgmentRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t) : Type :=
  forall (i : nat) (bd : Index.Core.NodeRef idx), nth_error (decl_binders t) i = Some bd ->
    DeclDecisionRowRef de i.

Definition decl_judgment_ref {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t)
  : DeclJudgmentRef de := fun i bd H => decl_decision_row de i bd H.

(* the exact finite event site of a declaration event, derived from its retained trace/ordinal membership *)
Lemma decl_event_site_lt {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t) :
  de_ord de < trace_event_count bp (btr_ord (de_trace de)).
Proof.
  unfold trace_event_count. rewrite (btr_at (de_trace de)). exact (nth_error_lt _ _ _ (de_at de)).
Qed.
Definition decl_event_site {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t)
  : EvSite bp := BlockEventAt (btr_ord (de_trace de)) (de_ord de) (decl_event_site_lt de).

(* two lists paired index-wise: a common index that both hit lands in the pairing *)
Lemma nth_error_combine {A B : Type} (l1 : list A) (l2 : list B) (i : nat) (a : A) (b : B) :
  nth_error l1 i = Some a -> nth_error l2 i = Some b -> nth_error (combine l1 l2) i = Some (a, b).
Proof.
  revert l2 i. induction l1 as [|x xs IH]; intros l2 i H1 H2; [ destruct i; discriminate H1 |].
  destruct l2 as [|y ys]; [ destruct i; discriminate H2 |].
  destruct i as [|i']; cbn in *; [ injection H1 as <-; injection H2 as <-; reflexivity | exact (IH ys i' H1 H2) ].
Qed.

(* whether a retained decl row is nonblank *)
Definition is_nonblank_row (r : DeclBinderDecisionData) : bool :=
  match r with DeclBlankData => false | _ => true end.

(* the additions at a declaration event's exact site are exactly its projected nonblank establishments *)
Lemma decl_event_adds {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t) :
  event_adds (decl_event_site de) = decl_rows_adds (de_sc de) t (de_rows de).
Proof.
  unfold decl_event_site.
  rewrite (event_adds_block bp (btr_ord (de_trace de)) (de_ord de) (decl_event_site_lt de)
             (btr_row (de_trace de)) (BEvDecl (de_sc de) t (de_rows de)) (btr_at (de_trace de)) (de_at de)).
  cbn [bev_adds]. reflexivity.
Qed.

(* the canonical addition ordinal of a decl row: the count of nonblank rows strictly before its binder index *)
Definition decl_new_rank {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t)
  (i : nat) : nat := length (filter is_nonblank_row (firstn i (de_rows de))).

(* the nonblank branch of the decl addition body is exactly the binder's establishment option *)
Lemma decl_add_at_nonblank_eq {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (row : DeclBinderDecisionData) (bd : Index.Core.NodeRef idx) :
  row <> DeclBlankData ->
  decl_add_at sc (row, bd) = match node_binder_est sc bd with Some e => [e] | None => [] end.
Proof. intro Hnb. destruct row; [ exfalso; apply Hnb; reflexivity | reflexivity.. ]. Qed.

(* the decl decision is blank exactly when the binder has no name *)
Lemma decl_decide_none_blank {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) (t bd : Index.Core.NodeRef idx) (i : nat) :
  binder_ident bd = None -> decl_binder_decide env t i bd = DeclBlankData.
Proof. intro Hid. unfold decl_binder_decide. rewrite Hid. reflexivity. Qed.
Lemma decl_decide_some_nonblank {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) (t bd : Index.Core.NodeRef idx) (i : nat) (n : Names.OrdinaryIdentifier) :
  binder_ident bd = Some n -> decl_binder_decide env t i bd <> DeclBlankData.
Proof.
  intro Hid. unfold decl_binder_decide. rewrite Hid.
  destruct (find_ord (binder_name_matches n) 0 (firstn i (decl_binders t))) as [[j _]|]; [ discriminate |].
  destruct (find_two_ord (same_block_cand n) 0 env) as [[j0 j1]|]; [ discriminate |].
  destruct (find_ord (same_block_cand n) 0 env) as [[j _]|]; discriminate.
Qed.

(* the decl addition body yields nothing or exactly the one binder establishment *)
Lemma decl_add_at_single {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx} (sc : ScopeId s) :
  forall rb : DeclBinderDecisionData * Index.Core.NodeRef idx,
    decl_add_at sc rb = [] \/ exists e, decl_add_at sc rb = [e].
Proof.
  intros [row bd]. destruct row; cbn [decl_add_at]; try (left; reflexivity);
    destruct (node_binder_est sc bd) as [e|]; solve [ right; eexists; reflexivity | left; reflexivity ].
Qed.
Definition decl_add_at_single_sig {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx} (sc : ScopeId s) :
  forall rb : DeclBinderDecisionData * Index.Core.NodeRef idx,
    (decl_add_at sc rb = []) + { e : Est s | decl_add_at sc rb = [e] }.
Proof.
  intros [row bd]. destruct row; cbn [decl_add_at]; try (left; reflexivity);
    destruct (node_binder_est sc bd) as [e|]; solve [ right; exists e; reflexivity | left; reflexivity ].
Defined.

(* the canonical nonblank rank equals the flat_map's own contributor count over the paired binders *)
Lemma decl_new_rank_adds_eq {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t) (i : nat) :
  decl_new_rank de i = adds_before (decl_add_at (de_sc de)) (combine (de_rows de) (decl_binders t)) i.
Proof.
  unfold decl_new_rank, adds_before. symmetry.
  apply (filter_firstn_len_eq
           (fun rb => match decl_add_at (de_sc de) rb with [] => false | _ => true end)
           is_nonblank_row (combine (de_rows de) (decl_binders t)) (de_rows de)).
  - rewrite combine_length, <- (de_rows_length de), Nat.min_id. reflexivity.
  - intros k x y Hx Hy.
    assert (Hklt : k < length (decl_binders t))
      by (rewrite <- (de_rows_length de); apply nth_error_Some; rewrite Hy; discriminate).
    destruct (nth_error (decl_binders t) k) as [bdk|] eqn:Hbd; [| apply nth_error_None in Hbd; lia].
    assert (Hxc : x = (y, bdk)).
    { pose proof (nth_error_combine (de_rows de) (decl_binders t) k y bdk Hy Hbd) as Hc.
      rewrite Hx in Hc. injection Hc as Hc. exact Hc. }
    subst x.
    pose proof (decl_decide_rows_nth (map es_est (bs_members (decl_state_before de))) t k bdk Hbd) as Hn.
    rewrite <- (de_rows_decide de) in Hn. rewrite Hn in Hy. injection Hy as Hy.
    destruct (binder_ident bdk) as [n|] eqn:Hid.
    + assert (Hynb : y <> DeclBlankData) by (rewrite <- Hy; exact (decl_decide_some_nonblank _ t bdk k n Hid)).
      rewrite (decl_add_at_nonblank_eq (de_sc de) y bdk Hynb).
      destruct (decl_binder_est_some (de_sc de) t bdk n (nth_error_In _ _ Hbd) Hid) as [e He'].
      rewrite He'. destruct y; [ exfalso; apply Hynb; reflexivity | reflexivity.. ].
    + assert (Hyb : y = DeclBlankData) by (rewrite <- Hy; exact (decl_decide_none_blank _ t bdk k Hid)).
      rewrite Hyb. reflexivity.
Qed.

(* forward: a nonblank row's binder establishment is the exact addition at its canonical rank at the site *)
Lemma decl_nonblank_addition_at {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t) (i : nat)
  (r : DeclDecisionRowRef de i) (e : Est s)
  (Hnb : decl_row_decision r <> DeclBlankData)
  (He : node_binder_est (de_sc de) (decl_row_subject r) = Some e) :
  nth_error (event_adds (decl_event_site de)) (decl_new_rank de i) = Some e.
Proof.
  rewrite decl_event_adds. unfold decl_rows_adds. rewrite decl_new_rank_adds_eq.
  apply (flat_map_opt_nth (decl_add_at (de_sc de)) (decl_add_at_single (de_sc de))
           (combine (de_rows de) (decl_binders t)) i (decl_row_decision r, decl_row_subject r) e).
  - apply nth_error_combine; [ exact (ddr_at r) | exact (dba_at (ddr_binder r)) ].
  - rewrite (decl_add_at_nonblank_eq (de_sc de) (decl_row_decision r) (decl_row_subject r) Hnb).
    rewrite He. reflexivity.
Qed.

(* the paired lists split back: a combine hit is a hit in each component at the same index *)
Lemma nth_error_combine_inv {A B : Type} (l1 : list A) (l2 : list B) (j : nat) (a : A) (b : B) :
  nth_error (combine l1 l2) j = Some (a, b) -> nth_error l1 j = Some a /\ nth_error l2 j = Some b.
Proof.
  revert l2 j. induction l1 as [|x xs IH]; intros [|y ys] [|j'] H; cbn in H; try discriminate.
  - injection H as <- <-. split; reflexivity.
  - exact (IH ys j' H).
Qed.

(* the retained decl row is exactly the canonical decision for its exact binder and predecessor state *)
Lemma decl_row_canonical {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t) (i : nat)
  (r : DeclDecisionRowRef de i) :
  decl_row_decision r
    = decl_binder_decide (map es_est (bs_members (decl_state_before de))) t i (decl_row_subject r).
Proof.
  unfold decl_row_decision, decl_row_subject. pose proof (ddr_at r) as Ha. rewrite de_rows_decide in Ha.
  rewrite (decl_decide_rows_nth _ t i (dba_node (ddr_binder r)) (dba_at (ddr_binder r))) in Ha.
  injection Ha as Ha. exact (eq_sym Ha).
Qed.

(* a nonblank decl row always has its exact binder establishment: its binder is named and binder-role *)
Definition decl_row_nonblank_est {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t) (i : nat)
  (r : DeclDecisionRowRef de i) :
  decl_row_decision r <> DeclBlankData -> { e : Est s | node_binder_est (de_sc de) (decl_row_subject r) = Some e }.
Proof.
  intro Hnb. destruct (binder_ident (decl_row_subject r)) as [n|] eqn:Hid.
  - exact (decl_binder_est_some (de_sc de) t (decl_row_subject r) n
             (nth_error_In _ _ (dba_at (ddr_binder r))) Hid).
  - exfalso. apply Hnb. rewrite (decl_row_canonical de i r).
    exact (decl_decide_none_blank _ t (decl_row_subject r) i Hid).
Defined.

(* decidable equality on decl decision data, and hence on the options that decl ref pins live in *)
Definition dbd_eq_dec (a b : DeclBinderDecisionData) : {a = b} + {a <> b}.
Proof. decide equality; apply Nat.eq_dec. Defined.
Definition option_dbd_eq_dec (a b : option DeclBinderDecisionData) : {a = b} + {a <> b}.
Proof. decide equality. apply dbd_eq_dec. Defined.

(* the exact decl binder occurrence and decision-row ref are positionally unique at their event and index *)
Lemma declbinderat_positional {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} {de : DeclEventRef bp t} {i : nat}
  (a b : DeclBinderAt de i) : a = b.
Proof.
  destruct a as [na Ha], b as [nb Hb].
  assert (na = nb) by (pose proof (eq_trans (eq_sym Ha) Hb) as E; injection E as E; exact E).
  subst nb. f_equal. apply (UIP_dec option_noderef_eq_dec).
Qed.
Lemma decldecisionrowref_positional {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} {de : DeclEventRef bp t} {i : nat}
  (a b : DeclDecisionRowRef de i) : a = b.
Proof.
  destruct a as [ba ra Ha], b as [bb rb Hb].
  assert (Hr : ra = rb) by (pose proof (eq_trans (eq_sym Ha) Hb) as E; injection E as E; exact E).
  subst rb. rewrite (declbinderat_positional ba bb). f_equal. apply (UIP_dec option_dbd_eq_dec).
Qed.

(* the one exact event addition of a nonblank row, at the canonical rank: the term the consequence carries *)
Definition decl_row_addition {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t) (i : nat)
  (r : DeclDecisionRowRef de i) (e : Est s) (Hnb : decl_row_decision r <> DeclBlankData)
  (He : node_binder_est (de_sc de) (decl_row_subject r) = Some e)
  : EventAdditionRef bp (decl_event_site de) (decl_new_rank de i) :=
  mk_event_addition e (decl_nonblank_addition_at de i r e Hnb He).

(* the exact consequence of one decl decision row: the binder establishment addition, or exact no-addition *)
Inductive DeclRowConsequence {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t)
  (i : nat) (r : DeclDecisionRowRef de i) : Type :=
| DeclNoAddition (Hb : decl_row_decision r = DeclBlankData)
| DeclBinderAddition (e : Est s) (Hnb : decl_row_decision r <> DeclBlankData)
    (He : node_binder_est (de_sc de) (decl_row_subject r) = Some e)
    (add : EventAdditionRef bp (decl_event_site de) (decl_new_rank de i)).
Arguments DeclNoAddition {p idx s d bp t de i r} _.
Arguments DeclBinderAddition {p idx s d bp t de i r} _ _ _ _.

(* the one canonical consequence of a decl row, dispatched on its tag: nonblank adds, blank does not *)
Definition decl_row_consequence {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t)
  (i : nat) (r : DeclDecisionRowRef de i) : DeclRowConsequence de i r.
Proof.
  destruct (decl_row_decision r) as [| e0 | | m0 | a0 a1] eqn:Hd;
    [ exact (DeclNoAddition Hd)
    | assert (Hnb : decl_row_decision r <> DeclBlankData) by (rewrite Hd; discriminate);
      destruct (decl_row_nonblank_est de i r Hnb) as [e He];
      exact (DeclBinderAddition e Hnb He (decl_row_addition de i r e Hnb He)) ..].
Defined.

(* the exact addition a consequence carries: the binder establishment, or none for a blank row *)
Definition decl_consequence_addition {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} {de : DeclEventRef bp t}
  {i : nat} {r : DeclDecisionRowRef de i} (c : DeclRowConsequence de i r)
  : option (EventAdditionRef bp (decl_event_site de) (decl_new_rank de i)) :=
  match c with DeclNoAddition _ => None | DeclBinderAddition _ _ _ add => Some add end.

(* the exact source of a decl event addition: the unique nonblank decision row at the canonical rank *)
Record DeclAdditionSourceRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t)
  (k : nat) (ea : EventAdditionRef bp (decl_event_site de) k) : Type := mk_decl_source {
  das_index : nat ;
  das_row   : DeclDecisionRowRef de das_index ;
  das_nonblank : decl_row_decision das_row <> DeclBlankData ;
  das_rank  : decl_new_rank de das_index = k
}.
Arguments mk_decl_source {p idx s d bp t de k ea} _ _ _ _.
Arguments das_index {p idx s d bp t de k ea} _.
Arguments das_row {p idx s d bp t de k ea} _.
Arguments das_nonblank {p idx s d bp t de k ea} _.
Arguments das_rank {p idx s d bp t de k ea} _.

(* every decl event addition is sourced by exactly its one nonblank decision row at the canonical rank *)
Definition decl_addition_source_ref {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t)
  (k : nat) (ea : EventAdditionRef bp (decl_event_site de) k) : DeclAdditionSourceRef de k ea.
Proof.
  pose proof (ea_at ea) as Hat. rewrite decl_event_adds in Hat. unfold decl_rows_adds in Hat.
  destruct (flat_map_opt_source (decl_add_at (de_sc de)) (decl_add_at_single_sig (de_sc de))
              _ k (ea_est ea) Hat) as [j [a [Hj [Ha Hcnt]]]].
  destruct a as [row bd]. destruct (nth_error_combine_inv (de_rows de) (decl_binders t) j row bd Hj) as [Hrow Hbd].
  assert (Hnb : row <> DeclBlankData)
    by (intro Hb; subst row; cbn [decl_add_at] in Ha; discriminate Ha).
  refine (mk_decl_source j (mk_decl_row (mk_decl_binder_at bd Hbd) row Hrow) _ _).
  - cbn. exact Hnb.
  - rewrite decl_new_rank_adds_eq. exact Hcnt.
Defined.

(* the canonical nonblank rank is injective across nonblank rows: equal rank forces the same binder index *)
Lemma decl_new_rank_inj {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t)
  (i i' : nat) (r : DeclDecisionRowRef de i) (r' : DeclDecisionRowRef de i')
  (e e' : Est s)
  (Hnb : decl_row_decision r <> DeclBlankData) (He : node_binder_est (de_sc de) (decl_row_subject r) = Some e)
  (Hnb' : decl_row_decision r' <> DeclBlankData) (He' : node_binder_est (de_sc de) (decl_row_subject r') = Some e') :
  decl_new_rank de i = decl_new_rank de i' -> i = i'.
Proof.
  intro Heq. rewrite !decl_new_rank_adds_eq in Heq.
  apply (adds_before_inj (decl_add_at (de_sc de)) (combine (de_rows de) (decl_binders t)) i i'
           (decl_row_decision r, decl_row_subject r) (decl_row_decision r', decl_row_subject r') e e').
  - apply nth_error_combine; [ exact (ddr_at r) | exact (dba_at (ddr_binder r)) ].
  - rewrite (decl_add_at_nonblank_eq (de_sc de) (decl_row_decision r) (decl_row_subject r) Hnb), He. reflexivity.
  - apply nth_error_combine; [ exact (ddr_at r') | exact (dba_at (ddr_binder r')) ].
  - rewrite (decl_add_at_nonblank_eq (de_sc de) (decl_row_decision r') (decl_row_subject r') Hnb'), He'. reflexivity.
  - exact Heq.
Qed.

(* round trip: a nonblank row's consequence addition sources back to the exact same binder index and ref *)
Lemma decl_row_roundtrip {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t) (i : nat)
  (r : DeclDecisionRowRef de i) (e : Est s) (Hnb : decl_row_decision r <> DeclBlankData)
  (He : node_binder_est (de_sc de) (decl_row_subject r) = Some e) :
  das_index (decl_addition_source_ref de (decl_new_rank de i) (decl_row_addition de i r e Hnb He)) = i.
Proof.
  set (src := decl_addition_source_ref de (decl_new_rank de i) (decl_row_addition de i r e Hnb He)).
  destruct (decl_row_nonblank_est de (das_index src) (das_row src) (das_nonblank src)) as [e2 He2].
  apply (decl_new_rank_inj de (das_index src) i (das_row src) r e2 e (das_nonblank src) He2 Hnb He).
  exact (das_rank src).
Qed.
Lemma decl_row_roundtrip_ref {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t) (i : nat)
  (r : DeclDecisionRowRef de i) (e : Est s) (Hnb : decl_row_decision r <> DeclBlankData)
  (He : node_binder_est (de_sc de) (decl_row_subject r) = Some e) :
  eq_rect _ (fun k => DeclDecisionRowRef de k)
    (das_row (decl_addition_source_ref de (decl_new_rank de i) (decl_row_addition de i r e Hnb He)))
    i (decl_row_roundtrip de i r e Hnb He) = r.
Proof. apply decldecisionrowref_positional. Qed.

(* round trip: any decl addition sources to a row whose consequence addition is that exact same addition *)
Lemma decl_addition_roundtrip {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.Core.NodeRef idx} (de : DeclEventRef bp t)
  (k : nat) (ea : EventAdditionRef bp (decl_event_site de) k)
  (e : Est s) (He : node_binder_est (de_sc de)
                      (decl_row_subject (das_row (decl_addition_source_ref de k ea))) = Some e) :
  eq_rect _ (fun m => EventAdditionRef bp (decl_event_site de) m)
    (decl_row_addition de (das_index (decl_addition_source_ref de k ea)) (das_row (decl_addition_source_ref de k ea))
       e (das_nonblank (decl_addition_source_ref de k ea)) He)
    k (das_rank (decl_addition_source_ref de k ea)) = ea.
Proof. apply eventadditionref_positional. Qed.

Lemma filter_flat_map {A B} (P : B -> bool) (g : A -> list B) (l : list A) :
  filter P (flat_map g l) = flat_map (fun x => filter P (g x)) l.
Proof.
  induction l as [|a t IH]; [ reflexivity |].
  cbn. rewrite filter_app, IH. reflexivity.
Qed.

Lemma filter_seq_member_le {B} (F : nat -> list B) (P : B -> bool) (T i : nat) :
  i < T ->
  length (filter P (F i)) <= length (filter P (flat_map F (seq 0 T))).
Proof.
  intro Hi.
  replace (seq 0 T) with (seq 0 i ++ seq i (T - i)) by (rewrite <- seq_app; f_equal; lia).
  replace (T - i) with (S (T - S i)) by lia.
  cbn [seq]. rewrite flat_map_app. cbn [flat_map].
  rewrite !filter_app, !length_app. lia.
Qed.

(* the causal cut of a use inside a block: the exact count of fully earlier direct statements *)
Fixpoint count_while {A} (f : A -> bool) (l : list A) : nat :=
  match l with
  | [] => 0
  | x :: t => if f x then S (count_while f t) else 0
  end.

Lemma count_while_le {A} (f : A -> bool) (l : list A) : count_while f l <= length l.
Proof.
  induction l as [|x t IH]; cbn; [ lia |]. destruct (f x); lia.
Qed.

Lemma count_while_prefix {A} (f : A -> bool) :
  forall (l : list A) (j : nat) (x : A),
  j < count_while f l -> nth_error l j = Some x -> f x = true.
Proof.
  induction l as [|a t IH]; intros j x Hj Hx; [ destruct j; discriminate Hx |].
  cbn in Hj. destruct (f a) eqn:Ha; [| lia ].
  destruct j as [|j']; [ injection Hx as <-; exact Ha |].
  cbn in Hx. apply (IH j' x); [ lia | exact Hx ].
Qed.

Lemma count_while_here {A} (f : A -> bool) :
  forall (l : list A) (x : A),
  nth_error l (count_while f l) = Some x -> f x = false.
Proof.
  induction l as [|a t IH]; intros x Hx; [ destruct (count_while f []); discriminate Hx |].
  cbn in Hx |- *. destruct (f a) eqn:Ha; [ exact (IH x Hx) | injection Hx as <-; exact Ha ].
Qed.

Definition cut_of {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (evs : list (BlockEv s)) (u : Index.Core.NodeRef idx) : nat :=
  count_while (fun ev => Nat.ltb (Index.Core.node_extent (bev_node ev)) (Index.Core.nr_pos u)) evs.

(* the covering-block test: the exact retained source window of the old block visibility rule *)
Definition covers_use {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (u : Index.Core.NodeRef idx) (tr : TraceRow s) : bool :=
  andb (Index.Edges.fileref_eqb (Index.Core.nr_file (Index.Refs.bl_node (trow_block tr))) (Index.Core.nr_file u))
  (andb (Nat.ltb (Index.Core.nr_pos (Index.Refs.bl_node (trow_block tr))) (Index.Core.nr_pos u))
        (Nat.leb (Index.Core.nr_pos u) (Index.Core.node_extent (Index.Refs.bl_node (trow_block tr))))).

Definition vstart_before {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (u : Index.Core.NodeRef idx) (er : EstablishmentRef bp) : bool :=
  Nat.ltb (est_vstart (es_est er)) (Index.Core.nr_pos u).

(* the current declaration event's exactly visible additions at this use — a private builder helper only *)
Definition cur_adds {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.Core.NodeRef idx) (tix cut : nat) : list (EstablishmentRef bp) :=
  filter (vstart_before u) (block_ev_refs bp tix cut).

(* one exact current-event addition visible at a use: a not-yet-visible addition cannot inhabit this type *)
Record CurAddRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  (c : BlockCutRef tr) (u : Index.Core.NodeRef idx) : Type := mk_cur_add {
  ca_ref : EstablishmentRef bp ;
  ca_in  : In ca_ref (block_ev_refs bp (btr_ord tr) (bc_ord c)) ;
  ca_vis : vstart_before u ca_ref = true
}.
Arguments mk_cur_add {p idx s d bp b tr c u} _ _ _.
Arguments ca_ref {p idx s d bp b tr c u} _.
Arguments ca_in {p idx s d bp b tr c u} _.
Arguments ca_vis {p idx s d bp b tr c u} _.

(* build the exact visible current additions from a sublist of the current event's refs, threading membership *)
Fixpoint cur_add_scan {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  (c : BlockCutRef tr) (u : Index.Core.NodeRef idx) (l : list (EstablishmentRef bp)) {struct l}
  : (forall er, In er l -> In er (block_ev_refs bp (btr_ord tr) (bc_ord c))) -> list (CurAddRef c u) :=
  match l with
  | [] => fun _ => []
  | er :: rest => fun Hsub =>
      let tail := cur_add_scan c u rest (fun er' Hin => Hsub er' (or_intror Hin)) in
      match Bool.bool_dec (vstart_before u er) true with
      | left Hvis => mk_cur_add er (Hsub er (or_introl eq_refl)) Hvis :: tail
      | right _ => tail
      end
  end.
Definition cur_add_refs {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  (c : BlockCutRef tr) (u : Index.Core.NodeRef idx) : list (CurAddRef c u) :=
  cur_add_scan c u (block_ev_refs bp (btr_ord tr) (bc_ord c)) (fun er H => H).

(* the visible current additions project back to exactly the filtered current-event refs *)
Lemma cur_add_scan_proj {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  (c : BlockCutRef tr) (u : Index.Core.NodeRef idx) (l : list (EstablishmentRef bp))
  (H : forall er, In er l -> In er (block_ev_refs bp (btr_ord tr) (bc_ord c))) :
  map ca_ref (cur_add_scan c u l H) = filter (vstart_before u) l.
Proof.
  revert H. induction l as [|er rest IH]; intro H; [ reflexivity |].
  cbn [cur_add_scan filter]. destruct (Bool.bool_dec (vstart_before u er) true) as [Hvis|Hvis].
  - cbn [map ca_ref]. rewrite Hvis. rewrite (IH (fun er' Hin => H er' (or_intror Hin))). reflexivity.
  - apply Bool.not_true_is_false in Hvis. rewrite Hvis.
    rewrite (IH (fun er' Hin => H er' (or_intror Hin))). reflexivity.
Qed.
Lemma cur_add_refs_proj {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  (c : BlockCutRef tr) (u : Index.Core.NodeRef idx) :
  map ca_ref (cur_add_refs c u) = cur_adds bp u (btr_ord tr) (bc_ord c).
Proof. unfold cur_add_refs, cur_adds. apply cur_add_scan_proj. Qed.

Lemma cut_of_le {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (evs : list (BlockEv s)) (u : Index.Core.NodeRef idx) : cut_of evs u <= length evs.
Proof. unfold cut_of. apply count_while_le. Qed.

(* the exact block use context: covering trace, cut, predecessor state, and visible current-event additions *)
Record BlockUseRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.Core.NodeRef idx) : Type := mk_block_use {
  bu_block : Index.Refs.BlockRef idx ;
  bu_trace : BlockTraceRef bp (Index.Refs.bl_node bu_block) ;
  bu_cut   : BlockCutRef bu_trace ;
  bu_covers : covers_use u (btr_row bu_trace) = true ;
  bu_cut_at : bc_ord bu_cut = cut_of (trow_evs (btr_row bu_trace)) u ;
  bu_cur   : list (CurAddRef bu_cut u) ;
  bu_cur_ok : map ca_ref bu_cur = cur_adds bp u (btr_ord bu_trace) (bc_ord bu_cut)
}.
Arguments mk_block_use {p idx s d bp u} _ _ _ _ _ _ _.
Arguments bu_block {p idx s d bp u} _.
Arguments bu_trace {p idx s d bp u} _.
Arguments bu_cut {p idx s d bp u} _.
Arguments bu_covers {p idx s d bp u} _.
Arguments bu_cut_at {p idx s d bp u} _.
Arguments bu_cur {p idx s d bp u} _.
Arguments bu_cur_ok {p idx s d bp u} _.

(* projections keeping the resolution surface stable: the trace ordinal, cut, row, state, and current members *)
Definition bc_row {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (bc : BlockUseRef bp u) : TraceRow s :=
  btr_row (bu_trace bc).
Definition bc_tix {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (bc : BlockUseRef bp u) : nat :=
  btr_ord (bu_trace bc).
Definition bc_cut {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (bc : BlockUseRef bp u) : nat :=
  bc_ord (bu_cut bc).
Definition bc_state {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (bc : BlockUseRef bp u)
  : BlockStateRef (bu_cut bc) := block_state (bu_cut bc).
Definition bc_pre {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (bc : BlockUseRef bp u)
  : list (EstablishmentRef bp) := bs_members (bc_state bc).
Definition bc_cur {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (bc : BlockUseRef bp u)
  : list (EstablishmentRef bp) := map ca_ref (bu_cur bc).

(* the retained pins, now derived over the exact projections *)
Definition bc_at {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (bc : BlockUseRef bp u)
  : nth_error (bp_traces bp) (bc_tix bc) = Some (bc_row bc) := btr_at (bu_trace bc).
Definition bc_cut_pin {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (bc : BlockUseRef bp u)
  : bc_cut bc = cut_of (trow_evs (bc_row bc)) u := bu_cut_at bc.
Definition bc_pre_pin {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (bc : BlockUseRef bp u)
  : bc_pre bc = state_refs bp (bc_tix bc) (bc_cut bc) := eq_refl.
Definition bc_cur_pin {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (bc : BlockUseRef bp u)
  : bc_cur bc = cur_adds bp u (bc_tix bc) (bc_cut bc) := bu_cur_ok bc.

Definition locate_block_ctx {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.Core.NodeRef idx) : option (BlockUseRef bp u) :=
  match trace_scan bp (covers_use u) 0 (bp_traces bp) (eq_sym (skipn_O _)) with
  | Some h =>
      let tr := mk_block_trace (th_ord h) (th_row h) (th_at h) eq_refl in
      let c := mk_block_cut (tr := tr) (cut_of (trow_evs (th_row h)) u) (cut_of_le _ u) in
      Some (mk_block_use (trow_block (th_row h)) tr c (th_ok h) eq_refl
              (cur_add_refs c u) (cur_add_refs_proj c u))
  | None => None
  end.

(* the one exact use-context object ordinary resolution consumes *)
Record UseEnvironmentRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.Core.NodeRef idx) : Type := mk_use_env {
  ue_pkg : PI.PackageRef s ;
  ue_pkg_pin : ue_pkg = PI.package_of_file s (Index.Core.nr_file u) ;
  ue_block : option (BlockUseRef bp u) ;
  ue_block_pin : ue_block = locate_block_ctx bp u
}.
Arguments mk_use_env {p idx s d bp u} _ _ _ _.
Arguments ue_pkg {p idx s d bp u} _.
Arguments ue_pkg_pin {p idx s d bp u} _.
Arguments ue_block {p idx s d bp u} _.
Arguments ue_block_pin {p idx s d bp u} _.

Definition ue_pkg_refs {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (ue : UseEnvironmentRef bp u)
  : list (EstablishmentRef bp) := package_env_refs bp (ue_pkg ue).
Definition ue_pkg_refs_pin {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (ue : UseEnvironmentRef bp u)
  : ue_pkg_refs ue = package_env_refs bp (ue_pkg ue) := eq_refl.

Definition use_env {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.Core.NodeRef idx) : UseEnvironmentRef bp u :=
  mk_use_env (PI.package_of_file s (Index.Core.nr_file u)) eq_refl (locate_block_ctx bp u) eq_refl.

(* the visible occupancy members at this use: block-scoped name matches of pre-state plus gated current *)
Definition bc_visible {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (bc : BlockUseRef bp u)
  (n : Names.OrdinaryIdentifier) : list (EstablishmentRef bp) :=
  filter (fun er => same_block_cand n (es_est er)) (bc_pre bc ++ bc_cur bc).

Definition pkg_named {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : list (EstablishmentRef bp) :=
  filter (fun er => Names.ordinary_equalb (est_name (es_est er)) n) (ue_pkg_refs ue).

(* the exact visible groups over a use environment: local block-visible members and package members (§7.7) *)
Record LocalVisibleGroupRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : Type := mk_local_visible {
  lvg_members : list (EstablishmentRef bp) ;
  lvg_ok : lvg_members = match ue_block ue with Some bc => bc_visible bc n | None => [] end
}.
Arguments mk_local_visible {p idx s d bp u ue n} _ _.
Arguments lvg_members {p idx s d bp u ue n} _.
Arguments lvg_ok {p idx s d bp u ue n} _.
Definition local_visible_group {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : LocalVisibleGroupRef ue n :=
  mk_local_visible _ eq_refl.

Record PackageVisibleGroupRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : Type := mk_pkg_visible {
  pvg_members : list (EstablishmentRef bp) ;
  pvg_ok : pvg_members = pkg_named ue n
}.
Arguments mk_pkg_visible {p idx s d bp u ue n} _ _.
Arguments pvg_members {p idx s d bp u ue n} _.
Arguments pvg_ok {p idx s d bp u ue n} _.
Definition package_visible_group {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : PackageVisibleGroupRef ue n :=
  mk_pkg_visible _ eq_refl.

(* a redeclaration root at some exact scope for a name: the derived canonical group root, never supplied free *)
Definition RedeclRoot {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (n : Names.OrdinaryIdentifier) : Type :=
  { sc : ScopeId s & RedeclarationRef bp sc n }.

(* the exact status of the local visible group, indexed by the exact group ref, not a raw member list *)
Inductive LocalVisibleGroupStatusRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : Type :=
| LocalGroupAbsent (H : lvg_members (local_visible_group ue n) = [])
| LocalGroupUnique (m : EstablishmentRef bp) (H : lvg_members (local_visible_group ue n) = [m])
| LocalGroupRedeclared (m1 m2 : EstablishmentRef bp) (rest : list (EstablishmentRef bp))
    (H : lvg_members (local_visible_group ue n) = m1 :: m2 :: rest).
Arguments LocalGroupAbsent {p idx s d bp u ue n} _.
Arguments LocalGroupUnique {p idx s d bp u ue n} _ _.
Arguments LocalGroupRedeclared {p idx s d bp u ue n} _ _ _ _.
Inductive PackageVisibleGroupStatusRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : Type :=
| PackageGroupAbsent (H : pvg_members (package_visible_group ue n) = [])
| PackageGroupUnique (m : EstablishmentRef bp) (H : pvg_members (package_visible_group ue n) = [m])
| PackageGroupRedeclared (m1 m2 : EstablishmentRef bp) (rest : list (EstablishmentRef bp))
    (H : pvg_members (package_visible_group ue n) = m1 :: m2 :: rest).
Arguments PackageGroupAbsent {p idx s d bp u ue n} _.
Arguments PackageGroupUnique {p idx s d bp u ue n} _ _.
Arguments PackageGroupRedeclared {p idx s d bp u ue n} _ _ _ _.

(* the one canonical exact status of each visible group, forced by the group's own member shape *)
Definition local_group_status_ref {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : LocalVisibleGroupStatusRef ue n.
Proof.
  destruct (lvg_members (local_visible_group ue n)) as [|m [|m2 rest]] eqn:H.
  - exact (LocalGroupAbsent H). - exact (LocalGroupUnique m H). - exact (LocalGroupRedeclared m m2 rest H).
Defined.
Definition package_group_status_ref {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : PackageVisibleGroupStatusRef ue n.
Proof.
  destruct (pvg_members (package_visible_group ue n)) as [|m [|m2 rest]] eqn:H.
  - exact (PackageGroupAbsent H). - exact (PackageGroupUnique m H). - exact (PackageGroupRedeclared m m2 rest H).
Defined.

(* the exact local visible redeclaration: the exact >=2-member group evidence, from which the root is DERIVED *)
Record LocalVisibleRedeclarationRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : Type := mk_local_vredecl {
  lvrr_m1 : EstablishmentRef bp ; lvrr_m2 : EstablishmentRef bp ;
  lvrr_rest : list (EstablishmentRef bp) ;
  lvrr_visible : lvg_members (local_visible_group ue n) = lvrr_m1 :: lvrr_m2 :: lvrr_rest
}.
Arguments mk_local_vredecl {p idx s d bp u ue n} _ _ _ _.
Arguments lvrr_m1 {p idx s d bp u ue n} _.
Arguments lvrr_m2 {p idx s d bp u ue n} _.
Arguments lvrr_rest {p idx s d bp u ue n} _.
Arguments lvrr_visible {p idx s d bp u ue n} _.
Record PackageVisibleRedeclarationRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : Type := mk_pkg_vredecl {
  pvrr_m1 : EstablishmentRef bp ; pvrr_m2 : EstablishmentRef bp ;
  pvrr_rest : list (EstablishmentRef bp) ;
  pvrr_visible : pvg_members (package_visible_group ue n) = pvrr_m1 :: pvrr_m2 :: pvrr_rest
}.
Arguments mk_pkg_vredecl {p idx s d bp u ue n} _ _ _ _.
Arguments pvrr_m1 {p idx s d bp u ue n} _.
Arguments pvrr_m2 {p idx s d bp u ue n} _.
Arguments pvrr_rest {p idx s d bp u ue n} _.
Arguments pvrr_visible {p idx s d bp u ue n} _.

(* a block-occupancy match at a trace's event is a member of that block's canonical group *)
Lemma block_cand_matches {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix eix : nat) (tr : TraceRow s) (n : Names.OrdinaryIdentifier)
  (er : EstablishmentRef bp) :
  nth_error (bp_traces bp) tix = Some tr ->
  In er (block_ev_refs bp tix eix) ->
  same_block_cand n (es_est er) = true ->
  scope_name_matches (BlockScope (trow_block tr)) n er = true.
Proof.
  intros Htr Hin Hc. unfold same_block_cand in Hc. apply andb_prop in Hc as [_ Hname].
  unfold scope_name_matches.
  rewrite (trace_add_scope bp tix eix tr er Htr Hin).
  rewrite (proj2 (scope_eqb_spec _ _) eq_refl). exact Hname.
Qed.

Lemma pkg_name_matches {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pr : PI.PackageRef s) (eix : nat) (n : Names.OrdinaryIdentifier)
  (er : EstablishmentRef bp) :
  In er (pkg_ev_refs bp (PI.pr_pos pr) eix) ->
  Names.ordinary_equalb (est_name (es_est er)) n = true ->
  scope_name_matches (PackageScope pr) n er = true.
Proof.
  intros Hin Hname. unfold scope_name_matches.
  rewrite (ledger_add_scope bp (PI.pr_pos pr) eix pr er (packages_nth s pr) Hin).
  rewrite (proj2 (scope_eqb_spec _ _) eq_refl). exact Hname.
Qed.

(* two visible same-name block members witness at least two members of the canonical group *)
Lemma block_visible_le {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.Core.NodeRef idx) (tix cut : nat) (tr : TraceRow s)
  (n : Names.OrdinaryIdentifier) :
  nth_error (bp_traces bp) tix = Some tr ->
  cut <= length (trow_evs tr) ->
  length (filter (fun er => same_block_cand n (es_est er)) (state_refs bp tix cut))
  + length (filter (fun er => same_block_cand n (es_est er)) (cur_adds bp u tix cut))
  <= length (group_refs bp (BlockScope (trow_block tr)) n).
Proof.
  intros Htr Hcut.
  destruct (bp_traces_row bp tr (nth_error_In _ _ Htr)) as [pr [r [Hb [_ [_ Hform]]]]].
  assert (Hpix : trow_pkg tr = PI.pr_pos pr) by (rewrite Hform; reflexivity).
  assert (Hstate :
    length (filter (fun er => same_block_cand n (es_est er)) (state_refs bp tix cut))
    <= length (flat_map (fun eix => filter (scope_name_matches (BlockScope (trow_block tr)) n)
                            (block_ev_refs bp tix eix)) (seq 0 cut))).
  { unfold state_refs. rewrite Htr. rewrite filter_app, length_app.
    assert (Hseed : filter (fun er => same_block_cand n (es_est er)) (ledger_refs bp (trow_pkg tr)) = []).
    { apply filter_all_false. intros er Hin.
      unfold ledger_refs in Hin. apply in_flat_map in Hin. destruct Hin as [eix [_ Hin]].
      rewrite Hpix in Hin. unfold same_block_cand, is_block_scoped.
      rewrite (ledger_add_scope bp (PI.pr_pos pr) eix pr er (packages_nth s pr) Hin). reflexivity. }
    rewrite Hseed. cbn [length]. rewrite filter_flat_map.
    apply flat_map_length_le. intros eix _.
    apply filter_impl_le. intros er Hin HP.
    exact (block_cand_matches bp tix eix tr n er Htr Hin HP). }
  assert (Hcur :
    length (filter (fun er => same_block_cand n (es_est er)) (cur_adds bp u tix cut))
    <= length (filter (scope_name_matches (BlockScope (trow_block tr)) n) (block_ev_refs bp tix cut))).
  { unfold cur_adds. rewrite filter_filter.
    apply filter_impl_le. intros er Hin Hand.
    apply andb_prop in Hand as [_ HP].
    exact (block_cand_matches bp tix cut tr n er Htr Hin HP). }
  assert (Htrace :
    length (flat_map (fun eix => filter (scope_name_matches (BlockScope (trow_block tr)) n)
                        (block_ev_refs bp tix eix)) (seq 0 cut))
    + length (filter (scope_name_matches (BlockScope (trow_block tr)) n) (block_ev_refs bp tix cut))
    <= length (flat_map (fun eix => filter (scope_name_matches (BlockScope (trow_block tr)) n)
                            (block_ev_refs bp tix eix)) (seq 0 (length (trow_evs tr))))).
  { destruct (Nat.eq_dec cut (length (trow_evs tr))) as [->|Hne].
    - assert (Hnil : block_ev_refs bp tix (length (trow_evs tr)) = []).
      { unfold block_ev_refs.
        destruct (lt_dec (length (trow_evs tr)) (trace_event_count bp tix)) as [Hlt|]; [| reflexivity ].
        exfalso. revert Hlt. unfold trace_event_count. rewrite Htr. lia. }
      rewrite Hnil. cbn [filter length]. lia.
    - replace (seq 0 (length (trow_evs tr)))
        with (seq 0 cut ++ seq cut (length (trow_evs tr) - cut))
        by (rewrite <- seq_app; f_equal; lia).
      replace (length (trow_evs tr) - cut) with (S (length (trow_evs tr) - S cut)) by lia.
      cbn [seq]. rewrite flat_map_app. cbn [flat_map]. rewrite !length_app. lia. }
  assert (Hgroup :
    length (flat_map (fun eix => filter (scope_name_matches (BlockScope (trow_block tr)) n)
                        (block_ev_refs bp tix eix)) (seq 0 (length (trow_evs tr))))
    <= length (group_refs bp (BlockScope (trow_block tr)) n)).
  { unfold group_refs, all_establishment_refs. rewrite filter_app, length_app.
    assert (Hself : flat_map (fun eix => filter (scope_name_matches (BlockScope (trow_block tr)) n)
                        (block_ev_refs bp tix eix)) (seq 0 (length (trow_evs tr)))
                  = filter (scope_name_matches (BlockScope (trow_block tr)) n) (trace_refs bp tix)).
    { unfold trace_refs, trace_event_count. rewrite Htr. rewrite filter_flat_map. reflexivity. }
    rewrite Hself.
    assert (Hmid : length (filter (scope_name_matches (BlockScope (trow_block tr)) n) (trace_refs bp tix))
      <= length (filter (scope_name_matches (BlockScope (trow_block tr)) n)
                   (flat_map (trace_refs bp) (seq 0 (length (bp_traces bp)))))).
    { apply (filter_seq_member_le (fun tix' => trace_refs bp tix')
               (scope_name_matches (BlockScope (trow_block tr)) n)).
      apply nth_error_Some. rewrite Htr. discriminate. }
    lia. }
  lia.
Qed.

Lemma pkg_visible_le {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pr : PI.PackageRef s) (n : Names.OrdinaryIdentifier) :
  length (filter (fun er => Names.ordinary_equalb (est_name (es_est er)) n)
                 (package_env_refs bp pr))
  <= length (group_refs bp (PackageScope pr) n).
Proof.
  apply Nat.le_trans with
    (m := length (filter (scope_name_matches (PackageScope pr) n) (package_env_refs bp pr))).
  - unfold package_env_refs, ledger_refs. rewrite !filter_flat_map.
    apply flat_map_length_le. intros eix _.
    apply filter_impl_le. intros er Hin Hname.
    exact (pkg_name_matches bp pr eix n er Hin Hname).
  - unfold group_refs, all_establishment_refs. rewrite filter_app, length_app.
    assert (Hself : filter (scope_name_matches (PackageScope pr) n) (package_env_refs bp pr)
                  = filter (scope_name_matches (PackageScope pr) n) (ledger_refs bp (PI.pr_pos pr)))
      by reflexivity.
    rewrite Hself.
    assert (Hmid : length (filter (scope_name_matches (PackageScope pr) n) (ledger_refs bp (PI.pr_pos pr)))
      <= length (filter (scope_name_matches (PackageScope pr) n)
                   (flat_map (ledger_refs bp) (seq 0 (length (bp_ledgers bp)))))).
    { apply (filter_seq_member_le (fun pix => ledger_refs bp pix) (scope_name_matches (PackageScope pr) n)).
      apply nth_error_Some. rewrite (bp_ledgers_at bp pr). discriminate. }
    lia.
Qed.

Lemma block_group_two {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (bc : BlockUseRef bp u)
  (n : Names.OrdinaryIdentifier) (er1 er2 : EstablishmentRef bp) (rest : list (EstablishmentRef bp)) :
  bc_visible bc n = er1 :: er2 :: rest ->
  2 <= length (group_refs bp (BlockScope (trow_block (bc_row bc))) n).
Proof.
  intro Hv. unfold bc_visible in Hv.
  rewrite (bc_pre_pin bc), (bc_cur_pin bc), filter_app in Hv.
  assert (Hlen : 2 <= length (filter (fun er => same_block_cand n (es_est er))
                                (state_refs bp (bc_tix bc) (bc_cut bc)))
                     + length (filter (fun er => same_block_cand n (es_est er))
                                 (cur_adds bp u (bc_tix bc) (bc_cut bc))))
    by (rewrite <- length_app, Hv; cbn; lia).
  eapply Nat.le_trans; [ exact Hlen |].
  apply (block_visible_le bp u (bc_tix bc) (bc_cut bc) (bc_row bc) n (bc_at bc)).
  rewrite (bc_cut_pin bc). apply count_while_le.
Qed.

Lemma pkg_group_two {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) (er1 er2 : EstablishmentRef bp) (rest : list (EstablishmentRef bp)) :
  pkg_named ue n = er1 :: er2 :: rest ->
  2 <= length (group_refs bp (PackageScope (ue_pkg ue)) n).
Proof.
  intro Hv. unfold pkg_named in Hv. rewrite (ue_pkg_refs_pin ue) in Hv.
  eapply Nat.le_trans; [| apply (pkg_visible_le bp (ue_pkg ue) n) ].
  rewrite Hv. cbn. lia.
Qed.

(* the canonical redeclaration root, DERIVED from the exact visible group; the covering scope is forced by it *)
Definition lvrr_root {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} {ue : UseEnvironmentRef bp u}
  {n : Names.OrdinaryIdentifier} (r : LocalVisibleRedeclarationRef ue n) : RedeclRoot bp n.
Proof.
  pose proof (lvrr_visible r) as Hv. rewrite (lvg_ok (local_visible_group ue n)) in Hv.
  destruct (ue_block ue) as [bc|] eqn:Hb; [| discriminate Hv ].
  exact (existT _ (BlockScope (trow_block (bc_row bc)))
           (mk_redeclaration (binding_group bp (BlockScope (trow_block (bc_row bc))) n)
              (block_group_two bc n (lvrr_m1 r) (lvrr_m2 r) (lvrr_rest r) Hv))).
Defined.
Definition pvrr_root {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} {ue : UseEnvironmentRef bp u}
  {n : Names.OrdinaryIdentifier} (r : PackageVisibleRedeclarationRef ue n) : RedeclRoot bp n :=
  existT _ (PackageScope (ue_pkg ue))
    (mk_redeclaration (binding_group bp (PackageScope (ue_pkg ue)) n)
       (pkg_group_two ue n (pvrr_m1 r) (pvrr_m2 r) (pvrr_rest r)
          (eq_trans (eq_sym (pvg_ok (package_visible_group ue n))) (pvrr_visible r)))).

(* the exact canonical resolution result: one outcome per case, each pinned to the exact use and visible-group *)
Inductive ResolutionRef {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : Type :=
| ResolvedLocal : forall (m : EstablishmentRef bp),
    lvg_members (local_visible_group ue n) = [m] -> ResolutionRef ue n
| ResolvedPackage : forall (m : EstablishmentRef bp),
    lvg_members (local_visible_group ue n) = [] ->
    pvg_members (package_visible_group ue n) = [m] -> ResolutionRef ue n
| ResolvedPredeclared : forall (pn : Names.PredeclaredName),
    lvg_members (local_visible_group ue n) = [] ->
    pvg_members (package_visible_group ue n) = [] ->
    Names.classify_predeclared (Names.ordinary_spelling n) = Some pn -> ResolutionRef ue n
| ResolutionRedeclaredLocal : forall (rr : LocalVisibleRedeclarationRef ue n), ResolutionRef ue n
| ResolutionRedeclaredPackage : forall (rr : PackageVisibleRedeclarationRef ue n),
    lvg_members (local_visible_group ue n) = [] -> ResolutionRef ue n
| ResolutionUnbound :
    lvg_members (local_visible_group ue n) = [] ->
    pvg_members (package_visible_group ue n) = [] ->
    Names.classify_predeclared (Names.ordinary_spelling n) = None -> ResolutionRef ue n.
Arguments ResolvedLocal {p idx s d bp u ue n} _ _.
Arguments ResolvedPackage {p idx s d bp u ue n} _ _ _.
Arguments ResolvedPredeclared {p idx s d bp u ue n} _ _ _ _.
Arguments ResolutionRedeclaredLocal {p idx s d bp u ue n} _.
Arguments ResolutionRedeclaredPackage {p idx s d bp u ue n} _ _.
Arguments ResolutionUnbound {p idx s d bp u ue n} _ _ _.

(* the one canonical resolution, consuming the exact group statuses: block visibility shadows the package *)
Definition resolution_ref {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : ResolutionRef ue n.
Proof.
  destruct (local_group_status_ref ue n) as [Hl | m Hl | m1 m2 rest Hl].
  - destruct (package_group_status_ref ue n) as [Hp | pm Hp | pm1 pm2 prest Hp].
    + destruct (Names.classify_predeclared (Names.ordinary_spelling n)) as [pn|] eqn:Hc.
      * exact (ResolvedPredeclared pn Hl Hp Hc).
      * exact (ResolutionUnbound Hl Hp Hc).
    + exact (ResolvedPackage pm Hl Hp).
    + exact (ResolutionRedeclaredPackage (mk_pkg_vredecl pm1 pm2 prest Hp) Hl).
  - exact (ResolvedLocal m Hl).
  - exact (ResolutionRedeclaredLocal (mk_local_vredecl m1 m2 rest Hl)).
Defined.

(* one-way projections a consumer reads: the bound object as an idx-level ref, and the redeclaration root *)
Definition resolution_object_view {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} {ue : UseEnvironmentRef bp u}
  {n : Names.OrdinaryIdentifier} (r : ResolutionRef ue n) : option (ObjectRef idx) :=
  match r with
  | ResolvedLocal m _ => Some (SourceObject (est_origin (es_est m)))
  | ResolvedPackage m _ _ => Some (SourceObject (est_origin (es_est m)))
  | ResolvedPredeclared pn _ _ _ => Some (PredeclaredObject pn)
  | _ => None
  end.

Definition resolution_redecl_root {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} {ue : UseEnvironmentRef bp u}
  {n : Names.OrdinaryIdentifier} (r : ResolutionRef ue n) : option (RedeclRoot bp n) :=
  match r with
  | ResolutionRedeclaredLocal rr => Some (lvrr_root rr)
  | ResolutionRedeclaredPackage rr _ => Some (pvrr_root rr)
  | _ => None
  end.

Definition resolve {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.Core.NodeRef idx) (n : Names.OrdinaryIdentifier)
  : ResolutionRef (use_env bp u) n := resolution_ref (use_env bp u) n.

(* every resolution is exactly one of bound / redeclared / unbound: the projections are complete and exclusive *)
Lemma resolution_trichotomy {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.Core.NodeRef idx} {ue : UseEnvironmentRef bp u}
  {n : Names.OrdinaryIdentifier} (r : ResolutionRef ue n) :
  (exists o, resolution_object_view r = Some o /\ resolution_redecl_root r = None)
  \/ (resolution_object_view r = None /\ exists rr, resolution_redecl_root r = Some rr)
  \/ (resolution_object_view r = None /\ resolution_redecl_root r = None).
Proof.
  destruct r; cbn.
  - left. eexists. split; reflexivity.
  - left. eexists. split; reflexivity.
  - left. eexists. split; reflexivity.
  - right. left. split; [ reflexivity | eexists; reflexivity ].
  - right. left. split; [ reflexivity | eexists; reflexivity ].
  - right. right. split; reflexivity.
Qed.
(* every redeclaration root exposes at least two canonical group members: it can bind nothing *)
Lemma redecl_root_two {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {n : Names.OrdinaryIdentifier} (root : RedeclRoot bp n) :
  2 <= length (bg_members (rr_group (projT2 root))).
Proof. exact (rr_two (projT2 root)). Qed.

(* a short event's additions become visible only past the whole statement *)
Lemma new_est_vstart {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.Refs.BlockRef idx) {st : Index.Refs.ShortStmtRef idx} {i : nat}
  (e : Index.Edges.ShortLhsEdge st i) (n : Names.OrdinaryIdentifier) :
  est_vstart (new_est (s := s) br e n) = Index.Core.node_extent (Index.Refs.sh_node st).
Proof.
  cbn [new_est est_vstart]. unfold vis_start.
  rewrite (Index.Edges.sl_role e).
  unfold Index.Edges.sl_child. rewrite (Index.Child.ca_node_parent (Index.Edges.sl_at e)). reflexivity.
Qed.

(* every short addition becomes visible only past the whole statement, a pure fact of the projected New rows *)
Lemma short_rows_adds_vstart {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.Refs.BlockRef idx) (st : Index.Refs.ShortStmtRef idx) (rows : list ShortLeftDecisionData) (e : Est s) :
  In e (short_rows_adds br st rows) -> est_vstart e = Index.Core.node_extent (Index.Refs.sh_node st).
Proof.
  unfold short_rows_adds, short_add_at. intro Hin. apply in_flat_map in Hin. destruct Hin as [x [_ Hin]].
  destruct x as [i ed]. destruct (nth_error rows i) as [row|]; try (exact (match Hin with end)).
  destruct row; try (exact (match Hin with end)).
  destruct Hin as [<-|F]; [| destruct F ]. apply new_est_vstart.
Qed.

(* within the short statement, its own additions are gated out of every use environment *)
Lemma short_cur_adds_empty {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.Core.NodeRef idx) (tix cut : nat) (tr : TraceRow s)
  (st' : Index.Refs.ShortStmtRef idx) (rows : list ShortLeftDecisionData) :
  nth_error (bp_traces bp) tix = Some tr ->
  nth_error (trow_evs tr) cut = Some (BEvShort st' rows) ->
  Index.Core.nr_pos u <= Index.Core.node_extent (Index.Refs.sh_node st') ->
  cur_adds bp u tix cut = [].
Proof.
  intros Htr Hev Hle. unfold cur_adds.
  apply filter_all_false. intros er Hin.
  unfold block_ev_refs in Hin. revert Hin.
  destruct (lt_dec cut (trace_event_count bp tix)) as [Hlt|]; intro Hin; [| destruct Hin ].
  pose proof (refs_of_event_est_in (BlockEventAt tix cut Hlt) er Hin) as Hest.
  rewrite (event_adds_block bp tix cut Hlt tr _ Htr Hev) in Hest.
  cbn [bev_adds] in Hest.
  unfold vstart_before.
  rewrite (short_rows_adds_vstart _ st' rows (es_est er) Hest).
  apply Nat.ltb_ge. exact Hle.
Qed.

(* the observational declaration-group view: shared scope, spelling, and ordered member projection *)
Record DeclarationGroupRef {p} {idx : Index.Core.ProgramIndex p} (s : PI.PackageSurface idx) : Type
  := mk_decl_group {
  dg_scope   : ScopeId s ;
  dg_name    : Names.OrdinaryIdentifier ;
  dg_members : list (Est s)
}.
Arguments mk_decl_group {p idx s} _ _ _.
Arguments dg_scope {p idx s} _.
Arguments dg_name {p idx s} _.
Arguments dg_members {p idx s} _.

Definition group_view {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {sc : ScopeId s} {n : Names.OrdinaryIdentifier}
  (rr : RedeclarationRef bp sc n) : DeclarationGroupRef s :=
  mk_decl_group sc n (map es_est (bg_members (rr_group rr))).

Definition redecl_view {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {n : Names.OrdinaryIdentifier} (root : RedeclRoot bp n)
  : DeclarationGroupRef s := group_view (projT2 root).

(* one exact redeclared-group projection per canonical group, keyed at its exact first member *)
Definition redeclared_groups {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : list (DeclarationGroupRef s) :=
  flat_map (fun er =>
    match group_refs bp (est_scope (es_est er)) (est_name (es_est er)) with
    | er0 :: _ :: _ =>
        if est_eqb (es_est er0) (es_est er)
        then [ mk_decl_group (est_scope (es_est er)) (est_name (es_est er))
                 (map es_est (group_refs bp (est_scope (es_est er)) (est_name (es_est er)))) ]
        else []
    | _ => []
    end) (all_establishment_refs bp).

(* the visible group at a use: the block group when the use sits in a block, else the package group *)
Definition group_at_use {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.Core.NodeRef idx) (n : Names.OrdinaryIdentifier)
  : list (EstablishmentRef bp) :=
  match ue_block (use_env bp u) with
  | Some bc => match bc_visible bc n with [] => pkg_named (use_env bp u) n | v => v end
  | None => pkg_named (use_env bp u) n
  end.

(* main status stays a projection over the exact retained package environment refs *)
Definition package_main {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pr : PI.PackageRef s) : MainStatus s pr :=
  main_status_of (map es_est (package_env_refs bp pr)) pr.

Theorem package_main_sound {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pr : PI.PackageRef s) :
  main_status_ests (package_main bp pr) = main_ests_of (map es_est (package_env_refs bp pr)) pr.
Proof. unfold package_main. apply main_status_ests_of. Qed.

Lemma main_is_package_local {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pr : PI.PackageRef s) :
  forall m, In m (main_status_ests (package_main bp pr)) ->
    is_func_est m = true /\ est_scope m = PackageScope pr.
Proof.
  intros m Hin. rewrite package_main_sound in Hin. unfold main_ests_of in Hin.
  apply filter_In in Hin. destruct Hin as [_ Hcond].
  apply andb_prop in Hcond as [Hf Hrest]. apply andb_prop in Hrest as [_ Hsc].
  split; [exact Hf|].
  destruct (est_scope m) as [q|] eqn:E; [| discriminate Hsc].
  apply PI.packageref_eqb_spec in Hsc; subst q; reflexivity.
Qed.

(* the ledger/trace ordinal and the event ordinal of a valid site *)
Definition site_outer {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) : nat :=
  match site with PkgEventAt pix _ _ => pix | BlockEventAt tix _ _ => tix end.
Definition site_eix {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) : nat :=
  match site with PkgEventAt _ eix _ => eix | BlockEventAt _ eix _ => eix end.

Lemma refs_scan_keys {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) :
  forall l k (E : l = skipn k (event_adds site)),
  map (fun er => (es_site er, es_ix er)) (refs_scan site k l E)
  = map (fun ix => (site, ix)) (seq k (length l)).
Proof.
  induction l as [|e0 rest IH]; intros k E; [ reflexivity |].
  cbn. rewrite IH. reflexivity.
Qed.

Lemma refs_of_event_keys {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) :
  map (fun er => (es_site er, es_ix er)) (refs_of_event site)
  = map (fun ix => (site, ix)) (seq 0 (length (event_adds site))).
Proof. apply refs_scan_keys. Qed.

(* the keys of one event's refs are distinct: they share the site and carry distinct addition indices *)
Lemma event_keys_nodup {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) :
  NoDup (map (fun er => (es_site er, es_ix er)) (refs_of_event site)).
Proof.
  rewrite refs_of_event_keys. apply nodup_map_inj;
    [ intros x y H; congruence | apply seq_NoDup ].
Qed.

(* one ledger's establishment keys are distinct, every one carrying that ledger's package ordinal *)
Lemma ledger_keys_nodup {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pix : nat) :
  NoDup (map (fun er => (es_site er, es_ix er)) (ledger_refs bp pix)).
Proof.
  unfold ledger_refs. rewrite map_flat_map.
  apply (flat_map_nodup_key _ (fun kp => site_eix (fst kp)) (fun eix => eix));
    [ rewrite map_id; apply seq_NoDup | | ].
  - intros eix _. unfold pkg_ev_refs.
    destruct (lt_dec eix (pkg_event_count bp pix)) as [H|]; [ apply event_keys_nodup | cbn; constructor ].
  - intros eix kp _ Hin. apply in_map_iff in Hin. destruct Hin as [er [<- Hin]].
    unfold pkg_ev_refs in Hin. revert Hin.
    destruct (lt_dec eix (pkg_event_count bp pix)) as [H|]; intro Hin; [| destruct Hin ].
    cbn [fst]. rewrite (refs_of_event_site (PkgEventAt pix eix H) er Hin). reflexivity.
Qed.

(* one trace's establishment keys are distinct, every one carrying that trace's ordinal *)
Lemma trace_keys_nodup {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix : nat) :
  NoDup (map (fun er => (es_site er, es_ix er)) (trace_refs bp tix)).
Proof.
  unfold trace_refs. rewrite map_flat_map.
  apply (flat_map_nodup_key _ (fun kp => site_eix (fst kp)) (fun eix => eix));
    [ rewrite map_id; apply seq_NoDup | | ].
  - intros eix _. unfold block_ev_refs.
    destruct (lt_dec eix (trace_event_count bp tix)) as [H|]; [ apply event_keys_nodup | cbn; constructor ].
  - intros eix kp _ Hin. apply in_map_iff in Hin. destruct Hin as [er [<- Hin]].
    unfold block_ev_refs in Hin. revert Hin.
    destruct (lt_dec eix (trace_event_count bp tix)) as [H|]; intro Hin; [| destruct Hin ].
    cbn [fst]. rewrite (refs_of_event_site (BlockEventAt tix eix H) er Hin). reflexivity.
Qed.

(* every retained establishment is one exact event addition, exactly once (site and index key) *)
Theorem establishment_refs_once {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) :
  NoDup (map (fun er => (es_site er, es_ix er)) (all_establishment_refs bp)).
Proof.
  unfold all_establishment_refs. rewrite map_app. apply nodup_app_disjoint.
  - rewrite map_flat_map.
    apply (flat_map_nodup_key _ (fun kp => site_outer (fst kp)) (fun pix => pix));
      [ rewrite map_id; apply seq_NoDup | intros pix _; apply ledger_keys_nodup | ].
    intros pix kp _ Hin. apply in_map_iff in Hin. destruct Hin as [er [<- Hin]].
    unfold ledger_refs in Hin. apply in_flat_map in Hin. destruct Hin as [eix [_ Hin]].
    unfold pkg_ev_refs in Hin. revert Hin.
    destruct (lt_dec eix (pkg_event_count bp pix)) as [H|]; intro Hin; [| destruct Hin ].
    cbn [fst]. rewrite (refs_of_event_site (PkgEventAt pix eix H) er Hin). reflexivity.
  - rewrite map_flat_map.
    apply (flat_map_nodup_key _ (fun kp => site_outer (fst kp)) (fun tix => tix));
      [ rewrite map_id; apply seq_NoDup | intros tix _; apply trace_keys_nodup | ].
    intros tix kp _ Hin. apply in_map_iff in Hin. destruct Hin as [er [<- Hin]].
    unfold trace_refs in Hin. apply in_flat_map in Hin. destruct Hin as [eix [_ Hin]].
    unfold block_ev_refs in Hin. revert Hin.
    destruct (lt_dec eix (trace_event_count bp tix)) as [H|]; intro Hin; [| destruct Hin ].
    cbn [fst]. rewrite (refs_of_event_site (BlockEventAt tix eix H) er Hin). reflexivity.
  - intros kp Hpk Htk.
    apply in_map_iff in Hpk. destruct Hpk as [erp [Hkp Hinp]].
    apply in_map_iff in Htk. destruct Htk as [ert [Hkt Hint]].
    apply in_flat_map in Hinp. destruct Hinp as [pix [_ Hinp]].
    unfold ledger_refs in Hinp. apply in_flat_map in Hinp. destruct Hinp as [peix [_ Hinp]].
    unfold pkg_ev_refs in Hinp. revert Hinp.
    destruct (lt_dec peix (pkg_event_count bp pix)) as [Hp|]; intro Hinp; [| destruct Hinp ].
    apply in_flat_map in Hint. destruct Hint as [tix [_ Hint]].
    unfold trace_refs in Hint. apply in_flat_map in Hint. destruct Hint as [teix [_ Hint]].
    unfold block_ev_refs in Hint. revert Hint.
    destruct (lt_dec teix (trace_event_count bp tix)) as [Ht|]; intro Hint; [| destruct Hint ].
    pose proof (refs_of_event_site (PkgEventAt pix peix Hp) erp Hinp) as Hsp.
    pose proof (refs_of_event_site (BlockEventAt tix teix Ht) ert Hint) as Hst.
    rewrite <- Hkp in Hkt. injection Hkt as Hsite _.
    rewrite Hst, Hsp in Hsite. discriminate Hsite.
Qed.


(* each short fact case names its exact evidence, keyed by the retained decision row (contract §9.3) *)
Lemma short_lhs_blank {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (pre : BlockStateRef c) {st : Index.Refs.ShortStmtRef idx} {i : nat}
  (e : Index.Edges.ShortLhsEdge st i) (row : ShortLeftDecisionData) (f : ShortLhsFact pre e row) :
  match row with ShortBlankData => binder_ident (Index.Edges.sl_child e) = None | _ => True end.
Proof. destruct f; cbn; solve [ exact I | assumption ]. Qed.

Lemma short_lhs_duplicate {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (pre : BlockStateRef c) {st : Index.Refs.ShortStmtRef idx} {i : nat}
  (e : Index.Edges.ShortLhsEdge st i) (row : ShortLeftDecisionData) (f : ShortLhsFact pre e row) :
  match row with
  | ShortDuplicateData j => exists (n : Names.OrdinaryIdentifier) (ej : Index.Edges.ShortLhsEdge st j) (Hj : j < i),
      binder_ident (Index.Edges.sl_child e) = Some n /\ binder_ident (Index.Edges.sl_child ej) = Some n
      /\ find_dup i n (Index.Edges.short_lhs_edges st) = Some (existT _ j (ej, Hj))
  | _ => True end.
Proof.
  destruct f as [H | n j ej Hj Hb Hbej Hd | n Hb Hd Hm | n mr Hb Hd Hft Ho Hv
                | n mr Hb Hd Hft Ho Hv | n grp mr1 mr2 Hb Hd Hft Hlg Hs1 Hs2]; cbn; try exact I.
  exists n, ej, Hj. split; [ exact Hb | split; [ exact Hbej | exact Hd ] ].
Qed.

Lemma short_lhs_new {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (pre : BlockStateRef c) {st : Index.Refs.ShortStmtRef idx} {i : nat}
  (e : Index.Edges.ShortLhsEdge st i) (row : ShortLeftDecisionData) (f : ShortLhsFact pre e row) :
  match row with
  | ShortNewData n =>
      binder_ident (Index.Edges.sl_child e) = Some n
      /\ find_dup i n (Index.Edges.short_lhs_edges st) = None
      /\ (forall mr : BlockMemberRef pre, same_block_cand n (es_est (bm_ref mr)) = false)
  | _ => True end.
Proof.
  destruct f as [H | n j ej Hj Hb Hbej Hd | n Hb Hd Hm | n mr Hb Hd Hft Ho Hv
                | n mr Hb Hd Hft Ho Hv | n grp mr1 mr2 Hb Hd Hft Hlg Hs1 Hs2]; cbn; try exact I.
  split; [ exact Hb | split; [ exact Hd | exact Hm ] ].
Qed.

Lemma short_lhs_existing {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (pre : BlockStateRef c) {st : Index.Refs.ShortStmtRef idx} {i : nat}
  (e : Index.Edges.ShortLhsEdge st i) (row : ShortLeftDecisionData) (f : ShortLhsFact pre e row) :
  match row with
  | ShortExistingVariableData m => exists (n : Names.OrdinaryIdentifier) (mr : BlockMemberRef pre),
      bm_ord mr = m /\ binder_ident (Index.Edges.sl_child e) = Some n
      /\ find_dup i n (Index.Edges.short_lhs_edges st) = None
      /\ find_two_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = None
      /\ find_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = Some (bm_ord mr, es_est (bm_ref mr))
      /\ is_variable_binder (est_node (es_est (bm_ref mr))) = true
  | ShortExistingNonVariableData m => exists (n : Names.OrdinaryIdentifier) (mr : BlockMemberRef pre),
      bm_ord mr = m /\ binder_ident (Index.Edges.sl_child e) = Some n
      /\ find_dup i n (Index.Edges.short_lhs_edges st) = None
      /\ find_two_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = None
      /\ find_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = Some (bm_ord mr, es_est (bm_ref mr))
      /\ is_variable_binder (est_node (es_est (bm_ref mr))) = false
  | _ => True end.
Proof.
  destruct f as [H | n j ej Hj Hb Hbej Hd | n Hb Hd Hm | n mr Hb Hd Hft Ho Hv
                | n mr Hb Hd Hft Ho Hv | n grp mr1 mr2 Hb Hd Hft Hlg Hs1 Hs2]; cbn; try exact I.
  - exists n, mr. repeat split; solve [ reflexivity | assumption ].
  - exists n, mr. repeat split; solve [ reflexivity | assumption ].
Qed.

Lemma short_lhs_ambiguous {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (pre : BlockStateRef c) {st : Index.Refs.ShortStmtRef idx} {i : nat}
  (e : Index.Edges.ShortLhsEdge st i) (row : ShortLeftDecisionData) (f : ShortLhsFact pre e row) :
  match row with
  | ShortAmbiguousData j k => exists (n : Names.OrdinaryIdentifier) (grp : LocalGroupRef pre n)
      (mr1 mr2 : BlockMemberRef pre),
      bm_ord mr1 = j /\ bm_ord mr2 = k /\ binder_ident (Index.Edges.sl_child e) = Some n
      /\ find_dup i n (Index.Edges.short_lhs_edges st) = None
      /\ find_two_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = Some (bm_ord mr1, bm_ord mr2)
      /\ lg_members grp = local_group_refs pre n
      /\ same_block_cand n (es_est (bm_ref mr1)) = true
      /\ same_block_cand n (es_est (bm_ref mr2)) = true
  | _ => True end.
Proof.
  destruct f as [H | n j ej Hj Hb Hbej Hd | n Hb Hd Hm | n mr Hb Hd Hft Ho Hv
                | n mr Hb Hd Hft Ho Hv | n grp mr1 mr2 Hb Hd Hft Hlg Hs1 Hs2]; cbn; try exact I.
  exists n, grp, mr1, mr2. repeat split; solve [ reflexivity | assumption ].
Qed.

(* each decl fact case names its exact evidence, keyed by the retained decision row (contract §9.4) *)
Lemma decl_lhs_blank {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b0 : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b0}
  {c : BlockCutRef tr} (pre : BlockStateRef c) (t : Index.Core.NodeRef idx) (i : nat) (bd : Index.Core.NodeRef idx)
  (row : DeclBinderDecisionData) (f : DeclBinderFact pre t i bd row) :
  match row with DeclBlankData => binder_ident bd = None | _ => True end.
Proof. destruct f; cbn; solve [ exact I | assumption ]. Qed.

Lemma decl_lhs_duplicate {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b0 : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b0}
  {c : BlockCutRef tr} (pre : BlockStateRef c) (t : Index.Core.NodeRef idx) (i : nat) (bd : Index.Core.NodeRef idx)
  (row : DeclBinderDecisionData) (f : DeclBinderFact pre t i bd row) :
  match row with
  | DeclDuplicateEarlierData j => exists (n : Names.OrdinaryIdentifier) (bj : Index.Core.NodeRef idx),
      binder_ident bd = Some n /\ j < i /\ nth_error (decl_binders t) j = Some bj
      /\ binder_ident bj = Some n
      /\ find_ord (binder_name_matches n) 0 (firstn i (decl_binders t)) = Some (j, bj)
  | _ => True end.
Proof.
  destruct f as [H | n j bj Hb Hlt Hjn Hbj Hdup | n Hb Hfnd Hm | n mr Hb Hfnd Hft Ho
                | n grp mr1 mr2 Hb Hfnd Hft Hlg Hs1 Hs2]; cbn; try exact I.
  exists n, bj. repeat split; assumption.
Qed.

Lemma decl_lhs_fresh {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b0 : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b0}
  {c : BlockCutRef tr} (pre : BlockStateRef c) (t : Index.Core.NodeRef idx) (i : nat) (bd : Index.Core.NodeRef idx)
  (row : DeclBinderDecisionData) (f : DeclBinderFact pre t i bd row) :
  match row with
  | DeclFreshData => exists (n : Names.OrdinaryIdentifier),
      binder_ident bd = Some n
      /\ find_ord (binder_name_matches n) 0 (firstn i (decl_binders t)) = None
      /\ (forall mr : BlockMemberRef pre, same_block_cand n (es_est (bm_ref mr)) = false)
  | _ => True end.
Proof.
  destruct f as [H | n j bj Hb Hlt Hjn Hbj Hdup | n Hb Hfnd Hm | n mr Hb Hfnd Hft Ho
                | n grp mr1 mr2 Hb Hfnd Hft Hlg Hs1 Hs2]; cbn; try exact I.
  exists n. repeat split; assumption.
Qed.

Lemma decl_lhs_redeclared {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b0 : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b0}
  {c : BlockCutRef tr} (pre : BlockStateRef c) (t : Index.Core.NodeRef idx) (i : nat) (bd : Index.Core.NodeRef idx)
  (row : DeclBinderDecisionData) (f : DeclBinderFact pre t i bd row) :
  match row with
  | DeclRedeclaredPriorData m => exists (n : Names.OrdinaryIdentifier) (mr : BlockMemberRef pre),
      bm_ord mr = m /\ binder_ident bd = Some n
      /\ find_ord (binder_name_matches n) 0 (firstn i (decl_binders t)) = None
      /\ find_two_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = None
      /\ find_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = Some (bm_ord mr, es_est (bm_ref mr))
  | _ => True end.
Proof.
  destruct f as [H | n j bj Hb Hlt Hjn Hbj Hdup | n Hb Hfnd Hm | n mr Hb Hfnd Hft Ho
                | n grp mr1 mr2 Hb Hfnd Hft Hlg Hs1 Hs2]; cbn; try exact I.
  exists n, mr. repeat split; solve [ reflexivity | assumption ].
Qed.

Lemma decl_lhs_ambiguous {p} {idx : Index.Core.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b0 : Index.Core.NodeRef idx} {tr : BlockTraceRef bp b0}
  {c : BlockCutRef tr} (pre : BlockStateRef c) (t : Index.Core.NodeRef idx) (i : nat) (bd : Index.Core.NodeRef idx)
  (row : DeclBinderDecisionData) (f : DeclBinderFact pre t i bd row) :
  match row with
  | DeclAlreadyAmbiguousData j k => exists (n : Names.OrdinaryIdentifier) (grp : LocalGroupRef pre n)
      (mr1 mr2 : BlockMemberRef pre),
      bm_ord mr1 = j /\ bm_ord mr2 = k /\ binder_ident bd = Some n
      /\ find_ord (binder_name_matches n) 0 (firstn i (decl_binders t)) = None
      /\ find_two_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = Some (bm_ord mr1, bm_ord mr2)
      /\ lg_members grp = local_group_refs pre n
      /\ same_block_cand n (es_est (bm_ref mr1)) = true
      /\ same_block_cand n (es_est (bm_ref mr2)) = true
  | _ => True end.
Proof.
  destruct f as [H | n j bj Hb Hlt Hjn Hbj Hdup | n Hb Hfnd Hm | n mr Hb Hfnd Hft Ho
                | n grp mr1 mr2 Hb Hfnd Hft Hlg Hs1 Hs2]; cbn; try exact I.
  exists n, grp, mr1, mr2. repeat split; solve [ reflexivity | assumption ].
Qed.
