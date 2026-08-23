(* Bindings — binders, blocks, objects, scopes, ordinary-name resolution, and package-scope function declarations. *)

From Stdlib Require Import String List Bool Arith PeanoNat Lia Eqdep_dec PArith NArith.
From Fido Require Import Syntax Names Index Compilable.PackageIdentity.
Import ListNotations.

Module PI := Compilable.PackageIdentity.

(* a declaration binder role: a const/var/type spec name; a short-left is NOT a declaration binder *)
Definition is_binder_role (r : Index.Role) : bool :=
  match r with Index.RSpecName _ => true | _ => false end.

Record BinderRef {p} (idx : Index.ProgramIndex p) : Type := binder_ref {
  binder_node : Index.NodeRef idx ;
  binder_ok   : is_binder_role (Index.node_role binder_node) = true
}.
Arguments binder_ref {p idx} _ _.
Arguments binder_node {p idx} _.
Arguments binder_ok {p idx} _.

Lemma binderref_positional {p} {idx : Index.ProgramIndex p} (a b : BinderRef idx) :
  binder_node a = binder_node b -> a = b.
Proof. destruct a as [na Ha], b as [nb Hb]; cbn; intro E; subst nb; f_equal; apply (UIP_dec Bool.bool_dec). Qed.

(* a package-scope function declaration reference; the fixed main is its only current inhabitant (C9 adds funcs) *)
Inductive FunctionDeclRef {p} (idx : Index.ProgramIndex p) : Type :=
| FixedMainFunction : Index.MainOccurrenceRef idx -> FunctionDeclRef idx.
Arguments FixedMainFunction {p idx} _.

Definition function_occ {p} {idx : Index.ProgramIndex p} (f : FunctionDeclRef idx) : Index.MainOccurrenceRef idx :=
  match f with FixedMainFunction mo => mo end.
Definition function_node {p} {idx : Index.ProgramIndex p} (f : FunctionDeclRef idx) : Index.NodeRef idx :=
  Index.mo_node (function_occ f).

(* the exact function signature profile; the fixed main's profile is exactly zero parameters and zero results *)
Record FunctionProfile {p} (idx : Index.ProgramIndex p) : Type := mk_profile {
  fpr_params  : list (Index.NodeRef idx) ;
  fpr_results : list (Index.NodeRef idx)
}.
Arguments mk_profile {p idx} _ _.
Arguments fpr_params {p idx} _.
Arguments fpr_results {p idx} _.
Definition function_profile {p} {idx : Index.ProgramIndex p} (f : FunctionDeclRef idx) : FunctionProfile idx :=
  match f with FixedMainFunction _ => mk_profile [] [] end.
Lemma fixed_main_profile {p} {idx : Index.ProgramIndex p} (f : FunctionDeclRef idx) :
  fpr_params (function_profile f) = [] /\ fpr_results (function_profile f) = [].
Proof. destruct f; split; reflexivity. Qed.

(* a short-origin establishment's exact source identity: the statement, the left index, and its exact edge *)
Record ShortNewRef {p} (idx : Index.ProgramIndex p) : Type := mk_short_new {
  snr_stmt : Index.ShortStmtRef idx ;
  snr_ix   : nat ;
  snr_edge : Index.ShortLhsEdge snr_stmt snr_ix
}.
Arguments mk_short_new {p idx} _ _ _.
Arguments snr_stmt {p idx} _.
Arguments snr_ix {p idx} _.
Arguments snr_edge {p idx} _.

(* a declaration origin: a declaration binder, a package-scope function declaration, or an exact ShortNew *)
Inductive DeclOrigin {p} (idx : Index.ProgramIndex p) : Type :=
| DOBinder : BinderRef idx -> DeclOrigin idx
| DOFunc   : FunctionDeclRef idx -> DeclOrigin idx
| DOShort  : ShortNewRef idx -> DeclOrigin idx.
Arguments DOBinder {p idx} _.
Arguments DOFunc {p idx} _.
Arguments DOShort {p idx} _.

(* the establishing source occurrence of a declaration origin: binder token, function declaration, or left *)
Definition do_node {p} {idx : Index.ProgramIndex p} (o : DeclOrigin idx) : Index.NodeRef idx :=
  match o with
  | DOBinder b => binder_node b
  | DOFunc f => function_node f
  | DOShort sn => Index.sl_child (snr_edge sn)
  end.

(* an object a name resolves to: a predeclared identity, or a source declaration (a binder or a function) *)
Inductive ObjectRef {p} (idx : Index.ProgramIndex p) : Type :=
| PredeclaredObject : Names.PredeclaredName -> ObjectRef idx
| SourceObject      : DeclOrigin idx -> ObjectRef idx.
Arguments PredeclaredObject {p idx} _.
Arguments SourceObject {p idx} _.

Inductive ScopeId {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
| PackageScope : PI.PackageRef s -> ScopeId s
| BlockScope   : Index.BlockRef idx -> ScopeId s.
Arguments PackageScope {p idx s} _.
Arguments BlockScope {p idx s} _.

(* a block binder's visibility start: type at its position, else its enclosing spec/statement parent's extent *)
Definition vis_start {p} {idx : Index.ProgramIndex p} (b : Index.NodeRef idx) : nat :=
  match Index.node_role b with
  | Index.RSpecName Index.TypeSpecF => Index.nr_pos b
  | Index.RSpecName _ => match Index.node_parent b with Some par => Index.node_extent par | None => Index.nr_pos b end
  | Index.RShortLhs   => match Index.node_parent b with Some par => Index.node_extent par | None => Index.nr_pos b end
  | _ => Index.nr_pos b
  end.

Definition binder_ident {p} {idx : Index.ProgramIndex p} (b : Index.NodeRef idx) : option Names.OrdinaryIdentifier :=
  match Index.node_view b with Index.VBindingName (Syntax.BNamed n) => Some n | _ => None end.

Lemma spec_binder {p} {idx : Index.ProgramIndex p} (b : Index.NodeRef idx) (fl : Index.SpecFlavor) :
  Index.node_role b = Index.RSpecName fl -> is_binder_role (Index.node_role b) = true.
Proof. intro H; rewrite H; reflexivity. Qed.

(* whether a binder node spells a given name *)
Definition binder_name_matches {p} {idx : Index.ProgramIndex p}
  (n : Names.OrdinaryIdentifier) (b : Index.NodeRef idx) : bool :=
  match binder_ident b with Some m => Names.ordinary_equalb m n | None => false end.

(* the source identifier "main"; the fixed package-scope main function establishes under this ordinary name *)
Definition main_ident : Names.OrdinaryIdentifier :=
  Names.MakeOrdinary (Names.MakeIdentifier "main"%string eq_refl) eq_refl.

Record Est {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type := mk_est {
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
Definition est_node {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} (e : Est s) : Index.NodeRef idx :=
  do_node (est_origin e).

(* a declaration binder establishes its name at the given scope; only an exact spec-name edge establishes here *)
Definition spec_name_est {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {fl : Index.SpecFlavor} {sp : Index.SpecRef idx fl} {i : nat}
  (sc : ScopeId s) (ne : Index.SpecNameEdge sp i) : option (Est s) :=
  match binder_ident (Index.sn_child ne) with
  | Some n => Some (mk_est (DOBinder (binder_ref (Index.sn_child ne) (spec_binder _ fl (Index.sn_role ne))))
                          n sc (vis_start (Index.sn_child ne)))
  | None => None
  end.

(* one spec's establishments at its scope: every named binder among its exact name edges, in name order *)
Definition spec_ests {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {fl : Index.SpecFlavor} (sc : ScopeId s) (sp : Index.SpecRef idx fl) : list (Est s) :=
  flat_map (fun x => match spec_name_est sc (projT2 x) with Some e => [e] | None => [] end)
           (Index.spec_name_edges sp).

(* the spec emission of one occurrence, factored over its view so laws can invert it exactly *)
Definition spec_emit {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (r : Index.NodeRef idx) (v : Index.NodeView) (Hv : Index.node_view r = v) : list (Est s) :=
  match v as v0 return Index.node_view r = v0 -> list (Est s) with
  | Index.VConstSpec sh => fun Hv0 => spec_ests sc (Index.mkSpecRef (fl := Index.ConstSpecF) r sh Hv0)
  | Index.VVarSpec sh => fun Hv0 => spec_ests sc (Index.mkSpecRef (fl := Index.VarSpecF) r sh Hv0)
  | Index.VTypeSpec sh => fun Hv0 => spec_ests sc (Index.mkSpecRef (fl := Index.TypeSpecF) r sh Hv0)
  | _ => fun _ => []
  end Hv.

(* one declaration's establishments: each child spec's named binders, in spec order *)
Definition decl_ests {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (d : Index.NodeRef idx) : list (Est s) :=
  flat_map (fun x => spec_emit sc (Index.ca_child (projT2 x)) (Index.node_view (Index.ca_child (projT2 x))) eq_refl)
           (Index.all_children d).

(* a declaration statement's or top-level declaration's establishments: its one declaration child's specs *)
Definition stmt_decl_ests {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (t : Index.NodeRef idx) : list (Est s) :=
  match Index.child_at_opt t 0 with
  | Some e => decl_ests sc (Index.ca_child e)
  | None => []
  end.

(* one spec's binder nodes, one per exact name edge in name order — blank and named alike *)
Definition spec_binder_nodes {p} {idx : Index.ProgramIndex p}
  {fl : Index.SpecFlavor} (sp : Index.SpecRef idx fl) : list (Index.NodeRef idx) :=
  map (fun x => Index.sn_child (projT2 x)) (Index.spec_name_edges sp).

(* the binder nodes of one spec occurrence, factored over its view *)
Definition spec_binders_view {p} {idx : Index.ProgramIndex p}
  (r : Index.NodeRef idx) (v : Index.NodeView) (Hv : Index.node_view r = v) : list (Index.NodeRef idx) :=
  match v as v0 return Index.node_view r = v0 -> list (Index.NodeRef idx) with
  | Index.VConstSpec sh => fun Hv0 => spec_binder_nodes (Index.mkSpecRef (fl := Index.ConstSpecF) r sh Hv0)
  | Index.VVarSpec sh => fun Hv0 => spec_binder_nodes (Index.mkSpecRef (fl := Index.VarSpecF) r sh Hv0)
  | Index.VTypeSpec sh => fun Hv0 => spec_binder_nodes (Index.mkSpecRef (fl := Index.TypeSpecF) r sh Hv0)
  | _ => fun _ => []
  end Hv.

(* one declaration's binder nodes: each child spec's binders, in spec order *)
Definition decl_binder_nodes {p} {idx : Index.ProgramIndex p} (d : Index.NodeRef idx) : list (Index.NodeRef idx) :=
  flat_map (fun x => spec_binders_view (Index.ca_child (projT2 x))
                       (Index.node_view (Index.ca_child (projT2 x))) eq_refl)
           (Index.all_children d).

(* a declaration statement's or top declaration's flat binder sequence, in source order *)
Definition decl_binders {p} {idx : Index.ProgramIndex p} (t : Index.NodeRef idx) : list (Index.NodeRef idx) :=
  match Index.child_at_opt t 0 with
  | Some e => decl_binder_nodes (Index.ca_child e)
  | None => []
  end.

(* a package-scope function declaration: the fixed main establishes the name main at package scope *)
Definition make_main_est {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (b : Index.NodeRef idx) : option (Est s) :=
  (match Index.is_main_view (Index.node_view b) as m
     return Index.is_main_view (Index.node_view b) = m -> option (Est s) with
   | true => fun H => Some (mk_est (DOFunc (FixedMainFunction (Index.mkMainOccurrenceRef b H))) main_ident (PackageScope pr) (Index.nr_pos b))
   | false => fun _ => None
   end) eq_refl.

(* the package-scope establishments of one occurrence: a fixed main, or a top-level declaration's binders *)
Inductive MainStatus {p} {idx : Index.ProgramIndex p}
  (s : PI.PackageSurface idx) (pr : PI.PackageRef s) : Type :=
| MainMissing : MainStatus s pr
| MainOne : Est s -> MainStatus s pr
| MainMultiple : Est s -> Est s -> list (Est s) -> MainStatus s pr.
Arguments MainMissing {p idx s pr}.
Arguments MainOne {p idx s pr} _.
Arguments MainMultiple {p idx s pr} _ _ _.

Definition main_status_ests {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {pr : PI.PackageRef s}
  (st : MainStatus s pr) : list (Est s) :=
  match st with
  | MainMissing => []
  | MainOne m => [m]
  | MainMultiple m1 m2 rest => m1 :: m2 :: rest
  end.

(* a function-declaration establishment (DOFunc); the fixed main is its only current inhabitant *)
Definition is_func_est {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} (e : Est s) : bool :=
  match est_origin e with DOFunc _ => true | _ => false end.

(* the package-scope function declarations named main in one package, in establishment order *)
Definition main_ests_of {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (ests : list (Est s)) (pr : PI.PackageRef s) : list (Est s) :=
  filter (fun e => andb (is_func_est e)
                        (andb (Names.ordinary_equalb (est_name e) main_ident)
                              (match est_scope e with PackageScope q => PI.packageref_eqb q pr | _ => false end)))
         ests.

Definition main_status_of {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (ests : list (Est s)) (pr : PI.PackageRef s) : MainStatus s pr :=
  match main_ests_of ests pr with
  | [] => MainMissing
  | m :: nil => MainOne m
  | m1 :: m2 :: rest => MainMultiple m1 m2 rest
  end.

Lemma main_status_ests_of {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (ests : list (Est s)) (pr : PI.PackageRef s) :
  main_status_ests (main_status_of ests pr) = main_ests_of ests pr.
Proof. unfold main_status_of; destruct (main_ests_of ests pr) as [|m1 [|m2 rest]]; reflexivity. Qed.

(* declaration groups: the establishments sharing one exact scope and spelling *)

Definition noderef_eqb {p} {idx : Index.ProgramIndex p} (a b : Index.NodeRef idx) : bool :=
  andb (Index.fileref_eqb (Index.nr_file a) (Index.nr_file b)) (Nat.eqb (Index.nr_pos a) (Index.nr_pos b)).

Lemma noderef_eqb_spec {p} {idx : Index.ProgramIndex p} (a b : Index.NodeRef idx) :
  noderef_eqb a b = true <-> a = b.
Proof.
  unfold noderef_eqb; split.
  - intro H; apply andb_true_iff in H as [Hf Hp].
    apply Index.fileref_eqb_spec in Hf. apply Nat.eqb_eq in Hp. apply Index.noderef_positional; assumption.
  - intro H; subst b. rewrite (proj2 (Index.fileref_eqb_spec _ _) eq_refl), Nat.eqb_refl; reflexivity.
Qed.

Definition scope_eqb {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} (a b : ScopeId s) : bool :=
  match a, b with
  | PackageScope pa, PackageScope pb => PI.packageref_eqb pa pb
  | BlockScope ba, BlockScope bb => noderef_eqb (Index.bl_node ba) (Index.bl_node bb)
  | _, _ => false
  end.

Lemma scope_eqb_spec {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} (a b : ScopeId s) :
  scope_eqb a b = true <-> a = b.
Proof.
  destruct a as [pa|ba], b as [pb|bb]; cbn; split; try discriminate.
  - intro H; apply PI.packageref_eqb_spec in H; subst; reflexivity.
  - intro H; injection H as <-; apply (proj2 (PI.packageref_eqb_spec _ _) eq_refl).
  - intro H; apply noderef_eqb_spec in H; apply Index.blockref_positional in H; subst; reflexivity.
  - intro H; injection H as <-; apply (proj2 (noderef_eqb_spec _ _) eq_refl).
Qed.

(* two establishments belong to the same declaration group iff they share an exact scope and spelling *)
Definition same_group {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} (a b : Est s) : bool :=
  andb (scope_eqb (est_scope a) (est_scope b)) (Names.ordinary_equalb (est_name a) (est_name b)).

(* two establishments are the same establishment iff they share their exact source occurrence *)
Definition est_eqb {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} (a b : Est s) : bool :=
  noderef_eqb (est_node a) (est_node b).

(* the ordered members of e's group over an establishment list: shared exact scope and spelling, list order *)
Definition is_block_scoped {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} (e : Est s) : bool :=
  match est_scope e with BlockScope _ => true | PackageScope _ => false end.

(* a binder introduces a variable object exactly when it is a short-lhs or var-spec name *)
Definition is_variable_binder {p} {idx : Index.ProgramIndex p} (b : Index.NodeRef idx) : bool :=
  match Index.node_role b with Index.RShortLhs | Index.RSpecName Index.VarSpecF => true | _ => false end.

Definition is_explicit_const_spec {p} {idx : Index.ProgramIndex p} (c : Index.NodeRef idx) : bool :=
  match Index.node_view c with Index.VConstSpec (Index.CSExplicit _ _ _) => true | _ => false end.

(* a const spec is explicit exactly when its retained shape is; the ref's shape is the one authority *)
Definition cs_explicit {p} {idx : Index.ProgramIndex p} (cs : Index.SpecRef idx Index.ConstSpecF) : bool :=
  match Index.sp_shape cs with Index.CSExplicit _ _ _ => true | Index.CSInherited _ => false end.

(* the first earlier left edge of the same exact statement repeating this name, with its exact index *)
Fixpoint find_dup {p} {idx : Index.ProgramIndex p} {st : Index.ShortStmtRef idx}
  (i : nat) (n : Names.OrdinaryIdentifier) (l : list { j : nat & Index.ShortLhsEdge st j }) {struct l}
  : option { j : nat & (Index.ShortLhsEdge st j * (j < i))%type } :=
  match l with
  | [] => None
  | existT _ j e :: rest =>
      match lt_dec j i with
      | left Hj =>
          if match binder_ident (Index.sl_child e) with
             | Some m => Names.ordinary_equalb m n | None => false end
          then Some (existT _ j (e, Hj)) else find_dup i n rest
      | right _ => find_dup i n rest
      end
  end.

(* the exact first-in-group evidence: the spec is a file root or sits at ordinal zero under its parent *)
Inductive ConstFirst {p} {idx : Index.ProgramIndex p} (cs : Index.SpecRef idx Index.ConstSpecF) : Type :=
| CFRoot : Index.node_parent (Index.sp_node cs) = None -> ConstFirst cs
| CFOrd0 : forall se : Index.SelfEdge (Index.sp_node cs), Index.se_ord se = 0 -> ConstFirst cs.
Arguments CFRoot {p idx cs} _.
Arguments CFOrd0 {p idx cs} _ _.

(* the exact immediate predecessor: the canonical edges of predecessor and spec at adjacent ordinals *)
Record ConstAdjacency {p} {idx : Index.ProgramIndex p}
  (cs pred : Index.SpecRef idx Index.ConstSpecF) : Type := mk_const_adj {
  cad_parent  : Index.NodeRef idx ;
  cad_ord     : nat ;
  cad_pred_at : Index.ChildAt cad_parent cad_ord ;
  cad_pred_eq : Index.sp_node pred = Index.ca_child cad_pred_at ;
  cad_self_at : Index.ChildAt cad_parent (S cad_ord) ;
  cad_self_eq : Index.sp_node cs = Index.ca_child cad_self_at
}.
Arguments mk_const_adj {p idx cs pred} _ _ _ _ _ _.
Arguments cad_parent {p idx cs pred} _.
Arguments cad_ord {p idx cs pred} _.
Arguments cad_pred_at {p idx cs pred} _.
Arguments cad_pred_eq {p idx cs pred} _.
Arguments cad_self_at {p idx cs pred} _.
Arguments cad_self_eq {p idx cs pred} _.

(* the exact const-spec judgment: explicit, first inherited, or inherited with its exact predecessor chain *)
Inductive ConstJudgment {p} {idx : Index.ProgramIndex p} : Index.SpecRef idx Index.ConstSpecF -> Type :=
| CJExplicit : forall cs, cs_explicit cs = true -> ConstJudgment cs
| CJFirstInherited : forall cs, cs_explicit cs = false -> ConstFirst cs -> ConstJudgment cs
| CJInherited : forall cs pred, cs_explicit cs = false -> ConstAdjacency cs pred ->
                ConstJudgment pred -> ConstJudgment cs.

(* the effective explicit origin, projected through the exact retained predecessor chain *)
Fixpoint const_origin {p} {idx : Index.ProgramIndex p} {cs : Index.SpecRef idx Index.ConstSpecF}
  (j : ConstJudgment cs) : option { o : Index.SpecRef idx Index.ConstSpecF & cs_explicit o = true } :=
  match j with
  | CJExplicit c He => Some (existT _ c He)
  | CJFirstInherited _ _ _ => None
  | CJInherited _ _ _ _ jp => const_origin jp
  end.

(* the exact immediate predecessor a judgment retains, when it has one *)
Definition const_pred {p} {idx : Index.ProgramIndex p} {cs : Index.SpecRef idx Index.ConstSpecF}
  (j : ConstJudgment cs) : option (Index.SpecRef idx Index.ConstSpecF) :=
  match j with
  | CJExplicit _ _ => None
  | CJFirstInherited _ _ _ => None
  | CJInherited _ pred _ _ _ => Some pred
  end.

(* judge the const spec at ordinal k under its declaration, chaining structurally on the ordinal *)
Fixpoint const_judge {p} {idx : Index.ProgramIndex p} (par : Index.NodeRef idx)
  (Hd : Index.node_view par = Index.VDecl Index.ConstSpecF) (k : nat) {struct k}
  : forall (e : Index.ChildAt par k) (cs : Index.SpecRef idx Index.ConstSpecF),
    Index.sp_node cs = Index.ca_child e -> ConstJudgment cs :=
  match k with
  | O => fun e cs Hnode =>
      match Bool.bool_dec (cs_explicit cs) true with
      | left He => CJExplicit cs He
      | right Hne =>
          CJFirstInherited cs (Bool.not_true_is_false _ Hne)
            (CFOrd0 (Index.mkSelfEdge par 0 e (eq_sym Hnode)) eq_refl)
      end
  | S k' => fun e cs Hnode =>
      match Bool.bool_dec (cs_explicit cs) true with
      | left He => CJExplicit cs He
      | right Hne =>
          let pca := Index.child_at_lt par k' (Index.ca_pred_lt e) in
          let pred := Index.spec_child_at par k' Hd pca in
          CJInherited cs (proj1_sig pred) (Bool.not_true_is_false _ Hne)
            (mk_const_adj par k' pca (proj2_sig pred) e Hnode)
            (const_judge par Hd k' pca (proj1_sig pred) (proj2_sig pred))
      end
  end.

(* a const spec that sits under a parent sits under its const declaration *)
Lemma self_parent_decl {p} {idx : Index.ProgramIndex p} (cs : Index.SpecRef idx Index.ConstSpecF)
  (se : Index.SelfEdge (Index.sp_node cs)) :
  Index.node_view (Index.se_parent se) = Index.VDecl Index.ConstSpecF.
Proof.
  pose proof (Index.ca_at (Index.se_at se)) as Hat.
  rewrite (Index.se_child_eq se) in Hat.
  destruct (Index.node_child_const_parent (Index.se_parent se) (Index.sp_node cs)
              (Index.se_ord se) (Index.sp_shape cs) Hat (Index.sp_ok cs)) as [fl Hfl].
  destruct fl; [ exact Hfl | | ];
    (pose proof (Index.node_child_decl_spec (Index.se_parent se) (Index.sp_node cs) _
                   (Index.se_ord se) Hfl Hat) as Hclass;
     rewrite (Index.sp_ok cs) in Hclass; cbn in Hclass; destruct Hclass).
Qed.

(* the one canonical judgment of a const spec, decided at its exact canonical position *)
Definition const_judgment_of {p} {idx : Index.ProgramIndex p}
  (cs : Index.SpecRef idx Index.ConstSpecF) : ConstJudgment cs :=
  (match Index.node_parent (Index.sp_node cs) as o
         return Index.node_parent (Index.sp_node cs) = o -> ConstJudgment cs with
   | Some par => fun Hp =>
       let se := Index.self_edge_of (Index.sp_node cs) par Hp in
       const_judge (Index.se_parent se) (self_parent_decl cs se) (Index.se_ord se)
         (Index.se_at se) cs (eq_sym (Index.se_child_eq se))
   | None => fun Hp =>
       match Bool.bool_dec (cs_explicit cs) true with
       | left He => CJExplicit cs He
       | right Hne => CJFirstInherited cs (Bool.not_true_is_false _ Hne) (CFRoot Hp)
       end
   end) eq_refl.

(* the const-spec emission of one occurrence, factored over its view so laws can invert it exactly *)
Definition const_ref_emit {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx)
  (v : Index.NodeView) (Hv : Index.node_view r = v) : list (Index.SpecRef idx Index.ConstSpecF) :=
  match v as v0 return Index.node_view r = v0 -> _ with
  | Index.VConstSpec sh => fun Hv0 => [Index.mkSpecRef (fl := Index.ConstSpecF) r sh Hv0]
  | _ => fun _ => []
  end Hv.

Lemma const_ref_emit_cover {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx)
  (v : Index.NodeView) (Hv : Index.node_view r = v) (sh : Index.ConstShape) :
  v = Index.VConstSpec sh ->
  exists cs', In cs' (const_ref_emit r v Hv) /\ Index.sp_node cs' = r.
Proof.
  intro E. revert Hv. subst v. intro Hv. cbn.
  eexists. split; [ left; reflexivity | reflexivity ].
Qed.

(* every represented const spec of the surface, in exact source order: file order, then position order *)
Definition const_specs_of_file {p} {idx : Index.ProgramIndex p} (fr : Index.FileRef idx)
  : list (Index.SpecRef idx Index.ConstSpecF) :=
  flat_map (fun pos => match Index.mk_noderef fr (Pos.of_succ_nat pos) with
                       | Some r => const_ref_emit r (Index.node_view r) eq_refl
                       | None => []
                       end)
           (seq 0 (Index.occ_count fr)).
Definition const_subjects {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
  : list (Index.SpecRef idx Index.ConstSpecF) :=
  flat_map (fun pr => flat_map const_specs_of_file (PI.pkg_members pr)) (PI.packages s).

(* the one canonical const-judgment table of the surface *)
Definition const_table {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
  : list { cs : Index.SpecRef idx Index.ConstSpecF & ConstJudgment cs } :=
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
Definition same_block_cand {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (n : Names.OrdinaryIdentifier) (e : Est s) : bool :=
  andb (is_block_scoped e) (Names.ordinary_equalb (est_name e) n).

(* the exact new establishment a ShortNew left creates: its origin ties the statement, index, and edge *)
Definition new_est {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) {st : Index.ShortStmtRef idx} {i : nat}
  (e : Index.ShortLhsEdge st i) (n : Names.OrdinaryIdentifier) : Est s :=
  mk_est (DOShort (mk_short_new st i e)) n (BlockScope br) (vis_start (Index.sl_child e)).

(* the canonical short-left decision as cheap descriptive data, retained in the event, authoritative only as a row *)
Inductive ShortLeftDecisionData : Type :=
| ShortBlankData
| ShortDuplicateData (earlier : nat)
| ShortNewData (n : Names.OrdinaryIdentifier)
| ShortExistingVariableData (member : nat)
| ShortExistingNonVariableData (member : nat)
| ShortAmbiguousData (first second : nat).

(* the one canonical decision per left, in fixed precedence: blank, earliest duplicate, ambiguous, existing, new *)
Definition short_left_decide {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) {st : Index.ShortStmtRef idx} {i : nat} (e : Index.ShortLhsEdge st i)
  : ShortLeftDecisionData :=
  match binder_ident (Index.sl_child e) with
  | None => ShortBlankData
  | Some n =>
      match find_dup i n (Index.short_lhs_edges st) with
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
Definition short_decide_rows {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) (st : Index.ShortStmtRef idx) : list ShortLeftDecisionData :=
  map (fun x => match x with existT _ i e => short_left_decide env e end) (Index.short_lhs_edges st).

(* event additions as the ordered projection of the retained New rows — the one and only source of short additions *)
Definition short_rows_adds {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) (st : Index.ShortStmtRef idx) (rows : list ShortLeftDecisionData) : list (Est s) :=
  flat_map (fun x => match x with existT _ i e =>
     match nth_error rows i with Some (ShortNewData n) => [new_est br e n] | _ => [] end end)
    (Index.short_lhs_edges st).
Lemma short_rows_adds_scope {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) (st : Index.ShortStmtRef idx) (rows : list ShortLeftDecisionData) (e : Est s) :
  In e (short_rows_adds br st rows) -> est_scope e = BlockScope br.
Proof.
  unfold short_rows_adds. intro Hin. apply in_flat_map in Hin. destruct Hin as [x [_ Hin]].
  destruct x as [i ed]. destruct (nth_error rows i) as [row|]; try (exact (match Hin with end)).
  destruct row; try (exact (match Hin with end)).
  destruct Hin as [<-|F]; [ reflexivity | destruct F ].
Qed.

(* a declaration establishment rebuilt from its binder node alone, equal to the spec-edge establishment *)
Definition node_binder_est {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (bd : Index.NodeRef idx) : option (Est s) :=
  match binder_ident bd with
  | Some n =>
      match Bool.bool_dec (is_binder_role (Index.node_role bd)) true with
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
Definition decl_binder_decide {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) (t : Index.NodeRef idx) (i : nat) (bd : Index.NodeRef idx) : DeclBinderDecisionData :=
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
Definition decl_decide_rows {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) (t : Index.NodeRef idx) : list DeclBinderDecisionData :=
  map (fun ib => decl_binder_decide env t (fst ib) (snd ib))
      (combine (seq 0 (length (decl_binders t))) (decl_binders t)).

(* decl additions as the ordered projection of the retained nonblank rows — the one source of decl additions *)
Definition decl_rows_adds {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (t : Index.NodeRef idx) (rows : list DeclBinderDecisionData) : list (Est s) :=
  flat_map (fun rb => match rb with
                      | (DeclBlankData, _) => []
                      | (_, bd) => match node_binder_est sc bd with Some e => [e] | None => [] end
                      end)
           (combine rows (decl_binders t)).

Lemma node_binder_est_scope {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (bd : Index.NodeRef idx) (e : Est s) :
  node_binder_est sc bd = Some e -> est_scope e = sc.
Proof.
  unfold node_binder_est. destruct (binder_ident bd) as [n|]; [| discriminate].
  destruct (Bool.bool_dec (is_binder_role (Index.node_role bd)) true) as [Hr|_]; intro H;
    [ injection H as <-; reflexivity | discriminate H ].
Qed.

Lemma decl_rows_adds_scope {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (t : Index.NodeRef idx) (rows : list DeclBinderDecisionData) (e : Est s) :
  In e (decl_rows_adds sc t rows) -> est_scope e = sc.
Proof.
  unfold decl_rows_adds. intro Hin. apply in_flat_map in Hin. destruct Hin as [rb [_ Hin]].
  assert (Hgen : forall bd, In e (match node_binder_est sc bd with Some e0 => [e0] | None => [] end)
                            -> est_scope e = sc).
  { intros bd H. destruct (node_binder_est sc bd) as [e0|] eqn:Hn; [| destruct H].
    destruct H as [<-|F]; [ exact (node_binder_est_scope sc bd e0 Hn) | destruct F ]. }
  destruct rb as [row bd]. destruct row;
    [ destruct Hin | exact (Hgen bd Hin) | exact (Hgen bd Hin) | exact (Hgen bd Hin) | exact (Hgen bd Hin) ].
Qed.

Lemma stmt_has_parent {p} {idx : Index.ProgramIndex p} (st : Index.ShortStmtRef idx) :
  Index.node_parent (Index.sh_node st) = None -> False.
Proof.
  intro Hp. pose proof (Index.parentless_view_file (Index.sh_node st) Hp) as Hv.
  rewrite (Index.sh_ok st) in Hv. discriminate Hv.
Qed.

Lemma stmt_parent_block {p} {idx : Index.ProgramIndex p} (st : Index.ShortStmtRef idx)
  (par : Index.NodeRef idx) :
  Index.node_parent (Index.sh_node st) = Some par -> Index.node_view par = Index.VBlock.
Proof.
  intro Hp.
  destruct (Index.all_children_of_parent (Index.sh_node st) par Hp) as [k [e [Hrow Hc]]].
  apply (Index.child_at_stmt_block e (Index.SSShort (Index.sh_names st) (Index.sh_values st))).
  rewrite Hc. exact (Index.sh_ok st).
Qed.

Lemma stmt_parent_not_block {p} {idx : Index.ProgramIndex p} (st : Index.ShortStmtRef idx)
  (par : Index.NodeRef idx) :
  Index.node_parent (Index.sh_node st) = Some par ->
  Index.is_block_view (Index.node_view par) = false -> False.
Proof. intros Hp Hb. rewrite (stmt_parent_block st par Hp) in Hb. discriminate Hb. Qed.


(* one retained block event: expr statement, judged declaration, or judged short — no raw predecessor env stored *)
Inductive BlockEv {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
| BEvExpr : Index.NodeRef idx -> BlockEv s
| BEvDecl : forall (sc : ScopeId s) (t : Index.NodeRef idx), list DeclBinderDecisionData -> BlockEv s
| BEvShort : forall (st : Index.ShortStmtRef idx), list ShortLeftDecisionData -> BlockEv s.
Arguments BEvExpr {p idx s} _.
Arguments BEvDecl {p idx s} _ _ _.
Arguments BEvShort {p idx s} _ _.

Definition bev_node {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (ev : BlockEv s) : Index.NodeRef idx :=
  match ev with
  | BEvExpr r => r
  | BEvDecl _ t _ => t
  | BEvShort st _ => Index.sh_node st
  end.

(* the exact ordered additions of one event; a short's News need its exact block for their scope *)
Definition bev_adds {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) (ev : BlockEv s) : list (Est s) :=
  match ev with
  | BEvExpr _ => []
  | BEvDecl sc t rows => decl_rows_adds sc t rows
  | BEvShort st rows => short_rows_adds br st rows
  end.

(* one package event: the exact top occurrence and its exact ordered additions *)
Definition PkgEv {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
  (Index.NodeRef idx * list (Est s))%type.

(* one block trace row: the exact block, its package position, and its events in statement order *)
Definition TraceRow {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
  (Index.BlockRef idx * nat * list (BlockEv s))%type.
Definition trow_block {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (t : TraceRow s) : Index.BlockRef idx := fst (fst t).
Definition trow_pkg {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (t : TraceRow s) : nat := snd (fst t).
Definition trow_evs {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (t : TraceRow s) : list (BlockEv s) := snd t.

(* the retained phase graph: the package ledgers, the block traces, and the const judgment table *)
Definition PhaseData {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
  (list (list (PkgEv s)) * list (TraceRow s)
   * list { cs : Index.SpecRef idx Index.ConstSpecF & ConstJudgment cs })%type.

(* the one canonical builder; Internal is plumbing under the phase pin, never a client authority *)
Section Build.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p}.
Variable s : PI.PackageSurface idx.

Definition pkg_event_at (pr : PI.PackageRef s) (r : Index.NodeRef idx) : option (PkgEv s) :=
  match Index.node_view r with
  | Index.VTop Index.TSMain =>
      match make_main_est pr r with Some e0 => Some (r, [e0]) | None => None end
  | Index.VTop Index.TSTopDecl => Some (r, stmt_decl_ests (PackageScope pr) r)
  | _ => None
  end.

Definition ledger_of (pr : PI.PackageRef s) : list (PkgEv s) :=
  flat_map (fun fr =>
    flat_map (fun pos => match Index.mk_noderef fr (Pos.of_succ_nat pos) with
                         | Some r => match pkg_event_at pr r with Some ev => [ev] | None => [] end
                         | None => [] end)
             (seq 0 (Index.occ_count fr)))
    (PI.pkg_members pr).

Definition pkg_env_of (pr : PI.PackageRef s) : list (Est s) :=
  flat_map snd (ledger_of pr).

Definition block_event (br : Index.BlockRef idx) (env : list (Est s)) (c : Index.NodeRef idx)
  (v : Index.NodeView) (Hv : Index.node_view c = v) : BlockEv s :=
  match v as v0 return Index.node_view c = v0 -> BlockEv s with
  | Index.VStmt Index.SSDecl => fun _ =>
      BEvDecl (BlockScope br) c (decl_decide_rows env c)
  | Index.VStmt (Index.SSShort nn nv) => fun Hv0 =>
      BEvShort (Index.mkShortStmtRef c nn nv Hv0)
        (short_decide_rows env (Index.mkShortStmtRef c nn nv Hv0))
  | _ => fun _ => BEvExpr c
  end Hv.

Fixpoint block_fold (br : Index.BlockRef idx)
  (l : list { o : nat & Index.ChildAt (Index.bl_node br) o }) (env : list (Est s)) {struct l}
  : list (BlockEv s) :=
  match l with
  | [] => []
  | x :: t =>
      let ev := block_event br env (Index.ca_child (projT2 x))
                  (Index.node_view (Index.ca_child (projT2 x))) eq_refl in
      ev :: block_fold br t (env ++ bev_adds br ev)
  end.

Definition traces_of_pkg (pr : PI.PackageRef s) : list (TraceRow s) :=
  let pe := pkg_env_of pr in
  flat_map (fun fr =>
    flat_map (fun pos =>
      match Index.mk_noderef fr (Pos.of_succ_nat pos) with
      | Some r =>
          (match Index.is_block_view (Index.node_view r) as bv
                 return Index.is_block_view (Index.node_view r) = bv -> list (TraceRow s) with
           | true => fun Hb =>
               [ (Index.mkBlockRef r Hb, PI.pr_pos pr,
                  block_fold (Index.mkBlockRef r Hb)
                    (Index.all_children (Index.bl_node (Index.mkBlockRef r Hb))) pe) ]
           | false => fun _ => []
           end) eq_refl
      | None => [] end)
      (seq 0 (Index.occ_count fr)))
    (PI.pkg_members pr).

Definition phase_data : PhaseData s :=
  (map ledger_of (PI.packages s),
   flat_map traces_of_pkg (PI.packages s),
   const_table s).

End Build.

(* PhaseData is transparent, inspectable, carries no authority; the sealed certificate below is the sole authority *)
Module Type PHASE_CERT.
  Parameter Certified : forall {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx),
    PhaseData s -> Prop.
  Parameter canonical : forall {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx),
    Certified s (phase_data s).
  Parameter certified_canonical : forall {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
    (d : PhaseData s), Certified s d -> d = phase_data s.
End PHASE_CERT.
Module PhaseCert : PHASE_CERT.
  Definition Certified {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
    (d : PhaseData s) : Prop := d = phase_data s.
  Definition canonical {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
    : Certified s (phase_data s) := eq_refl.
  Definition certified_canonical {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
    (d : PhaseData s) (c : Certified s d) : d = phase_data s := c.
End PhaseCert.

(* the phase authority: an abstract certificate that exact data d is the canonical phase; unforgeable *)
Definition BindingPhase {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
  (d : PhaseData s) : Prop := PhaseCert.Certified s d.
Definition bindings {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
  : BindingPhase s (phase_data s) := PhaseCert.canonical s.
(* the certificate's data is the canonical computation — the authority-to-canonicity bridge the laws consume *)
Definition bp_canonical {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : d = phase_data s := PhaseCert.certified_canonical s d bp.

Definition bp_ledgers {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : list (list (PkgEv s)) := fst (fst d).
Definition bp_traces {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : list (TraceRow s) := snd (fst d).
Definition bp_consts {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : list { cs : Index.SpecRef idx Index.ConstSpecF & ConstJudgment cs } :=
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

Lemma nodeview_eq_dec : forall a b : Index.NodeView, {a = b} + {a <> b}.
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
Lemma specref_positional {p} {idx : Index.ProgramIndex p} {fl : Index.SpecFlavor}
  (a b : Index.SpecRef idx fl) : Index.sp_node a = Index.sp_node b -> a = b.
Proof.
  destruct a as [na sha Ha], b as [nb shb Hb]; cbn; intro E; subst nb.
  assert (Hv : Index.spec_view_of fl sha = Index.spec_view_of fl shb)
    by (rewrite <- Ha, <- Hb; reflexivity).
  assert (Hsh : sha = shb) by (destruct fl; cbn in Hv; injection Hv as Hv; exact Hv).
  subst shb. f_equal. apply (UIP_dec nodeview_eq_dec).
Qed.

(* a short-statement ref is identified by its node: the counts and the view proof are forced *)
Lemma shortstmtref_positional {p} {idx : Index.ProgramIndex p}
  (a b : Index.ShortStmtRef idx) : Index.sh_node a = Index.sh_node b -> a = b.
Proof.
  destruct a as [na nna nva Ha], b as [nb nnb nvb Hb]; cbn; intro E; subst nb.
  assert (Hv : Index.VStmt (Index.SSShort nna nva) = Index.VStmt (Index.SSShort nnb nvb))
    by (rewrite <- Ha, <- Hb; reflexivity).
  injection Hv as Hnn Hnv. subst nnb nvb.
  f_equal. apply (UIP_dec nodeview_eq_dec).
Qed.

(* every node's position is in range on its own file *)
Lemma nr_pos_lt {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx) :
  Index.nr_pos r < Index.occ_count (Index.nr_file r).
Proof.
  destruct (Index.occ_in_number_file r) as [f [Hin Hcount]].
  destruct (Index.number_file_positions f) as [n Hpos].
  assert (Hinp : In (Index.nr_pos r) (map fst (Index.number_file f)))
    by (apply in_map_iff; exists (Index.nr_pos r, Index.occ_at r); split; [ reflexivity | exact Hin ]).
  rewrite Hpos in Hinp. apply in_seq in Hinp.
  assert (Hlen : length (Index.number_file f) = n).
  { apply (f_equal (@length nat)) in Hpos.
    rewrite length_map, length_seq in Hpos. exact Hpos. }
  lia.
Qed.

(* the subjects enumeration covers every const spec: some entry shares its exact node *)
Lemma const_subjects_cover {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
  (cs : Index.SpecRef idx Index.ConstSpecF) :
  exists cs', In cs' (const_subjects s) /\ Index.sp_node cs' = Index.sp_node cs.
Proof.
  set (r := Index.sp_node cs).
  assert (Hfile : In (Index.nr_file r) (PI.pkg_members (PI.package_of_file s (Index.nr_file r))))
    by apply PI.pkg_members_of_file.
  assert (Hentry : exists cs', In cs' (const_specs_of_file (Index.nr_file r))
                               /\ Index.sp_node cs' = r).
  { unfold const_specs_of_file.
    assert (Hmk : Index.mk_noderef (Index.nr_file r) (Pos.of_succ_nat (Index.nr_pos r)) = Some r)
      by (rewrite <- Index.nr_key_pos; apply Index.mk_noderef_self).
    assert (Hin : exists cs', In cs' (const_ref_emit r (Index.node_view r) eq_refl)
                  /\ Index.sp_node cs' = r).
    { exact (const_ref_emit_cover r (Index.node_view r) eq_refl (Index.sp_shape cs) (Index.sp_ok cs)). }
    destruct Hin as [cs' [Hin' Hnode']].
    exists cs'. split; [| exact Hnode' ].
    apply in_flat_map. exists (Index.nr_pos r). split.
    - apply in_seq. pose proof (nr_pos_lt r). lia.
    - rewrite Hmk. exact Hin'. }
  destruct Hentry as [cs' [Hin' Hnode']].
  exists cs'. split; [| exact Hnode' ].
  unfold const_subjects. apply in_flat_map.
  exists (PI.package_of_file s (Index.nr_file r)). split; [ apply PI.packages_complete |].
  apply in_flat_map. exists (Index.nr_file r). split; [ exact Hfile | exact Hin' ].
Qed.

Record ConstSpecJudgmentRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (cs : Index.SpecRef idx Index.ConstSpecF) : Type := mk_cjr {
  cjr_ord : nat ;
  cjr_row : { c : Index.SpecRef idx Index.ConstSpecF & ConstJudgment c } ;
  cjr_at  : nth_error (bp_consts bp) cjr_ord = Some cjr_row ;
  cjr_subject : projT1 cjr_row = cs
}.
Arguments mk_cjr {p idx s d bp cs} _ _ _ _.
Arguments cjr_ord {p idx s d bp cs} _.
Arguments cjr_row {p idx s d bp cs} _.
Arguments cjr_at {p idx s d bp cs} _.
Arguments cjr_subject {p idx s d bp cs} _.

Lemma specref_of_nodes {p} {idx : Index.ProgramIndex p} {fl : Index.SpecFlavor}
  (a b : Index.SpecRef idx fl) : noderef_eqb (Index.sp_node a) (Index.sp_node b) = true -> a = b.
Proof. intro H. apply specref_positional. apply noderef_eqb_spec. exact H. Qed.

Fixpoint cjr_scan {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (cs : Index.SpecRef idx Index.ConstSpecF) (k : nat)
  (l : list { c : Index.SpecRef idx Index.ConstSpecF & ConstJudgment c }) {struct l}
  : l = skipn k (bp_consts bp) -> option (ConstSpecJudgmentRef bp cs) :=
  match l with
  | [] => fun _ => None
  | row :: rest => fun E =>
      match Bool.bool_dec (noderef_eqb (Index.sp_node (projT1 row)) (Index.sp_node cs)) true with
      | left Hb => Some (mk_cjr k row (Index.skipn_head_at (bp_consts bp) rest k row E)
                                (specref_of_nodes (projT1 row) cs Hb))
      | right _ => cjr_scan bp cs (S k) rest (Index.skipn_tail_at (bp_consts bp) rest k row E)
      end
  end.

Lemma cjr_scan_finds {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (cs : Index.SpecRef idx Index.ConstSpecF) :
  forall l k (E : l = skipn k (bp_consts bp)),
  (exists row, In row l /\ Index.sp_node (projT1 row) = Index.sp_node cs) ->
  cjr_scan bp cs k l E <> None.
Proof.
  induction l as [|row rest IH]; intros k E [row0 [Hin Hnode]]; [ destruct Hin |].
  cbn. destruct (Bool.bool_dec (noderef_eqb (Index.sp_node (projT1 row)) (Index.sp_node cs)) true)
    as [|Hne]; [ discriminate |].
  destruct Hin as [Hhead|Hin].
  - exfalso. apply Hne. subst row0. apply noderef_eqb_spec. exact Hnode.
  - apply (IH (S k) (Index.skipn_tail_at (bp_consts bp) rest k row E)).
    exists row0. split; [ exact Hin | exact Hnode ].
Qed.

(* the retained const table's subjects are exactly the canonical enumeration *)
Lemma bp_consts_subjects {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) :
  map (fun row => projT1 row) (bp_consts bp) = const_subjects s.
Proof.
  unfold bp_consts. rewrite (bp_canonical bp). cbn [phase_data snd].
  unfold const_table. rewrite map_map.
  etransitivity; [ apply map_ext; intro cs; reflexivity | apply map_id ].
Qed.

Lemma bp_consts_cover {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (cs : Index.SpecRef idx Index.ConstSpecF) :
  exists row, In row (bp_consts bp) /\ Index.sp_node (projT1 row) = Index.sp_node cs.
Proof.
  destruct (const_subjects_cover s cs) as [cs' [Hin Hnode]].
  assert (Hin' : In cs' (map (fun row => projT1 row) (bp_consts bp)))
    by (rewrite bp_consts_subjects; exact Hin).
  apply in_map_iff in Hin'. destruct Hin' as [row [Hproj Hrow]].
  exists row. split; [ exact Hrow | rewrite Hproj; exact Hnode ].
Qed.

(* the sole ordinary const-judgment lookup: total, returning the exact retained phase row *)
Definition const_spec_judgment {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (cs : Index.SpecRef idx Index.ConstSpecF) : ConstSpecJudgmentRef bp cs :=
  (match cjr_scan bp cs 0 (bp_consts bp) eq_refl as o
         return cjr_scan bp cs 0 (bp_consts bp) eq_refl = o -> ConstSpecJudgmentRef bp cs with
   | Some r => fun _ => r
   | None => fun E =>
       False_rect _ (cjr_scan_finds bp cs (bp_consts bp) 0 eq_refl (bp_consts_cover bp cs) E)
   end) eq_refl.


(* the exact retained event count at one ledger or trace ordinal; absent ordinals hold no events *)
Definition pkg_event_count {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pix : nat) : nat :=
  match nth_error (bp_ledgers bp) pix with Some l => length l | None => 0 end.
Definition trace_event_count {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix : nat) : nat :=
  match nth_error (bp_traces bp) tix with Some tr => length (trow_evs tr) | None => 0 end.

(* the exact retained package event at a valid ordinal: total, no option — the bound forces the ledger present *)
Definition pkg_row {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pix eix : nat) (H : eix < pkg_event_count bp pix) : PkgEv s :=
  (match nth_error (bp_ledgers bp) pix as o
         return eix < (match o with Some l => length l | None => 0 end) -> PkgEv s with
   | Some l => fun H' => Index.nth_lt l eix H'
   | None => fun H' => False_rect _ (Nat.nlt_0_r eix H')
   end) H.
Definition trace_row_at {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix : nat) (H : nth_error (bp_traces bp) tix <> None) : TraceRow s :=
  (match nth_error (bp_traces bp) tix as o return o <> None -> TraceRow s with
   | Some tr => fun _ => tr
   | None => fun H' => False_rect _ (H' eq_refl)
   end) H.
Definition blk_ev_row {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix eix : nat) (H : eix < trace_event_count bp tix) : BlockEv s :=
  (match nth_error (bp_traces bp) tix as o
         return eix < (match o with Some tr => length (trow_evs tr) | None => 0 end) -> BlockEv s with
   | Some tr => fun H' => Index.nth_lt (trow_evs tr) eix H'
   | None => fun H' => False_rect _ (Nat.nlt_0_r eix H')
   end) H.
Definition blk_ev_block {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix eix : nat) (H : eix < trace_event_count bp tix) : Index.BlockRef idx :=
  (match nth_error (bp_traces bp) tix as o
         return eix < (match o with Some tr => length (trow_evs tr) | None => 0 end) -> Index.BlockRef idx with
   | Some tr => fun _ => trow_block tr
   | None => fun H' => False_rect _ (Nat.nlt_0_r eix H')
   end) H.

(* one exact VALID event site: ledger/trace + in-range ordinal; invalid coordinates unrepresentable, lookups total *)
Inductive EvSite {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : Type :=
| PkgEventAt : forall (pix eix : nat), eix < pkg_event_count bp pix -> EvSite bp
| BlockEventAt : forall (tix eix : nat), eix < trace_event_count bp tix -> EvSite bp.
Arguments PkgEventAt {p idx s d bp} _ _ _.
Arguments BlockEventAt {p idx s d bp} _ _ _.

(* the exact retained additions of the event at a valid site — total *)
Definition event_adds {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) : list (Est s) :=
  match site with
  | PkgEventAt pix eix H => snd (pkg_row bp pix eix H)
  | BlockEventAt tix eix H => bev_adds (blk_ev_block bp tix eix H) (blk_ev_row bp tix eix H)
  end.

(* one exact in-range addition of an event, pinned to its retained payload; its site and index are TYPE indices *)
Record EventAdditionRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (site : EvSite bp) (ix : nat) : Type := mk_event_addition {
  ea_est : Est s ;
  ea_at  : nth_error (event_adds site) ix = Some ea_est
}.
Arguments mk_event_addition {p idx s d bp site ix} _ _.
Arguments ea_est {p idx s d bp site ix} _.
Arguments ea_at {p idx s d bp site ix} _.

(* the exact phase-owned establishment identity: its creating event and its exact in-range addition there *)
Record EstablishmentRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : Type := mk_establishment {
  es_site : EvSite bp ;
  es_ix   : nat ;
  es_add  : EventAdditionRef bp es_site es_ix
}.
Arguments mk_establishment {p idx s d bp} _ _ _.
Arguments es_site {p idx s d bp} _.
Arguments es_ix {p idx s d bp} _.
Arguments es_add {p idx s d bp} _.

Definition es_est {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (er : EstablishmentRef bp) : Est s :=
  ea_est (es_add er).

(* a total in-range witness from a successful positional lookup *)
Lemma nth_error_lt {A} (l : list A) (k : nat) (e : A) : nth_error l k = Some e -> k < length l.
Proof. intro H. apply nth_error_Some. rewrite H. discriminate. Qed.

(* the addition of an establishment sits at an intrinsically in-range index of its event *)
Definition es_lt {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (er : EstablishmentRef bp)
  : es_ix er < length (event_adds (es_site er)) :=
  nth_error_lt (event_adds (es_site er)) (es_ix er) (es_est er) (ea_at (es_add er)).

(* the exact establishment refs of one event: one per retained addition, positionally enumerated, no invalid index *)
Fixpoint refs_scan {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) (k : nat) (l : list (Est s)) {struct l}
  : l = skipn k (event_adds site) -> list (EstablishmentRef bp) :=
  match l with
  | [] => fun _ => []
  | e0 :: rest => fun E =>
      mk_establishment site k
        (mk_event_addition e0 (Index.skipn_head_at (event_adds site) rest k e0 E))
      :: refs_scan site (S k) rest (Index.skipn_tail_at (event_adds site) rest k e0 E)
  end.
Definition refs_of_event {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) : list (EstablishmentRef bp) :=
  refs_scan site 0 (event_adds site) (eq_sym (skipn_O _)).

(* the establishment refs of the package event at one ordinal — the event's additions when in range, else none *)
Definition pkg_ev_refs {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pix eix : nat) : list (EstablishmentRef bp) :=
  match lt_dec eix (pkg_event_count bp pix) with
  | left H => refs_of_event (PkgEventAt pix eix H)
  | right _ => []
  end.
Definition block_ev_refs {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix eix : nat) : list (EstablishmentRef bp) :=
  match lt_dec eix (trace_event_count bp tix) with
  | left H => refs_of_event (BlockEventAt tix eix H)
  | right _ => []
  end.

(* every ledger's / trace's events in order; every actual establishment of the phase *)
Definition ledger_refs {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pix : nat) : list (EstablishmentRef bp) :=
  flat_map (pkg_ev_refs bp pix) (seq 0 (pkg_event_count bp pix)).
Definition trace_refs {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix : nat) : list (EstablishmentRef bp) :=
  flat_map (block_ev_refs bp tix) (seq 0 (trace_event_count bp tix)).
Definition all_establishment_refs {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : list (EstablishmentRef bp) :=
  flat_map (ledger_refs bp) (seq 0 (length (bp_ledgers bp)))
  ++ flat_map (trace_refs bp) (seq 0 (length (bp_traces bp))).

(* the exact final package environment: the package's own event additions, as retained refs *)
Definition package_env_refs {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pr : PI.PackageRef s) : list (EstablishmentRef bp) :=
  ledger_refs bp (PI.pr_pos pr).

(* the exact members at one causal cut: the package seed then the additions of strictly-earlier block events *)
Definition state_refs {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix : nat) (cut : nat) : list (EstablishmentRef bp) :=
  match nth_error (bp_traces bp) tix with
  | Some tr =>
      ledger_refs bp (trow_pkg tr)
      ++ flat_map (block_ev_refs bp tix) (seq 0 cut)
  | None => []
  end.

(* the exact package ledger reference *)
Record PackageLedgerRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pr : PI.PackageRef s) : Type := mk_package_ledger {
  plr_evs : list (PkgEv s) ;
  plr_at  : nth_error (bp_ledgers bp) (PI.pr_pos pr) = Some plr_evs
}.
Arguments mk_package_ledger {p idx s d bp pr} _ _.
Arguments plr_evs {p idx s d bp pr} _.
Arguments plr_at {p idx s d bp pr} _.

Record PackageEventRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {pr : PI.PackageRef s} (l : PackageLedgerRef bp pr)
  (i : nat) : Type := mk_package_event {
  per_lt  : i < length (plr_evs l)
}.
Arguments mk_package_event {p idx s d bp pr l i} _.
Arguments per_lt {p idx s d bp pr l i} _.

Record PackageMemberRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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
Record BlockTraceRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (b : Index.NodeRef idx) : Type := mk_block_trace {
  btr_ord : nat ;
  btr_row : TraceRow s ;
  btr_at  : nth_error (bp_traces bp) btr_ord = Some btr_row ;
  btr_subject : Index.bl_node (trow_block btr_row) = b
}.
Arguments mk_block_trace {p idx s d bp b} _ _ _ _.
Arguments btr_ord {p idx s d bp b} _.
Arguments btr_row {p idx s d bp b} _.
Arguments btr_at {p idx s d bp b} _.
Arguments btr_subject {p idx s d bp b} _.

(* the exact finite causal cut: an ordinal at most the event count; an n-event trace has exactly cuts 0..n *)
Record BlockCutRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} (tr : BlockTraceRef bp b) : Type
  := mk_block_cut {
  bc_ord : nat ;
  bc_le  : bc_ord <= length (trow_evs (btr_row tr))
}.
Arguments mk_block_cut {p idx s d bp b tr} _ _.
Arguments bc_ord {p idx s d bp b tr} _.
Arguments bc_le {p idx s d bp b tr} _.

(* the exact causal state at one finite cut: its identity is the phase, trace, and cut, never its contents *)
Record BlockStateRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  (c : BlockCutRef tr) : Type := mk_block_state {
  bs_members : list (EstablishmentRef bp) ;
  bs_ok : bs_members = state_refs bp (btr_ord tr) (bc_ord c)
}.
Arguments mk_block_state {p idx s d bp b tr c} _ _.
Arguments bs_members {p idx s d bp b tr c} _.
Arguments bs_ok {p idx s d bp b tr c} _.

Definition block_state {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  (c : BlockCutRef tr) : BlockStateRef c := mk_block_state (state_refs bp (btr_ord tr) (bc_ord c)) eq_refl.

Record BlockMemberRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
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
Record BlockEventRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} (tr : BlockTraceRef bp b) : Type
  := mk_block_event {
  ber_ix : nat ;
  ber_lt : ber_ix < length (trow_evs (btr_row tr))
}.
Arguments mk_block_event {p idx s d bp b tr} _ _.
Arguments ber_ix {p idx s d bp b tr} _.
Arguments ber_lt {p idx s d bp b tr} _.

Definition ber_row {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  (e : BlockEventRef tr) : BlockEv s := Index.nth_lt (trow_evs (btr_row tr)) (ber_ix e) (ber_lt e).

(* the exact predecessor cut (the event's ordinal) and successor cut (its ordinal + 1), both in range *)
Definition ber_pre {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  (e : BlockEventRef tr) : BlockCutRef tr := mk_block_cut (ber_ix e) (Nat.lt_le_incl _ _ (ber_lt e)).
Definition ber_post {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  (e : BlockEventRef tr) : BlockCutRef tr := mk_block_cut (S (ber_ix e)) (ber_lt e).

(* the canonical occupancy group: one identity per exact phase, scope, and spelling *)
Definition scope_name_matches {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (sc : ScopeId s) (n : Names.OrdinaryIdentifier)
  (er : EstablishmentRef bp) : bool :=
  andb (scope_eqb (est_scope (es_est er)) sc) (Names.ordinary_equalb (est_name (es_est er)) n).

Definition group_refs {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (sc : ScopeId s) (n : Names.OrdinaryIdentifier)
  : list (EstablishmentRef bp) :=
  filter (scope_name_matches sc n) (all_establishment_refs bp).

Record BindingGroupRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (sc : ScopeId s) (n : Names.OrdinaryIdentifier) : Type
  := mk_binding_group {
  bg_members : list (EstablishmentRef bp) ;
  bg_ok : bg_members = group_refs bp sc n
}.
Arguments mk_binding_group {p idx s d bp sc n} _ _.
Arguments bg_members {p idx s d bp sc n} _.
Arguments bg_ok {p idx s d bp sc n} _.

Definition binding_group {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (sc : ScopeId s) (n : Names.OrdinaryIdentifier)
  : BindingGroupRef bp sc n := mk_binding_group (group_refs bp sc n) eq_refl.

(* the exact redeclaration root: the canonical group with its exact first two conflicting members *)
Record RedeclarationRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (sc : ScopeId s) (n : Names.OrdinaryIdentifier) : Type
  := mk_redeclaration {
  rr_group : BindingGroupRef bp sc n ;
  rr_two   : 2 <= length (bg_members rr_group)
}.
Arguments mk_redeclaration {p idx s d bp sc n} _ _.
Arguments rr_group {p idx s d bp sc n} _.
Arguments rr_two {p idx s d bp sc n} _.

(* the first-conflict event: the exact creating event of the group's second member *)
Definition rr_conflict_site {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {sc : ScopeId s} {n : Names.OrdinaryIdentifier}
  (rr : RedeclarationRef bp sc n) : option (EvSite bp) :=
  match bg_members (rr_group rr) with
  | _ :: m2 :: _ => Some (es_site m2)
  | _ => None
  end.

(* the visible occupancy group at one exact causal state *)
Record GroupAtStateRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
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

Definition group_at_state {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  (c : BlockCutRef tr) (n : Names.OrdinaryIdentifier) : GroupAtStateRef c n := mk_group_at_state _ eq_refl.
Lemma binder_ident_view {p} {idx : Index.ProgramIndex p} (b : Index.NodeRef idx)
  (n : Names.OrdinaryIdentifier) :
  binder_ident b = Some n -> Index.node_view b = Index.VBindingName (Syntax.BNamed n).
Proof.
  unfold binder_ident. destruct (Index.node_view b) as [| | | | |bn| | | | | | | |]; try discriminate.
  destruct bn; [| discriminate ]. intro H. injection H as <-. reflexivity.
Qed.

Lemma make_main_est_none {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (b : Index.NodeRef idx) :
  Index.is_main_view (Index.node_view b) = false -> make_main_est pr b = None.
Proof.
  intro Hf. unfold make_main_est.
  generalize (@eq_refl bool (Index.is_main_view (Index.node_view b))).
  destruct (Index.is_main_view (Index.node_view b)) at 2 3; intro e;
    [ exfalso; pose proof (eq_trans (eq_sym e) Hf) as Ht; discriminate Ht | reflexivity ].
Qed.

Lemma find_dup_sound {p} {idx : Index.ProgramIndex p} {st : Index.ShortStmtRef idx}
  (i : nat) (n : Names.OrdinaryIdentifier) :
  forall (l : list { j0 : nat & Index.ShortLhsEdge st j0 }) (j : nat)
         (w : (Index.ShortLhsEdge st j * (j < i))%type),
  find_dup i n l = Some (existT _ j w) ->
  In (existT _ j (fst w)) l
  /\ match binder_ident (Index.sl_child (fst w)) with
     | Some m => Names.ordinary_equalb m n | None => false end = true.
Proof.
  induction l as [|[k ek] rest IH]; intros j w Hf; [ discriminate Hf |].
  cbn in Hf. destruct (lt_dec k i) as [Hk|Hk].
  - destruct (match binder_ident (Index.sl_child ek) with
              | Some m => Names.ordinary_equalb m n | None => false end) eqn:Ht.
    + injection Hf as He H2. subst j.
      apply Eqdep_dec.inj_pair2_eq_dec in H2; [| exact Nat.eq_dec ]. subst w.
      split; [ left; reflexivity | exact Ht ].
    + destruct (IH j w Hf) as [Hin Hm]. split; [ right; exact Hin | exact Hm ].
  - destruct (IH j w Hf) as [Hin Hm]. split; [ right; exact Hin | exact Hm ].
Qed.

Lemma find_dup_earliest {p} {idx : Index.ProgramIndex p} {st : Index.ShortStmtRef idx}
  (i : nat) (n : Names.OrdinaryIdentifier) :
  forall (l : list { j0 : nat & Index.ShortLhsEdge st j0 }) (a m : nat),
  map (@projT1 _ _) l = seq a m ->
  forall (j : nat) (w : (Index.ShortLhsEdge st j * (j < i))%type),
  find_dup i n l = Some (existT _ j w) ->
  forall (k : nat) (ek : Index.ShortLhsEdge st k),
  In (existT _ k ek) l -> k < j -> k < i ->
  match binder_ident (Index.sl_child ek) with
  | Some m0 => Names.ordinary_equalb m0 n | None => false end = false.
Proof.
  induction l as [|[k0 e0] rest IH]; intros a m Hords j w Hf k ek Hin Hkj Hki; [ destruct Hin |].
  cbn in Hords. destruct m as [|m']; [ discriminate Hords |].
  injection Hords as Hk0 Hrest. subst k0.
  cbn in Hf. destruct (lt_dec a i) as [Ha|Ha].
  - destruct (match binder_ident (Index.sl_child e0) with
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

Lemma option_noderef_eq_dec {p} {idx : Index.ProgramIndex p} :
  forall a b : option (Index.NodeRef idx), {a = b} + {a <> b}.
Proof. decide equality. apply (dec_of_eqb noderef_eqb noderef_eqb_spec). Qed.

(* one canonical edge inhabitant per parent and ordinal *)
Lemma childat_unique {p} {idx : Index.ProgramIndex p} {par : Index.NodeRef idx} {k : nat}
  (a b : Index.ChildAt par k) : a = b.
Proof.
  destruct a as [ca Ha], b as [cb Hb].
  assert (E : ca = cb) by (rewrite Ha in Hb; injection Hb as Hb; exact Hb).
  subst cb. f_equal. apply (UIP_dec option_noderef_eq_dec).
Qed.

Lemma shortlhsedge_unique {p} {idx : Index.ProgramIndex p} {st : Index.ShortStmtRef idx} {i : nat}
  (a b : Index.ShortLhsEdge st i) : a = b.
Proof.
  destruct a as [ea la], b as [eb lb].
  assert (E : ea = eb) by apply childat_unique. subst eb.
  f_equal. apply Index.lt_unique.
Qed.

(* a self edge names the exact parent the parent relation retains *)
Lemma selfedge_parent {p} {idx : Index.ProgramIndex p} {r : Index.NodeRef idx}
  (se : Index.SelfEdge r) : Index.node_parent r = Some (Index.se_parent se).
Proof.
  pose proof (Index.ca_node_parent (Index.se_at se)) as H.
  rewrite (Index.se_child_eq se) in H. exact H.
Qed.

Lemma selfedge_ord_unique {p} {idx : Index.ProgramIndex p} {r : Index.NodeRef idx}
  (se1 se2 : Index.SelfEdge r) : Index.se_ord se1 = Index.se_ord se2.
Proof.
  pose proof (selfedge_parent se1) as H1. pose proof (selfedge_parent se2) as H2.
  rewrite H1 in H2. injection H2 as E.
  destruct se2 as [par2 o2 at2 eq2]; cbn in *.
  revert at2 eq2. rewrite <- E. intros at2 eq2.
  apply (Index.ca_ord_unique (Index.se_at se1) at2).
  rewrite (Index.se_child_eq se1), eq2. reflexivity.
Qed.

(* the first and adjacent cases are exact and disjoint *)
Lemma const_first_not_adjacent {p} {idx : Index.ProgramIndex p}
  (cs pred : Index.SpecRef idx Index.ConstSpecF)
  (cf : ConstFirst cs) (adj : ConstAdjacency cs pred) : False.
Proof.
  pose (se' := Index.mkSelfEdge (cad_parent adj) (S (cad_ord adj)) (cad_self_at adj)
                 (eq_sym (cad_self_eq adj))).
  destruct cf as [Hp|se H0].
  - pose proof (selfedge_parent se') as Hsp. rewrite Hp in Hsp. discriminate Hsp.
  - pose proof (selfedge_ord_unique se se') as He. rewrite H0 in He. cbn in He. discriminate He.
Qed.

(* the immediate predecessor is unique *)
Lemma const_pred_exact {p} {idx : Index.ProgramIndex p}
  (cs pred1 pred2 : Index.SpecRef idx Index.ConstSpecF)
  (a1 : ConstAdjacency cs pred1) (a2 : ConstAdjacency cs pred2) : pred1 = pred2.
Proof.
  pose proof (selfedge_parent (Index.mkSelfEdge (cad_parent a1) (S (cad_ord a1)) (cad_self_at a1)
                (eq_sym (cad_self_eq a1)))) as H1.
  pose proof (selfedge_parent (Index.mkSelfEdge (cad_parent a2) (S (cad_ord a2)) (cad_self_at a2)
                (eq_sym (cad_self_eq a2)))) as H2.
  pose proof (selfedge_ord_unique
                (Index.mkSelfEdge (cad_parent a1) (S (cad_ord a1)) (cad_self_at a1)
                   (eq_sym (cad_self_eq a1)))
                (Index.mkSelfEdge (cad_parent a2) (S (cad_ord a2)) (cad_self_at a2)
                   (eq_sym (cad_self_eq a2)))) as Eord.
  cbn in H1, H2, Eord. rewrite H1 in H2. injection H2 as Epar. injection Eord as Eord.
  destruct a1 as [par1 o1 pat1 peq1 sat1 seq1], a2 as [par2 o2 pat2 peq2 sat2 seq2]; cbn in *.
  subst par2 o2.
  apply specref_positional.
  rewrite peq1, peq2. f_equal. apply childat_unique.
Qed.

(* the origin projection follows the exact retained chain, one constructor at a time *)
Lemma const_origin_explicit {p} {idx : Index.ProgramIndex p}
  (cs : Index.SpecRef idx Index.ConstSpecF) (He : cs_explicit cs = true) :
  const_origin (CJExplicit cs He) = Some (existT _ cs He).
Proof. reflexivity. Qed.
Lemma const_origin_first {p} {idx : Index.ProgramIndex p}
  (cs : Index.SpecRef idx Index.ConstSpecF) (Hne : cs_explicit cs = false) (cf : ConstFirst cs) :
  const_origin (CJFirstInherited cs Hne cf) = None.
Proof. reflexivity. Qed.
Lemma const_origin_inherited {p} {idx : Index.ProgramIndex p}
  (cs pred : Index.SpecRef idx Index.ConstSpecF) (Hne : cs_explicit cs = false)
  (adj : ConstAdjacency cs pred) (jp : ConstJudgment pred) :
  const_origin (CJInherited cs pred Hne adj jp) = const_origin jp.
Proof. reflexivity. Qed.

(* the judgment constructor is forced by the exact source shape *)
Lemma const_judgment_forms {p} {idx : Index.ProgramIndex p}
  (cs : Index.SpecRef idx Index.ConstSpecF) (j : ConstJudgment cs) :
  match j with CJExplicit _ _ => cs_explicit cs = true | _ => cs_explicit cs = false end.
Proof. destruct j as [c He|c Hne cf|c pred Hne adj jp]; assumption. Qed.

(* no alternative predecessor decision can inhabit the same spec *)
Lemma const_pred_unique {p} {idx : Index.ProgramIndex p}
  (cs : Index.SpecRef idx Index.ConstSpecF) (j1 j2 : ConstJudgment cs) :
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

Lemma mk_noderef_key {p} {idx : Index.ProgramIndex p} (fr : Index.FileRef idx) (k : positive)
  (r : Index.NodeRef idx) : Index.mk_noderef fr k = Some r -> Index.nr_key r = k.
Proof.
  unfold Index.mk_noderef.
  generalize (@eq_refl bool (Collections.NodeMap.mem k (Index.cell_map fr))).
  destruct (Collections.NodeMap.mem k (Index.cell_map fr)) at 2 3; intro e;
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
Lemma files_emit_paths_nodup {p} {idx : Index.ProgramIndex p} :
  forall l : list (FilePath.T * Index.FileInfo),
  NoDup (map fst l) ->
  NoDup (map Index.fr_path
           (flat_map (fun kv => match Index.mk_fileref idx (fst kv) with
                                | Some fr => [fr] | None => [] end) l)).
Proof.
  induction l as [|kv rest IH]; intro Hk; [ constructor |].
  cbn [map] in Hk. apply NoDup_cons_iff in Hk. destruct Hk as [Hnotin Hk'].
  specialize (IH Hk'). cbn [flat_map].
  destruct (Index.mk_fileref idx (fst kv)) as [fr|] eqn:Hmk; [| cbn [app]; exact IH ].
  cbn [app map]. constructor; [| exact IH ].
  intro Hin. apply Hnotin.
  rewrite (Index.mk_fileref_path idx (fst kv) fr Hmk) in Hin.
  clear -Hin. induction rest as [|kv' rest' IH']; [ destruct Hin |].
  cbn [flat_map] in Hin. cbn [map].
  destruct (Index.mk_fileref idx (fst kv')) as [fr'|] eqn:Hmk'.
  - cbn [app map] in Hin. destruct Hin as [He|Hin];
      [ left; rewrite <- (Index.mk_fileref_path idx (fst kv') fr' Hmk'); exact He
      | right; exact (IH' Hin) ].
  - cbn [app] in Hin. right. exact (IH' Hin).
Qed.

Lemma all_files_paths_nodup {p} {idx : Index.ProgramIndex p} :
  NoDup (map Index.fr_path (Index.all_files idx)).
Proof.
  exact (files_emit_paths_nodup (Collections.FileMap.elements (Index.prog_map idx))
           (Collections.file_map_elements_keys_nodup (Index.prog_map idx))).
Qed.

Lemma all_files_nodup {p} {idx : Index.ProgramIndex p} : NoDup (Index.all_files idx).
Proof. exact (NoDup_map_inv _ _ all_files_paths_nodup). Qed.

Lemma pkg_members_nodup {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) : NoDup (PI.pkg_members pr).
Proof. unfold PI.pkg_members. apply NoDup_filter. apply all_files_nodup. Qed.

Lemma mk_packageref_pos {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (n : nat) (pr : PI.PackageRef s) : PI.mk_packageref s n = Some pr -> PI.pr_pos pr = n.
Proof.
  unfold PI.mk_packageref. destruct (lt_dec n (PI.package_count s));
    [ intro H; injection H as <-; reflexivity | discriminate ].
Qed.

Lemma packages_nodup {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) :
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
Lemma const_ref_emit_node {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx)
  (v : Index.NodeView) (Hv : Index.node_view r = v) (cs : Index.SpecRef idx Index.ConstSpecF) :
  In cs (const_ref_emit r v Hv) -> Index.sp_node cs = r.
Proof.
  destruct v; cbn; try (intros F; exact (match F with end)).
  intros [He|F]; [ rewrite <- He; reflexivity | destruct F ].
Qed.


Lemma const_ref_emit_nodup {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx)
  (v : Index.NodeView) (Hv : Index.node_view r = v) : NoDup (const_ref_emit r v Hv).
Proof. destruct v; cbn; repeat constructor; intros F; destruct F. Qed.


Lemma noderef_pos_of_key {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx) (pos : nat) :
  Index.nr_key r = Pos.of_succ_nat pos -> Index.nr_pos r = pos.
Proof.
  intro H. pose proof (Index.nr_key_pos r) as Hk. rewrite H in Hk.
  apply (f_equal Pos.to_nat) in Hk. rewrite !SuccNat2Pos.id_succ in Hk. lia.
Qed.

(* the const subjects are duplicate-free: one exact subject per source occurrence *)
Lemma const_subjects_nodup {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) :
  NoDup (const_subjects s).
Proof.
  unfold const_subjects.
  apply (flat_map_nodup _ (fun cs => PI.package_of_file s (Index.nr_file (Index.sp_node cs))));
    [ apply packages_nodup | |].
  - intros pr _.
    apply (flat_map_nodup _ (fun cs => Index.nr_file (Index.sp_node cs)));
      [ apply pkg_members_nodup | |].
    + intros fr _. unfold const_specs_of_file.
      apply (flat_map_nodup _ (fun cs => Index.nr_pos (Index.sp_node cs)));
        [ apply seq_NoDup | |].
      * intros pos _. destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|]; [| constructor ].
        apply const_ref_emit_nodup.
      * intros pos cs _ Hin.
        destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
        rewrite (const_ref_emit_node r _ _ cs Hin).
        exact (noderef_pos_of_key r pos (mk_noderef_key fr _ r Hmk)).
    + intros fr cs _ Hin.
      unfold const_specs_of_file in Hin. apply in_flat_map in Hin.
      destruct Hin as [pos [_ Hin]].
      destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
      rewrite (const_ref_emit_node r _ _ cs Hin).
      exact (Index.mk_noderef_file _ _ _ Hmk).
  - intros pr cs Hpr Hin.
    apply in_flat_map in Hin. destruct Hin as [fr [Hfr Hin]].
    unfold const_specs_of_file in Hin. apply in_flat_map in Hin.
    destruct Hin as [pos [_ Hin]].
    destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
    rewrite (const_ref_emit_node r _ _ cs Hin).
    rewrite (Index.mk_noderef_file _ _ _ Hmk).
    exact (PI.package_of_file_member s pr fr Hfr).
Qed.

(* a map distributes into a flat_map, block by block *)
Lemma map_flat_map {A B C} (f : B -> C) (g : A -> list B) (l : list A) :
  map f (flat_map g l) = flat_map (fun x => map f (g x)) l.
Proof. induction l as [|a t IH]; [ reflexivity | cbn; rewrite map_app, IH; reflexivity ]. Qed.

Lemma bp_consts_exactly_once {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (o1 o2 : nat)
  (row1 row2 : { c : Index.SpecRef idx Index.ConstSpecF & ConstJudgment c }) :
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
Lemma make_main_est_some {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (b : Index.NodeRef idx) (e : Est s) :
  make_main_est pr b = Some e ->
  (exists f, est_origin e = DOFunc f) /\ est_node e = b /\ est_scope e = PackageScope pr
  /\ est_name e = main_ident /\ est_vstart e = Index.nr_pos b.
Proof.
  unfold make_main_est.
  generalize (@eq_refl bool (Index.is_main_view (Index.node_view b))).
  destruct (Index.is_main_view (Index.node_view b)) at 2 3; intro Hm; [| discriminate ].
  intro He. injection He as <-. cbn.
  split; [ eexists; reflexivity |]. split; [ reflexivity |].
  split; [ reflexivity |]. split; reflexivity.
Qed.

Lemma make_main_est_fires {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (b : Index.NodeRef idx) :
  Index.is_main_view (Index.node_view b) = true -> make_main_est pr b <> None.
Proof.
  intro Hv. unfold make_main_est.
  generalize (@eq_refl bool (Index.is_main_view (Index.node_view b))).
  destruct (Index.is_main_view (Index.node_view b)) at 2 3; intro Hm;
    [ discriminate | exfalso; rewrite Hv in Hm; discriminate Hm ].
Qed.

(* the spec-name emission: the exact declaration-binder establishment on the exact name edge *)
Lemma spec_name_est_fields {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {fl : Index.SpecFlavor} {sp : Index.SpecRef idx fl} {i : nat}
  (sc : ScopeId s) (ne : Index.SpecNameEdge sp i) (e : Est s) :
  spec_name_est sc ne = Some e ->
  est_scope e = sc /\ est_node e = Index.sn_child ne
  /\ binder_ident (Index.sn_child ne) = Some (est_name e)
  /\ est_vstart e = vis_start (Index.sn_child ne)
  /\ (exists b, est_origin e = DOBinder b).
Proof.
  unfold spec_name_est.
  destruct (binder_ident (Index.sn_child ne)) as [n|] eqn:Hb; [| discriminate ].
  intro He. injection He as <-. cbn.
  split; [ reflexivity |]. split; [ reflexivity |].
  split; [ reflexivity |]. split; [ reflexivity |]. eexists; reflexivity.
Qed.

Lemma spec_ests_member {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {fl : Index.SpecFlavor} (sc : ScopeId s) (sp : Index.SpecRef idx fl) (e : Est s) :
  In e (spec_ests sc sp) ->
  exists i (ne : Index.SpecNameEdge sp i), spec_name_est sc ne = Some e.
Proof.
  intro Hin. unfold spec_ests in Hin. apply in_flat_map in Hin.
  destruct Hin as [x [_ Hin]].
  destruct (spec_name_est sc (projT2 x)) as [e0|] eqn:He; [| destruct Hin ].
  destruct Hin as [He0|F]; [| destruct F ].
  exists (projT1 x), (projT2 x). rewrite He, He0. reflexivity.
Qed.

(* the spec emission at an occurrence: members are its own name children's establishments *)
Lemma spec_emit_member {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (r : Index.NodeRef idx) (v : Index.NodeView) (Hv : Index.node_view r = v)
  (e : Est s) :
  In e (spec_emit sc r v Hv) ->
  est_scope e = sc
  /\ Index.node_parent (est_node e) = Some r
  /\ (exists b, est_origin e = DOBinder b)
  /\ binder_ident (est_node e) = Some (est_name e).
Proof.
  destruct v; cbv beta iota delta [spec_emit]; try (intros F; exact (match F with end)); intro Hin;
    (destruct (spec_ests_member _ _ _ Hin) as [i [ne He]];
     destruct (spec_name_est_fields _ ne _ He) as [Hsc [Hnode [Hb [_ Hor]]]];
     split; [ exact Hsc |];
     split; [ rewrite Hnode; exact (Index.sn_parent ne) |];
     split; [ exact Hor | rewrite Hnode; exact Hb ]).
Qed.

(* one declaration statement's establishments: scope exact, nodes exactly two parent hops below *)
Lemma stmt_decl_ests_member {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (t : Index.NodeRef idx) (e : Est s) :
  In e (stmt_decl_ests sc t) ->
  est_scope e = sc
  /\ (exists b, est_origin e = DOBinder b)
  /\ binder_ident (est_node e) = Some (est_name e)
  /\ (exists sp d, Index.node_parent (est_node e) = Some sp
                   /\ Index.node_parent sp = Some d /\ Index.node_parent d = Some t).
Proof.
  unfold stmt_decl_ests.
  destruct (Index.child_at_opt t 0) as [e0|] eqn:H0; [| intros F; exact (match F with end) ].
  intro Hin. unfold decl_ests in Hin. apply in_flat_map in Hin.
  destruct Hin as [[k ce] [_ Hin]].
  destruct (spec_emit_member _ _ _ _ _ Hin) as [Hsc [Hpar [Hor Hbn]]].
  split; [ exact Hsc |]. split; [ exact Hor |]. split; [ exact Hbn |].
  exists (Index.ca_child ce), (Index.ca_child e0).
  split; [ exact Hpar |].
  split; [ exact (Index.ca_node_parent ce) | exact (Index.ca_node_parent e0) ].
Qed.

Definition est_site {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (e : Est s) : option (Index.NodeRef idx) :=
  match est_origin e with
  | DOFunc _ => Some (est_node e)
  | DOShort _ => Index.node_parent (est_node e)
  | DOBinder _ =>
      match Index.node_parent (est_node e) with
      | Some sp => match Index.node_parent sp with
                   | Some d => Index.node_parent d
                   | None => None
                   end
      | None => None
      end
  end.

Lemma stmt_decl_ests_site {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (t : Index.NodeRef idx) (e : Est s) :
  In e (stmt_decl_ests sc t) -> est_site e = Some t.
Proof.
  intro Hin. destruct (stmt_decl_ests_member sc t e Hin)
    as [_ [[b Hor] [_ [sp [d [H1 [H2 H3]]]]]]].
  unfold est_site. rewrite Hor, H1, H2. exact H3.
Qed.
Lemma spec_ests_nodup {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {fl : Index.SpecFlavor} (sc : ScopeId s) (sp : Index.SpecRef idx fl) :
  NoDup (spec_ests sc sp).
Proof.
  unfold spec_ests.
  apply (flat_map_nodup_key _ (fun e => Index.nr_pos (est_node e))
           (fun x => Index.nr_pos (Index.sn_child (projT2 x)))).
  - apply (seq_map_nodup (@projT1 _ _) _ _ 0 (Index.shape_names fl (Index.sp_shape sp)));
      [ apply Index.spec_name_edges_ords |].
    intros x y _ _ Hlt. unfold Index.sn_child. apply Index.ca_pos_lt. exact Hlt.
  - intros x _. destruct (spec_name_est sc (projT2 x)); repeat constructor; intros F; destruct F.
  - intros x e _ Hin.
    destruct (spec_name_est sc (projT2 x)) as [e0|] eqn:He; [| destruct Hin ].
    destruct Hin as [He0|F]; [| destruct F ]. subst e0.
    destruct (spec_name_est_fields sc (projT2 x) e He) as [_ [Hnode _]].
    rewrite Hnode. reflexivity.
Qed.

Lemma spec_emit_nodup {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (r : Index.NodeRef idx) (v : Index.NodeView) (Hv : Index.node_view r = v) :
  NoDup (spec_emit sc r v Hv).
Proof.
  destruct v; cbv beta iota delta [spec_emit]; first [ apply spec_ests_nodup | constructor ].
Qed.

Lemma decl_ests_nodup {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (d : Index.NodeRef idx) : NoDup (decl_ests sc d).
Proof.
  unfold decl_ests.
  apply (flat_map_nodup_key _
           (fun e => match Index.node_parent (est_node e) with
                     | Some x => Index.nr_pos x | None => 0 end)
           (fun x => Index.nr_pos (Index.ca_child (projT2 x)))).
  - eapply (seq_map_nodup (@projT1 _ _)); [ apply Index.all_children_ords |].
    intros x y _ _ Hlt. apply Index.ca_pos_lt. exact Hlt.
  - intros x _. apply spec_emit_nodup.
  - intros x e _ Hin.
    destruct (spec_emit_member _ _ _ _ _ Hin) as [_ [Hpar _]].
    rewrite Hpar. reflexivity.
Qed.

Lemma stmt_decl_ests_nodup {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (t : Index.NodeRef idx) : NoDup (stmt_decl_ests sc t).
Proof.
  unfold stmt_decl_ests. destruct (Index.child_at_opt t 0); [ apply decl_ests_nodup | constructor ].
Qed.
Lemma shortstmtref_eq_dec {p} {idx : Index.ProgramIndex p} :
  forall a b : Index.ShortStmtRef idx, {a = b} + {a <> b}.
Proof.
  intros a b.
  destruct (Bool.bool_dec (noderef_eqb (Index.sh_node a) (Index.sh_node b)) true) as [H|H].
  - left. apply shortstmtref_positional. apply noderef_eqb_spec. exact H.
  - right. intro E. apply H. subst b. apply noderef_eqb_spec. reflexivity.
Qed.

Lemma spec_emit_eval {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {fl : Index.SpecFlavor} (sc : ScopeId s) (r : Index.NodeRef idx) (v : Index.NodeView)
  (Hv : Index.node_view r = v) (sh : Index.SpecShape fl) :
  v = Index.spec_view_of fl sh ->
  exists Hv0 : Index.node_view r = Index.spec_view_of fl sh,
    spec_emit sc r v Hv = spec_ests sc (Index.mkSpecRef (fl := fl) r sh Hv0).
Proof.
  intro E. revert Hv. subst v. intro Hv. exists Hv.
  destruct fl; reflexivity.
Qed.

Lemma spec_ests_cover {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {fl : Index.SpecFlavor} (sc : ScopeId s) (sp : Index.SpecRef idx fl) (i : nat)
  (ne : Index.SpecNameEdge sp i) (n : Names.OrdinaryIdentifier) :
  binder_ident (Index.sn_child ne) = Some n ->
  exists e, In e (spec_ests sc sp) /\ est_node e = Index.sn_child ne.
Proof.
  intro Hb.
  assert (Hin : In i (map (@projT1 _ _) (Index.spec_name_edges sp)))
    by (rewrite (Index.spec_name_edges_ords sp); apply in_seq_intro; exact (Index.sn_lt ne)).
  apply in_map_iff in Hin. destruct Hin as [x [Hx Hrow]].
  destruct x as [i' ne']. cbn [projT1] in Hx. subst i'.
  assert (Hc : Index.sn_child ne' = Index.sn_child ne)
    by (exact (Index.ca_det (Index.sn_at ne') (Index.sn_at ne))).
  assert (Hb' : binder_ident (Index.sn_child ne') = Some n) by (rewrite Hc; exact Hb).
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
Lemma decl_ests_cover {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (d : Index.NodeRef idx) {fl : Index.SpecFlavor}
  (spref : Index.SpecRef idx fl) (i : nat) (ne : Index.SpecNameEdge spref i)
  (n : Names.OrdinaryIdentifier) :
  Index.node_parent (Index.sp_node spref) = Some d ->
  binder_ident (Index.sn_child ne) = Some n ->
  exists e, In e (decl_ests sc d) /\ est_node e = Index.sn_child ne.
Proof.
  intros Hp Hb.
  destruct (Index.all_children_of_parent (Index.sp_node spref) d Hp) as [k [ed [Hrow Hc]]].
  destruct (spec_emit_eval (fl := fl) sc (Index.ca_child ed) (Index.node_view (Index.ca_child ed))
              eq_refl (Index.sp_shape spref))
    as [Hv0 Hemit]; [ rewrite Hc; exact (Index.sp_ok spref) |].
  assert (Hsp : Index.mkSpecRef (fl := fl) (Index.ca_child ed) (Index.sp_shape spref) Hv0 = spref)
    by (apply specref_positional; exact Hc).
  destruct (spec_ests_cover sc spref i ne n Hb) as [e0 [Hin Hnode]].
  exists e0. split; [| exact Hnode ].
  unfold decl_ests. apply in_flat_map. exists (existT _ k ed). split; [ exact Hrow |].
  cbn [projT1 projT2]. rewrite Hemit, Hsp. exact Hin.
Qed.

Lemma stmt_decl_ests_cover {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (t : Index.NodeRef idx) (et : Index.ChildAt t 0)
  {fl : Index.SpecFlavor} (spref : Index.SpecRef idx fl) (i : nat)
  (ne : Index.SpecNameEdge spref i) (n : Names.OrdinaryIdentifier) :
  Index.node_parent (Index.sp_node spref) = Some (Index.ca_child et) ->
  binder_ident (Index.sn_child ne) = Some n ->
  exists e, In e (stmt_decl_ests sc t) /\ est_node e = Index.sn_child ne.
Proof.
  intros Hp Hb. unfold stmt_decl_ests.
  destruct (Index.child_at_opt t 0) as [e0|] eqn:H0;
    [| exact (match Index.child_at_opt_some _ _ et H0 with end) ].
  assert (Hde : Index.ca_child e0 = Index.ca_child et) by (exact (Index.ca_det e0 et)).
  rewrite Hde.
  exact (decl_ests_cover sc (Index.ca_child et) spref i ne n Hp Hb).
Qed.

(* a spec-name edge exists at every spec-name-roled child ordinal: the role decodes the bound *)
Lemma specname_ordinal_lt {p} {idx : Index.ProgramIndex p} {fl : Index.SpecFlavor}
  (sp : Index.SpecRef idx fl) (i : nat) (eb : Index.ChildAt (Index.sp_node sp) i) :
  Index.node_role (Index.ca_child eb) = Index.RSpecName fl ->
  i < Index.shape_names fl (Index.sp_shape sp).
Proof.
  intro Hr. pose proof (Index.ca_role eb) as Hrole.
  rewrite Hr, (Index.sp_ok sp) in Hrole.
  pose proof (Index.child_at_count_lt eb) as Hcount.
  destruct fl.
  - destruct (Index.sp_shape sp) as [ht nn nv|nn] eqn:Hsh;
      cbn [Index.spec_view_of Index.layout_role Index.shape_names] in Hrole |- *.
    + destruct (i <? nn) eqn:Hlt; [ apply Nat.ltb_lt; exact Hlt |].
      destruct (andb ht (i =? nn)); discriminate Hrole.
    + assert (Hlc : Index.layout_count (Index.node_view (Index.sp_node sp)) = Some nn)
        by (rewrite (Index.sp_ok sp), Hsh; reflexivity).
      exact (Hcount nn Hlc).
  - destruct (Index.sp_shape sp) as [nn|ht nn nv] eqn:Hsh;
      cbn [Index.spec_view_of Index.layout_role Index.shape_names] in Hrole |- *.
    + destruct (i <? nn) eqn:Hlt; [ apply Nat.ltb_lt; exact Hlt | discriminate Hrole ].
    + destruct (i <? nn) eqn:Hlt; [ apply Nat.ltb_lt; exact Hlt |].
      destruct (andb ht (i =? nn)); discriminate Hrole.
  - destruct (Index.sp_shape sp) eqn:Hsh;
      cbn [Index.spec_view_of Index.layout_role Index.shape_names] in Hrole |- *;
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
Lemma packages_nth {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
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
Lemma refs_scan_site {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) (er : EstablishmentRef bp) :
  forall l k (E : l = skipn k (event_adds site)),
  In er (refs_scan site k l E) -> es_site er = site.
Proof.
  induction l as [|e0 rest IH]; intros k E Hin; [ destruct Hin |].
  destruct Hin as [<-|Hin]; [ reflexivity | exact (IH _ _ Hin) ].
Qed.

Lemma refs_of_event_site {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) (er : EstablishmentRef bp) :
  In er (refs_of_event site) -> es_site er = site.
Proof. apply refs_scan_site. Qed.

(* the emitted refs project the event's exact additions, in order *)
Lemma refs_scan_ests {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) :
  forall l k (E : l = skipn k (event_adds site)),
  map es_est (refs_scan site k l E) = l.
Proof.
  induction l as [|e0 rest IH]; intros k E; [ reflexivity |].
  cbn [refs_scan map]. f_equal. exact (IH (S k) _).
Qed.

Lemma refs_of_event_adds {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) :
  map es_est (refs_of_event site) = event_adds site.
Proof. apply refs_scan_ests. Qed.

(* every ref an event emits projects an exact retained addition of that event *)
Lemma refs_of_event_est_in {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) (er : EstablishmentRef bp) :
  In er (refs_of_event site) -> In (es_est er) (event_adds site).
Proof.
  intro Hin. rewrite <- refs_of_event_adds. apply in_map. exact Hin.
Qed.

Lemma refs_of_event_empty {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) :
  event_adds site = [] -> refs_of_event site = [].
Proof.
  intro H. pose proof (refs_of_event_adds site) as Hm. rewrite H in Hm.
  destruct (refs_of_event site); [ reflexivity | discriminate Hm ].
Qed.

(* the exact additions of one block event: total, no option — the eix-th event's ordered additions *)
Lemma blk_ev_row_eq {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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
  assert (Heq : Some (Index.nth_lt (trow_evs tr) eix H) = Some ev)
    by (rewrite <- (Index.nth_lt_nth_error (trow_evs tr) eix H); exact Hev).
  injection Heq as Heq. exact Heq.
Qed.
Lemma blk_ev_block_eq {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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
Lemma event_adds_block {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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
Lemma pkg_row_eq {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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
  assert (Heq : Some (Index.nth_lt l eix H) = Some row)
    by (rewrite <- (Index.nth_lt_nth_error l eix H); exact Hrow).
  injection Heq as Heq. exact Heq.
Qed.
Lemma event_adds_pkg {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pix eix : nat) (H : eix < pkg_event_count bp pix)
  (l : list (PkgEv s)) (row : PkgEv s) :
  nth_error (bp_ledgers bp) pix = Some l -> nth_error l eix = Some row ->
  event_adds (PkgEventAt pix eix H) = snd row.
Proof.
  intros Hl Hrow. cbn [event_adds]. rewrite (pkg_row_eq bp pix eix H l row Hl Hrow). reflexivity.
Qed.

Lemma spec_ests_scope {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {fl : Index.SpecFlavor} (sc : ScopeId s) (sp : Index.SpecRef idx fl) (e : Est s) :
  In e (spec_ests sc sp) -> est_scope e = sc.
Proof.
  unfold spec_ests. intro Hin. apply in_flat_map in Hin. destruct Hin as [x [_ Hin]].
  destruct (spec_name_est sc (projT2 x)) as [e0|] eqn:He0; [| destruct Hin ].
  destruct Hin as [<-|F]; [| destruct F ].
  exact (proj1 (spec_name_est_fields sc (projT2 x) e0 He0)).
Qed.

Lemma spec_emit_scope {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (r : Index.NodeRef idx) (v : Index.NodeView) (Hv : Index.node_view r = v)
  (e : Est s) :
  In e (spec_emit sc r v Hv) -> est_scope e = sc.
Proof.
  destruct v; cbv beta iota delta [spec_emit];
    try (intro F; destruct F); apply spec_ests_scope.
Qed.

Lemma decl_ests_scope {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (d : Index.NodeRef idx) (e : Est s) :
  In e (decl_ests sc d) -> est_scope e = sc.
Proof.
  unfold decl_ests. intro Hin. apply in_flat_map in Hin. destruct Hin as [x [_ Hin]].
  exact (spec_emit_scope sc _ _ eq_refl e Hin).
Qed.

Lemma stmt_decl_ests_scope {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (sc : ScopeId s) (t : Index.NodeRef idx) (e : Est s) :
  In e (stmt_decl_ests sc t) -> est_scope e = sc.
Proof.
  unfold stmt_decl_ests. destruct (Index.child_at_opt t 0) as [ce|];
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
  rewrite (Hpt k x (Index.skipn_head_at l t' k x Ht)).
  rewrite (IH (S k) (Index.skipn_tail_at l t' k x Ht)). reflexivity.
Qed.

Lemma firstn_nth_error {A} (l : list A) :
  forall n k x, nth_error (firstn n l) k = Some x -> nth_error l k = Some x.
Proof.
  induction l as [|a t IH]; intros [|n'] [|k'] x H; try discriminate H;
    [ exact H | exact (IH n' k' x H) ].
Qed.

(* the retained graph is exactly the one canonical construction: the phase pin names the builder *)
Lemma bp_ledgers_form {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : bp_ledgers bp = map (ledger_of s) (PI.packages s).
Proof. unfold bp_ledgers. rewrite (bp_canonical bp). reflexivity. Qed.

Lemma bp_traces_form {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : bp_traces bp = flat_map (traces_of_pkg s) (PI.packages s).
Proof. unfold bp_traces. rewrite (bp_canonical bp). reflexivity. Qed.

Lemma bp_consts_form {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : bp_consts bp = const_table s.
Proof. unfold bp_consts. rewrite (bp_canonical bp). reflexivity. Qed.

(* exactly one ledger per exact package, at the package's exact position *)
Lemma bp_ledgers_at {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pr : PI.PackageRef s) :
  nth_error (bp_ledgers bp) (PI.pr_pos pr) = Some (ledger_of s pr).
Proof.
  rewrite bp_ledgers_form. exact (map_nth_error _ _ _ (packages_nth s pr)).
Qed.

Lemma bp_ledgers_len {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : length (bp_ledgers bp) = length (PI.packages s).
Proof. rewrite bp_ledgers_form. apply length_map. Qed.

Lemma bp_ledgers_row {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pix : nat) (l : list (PkgEv s)) :
  nth_error (bp_ledgers bp) pix = Some l ->
  exists pr, nth_error (PI.packages s) pix = Some pr /\ l = ledger_of s pr.
Proof. rewrite bp_ledgers_form. apply map_nth_error_inv. Qed.

(* every retained ledger row is one exact canonical package event, and every such event is retained *)
Lemma ledger_row {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (row : PkgEv s) :
  In row (ledger_of s pr) ->
  exists r, In (Index.nr_file r) (PI.pkg_members pr) /\ pkg_event_at s pr r = Some row.
Proof.
  unfold ledger_of. intro Hin.
  apply in_flat_map in Hin. destruct Hin as [fr [Hfr Hin]].
  apply in_flat_map in Hin. destruct Hin as [pos [_ Hin]].
  destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
  destruct (pkg_event_at s pr r) as [row0|] eqn:Hev; [| destruct Hin ].
  destruct Hin as [<-|F]; [| destruct F ].
  exists r. rewrite (Index.mk_noderef_file fr _ r Hmk). split; [ exact Hfr | exact Hev ].
Qed.

Lemma ledger_covers {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.NodeRef idx) (row : PkgEv s) :
  In (Index.nr_file r) (PI.pkg_members pr) ->
  pkg_event_at s pr r = Some row ->
  In row (ledger_of s pr).
Proof.
  intros Hfr Hev. unfold ledger_of.
  apply in_flat_map. exists (Index.nr_file r). split; [ exact Hfr |].
  apply in_flat_map. exists (Index.nr_pos r).
  split; [ apply in_seq; pose proof (nr_pos_lt r); lia |].
  rewrite <- Index.nr_key_pos, Index.mk_noderef_self. cbv beta iota.
  rewrite Hev. left; reflexivity.
Qed.

(* a canonical package event carries its exact top occurrence as its site *)
Lemma pkg_event_at_fst {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.NodeRef idx) (row : PkgEv s) :
  pkg_event_at s pr r = Some row -> fst row = r.
Proof.
  unfold pkg_event_at. destruct (Index.node_view r) as [| | | | | | | | | | | |ts|]; try discriminate.
  destruct ts.
  - intro H. injection H as <-. reflexivity.
  - destruct (make_main_est pr r); intro H; [ injection H as <-; reflexivity | discriminate H ].
Qed.

(* every addition of a canonical package event establishes at exactly that package's scope *)
Lemma pkg_event_at_scope {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.NodeRef idx) (row : PkgEv s) (e : Est s) :
  pkg_event_at s pr r = Some row -> In e (snd row) ->
  est_scope e = PackageScope pr.
Proof.
  unfold pkg_event_at. destruct (Index.node_view r) as [| | | | | | | | | | | |ts|]; try discriminate.
  destruct ts.
  - intro H. injection H as <-. cbn. apply stmt_decl_ests_scope.
  - destruct (make_main_est pr r) as [e0|] eqn:Hm; intro H; [| discriminate H ].
    injection H as <-. cbn. intros [<-|F]; [| destruct F ].
    exact (proj1 (proj2 (proj2 (make_main_est_some pr r e0 Hm)))).
Qed.

(* every addition of a canonical package event sites at exactly its top occurrence *)
Lemma pkg_event_at_site {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.NodeRef idx) (row : PkgEv s) (e : Est s) :
  pkg_event_at s pr r = Some row -> In e (snd row) ->
  est_site e = Some r.
Proof.
  unfold pkg_event_at. destruct (Index.node_view r) as [| | | | | | | | | | | |ts|]; try discriminate.
  destruct ts.
  - intro H. injection H as <-. cbn. apply stmt_decl_ests_site.
  - destruct (make_main_est pr r) as [e0|] eqn:Hm; intro H; [| discriminate H ].
    injection H as <-. cbn. intros [<-|F]; [| destruct F ].
    destruct (make_main_est_some pr r e0 Hm) as [[f Hf] [Hnode _]].
    unfold est_site. rewrite Hf, Hnode. reflexivity.
Qed.

(* the refs of a package event establish at exactly that package's scope *)
Lemma ledger_add_scope {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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
  set (row := Index.nth_lt (ledger_of s pr) eix Heix).
  assert (Hrow : nth_error (ledger_of s pr) eix = Some row) by (apply Index.nth_lt_nth_error).
  rewrite (event_adds_pkg bp pix eix H (ledger_of s pr) row Hl Hrow) in Hest.
  destruct (ledger_row pr row (nth_error_In _ _ Hrow)) as [r [_ Hev]].
  exact (pkg_event_at_scope pr r row (es_est er) Hev Hest).
Qed.

(* every retained trace row is the canonical fold of its exact block over its package's final environment *)
Lemma bp_traces_row {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tr : TraceRow s) :
  In tr (bp_traces bp) ->
  exists (pr : PI.PackageRef s) (r : Index.NodeRef idx)
         (Hb : Index.is_block_view (Index.node_view r) = true),
    In pr (PI.packages s) /\ In (Index.nr_file r) (PI.pkg_members pr)
    /\ tr = (Index.mkBlockRef r Hb, PI.pr_pos pr,
             block_fold s (Index.mkBlockRef r Hb) (Index.all_children r)
               (pkg_env_of s pr)).
Proof.
  rewrite bp_traces_form. intro Hin.
  apply in_flat_map in Hin. destruct Hin as [pr [Hpr Hin]].
  unfold traces_of_pkg in Hin. cbv zeta in Hin.
  apply in_flat_map in Hin. destruct Hin as [fr [Hfr Hin]].
  apply in_flat_map in Hin. destruct Hin as [pos [_ Hin]].
  destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
  destruct (Bool.bool_dec (Index.is_block_view (Index.node_view r)) true) as [Hb|Hneq].
  - rewrite (bool_convoy_true _ _ _ Hb) in Hin.
    destruct Hin as [He|F]; [| destruct F ].
    exists pr, r, Hb.
    rewrite <- (Index.mk_noderef_file fr _ r Hmk) in Hfr.
    split; [ exact Hpr |]. split; [ exact Hfr |]. exact (eq_sym He).
  - rewrite (bool_convoy_false _ _ _ (Bool.not_true_is_false _ Hneq)) in Hin. destruct Hin.
Qed.

(* the trace of every represented block exists in the phase *)
Lemma traces_cover {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (r : Index.NodeRef idx) (Hb : Index.is_block_view (Index.node_view r) = true) :
  In (Index.mkBlockRef r Hb, PI.pr_pos (PI.package_of_file s (Index.nr_file r)),
      block_fold s (Index.mkBlockRef r Hb) (Index.all_children r)
        (pkg_env_of s (PI.package_of_file s (Index.nr_file r))))
     (bp_traces bp).
Proof.
  rewrite bp_traces_form.
  set (pr := PI.package_of_file s (Index.nr_file r)).
  apply in_flat_map. exists pr. split; [ apply PI.packages_complete |].
  unfold traces_of_pkg. cbv zeta.
  apply in_flat_map. exists (Index.nr_file r). split; [ apply PI.pkg_members_of_file |].
  apply in_flat_map. exists (Index.nr_pos r).
  split; [ apply in_seq; pose proof (nr_pos_lt r); lia |].
  rewrite <- Index.nr_key_pos, Index.mk_noderef_self. cbv beta iota.
  rewrite (bool_convoy_true _ _ _ Hb). left; reflexivity.
Qed.

(* one event per direct statement: the canonical fold maps the block's children one to one *)
Lemma block_fold_length {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) :
  forall (l : list { o : nat & Index.ChildAt (Index.bl_node br) o }) (env : list (Est s)),
  length (block_fold s br l env) = length l.
Proof.
  induction l as [|x t IH]; intro env; [ reflexivity |].
  cbn. rewrite IH. reflexivity.
Qed.

Lemma block_fold_nth {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) :
  forall (l : list { o : nat & Index.ChildAt (Index.bl_node br) o }) (env : list (Est s)) (j : nat)
         (x : { o : nat & Index.ChildAt (Index.bl_node br) o }),
  nth_error l j = Some x ->
  exists env',
    nth_error (block_fold s br l env) j
    = Some (block_event s br env' (Index.ca_child (projT2 x))
              (Index.node_view (Index.ca_child (projT2 x))) eq_refl).
Proof.
  induction l as [|x0 t IH]; intros env j x Hj; [ destruct j; discriminate Hj |].
  destruct j as [|j'].
  - injection Hj as <-. eexists. reflexivity.
  - cbn in Hj. cbn. exact (IH _ j' x Hj).
Qed.

(* the exact inverse: the j-th event is the canonical event of the j-th child over the exact threaded environment *)
Lemma block_fold_nth_env {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) :
  forall (l : list { o : nat & Index.ChildAt (Index.bl_node br) o }) (env : list (Est s)) (j : nat)
         (ev : BlockEv s),
  nth_error (block_fold s br l env) j = Some ev ->
  exists x,
    nth_error l j = Some x
    /\ ev = block_event s br
              (env ++ flat_map (bev_adds br) (firstn j (block_fold s br l env)))
              (Index.ca_child (projT2 x)) (Index.node_view (Index.ca_child (projT2 x))) eq_refl.
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
Lemma block_event_node {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) (env : list (Est s)) (c : Index.NodeRef idx)
  (v : Index.NodeView) (Hv : Index.node_view c = v) :
  bev_node (block_event s br env c v Hv) = c.
Proof.
  destruct v; cbn; try reflexivity.
  match goal with sh0 : Index.StmtShape |- _ => destruct sh0; reflexivity end.
Qed.

(* the canonical short event of a short statement, evaluated at its exact known view *)
Lemma block_event_short_eval {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) (env : list (Est s)) (c : Index.NodeRef idx)
  (v : Index.NodeView) (Hv : Index.node_view c = v) (nn nv : nat) :
  v = Index.VStmt (Index.SSShort nn nv) ->
  exists Hv0 : Index.node_view c = Index.VStmt (Index.SSShort nn nv),
    block_event s br env c v Hv
    = BEvShort (Index.mkShortStmtRef c nn nv Hv0)
        (short_decide_rows env (Index.mkShortStmtRef c nn nv Hv0)).
Proof. intro E. revert Hv. subst v. intro Hv. exists Hv. reflexivity. Qed.

(* every addition of a canonical block event establishes at its exact block scope *)
Lemma block_event_adds_scope {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br br' : Index.BlockRef idx) (env : list (Est s)) (c : Index.NodeRef idx)
  (v : Index.NodeView) (Hv : Index.node_view c = v) (e : Est s) :
  In e (bev_adds br' (block_event s br env c v Hv)) ->
  est_scope e = BlockScope br \/ est_scope e = BlockScope br'.
Proof.
  destruct v; cbn; try (intro F; destruct F).
  match goal with sh0 : Index.StmtShape |- _ => destruct sh0 as [| |nn nv] end; cbn.
  - intro F; destruct F.
  - intro Hin. left.
    exact (decl_rows_adds_scope (BlockScope br) c _ e Hin).
  - intro Hin. right.
    exact (short_rows_adds_scope br' _ _ e Hin).
Qed.

(* the refs of a block event establish at exactly that trace's block scope *)
Lemma trace_add_scope {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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
  remember (Index.nth_lt (trow_evs tr) eix Heix) as ev eqn:Hevdef.
  assert (Hev : nth_error (trow_evs tr) eix = Some ev) by (rewrite Hevdef; apply Index.nth_lt_nth_error).
  rewrite (event_adds_block bp tix eix Hlt tr ev Htr Hev) in Hest.
  destruct (bp_traces_row bp tr (nth_error_In _ _ Htr)) as [pr [r [Hb [_ [_ Hform]]]]].
  assert (Hevs : trow_evs tr = block_fold s (Index.mkBlockRef r Hb) (Index.all_children r)
                                 (pkg_env_of s pr)) by (rewrite Hform; reflexivity).
  assert (Hblk : trow_block tr = Index.mkBlockRef r Hb) by (rewrite Hform; reflexivity).
  rewrite Hevs in Hev.
  destruct (block_fold_nth_env _ _ _ _ _ Hev) as [x [_ He]].
  rewrite He in Hest. rewrite Hblk in Hest.
  destruct (block_event_adds_scope _ _ _ _ _ _ _ Hest) as [Hsc|Hsc]; rewrite Hblk; exact Hsc.
Qed.

(* the final package environment is exactly the ledger's additions, with retained provenance *)
Lemma package_env_ests {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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
Lemma state_refs_zero {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix : nat) (tr : TraceRow s) :
  nth_error (bp_traces bp) tix = Some tr ->
  state_refs bp tix 0 = ledger_refs bp (trow_pkg tr).
Proof.
  intro H. unfold state_refs. rewrite H. cbn [seq flat_map]. apply app_nil_r.
Qed.

Lemma state_refs_succ {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix i : nat) (tr : TraceRow s) :
  nth_error (bp_traces bp) tix = Some tr ->
  state_refs bp tix (S i) = state_refs bp tix i ++ block_ev_refs bp tix i.
Proof.
  intro H. unfold state_refs. rewrite H.
  rewrite seq_S. cbn [Nat.add]. rewrite flat_map_app.
  cbn [flat_map]. rewrite app_nil_r. apply app_assoc.
Qed.

(* cuts beyond the statement count add nothing: the trace has exactly statement_count + 1 states *)
Lemma state_refs_saturates {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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
Lemma state_member_site {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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

Lemma state_covers {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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
Lemma state_ests {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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
Lemma state_refs_expr_step {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (tix i : nat) (tr : TraceRow s) (r : Index.NodeRef idx) :
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
Lemma pkg_event_at_nodup {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.NodeRef idx) (row : PkgEv s) :
  pkg_event_at s pr r = Some row -> NoDup (snd row).
Proof.
  unfold pkg_event_at. destruct (Index.node_view r) as [| | | | | | | | | | | |ts|]; try discriminate.
  destruct ts.
  - intro H. injection H as <-. apply stmt_decl_ests_nodup.
  - destruct (make_main_est pr r) as [e0|]; intro H; [| discriminate H ].
    injection H as <-. cbn. repeat constructor. intro F; destruct F.
Qed.

(* each package ledger names each top occurrence at most once *)
Lemma ledger_nodes_nodup {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) : NoDup (map fst (ledger_of s pr)).
Proof.
  unfold ledger_of. rewrite map_flat_map.
  apply (flat_map_nodup_key _ Index.nr_file (fun fr => fr));
    [ rewrite map_id; apply pkg_members_nodup | |].
  - intros fr _. rewrite map_flat_map.
    apply (flat_map_nodup_key _ Index.nr_pos (fun pos => pos));
      [ rewrite map_id; apply seq_NoDup | |].
    + intros pos _.
      destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| constructor ].
      destruct (pkg_event_at s pr r) as [row|]; cbn; repeat constructor. intro F; destruct F.
    + intros pos rn _ Hin.
      destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
      destruct (pkg_event_at s pr r) as [row|] eqn:Hev; [| destruct Hin ].
      destruct Hin as [<-|F]; [| destruct F ].
      rewrite (pkg_event_at_fst pr r row Hev).
      exact (noderef_pos_of_key r pos (mk_noderef_key fr _ r Hmk)).
  - intros fr rn _ Hin. rewrite map_flat_map in Hin.
    apply in_flat_map in Hin. destruct Hin as [pos [_ Hin]].
    destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
    destruct (pkg_event_at s pr r) as [row|] eqn:Hev; [| destruct Hin ].
    destruct Hin as [<-|F]; [| destruct F ].
    rewrite (pkg_event_at_fst pr r row Hev).
    exact (Index.mk_noderef_file fr _ r Hmk).
Qed.

(* the final package environment is duplicate-free: one establishment per exact source site *)
Lemma pkg_env_nodup {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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
Lemma traces_nodes_nodup {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) :
  NoDup (map (fun tr => Index.bl_node (trow_block tr)) (bp_traces bp)).
Proof.
  rewrite bp_traces_form, map_flat_map.
  apply (flat_map_nodup_key _ (fun r => PI.package_of_file s (Index.nr_file r)) (fun pr => pr));
    [ rewrite map_id; apply packages_nodup | |].
  - intros pr _. unfold traces_of_pkg. cbv zeta. rewrite map_flat_map.
    apply (flat_map_nodup_key _ Index.nr_file (fun fr => fr));
      [ rewrite map_id; apply pkg_members_nodup | |].
    + intros fr _. rewrite map_flat_map.
      apply (flat_map_nodup_key _ Index.nr_pos (fun pos => pos));
        [ rewrite map_id; apply seq_NoDup | |].
      * intros pos _.
        destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| constructor ].
        destruct (Bool.bool_dec (Index.is_block_view (Index.node_view r)) true) as [Hb|Hneq];
          [ rewrite (bool_convoy_true _ _ _ Hb)
          | rewrite (bool_convoy_false _ _ _ (Bool.not_true_is_false _ Hneq)) ];
          cbn; repeat constructor. intro F; destruct F.
      * intros pos rn _ Hin.
        destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
        destruct (Bool.bool_dec (Index.is_block_view (Index.node_view r)) true) as [Hb|Hneq];
          [ rewrite (bool_convoy_true _ _ _ Hb) in Hin
          | rewrite (bool_convoy_false _ _ _ (Bool.not_true_is_false _ Hneq)) in Hin; destruct Hin ].
        destruct Hin as [<-|F]; [| destruct F ].
        exact (noderef_pos_of_key r pos (mk_noderef_key fr _ r Hmk)).
    + intros fr rn _ Hin. rewrite map_flat_map in Hin.
      apply in_flat_map in Hin. destruct Hin as [pos [_ Hin]].
      destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
      destruct (Bool.bool_dec (Index.is_block_view (Index.node_view r)) true) as [Hb|Hneq];
        [ rewrite (bool_convoy_true _ _ _ Hb) in Hin
        | rewrite (bool_convoy_false _ _ _ (Bool.not_true_is_false _ Hneq)) in Hin; destruct Hin ].
      destruct Hin as [<-|F]; [| destruct F ].
      exact (Index.mk_noderef_file fr _ r Hmk).
  - intros pr rn Hpr Hin.
    apply in_map_iff in Hin. destruct Hin as [tr [Hnode Hin]].
    unfold traces_of_pkg in Hin. cbv zeta in Hin.
    apply in_flat_map in Hin. destruct Hin as [fr [Hfr Hin]].
    apply in_flat_map in Hin. destruct Hin as [pos [_ Hin]].
    destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
    destruct (Bool.bool_dec (Index.is_block_view (Index.node_view r)) true) as [Hb|Hneq];
      [ rewrite (bool_convoy_true _ _ _ Hb) in Hin
      | rewrite (bool_convoy_false _ _ _ (Bool.not_true_is_false _ Hneq)) in Hin; destruct Hin ].
    destruct Hin as [<-|F]; [| destruct F ].
    cbn in Hnode. subst rn.
    rewrite (Index.mk_noderef_file fr _ r Hmk).
    exact (PI.package_of_file_member s pr fr Hfr).
Qed.

Lemma trace_at_unique {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (i j : nat) (tri trj : TraceRow s) :
  nth_error (bp_traces bp) i = Some tri -> nth_error (bp_traces bp) j = Some trj ->
  Index.bl_node (trow_block tri) = Index.bl_node (trow_block trj) -> i = j.
Proof.
  intros Hi Hj He.
  exact (nodup_map_nth _ _ i j tri trj (traces_nodes_nodup bp) Hi Hj He).
Qed.

(* one located trace: the exact ordinal, row, and retention pin of the first row satisfying a test *)
Record TraceHit {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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

Fixpoint trace_scan {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pred : TraceRow s -> bool) (k : nat) (l : list (TraceRow s)) {struct l}
  : l = skipn k (bp_traces bp) -> option (TraceHit bp pred) :=
  match l with
  | [] => fun _ => None
  | tr :: rest => fun E =>
      match Bool.bool_dec (pred tr) true with
      | left Hp => Some (mk_trace_hit k tr (Index.skipn_head_at (bp_traces bp) rest k tr E) Hp)
      | right _ => trace_scan bp pred (S k) rest (Index.skipn_tail_at (bp_traces bp) rest k tr E)
      end
  end.

Lemma trace_scan_finds {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pred : TraceRow s -> bool) :
  forall l k (E : l = skipn k (bp_traces bp)),
  (exists tr, In tr l /\ pred tr = true) ->
  trace_scan bp pred k l E <> None.
Proof.
  induction l as [|tr rest IH]; intros k E [tr0 [Hin Hp]]; [ destruct Hin |].
  cbn. destruct (Bool.bool_dec (pred tr) true) as [|Hne]; [ discriminate |].
  destruct Hin as [<-|Hin]; [ exact (False_ind _ (Hne Hp)) |].
  apply (IH (S k) (Index.skipn_tail_at (bp_traces bp) rest k tr E)).
  exists tr0. split; [ exact Hin | exact Hp ].
Qed.

(* the total exact block lookup: every represented block has exactly one retained trace *)
Definition block_trace {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (br : Index.BlockRef idx) : TraceHit bp
    (fun tr => noderef_eqb (Index.bl_node (trow_block tr)) (Index.bl_node br)) :=
  (match trace_scan bp _ 0 (bp_traces bp) (eq_sym (skipn_O _)) as o
         return trace_scan bp _ 0 (bp_traces bp) (eq_sym (skipn_O _)) = o -> _ with
   | Some h => fun _ => h
   | None => fun E =>
       False_rect _
         (trace_scan_finds bp _ (bp_traces bp) 0 (eq_sym (skipn_O _))
            (ex_intro _ _
               (conj (traces_cover bp (Index.bl_node br) (Index.bl_ok br))
                     (proj2 (noderef_eqb_spec _ _) eq_refl)))
            E)
   end) eq_refl.

Lemma block_trace_subject {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (br : Index.BlockRef idx) :
  Index.bl_node (trow_block (th_row (block_trace bp br))) = Index.bl_node br.
Proof.
  apply noderef_eqb_spec. exact (th_ok (block_trace bp br)).
Qed.

(* the retained trace of a block, as the exact typed trace ref *)
Definition trace_of_block {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (br : Index.BlockRef idx) : BlockTraceRef bp (Index.bl_node br) :=
  mk_block_trace (th_ord (block_trace bp br)) (th_row (block_trace bp br))
    (th_at (block_trace bp br)) (block_trace_subject bp br).

(* the enclosing block of a short statement, total by the accepted statement topology *)
Definition stmt_block {p} {idx : Index.ProgramIndex p} (st : Index.ShortStmtRef idx)
  : Index.BlockRef idx :=
  (match Index.node_parent (Index.sh_node st) as o
         return Index.node_parent (Index.sh_node st) = o -> Index.BlockRef idx with
   | Some par => fun E => Index.mkBlockRef par (f_equal Index.is_block_view (stmt_parent_block st par E))
   | None => fun E => False_rect _ (stmt_has_parent st E)
   end) eq_refl.

Definition noderef_eq_dec {p} {idx : Index.ProgramIndex p} (a b : Index.NodeRef idx)
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
Lemma stmt_block_parent {p} {idx : Index.ProgramIndex p} (st : Index.ShortStmtRef idx) :
  Index.node_parent (Index.sh_node st) = Some (Index.bl_node (stmt_block st)).
Proof.
  assert (Hex : exists par, Index.node_parent (Index.sh_node st) = Some par).
  { destruct (Index.node_parent (Index.sh_node st)) as [par|] eqn:Hp;
      [ exists par; reflexivity | exact (False_ind _ (stmt_has_parent st Hp)) ]. }
  destruct Hex as [par Hp].
  unfold stmt_block.
  rewrite (option_convoy_some noderef_eq_dec _ _ _ par Hp).
  exact Hp.
Qed.

(* the exact short event of every short statement exists at its statement ordinal in its block's trace *)
Lemma short_event_cover {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (st : Index.ShortStmtRef idx) (par : Index.NodeRef idx) (tr : TraceRow s) :
  Index.node_parent (Index.sh_node st) = Some par ->
  In tr (bp_traces bp) -> Index.bl_node (trow_block tr) = par ->
  exists eix (st'' : Index.ShortStmtRef idx) (rows : list ShortLeftDecisionData),
    nth_error (trow_evs tr) eix = Some (BEvShort st'' rows)
    /\ Index.sh_node st'' = Index.sh_node st.
Proof.
  intros Hp Hin Hnode.
  destruct (bp_traces_row bp tr Hin) as [pr [r [Hb [_ [_ Hform]]]]].
  assert (Hr : r = par)
    by (rewrite Hform in Hnode; cbn in Hnode; exact Hnode).
  subst r.
  destruct (Index.all_children_of_parent (Index.sh_node st) par Hp) as [j [e [_ Hc]]].
  destruct (Index.all_children_nth par j e) as [e' Hrow].
  assert (Hevs : trow_evs tr = block_fold s (Index.mkBlockRef par Hb) (Index.all_children par)
                                 (pkg_env_of s pr)) by (rewrite Hform; reflexivity).
  destruct (block_fold_nth (Index.mkBlockRef par Hb) (Index.all_children par)
              (pkg_env_of s pr) j (existT _ j e') Hrow) as [env' Hnth].
  cbn [projT2] in Hnth.
  assert (Hcc : Index.ca_child e' = Index.sh_node st)
    by exact (eq_trans (Index.ca_det e' e) Hc).
  assert (Hview : Index.node_view (Index.ca_child e')
                  = Index.VStmt (Index.SSShort (Index.sh_names st) (Index.sh_values st)))
    by (rewrite Hcc; exact (Index.sh_ok st)).
  destruct (block_event_short_eval (Index.mkBlockRef par Hb) env' (Index.ca_child e')
              _ eq_refl (Index.sh_names st) (Index.sh_values st) Hview) as [Hv0 Hev].
  pose proof (eq_trans Hnth (f_equal Some Hev)) as Hnth2.
  exists j. do 2 eexists.
  split; [ rewrite Hevs; exact Hnth2 |].
  cbn [Index.sh_node]. exact Hcc.
Qed.

(* one retained short event ref: the exact trace, statement ordinal, and judged event, pinned *)
Record ShortEventRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (st : Index.ShortStmtRef idx) : Type := mk_short_event {
  se_block : Index.BlockRef idx ;
  se_trace : BlockTraceRef bp (Index.bl_node se_block) ;
  se_ord   : nat ;
  se_stmt  : Index.ShortStmtRef idx ;
  se_rows  : list ShortLeftDecisionData ;
  se_at : nth_error (trow_evs (btr_row se_trace)) se_ord = Some (BEvShort se_stmt se_rows) ;
  se_subject : Index.sh_node se_stmt = Index.sh_node st
}.
Arguments mk_short_event {p idx s d bp st} _ _ _ _ _ _ _.
Arguments se_block {p idx s d bp st} _.
Arguments se_trace {p idx s d bp st} _.
Arguments se_ord {p idx s d bp st} _.
Arguments se_stmt {p idx s d bp st} _.
Arguments se_rows {p idx s d bp st} _.
Arguments se_at {p idx s d bp st} _.
Arguments se_subject {p idx s d bp st} _.

Definition is_short_match {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (st : Index.ShortStmtRef idx) (ev : BlockEv s) : bool :=
  match ev with
  | BEvShort st' _ => noderef_eqb (Index.sh_node st') (Index.sh_node st)
  | _ => false
  end.

Fixpoint short_scan {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (br : Index.BlockRef idx) (tr0 : BlockTraceRef bp (Index.bl_node br))
  (st : Index.ShortStmtRef idx) (k : nat) (l : list (BlockEv s)) {struct l}
  : l = skipn k (trow_evs (btr_row tr0)) -> option (ShortEventRef bp st) :=
  match l with
  | [] => fun _ => None
  | BEvShort st' sj :: rest => fun E =>
      match Bool.bool_dec (noderef_eqb (Index.sh_node st') (Index.sh_node st)) true with
      | left Hn =>
          Some (mk_short_event br tr0 k st' sj
                  (Index.skipn_head_at (trow_evs (btr_row tr0)) rest k (BEvShort st' sj) E)
                  (proj1 (noderef_eqb_spec _ _) Hn))
      | right _ =>
          short_scan br tr0 st (S k) rest
            (Index.skipn_tail_at (trow_evs (btr_row tr0)) rest k (BEvShort st' sj) E)
      end
  | ev :: rest => fun E =>
      short_scan br tr0 st (S k) rest
        (Index.skipn_tail_at (trow_evs (btr_row tr0)) rest k ev E)
  end.

Lemma short_scan_finds {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (br : Index.BlockRef idx) (tr0 : BlockTraceRef bp (Index.bl_node br))
  (st : Index.ShortStmtRef idx) :
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
  - destruct (Bool.bool_dec (noderef_eqb (Index.sh_node st') (Index.sh_node st)) true)
      as [|Hne]; [ discriminate |].
    destruct Hin as [He|Hin].
    + rewrite <- He in Hm. cbn in Hm. exact (False_ind _ (Hne Hm)).
    + apply IH. exists ev0. split; [ exact Hin | exact Hm ].
Qed.

Lemma short_event_present {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (st : Index.ShortStmtRef idx) :
  exists ev, In ev (trow_evs (btr_row (trace_of_block bp (stmt_block st))))
             /\ is_short_match st ev = true.
Proof.
  set (tr0 := trace_of_block bp (stmt_block st)).
  destruct (short_event_cover bp st (Index.bl_node (stmt_block st)) (btr_row tr0)
              (stmt_block_parent st) (nth_error_In _ _ (btr_at tr0)) (btr_subject tr0))
    as [eix [st'' [sj [Hnth Hsn]]]].
  exists (BEvShort st'' sj). split; [ exact (nth_error_In _ _ Hnth) |].
  cbn. apply noderef_eqb_spec. exact Hsn.
Qed.

(* the total exact short lookup: every short statement's retained event, judgment included *)
Definition short_event {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (st : Index.ShortStmtRef idx) : ShortEventRef bp st :=
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
Definition se_event {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.ShortStmtRef idx} (se : ShortEventRef bp st)
  : BlockEventRef (se_trace se) :=
  mk_block_event (se_ord se) (nth_error_lt _ _ _ (se_at se)).

Definition short_state_before {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.ShortStmtRef idx} (se : ShortEventRef bp st)
  : BlockStateRef (ber_pre (se_event se)) := block_state (ber_pre (se_event se)).

Definition short_state_after {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.ShortStmtRef idx} (se : ShortEventRef bp st)
  : BlockStateRef (ber_post (se_event se)) := block_state (ber_post (se_event se)).

(* the retained short rows are exactly the canonical decision over the exact predecessor state's members *)
Lemma se_rows_decide {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.ShortStmtRef idx} (se : ShortEventRef bp st) :
  se_rows se = short_decide_rows (map es_est (bs_members (short_state_before se))) (se_stmt se).
Proof.
  pose proof (se_at se) as Hat.
  set (tr := btr_row (se_trace se)) in *.
  destruct (bp_traces_row bp tr (nth_error_In _ _ (btr_at (se_trace se)))) as [pr [r [Hb [_ [_ Hform]]]]].
  assert (Hevs : trow_evs tr = block_fold s (Index.mkBlockRef r Hb) (Index.all_children r) (pkg_env_of s pr))
    by (rewrite Hform; reflexivity).
  pose proof Hat as Hat2. rewrite Hevs in Hat2.
  destruct (block_fold_nth_env (Index.mkBlockRef r Hb) (Index.all_children r) (pkg_env_of s pr)
              (se_ord se) _ Hat2) as [x [_ He]].
  set (c := Index.ca_child (projT2 x)) in *.
  assert (Hcc : Index.sh_node (se_stmt se) = c).
  { pose proof (f_equal bev_node He) as Hn. cbn [bev_node] in Hn.
    rewrite block_event_node in Hn. exact Hn. }
  assert (Hview : Index.node_view c
                  = Index.VStmt (Index.SSShort (Index.sh_names (se_stmt se)) (Index.sh_values (se_stmt se))))
    by (rewrite <- Hcc; exact (Index.sh_ok (se_stmt se))).
  destruct (block_event_short_eval (Index.mkBlockRef r Hb)
              (pkg_env_of s pr ++ flat_map (bev_adds (Index.mkBlockRef r Hb))
                 (firstn (se_ord se) (block_fold s (Index.mkBlockRef r Hb) (Index.all_children r)
                    (pkg_env_of s pr)))) c _ eq_refl
              (Index.sh_names (se_stmt se)) (Index.sh_values (se_stmt se)) Hview) as [Hv0 Heval].
  rewrite Heval in He.
  set (st'' := Index.mkShortStmtRef c (Index.sh_names (se_stmt se)) (Index.sh_values (se_stmt se)) Hv0) in *.
  assert (Hst : se_stmt se = st'') by (apply shortstmtref_positional; cbn [Index.sh_node]; exact Hcc).
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
  replace (trow_block tr) with (Index.mkBlockRef r Hb) by (rewrite Hform; reflexivity).
  rewrite Hevs. reflexivity.
Qed.

(* an exact predecessor-state member ref from a positional match over the state's projected members *)
Definition state_member_ref {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
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
Definition local_group_refs {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (st : BlockStateRef c) (nm : Names.OrdinaryIdentifier) : list (EstablishmentRef bp) :=
  filter (fun er => same_block_cand nm (es_est er)) (bs_members st).
Record LocalGroupRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (st : BlockStateRef c) (nm : Names.OrdinaryIdentifier) : Type := mk_local_group {
  lg_members : list (EstablishmentRef bp) ;
  lg_ok : lg_members = local_group_refs st nm
}.
Arguments mk_local_group {p idx s d bp b tr c st nm} _ _.
Arguments lg_members {p idx s d bp b tr c st nm} _.
Arguments lg_ok {p idx s d bp b tr c st nm} _.
Definition local_group {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (st : BlockStateRef c) (nm : Names.OrdinaryIdentifier) : LocalGroupRef st nm :=
  mk_local_group (local_group_refs st nm) eq_refl.

(* the exact short-left fact, INDEXED by the retained decision row: for a given row exactly one case inhabits *)
Inductive ShortLhsFact {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (pre : BlockStateRef c) {st : Index.ShortStmtRef idx} {i : nat}
  (e : Index.ShortLhsEdge st i) : ShortLeftDecisionData -> Type :=
| ShortBlankFact : binder_ident (Index.sl_child e) = None -> ShortLhsFact pre e ShortBlankData
| ShortDuplicateFact : forall (n : Names.OrdinaryIdentifier) (j : nat) (ej : Index.ShortLhsEdge st j)
    (Hj : j < i),
    binder_ident (Index.sl_child e) = Some n -> binder_ident (Index.sl_child ej) = Some n ->
    find_dup i n (Index.short_lhs_edges st) = Some (existT _ j (ej, Hj)) ->
    ShortLhsFact pre e (ShortDuplicateData j)
| ShortNewFact : forall (n : Names.OrdinaryIdentifier),
    binder_ident (Index.sl_child e) = Some n ->
    find_dup i n (Index.short_lhs_edges st) = None ->
    (forall mr : BlockMemberRef pre, same_block_cand n (es_est (bm_ref mr)) = false) ->
    ShortLhsFact pre e (ShortNewData n)
| ShortExistingVariableFact : forall (n : Names.OrdinaryIdentifier) (mr : BlockMemberRef pre),
    binder_ident (Index.sl_child e) = Some n ->
    find_dup i n (Index.short_lhs_edges st) = None ->
    find_two_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = None ->
    find_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = Some (bm_ord mr, es_est (bm_ref mr)) ->
    is_variable_binder (est_node (es_est (bm_ref mr))) = true ->
    ShortLhsFact pre e (ShortExistingVariableData (bm_ord mr))
| ShortExistingNonVariableFact : forall (n : Names.OrdinaryIdentifier) (mr : BlockMemberRef pre),
    binder_ident (Index.sl_child e) = Some n ->
    find_dup i n (Index.short_lhs_edges st) = None ->
    find_two_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = None ->
    find_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = Some (bm_ord mr, es_est (bm_ref mr)) ->
    is_variable_binder (est_node (es_est (bm_ref mr))) = false ->
    ShortLhsFact pre e (ShortExistingNonVariableData (bm_ord mr))
| ShortAmbiguousFact : forall (n : Names.OrdinaryIdentifier) (grp : LocalGroupRef pre n)
    (mr1 mr2 : BlockMemberRef pre),
    binder_ident (Index.sl_child e) = Some n ->
    find_dup i n (Index.short_lhs_edges st) = None ->
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
Definition short_lhs_fact {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (pre : BlockStateRef c) {st : Index.ShortStmtRef idx} {i : nat}
  (e : Index.ShortLhsEdge st i)
  : ShortLhsFact pre e (short_left_decide (map es_est (bs_members pre)) e).
Proof.
  unfold short_left_decide.
  destruct (binder_ident (Index.sl_child e)) as [n|] eqn:Hb; [| exact (ShortBlankFact Hb) ].
  destruct (find_dup i n (Index.short_lhs_edges st)) as [[j [ej Hj]]|] eqn:Hd.
  { destruct (find_dup_sound i n (Index.short_lhs_edges st) j (ej, Hj) Hd) as [_ Hm]. cbn in Hm.
    destruct (binder_ident (Index.sl_child ej)) as [m|] eqn:Hbej; [| discriminate Hm].
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
Lemma short_lhs_edge_at {p} {idx : Index.ProgramIndex p} (st : Index.ShortStmtRef idx) (i : nat) :
  i < Index.sh_names st ->
  { e : Index.ShortLhsEdge st i | nth_error (Index.short_lhs_edges st) i = Some (existT _ i e) }.
Proof.
  intro Hi.
  assert (Hlen : length (Index.short_lhs_edges st) = Index.sh_names st).
  { pose proof (Index.short_lhs_edges_ords st) as Ho.
    apply (f_equal (@length _)) in Ho. rewrite length_map, length_seq in Ho. exact Ho. }
  destruct (nth_error (Index.short_lhs_edges st) i) as [x|] eqn:Hx;
    [| exfalso; apply nth_error_None in Hx; lia ].
  assert (Hj : projT1 x = i).
  { pose proof (Index.short_lhs_edges_ords st) as Ho.
    apply (f_equal (fun l => nth_error l i)) in Ho.
    rewrite nth_error_map, Hx in Ho. cbn in Ho.
    rewrite (nth_error_nth' (seq 0 (Index.sh_names st)) 0) in Ho;
      [| rewrite length_seq; exact Hi ].
    rewrite seq_nth in Ho; [| exact Hi ]. cbn in Ho. injection Ho as Ho. exact Ho. }
  destruct x as [j e]. cbn in Hj. subst j. exists e. reflexivity.
Qed.

(* the exact per-left short fact ref: the canonical edge, the retained decision row, and its tag-indexed fact *)
Record ShortLhsFactRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.ShortStmtRef idx} (se : ShortEventRef bp st)
  (i : nat) : Type := mk_short_fact {
  slf_row  : ShortLeftDecisionData ;
  slf_edge : Index.ShortLhsEdge (se_stmt se) i ;
  slf_at   : nth_error (se_rows se) i = Some slf_row ;
  slf_fact : ShortLhsFact (short_state_before se) slf_edge slf_row
}.
Arguments mk_short_fact {p idx s d bp st se i} _ _ _ _.
Arguments slf_row {p idx s d bp st se i} _.
Arguments slf_edge {p idx s d bp st se i} _.
Arguments slf_at {p idx s d bp st se i} _.
Arguments slf_fact {p idx s d bp st se i} _.

(* the one canonical per-left fact: the retained row is exactly the canonical decision, and its fact is pinned *)
Definition short_lhs_fact_ref {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.ShortStmtRef idx} (se : ShortEventRef bp st)
  (i : nat) (Hi : i < Index.sh_names (se_stmt se)) : ShortLhsFactRef se i.
Proof.
  destruct (short_lhs_edge_at (se_stmt se) i Hi) as [e Hedge].
  apply (mk_short_fact
           (short_left_decide (map es_est (bs_members (short_state_before se))) e) e).
  - rewrite se_rows_decide. unfold short_decide_rows.
    rewrite nth_error_map, Hedge. reflexivity.
  - exact (short_lhs_fact (short_state_before se) e).
Defined.

(* the exact state-indexed short judgment: a view giving each left's canonical fact, never a caller table *)
Definition ShortJudgmentRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.ShortStmtRef idx} (se : ShortEventRef bp st) : Type :=
  forall i, i < Index.sh_names (se_stmt se) -> ShortLhsFactRef se i.

(* the one canonical exact short judgment: every left judged against the exact predecessor state *)
Definition short_judgment_ref {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.ShortStmtRef idx} (se : ShortEventRef bp st)
  : ShortJudgmentRef se := fun i Hi => short_lhs_fact_ref se i Hi.

(* every retained New row causes exactly its one event addition, the new establishment for that exact left *)
Lemma short_new_addition {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.ShortStmtRef idx} (se : ShortEventRef bp st)
  (i : nat) (n : Names.OrdinaryIdentifier) (e : Index.ShortLhsEdge (se_stmt se) i)
  (He : nth_error (Index.short_lhs_edges (se_stmt se)) i = Some (existT _ i e))
  (Hrow : nth_error (se_rows se) i = Some (ShortNewData n)) :
  In (new_est (s:=s) (se_block se) e n) (bev_adds (se_block se) (BEvShort (se_stmt se) (se_rows se))).
Proof.
  cbn [bev_adds]. unfold short_rows_adds. apply in_flat_map.
  exists (existT _ i e). split; [ exact (nth_error_In _ _ He) |].
  rewrite Hrow. left. reflexivity.
Qed.

(* and every event addition is caused by exactly one retained New row: no addition without its New decision *)
Lemma short_addition_is_new {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {st : Index.ShortStmtRef idx} (se : ShortEventRef bp st)
  (e' : Est s) :
  In e' (bev_adds (se_block se) (BEvShort (se_stmt se) (se_rows se))) ->
  exists (i : nat) (e : Index.ShortLhsEdge (se_stmt se) i) (n : Names.OrdinaryIdentifier),
    nth_error (se_rows se) i = Some (ShortNewData n) /\ e' = new_est (s:=s) (se_block se) e n.
Proof.
  cbn [bev_adds]. unfold short_rows_adds. intro Hin. apply in_flat_map in Hin.
  destruct Hin as [x [_ Hin]]. destruct x as [i e].
  destruct (nth_error (se_rows se) i) as [row|] eqn:Hrow; [| destruct Hin].
  destruct row; try (exact (match Hin with end)).
  destruct Hin as [<-|F]; [| destruct F].
  exists i, e, n. split; [ exact Hrow | reflexivity ].
Qed.

(* the retained judgment is about the exact queried statement *)
Lemma short_event_subject {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (st : Index.ShortStmtRef idx) :
  se_stmt (short_event bp st) = st.
Proof. apply shortstmtref_positional. exact (se_subject (short_event bp st)). Qed.

(* the leftmost left whose spelling repeats an earlier same-statement left: the syntactic find_dup SCDuplicate uses *)
Definition short_stmt_dup_name {p} {idx : Index.ProgramIndex p} (st : Index.ShortStmtRef idx)
  : option Names.OrdinaryIdentifier :=
  fold_right (fun x acc => match x with existT _ i e =>
     match binder_ident (Index.sl_child e) with
     | Some n => match find_dup i n (Index.short_lhs_edges st) with Some _ => Some n | None => acc end
     | None => acc end end)
   None (Index.short_lhs_edges st).

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
Record DeclEventRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (t : Index.NodeRef idx) : Type := mk_decl_event {
  de_block : Index.BlockRef idx ;
  de_trace : BlockTraceRef bp (Index.bl_node de_block) ;
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

Definition de_event {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.NodeRef idx} (de : DeclEventRef bp t)
  : BlockEventRef (de_trace de) := mk_block_event (de_ord de) (nth_error_lt _ _ _ (de_at de)).

Definition decl_state_before {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.NodeRef idx} (de : DeclEventRef bp t)
  : BlockStateRef (ber_pre (de_event de)) := block_state (ber_pre (de_event de)).

(* the exact declaration-binder classification against the predecessor state and earlier same-event binders *)
Inductive DeclLhsClass {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b0 : Index.NodeRef idx} {tr : BlockTraceRef bp b0}
  {c : BlockCutRef tr} (pre : BlockStateRef c) (t : Index.NodeRef idx) (i : nat) (bd : Index.NodeRef idx) : Type :=
| DCBlank : binder_ident bd = None -> DeclLhsClass pre t i bd
| DCDuplicateEarlier : forall (n : Names.OrdinaryIdentifier) (j : nat) (bj : Index.NodeRef idx),
    binder_ident bd = Some n -> j < i -> nth_error (decl_binders t) j = Some bj ->
    binder_ident bj = Some n -> DeclLhsClass pre t i bd
| DCRedeclaredPrior : forall (n : Names.OrdinaryIdentifier) (mr : BlockMemberRef pre),
    binder_ident bd = Some n ->
    find_ord (binder_name_matches n) 0 (firstn i (decl_binders t)) = None ->
    same_block_cand n (es_est (bm_ref mr)) = true -> DeclLhsClass pre t i bd
| DCAlreadyAmbiguous : forall (n : Names.OrdinaryIdentifier) (grp : LocalGroupRef pre n)
    (mr1 mr2 : BlockMemberRef pre),
    binder_ident bd = Some n ->
    find_ord (binder_name_matches n) 0 (firstn i (decl_binders t)) = None ->
    bm_ord mr1 < bm_ord mr2 -> same_block_cand n (es_est (bm_ref mr1)) = true ->
    same_block_cand n (es_est (bm_ref mr2)) = true -> DeclLhsClass pre t i bd
| DCFresh : forall (n : Names.OrdinaryIdentifier),
    binder_ident bd = Some n ->
    find_ord (binder_name_matches n) 0 (firstn i (decl_binders t)) = None ->
    (forall mr : BlockMemberRef pre, same_block_cand n (es_est (bm_ref mr)) = false) ->
    DeclLhsClass pre t i bd.
Arguments DCBlank {p idx s d bp b0 tr c pre t i bd} _.
Arguments DCDuplicateEarlier {p idx s d bp b0 tr c pre t i bd} _ _ _ _ _ _ _.
Arguments DCRedeclaredPrior {p idx s d bp b0 tr c pre t i bd} _ _ _ _ _.
Arguments DCAlreadyAmbiguous {p idx s d bp b0 tr c pre t i bd} _ _ _ _ _ _ _ _ _.
Arguments DCFresh {p idx s d bp b0 tr c pre t i bd} _ _ _ _.

(* the one deterministic exact declaration-binder classification *)
Definition decl_lhs_class {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b0 : Index.NodeRef idx} {tr : BlockTraceRef bp b0}
  {c : BlockCutRef tr} (pre : BlockStateRef c) (t : Index.NodeRef idx) (i : nat) (bd : Index.NodeRef idx)
  : DeclLhsClass pre t i bd.
Proof.
  destruct (binder_ident bd) as [n|] eqn:Hb; [| exact (DCBlank Hb) ].
  destruct (find_ord (binder_name_matches n) 0 (firstn i (decl_binders t))) as [[j bj]|] eqn:Hdup.
  { destruct (find_ord_found (binder_name_matches n) (firstn i (decl_binders t)) 0 j bj Hdup)
      as [_ [Hnth [Hbm _]]].
    rewrite Nat.sub_0_r in Hnth.
    destruct (nth_error_firstn_some (decl_binders t) i j bj Hnth) as [Hlt Hjn].
    unfold binder_name_matches in Hbm.
    destruct (binder_ident bj) as [m|] eqn:Hbj; [| discriminate Hbm].
    apply Names.ordinary_equalb_spec in Hbm. subst m.
    exact (DCDuplicateEarlier n j bj Hb Hlt Hjn Hbj). }
  destruct (find_two_ord (same_block_cand n) 0 (map es_est (bs_members pre))) as [[j0 j1]|] eqn:Hft.
  { destruct (find_two_ord_found (same_block_cand n) (map es_est (bs_members pre)) 0 j0 j1 Hft)
      as [_ [Hlt [Hex0 Hex1]]].
    destruct (nth_error (map es_est (bs_members pre)) j0) as [m0|] eqn:Hm0;
      [| exfalso; destruct Hex0 as [x0 [Hnx _]]; rewrite Nat.sub_0_r, Hm0 in Hnx; discriminate ].
    destruct (nth_error (map es_est (bs_members pre)) j1) as [m1|] eqn:Hm1;
      [| exfalso; destruct Hex1 as [x1 [Hnx _]]; rewrite Nat.sub_0_r, Hm1 in Hnx; discriminate ].
    destruct (state_member_ref pre j0 m0 Hm0) as [mr0 [He0 Ho0]].
    destruct (state_member_ref pre j1 m1 Hm1) as [mr1 [He1 Ho1]].
    apply (DCAlreadyAmbiguous n (local_group pre n) mr0 mr1 Hb Hdup).
    - rewrite Ho0, Ho1. exact Hlt.
    - rewrite He0. destruct Hex0 as [x0 [Hnx Hfx]]. rewrite Nat.sub_0_r, Hm0 in Hnx.
      injection Hnx as <-. exact Hfx.
    - rewrite He1. destruct Hex1 as [x1 [Hnx Hfx]]. rewrite Nat.sub_0_r, Hm1 in Hnx.
      injection Hnx as <-. exact Hfx. }
  destruct (find_ord (same_block_cand n) 0 (map es_est (bs_members pre))) as [[j m]|] eqn:Ho.
  { destruct (find_ord_found (same_block_cand n) (map es_est (bs_members pre)) 0 j m Ho)
      as [_ [Hn' [Hf _]]].
    rewrite Nat.sub_0_r in Hn'.
    destruct (state_member_ref pre j m Hn') as [mr [He Hoo]].
    apply (DCRedeclaredPrior n mr Hb Hdup). rewrite He. exact Hf. }
  { apply (DCFresh n Hb Hdup). intro mr.
    apply (find_ord_none (same_block_cand n) (map es_est (bs_members pre)) 0 Ho).
    apply (nth_error_In _ (bm_ord mr)). rewrite nth_error_map, (bm_at mr). reflexivity. }
Defined.

(* the exact declaration judgment: every flat binder classified against the exact predecessor state *)
Definition DeclJudgmentRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.NodeRef idx} (de : DeclEventRef bp t) : Type :=
  forall (i : nat) (bd : Index.NodeRef idx), nth_error (decl_binders t) i = Some bd ->
    DeclLhsClass (decl_state_before de) t i bd.

Definition decl_judgment_ref {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {t : Index.NodeRef idx} (de : DeclEventRef bp t)
  : DeclJudgmentRef de := fun i bd _ => decl_lhs_class (decl_state_before de) t i bd.

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

Definition cut_of {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (evs : list (BlockEv s)) (u : Index.NodeRef idx) : nat :=
  count_while (fun ev => Nat.ltb (Index.node_extent (bev_node ev)) (Index.nr_pos u)) evs.

(* the covering-block test: the exact retained source window of the old block visibility rule *)
Definition covers_use {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (u : Index.NodeRef idx) (tr : TraceRow s) : bool :=
  andb (Index.fileref_eqb (Index.nr_file (Index.bl_node (trow_block tr))) (Index.nr_file u))
  (andb (Nat.ltb (Index.nr_pos (Index.bl_node (trow_block tr))) (Index.nr_pos u))
        (Nat.leb (Index.nr_pos u) (Index.node_extent (Index.bl_node (trow_block tr))))).

Definition vstart_before {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (u : Index.NodeRef idx) (er : EstablishmentRef bp) : bool :=
  Nat.ltb (est_vstart (es_est er)) (Index.nr_pos u).

(* the current declaration event's exactly visible additions at this use — a private builder helper only *)
Definition cur_adds {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.NodeRef idx) (tix cut : nat) : list (EstablishmentRef bp) :=
  filter (vstart_before u) (block_ev_refs bp tix cut).

(* one exact current-event addition visible at a use: a not-yet-visible addition cannot inhabit this type *)
Record CurAddRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  (c : BlockCutRef tr) (u : Index.NodeRef idx) : Type := mk_cur_add {
  ca_ref : EstablishmentRef bp ;
  ca_in  : In ca_ref (block_ev_refs bp (btr_ord tr) (bc_ord c)) ;
  ca_vis : vstart_before u ca_ref = true
}.
Arguments mk_cur_add {p idx s d bp b tr c u} _ _ _.
Arguments ca_ref {p idx s d bp b tr c u} _.
Arguments ca_in {p idx s d bp b tr c u} _.
Arguments ca_vis {p idx s d bp b tr c u} _.

(* build the exact visible current additions from a sublist of the current event's refs, threading membership *)
Fixpoint cur_add_scan {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  (c : BlockCutRef tr) (u : Index.NodeRef idx) (l : list (EstablishmentRef bp)) {struct l}
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
Definition cur_add_refs {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  (c : BlockCutRef tr) (u : Index.NodeRef idx) : list (CurAddRef c u) :=
  cur_add_scan c u (block_ev_refs bp (btr_ord tr) (bc_ord c)) (fun er H => H).

(* the visible current additions project back to exactly the filtered current-event refs *)
Lemma cur_add_scan_proj {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  (c : BlockCutRef tr) (u : Index.NodeRef idx) (l : list (EstablishmentRef bp))
  (H : forall er, In er l -> In er (block_ev_refs bp (btr_ord tr) (bc_ord c))) :
  map ca_ref (cur_add_scan c u l H) = filter (vstart_before u) l.
Proof.
  revert H. induction l as [|er rest IH]; intro H; [ reflexivity |].
  cbn [cur_add_scan filter]. destruct (Bool.bool_dec (vstart_before u er) true) as [Hvis|Hvis].
  - cbn [map ca_ref]. rewrite Hvis. rewrite (IH (fun er' Hin => H er' (or_intror Hin))). reflexivity.
  - apply Bool.not_true_is_false in Hvis. rewrite Hvis.
    rewrite (IH (fun er' Hin => H er' (or_intror Hin))). reflexivity.
Qed.
Lemma cur_add_refs_proj {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  (c : BlockCutRef tr) (u : Index.NodeRef idx) :
  map ca_ref (cur_add_refs c u) = cur_adds bp u (btr_ord tr) (bc_ord c).
Proof. unfold cur_add_refs, cur_adds. apply cur_add_scan_proj. Qed.

Lemma cut_of_le {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (evs : list (BlockEv s)) (u : Index.NodeRef idx) : cut_of evs u <= length evs.
Proof. unfold cut_of. apply count_while_le. Qed.

(* the exact block use context: covering trace, cut, predecessor state, and visible current-event additions *)
Record BlockUseRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.NodeRef idx) : Type := mk_block_use {
  bu_block : Index.BlockRef idx ;
  bu_trace : BlockTraceRef bp (Index.bl_node bu_block) ;
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
Definition bc_row {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (bc : BlockUseRef bp u) : TraceRow s :=
  btr_row (bu_trace bc).
Definition bc_tix {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (bc : BlockUseRef bp u) : nat :=
  btr_ord (bu_trace bc).
Definition bc_cut {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (bc : BlockUseRef bp u) : nat :=
  bc_ord (bu_cut bc).
Definition bc_state {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (bc : BlockUseRef bp u)
  : BlockStateRef (bu_cut bc) := block_state (bu_cut bc).
Definition bc_pre {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (bc : BlockUseRef bp u)
  : list (EstablishmentRef bp) := bs_members (bc_state bc).
Definition bc_cur {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (bc : BlockUseRef bp u)
  : list (EstablishmentRef bp) := map ca_ref (bu_cur bc).

(* the retained pins, now derived over the exact projections *)
Definition bc_at {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (bc : BlockUseRef bp u)
  : nth_error (bp_traces bp) (bc_tix bc) = Some (bc_row bc) := btr_at (bu_trace bc).
Definition bc_cut_pin {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (bc : BlockUseRef bp u)
  : bc_cut bc = cut_of (trow_evs (bc_row bc)) u := bu_cut_at bc.
Definition bc_pre_pin {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (bc : BlockUseRef bp u)
  : bc_pre bc = state_refs bp (bc_tix bc) (bc_cut bc) := eq_refl.
Definition bc_cur_pin {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (bc : BlockUseRef bp u)
  : bc_cur bc = cur_adds bp u (bc_tix bc) (bc_cut bc) := bu_cur_ok bc.

Definition locate_block_ctx {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.NodeRef idx) : option (BlockUseRef bp u) :=
  match trace_scan bp (covers_use u) 0 (bp_traces bp) (eq_sym (skipn_O _)) with
  | Some h =>
      let tr := mk_block_trace (th_ord h) (th_row h) (th_at h) eq_refl in
      let c := mk_block_cut (tr := tr) (cut_of (trow_evs (th_row h)) u) (cut_of_le _ u) in
      Some (mk_block_use (trow_block (th_row h)) tr c (th_ok h) eq_refl
              (cur_add_refs c u) (cur_add_refs_proj c u))
  | None => None
  end.

(* the one exact use-context object ordinary resolution consumes *)
Record UseEnvironmentRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.NodeRef idx) : Type := mk_use_env {
  ue_pkg : PI.PackageRef s ;
  ue_pkg_pin : ue_pkg = PI.package_of_file s (Index.nr_file u) ;
  ue_block : option (BlockUseRef bp u) ;
  ue_block_pin : ue_block = locate_block_ctx bp u
}.
Arguments mk_use_env {p idx s d bp u} _ _ _ _.
Arguments ue_pkg {p idx s d bp u} _.
Arguments ue_pkg_pin {p idx s d bp u} _.
Arguments ue_block {p idx s d bp u} _.
Arguments ue_block_pin {p idx s d bp u} _.

Definition ue_pkg_refs {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (ue : UseEnvironmentRef bp u)
  : list (EstablishmentRef bp) := package_env_refs bp (ue_pkg ue).
Definition ue_pkg_refs_pin {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (ue : UseEnvironmentRef bp u)
  : ue_pkg_refs ue = package_env_refs bp (ue_pkg ue) := eq_refl.

Definition use_env {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.NodeRef idx) : UseEnvironmentRef bp u :=
  mk_use_env (PI.package_of_file s (Index.nr_file u)) eq_refl (locate_block_ctx bp u) eq_refl.

(* the visible occupancy members at this use: block-scoped name matches of pre-state plus gated current *)
Definition bc_visible {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (bc : BlockUseRef bp u)
  (n : Names.OrdinaryIdentifier) : list (EstablishmentRef bp) :=
  filter (fun er => same_block_cand n (es_est er)) (bc_pre bc ++ bc_cur bc).

Definition pkg_named {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : list (EstablishmentRef bp) :=
  filter (fun er => Names.ordinary_equalb (est_name (es_est er)) n) (ue_pkg_refs ue).

(* the exact visible groups over a use environment: local block-visible members and package members (§7.7) *)
Record LocalVisibleGroupRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : Type := mk_local_visible {
  lvg_members : list (EstablishmentRef bp) ;
  lvg_ok : lvg_members = match ue_block ue with Some bc => bc_visible bc n | None => [] end
}.
Arguments mk_local_visible {p idx s d bp u ue n} _ _.
Arguments lvg_members {p idx s d bp u ue n} _.
Arguments lvg_ok {p idx s d bp u ue n} _.
Definition local_visible_group {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : LocalVisibleGroupRef ue n :=
  mk_local_visible _ eq_refl.

Record PackageVisibleGroupRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : Type := mk_pkg_visible {
  pvg_members : list (EstablishmentRef bp) ;
  pvg_ok : pvg_members = pkg_named ue n
}.
Arguments mk_pkg_visible {p idx s d bp u ue n} _ _.
Arguments pvg_members {p idx s d bp u ue n} _.
Arguments pvg_ok {p idx s d bp u ue n} _.
Definition package_visible_group {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : PackageVisibleGroupRef ue n :=
  mk_pkg_visible _ eq_refl.

(* a block-occupancy match at a trace's event is a member of that block's canonical group *)
Lemma block_cand_matches {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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

Lemma pkg_name_matches {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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
Lemma block_visible_le {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.NodeRef idx) (tix cut : nat) (tr : TraceRow s)
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

Lemma pkg_visible_le {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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

Lemma block_group_two {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (bc : BlockUseRef bp u)
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

Lemma pkg_group_two {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) (er1 er2 : EstablishmentRef bp) (rest : list (EstablishmentRef bp)) :
  pkg_named ue n = er1 :: er2 :: rest ->
  2 <= length (group_refs bp (PackageScope (ue_pkg ue)) n).
Proof.
  intro Hv. unfold pkg_named in Hv. rewrite (ue_pkg_refs_pin ue) in Hv.
  eapply Nat.le_trans; [| apply (pkg_visible_le bp (ue_pkg ue) n) ].
  rewrite Hv. cbn. lia.
Qed.

(* a resolved object: predeclared identity, or the exact phase-owned establishment ref *)
Inductive BoundObject {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) : Type :=
| PredeclaredBound : Names.PredeclaredName -> BoundObject bp
| SourceBound : EstablishmentRef bp -> BoundObject bp.
Arguments PredeclaredBound {p idx s d bp} _.
Arguments SourceBound {p idx s d bp} _.

(* the idx-level object view Analysis payloads project; never a route back to a ref *)
Definition object_view {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (o : BoundObject bp) : ObjectRef idx :=
  match o with
  | PredeclaredBound pn => PredeclaredObject pn
  | SourceBound er => SourceObject (est_origin (es_est er))
  end.

Definition RedeclRoot {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (n : Names.OrdinaryIdentifier) : Type :=
  { sc : ScopeId s & RedeclarationRef bp sc n }.

Inductive Resolved {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (use : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) : Type :=
| RBound      : BoundObject bp -> Resolved bp use n
| RRedeclared : RedeclRoot bp n -> Resolved bp use n
| RUnbound    : Resolved bp use n.
Arguments RBound {p idx s d bp use n} _.
Arguments RRedeclared {p idx s d bp use n} _.
Arguments RUnbound {p idx s d bp use n}.

Definition pkg_decide {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : Resolved bp u n :=
  (match pkg_named ue n as v return pkg_named ue n = v -> Resolved bp u n with
   | [] => fun _ =>
       match Names.classify_predeclared (Names.ordinary_spelling n) with
       | Some pn => RBound (PredeclaredBound pn)
       | None => RUnbound
       end
   | er :: rest =>
       match rest as v2 return pkg_named ue n = er :: v2 -> Resolved bp u n with
       | [] => fun _ => RBound (SourceBound er)
       | er2 :: rest2 => fun Hv =>
           RRedeclared (existT _ (PackageScope (ue_pkg ue))
                          (mk_redeclaration (binding_group bp (PackageScope (ue_pkg ue)) n)
                             (pkg_group_two ue n er er2 rest2 Hv)))
       end
   end) eq_refl.

(* resolution: block visibility shadows the package; a unique visible member binds; two redeclare *)
Definition resolve_env {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) : Resolved bp u n :=
  match ue_block ue with
  | Some bc =>
      (match bc_visible bc n as v return bc_visible bc n = v -> Resolved bp u n with
       | [] => fun _ => pkg_decide ue n
       | er :: rest =>
           match rest as v2 return bc_visible bc n = er :: v2 -> Resolved bp u n with
           | [] => fun _ => RBound (SourceBound er)
           | er2 :: rest2 => fun Hv =>
               RRedeclared (existT _ (BlockScope (trow_block (bc_row bc)))
                              (mk_redeclaration
                                 (binding_group bp (BlockScope (trow_block (bc_row bc))) n)
                                 (block_group_two bc n er er2 rest2 Hv)))
           end
       end) eq_refl
  | None => pkg_decide ue n
  end.

Definition resolve {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  : Resolved bp u n := resolve_env (use_env bp u) n.

(* the exact inversion of resolution: each outcome names its exact visible evidence *)
Lemma pkg_decide_empty {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) :
  pkg_named ue n = [] ->
  pkg_decide ue n
  = match Names.classify_predeclared (Names.ordinary_spelling n) with
    | Some pn => RBound (PredeclaredBound pn)
    | None => RUnbound
    end.
Proof.
  intro H. unfold pkg_decide.
  generalize (@eq_refl (list (EstablishmentRef bp)) (pkg_named ue n)).
  destruct (pkg_named ue n) at 2 3.
  - intro Heq. reflexivity.
  - intro Heq. exfalso. rewrite H in Heq. discriminate Heq.
Qed.

Lemma pkg_decide_unique {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) (er : EstablishmentRef bp) :
  pkg_named ue n = [er] ->
  pkg_decide ue n = RBound (SourceBound er).
Proof.
  intro H. unfold pkg_decide.
  generalize (@eq_refl (list (EstablishmentRef bp)) (pkg_named ue n)).
  destruct (pkg_named ue n) at 2 3.
  - intro Heq. exfalso. rewrite H in Heq. discriminate Heq.
  - match goal with l0 : list (EstablishmentRef bp) |- _ => destruct l0 as [|er2 rest2] end.
    + intro Heq. rewrite H in Heq. injection Heq as ->. reflexivity.
    + intro Heq. exfalso. rewrite H in Heq. injection Heq as He1 He2. discriminate He2.
Qed.

Lemma pkg_decide_redeclared {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {u : Index.NodeRef idx} (ue : UseEnvironmentRef bp u)
  (n : Names.OrdinaryIdentifier) (er1 er2 : EstablishmentRef bp)
  (rest : list (EstablishmentRef bp)) :
  pkg_named ue n = er1 :: er2 :: rest ->
  exists rr : RedeclarationRef bp (PackageScope (ue_pkg ue)) n,
    pkg_decide ue n = RRedeclared (existT _ (PackageScope (ue_pkg ue)) rr).
Proof.
  intro H. unfold pkg_decide.
  generalize (@eq_refl (list (EstablishmentRef bp)) (pkg_named ue n)).
  destruct (pkg_named ue n) at 2 3.
  - intro Heq. exfalso. rewrite H in Heq. discriminate Heq.
  - match goal with l0 : list (EstablishmentRef bp) |- _ => destruct l0 as [|er2' rest2'] end.
    + intro Heq. exfalso. rewrite H in Heq. injection Heq as He1 He2. discriminate He2.
    + intro Heq. eexists. reflexivity.
Qed.

Lemma resolve_no_block {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) :
  locate_block_ctx bp u = None ->
  resolve bp u n = pkg_decide (use_env bp u) n.
Proof.
  intro Hloc. unfold resolve, resolve_env.
  change (ue_block (use_env bp u)) with (locate_block_ctx bp u).
  rewrite Hloc. reflexivity.
Qed.

Lemma resolve_block_empty {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (bc : BlockUseRef bp u) :
  locate_block_ctx bp u = Some bc ->
  bc_visible bc n = [] ->
  resolve bp u n = pkg_decide (use_env bp u) n.
Proof.
  intros Hloc H. unfold resolve, resolve_env.
  change (ue_block (use_env bp u)) with (locate_block_ctx bp u).
  rewrite Hloc.
  generalize (@eq_refl (list (EstablishmentRef bp)) (bc_visible bc n)).
  destruct (bc_visible bc n) at 2 3.
  - intro Heq. reflexivity.
  - intro Heq. exfalso. rewrite H in Heq. discriminate Heq.
Qed.

(* a unique visible block member binds exactly; block visibility shadows the package *)
Lemma resolve_block_unique {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (bc : BlockUseRef bp u) (er : EstablishmentRef bp) :
  locate_block_ctx bp u = Some bc ->
  bc_visible bc n = [er] ->
  resolve bp u n = RBound (SourceBound er).
Proof.
  intros Hloc H. unfold resolve, resolve_env.
  change (ue_block (use_env bp u)) with (locate_block_ctx bp u).
  rewrite Hloc.
  generalize (@eq_refl (list (EstablishmentRef bp)) (bc_visible bc n)).
  destruct (bc_visible bc n) at 2 3.
  - intro Heq. exfalso. rewrite H in Heq. discriminate Heq.
  - match goal with l0 : list (EstablishmentRef bp) |- _ => destruct l0 as [|er2 rest2] end.
    + intro Heq. rewrite H in Heq. injection Heq as ->. reflexivity.
    + intro Heq. exfalso. rewrite H in Heq. injection Heq as He1 He2. discriminate He2.
Qed.

(* two visible members return the exact phase-owned redeclaration root; it binds no object *)
Lemma resolve_block_redeclared {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  (bc : BlockUseRef bp u) (er1 er2 : EstablishmentRef bp) (rest : list (EstablishmentRef bp)) :
  locate_block_ctx bp u = Some bc ->
  bc_visible bc n = er1 :: er2 :: rest ->
  exists rr : RedeclarationRef bp (BlockScope (trow_block (bc_row bc))) n,
    resolve bp u n = RRedeclared (existT _ (BlockScope (trow_block (bc_row bc))) rr).
Proof.
  intros Hloc H. unfold resolve, resolve_env.
  change (ue_block (use_env bp u)) with (locate_block_ctx bp u).
  rewrite Hloc.
  generalize (@eq_refl (list (EstablishmentRef bp)) (bc_visible bc n)).
  destruct (bc_visible bc n) at 2 3.
  - intro Heq. exfalso. rewrite H in Heq. discriminate Heq.
  - match goal with l0 : list (EstablishmentRef bp) |- _ => destruct l0 as [|er2' rest2'] end.
    + intro Heq. exfalso. rewrite H in Heq. injection Heq as He1 He2. discriminate He2.
    + intro Heq. eexists. reflexivity.
Qed.

(* every redeclaration root exposes at least two canonical group members: it can bind nothing *)
Lemma redecl_root_two {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {n : Names.OrdinaryIdentifier} (root : RedeclRoot bp n) :
  2 <= length (bg_members (rr_group (projT2 root))).
Proof. exact (rr_two (projT2 root)). Qed.

(* a short event's additions become visible only past the whole statement *)
Lemma new_est_vstart {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) {st : Index.ShortStmtRef idx} {i : nat}
  (e : Index.ShortLhsEdge st i) (n : Names.OrdinaryIdentifier) :
  est_vstart (new_est (s := s) br e n) = Index.node_extent (Index.sh_node st).
Proof.
  cbn [new_est est_vstart]. unfold vis_start.
  rewrite (Index.sl_role e).
  unfold Index.sl_child. rewrite (Index.ca_node_parent (Index.sl_at e)). reflexivity.
Qed.

(* every short addition becomes visible only past the whole statement, a pure fact of the projected New rows *)
Lemma short_rows_adds_vstart {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) (st : Index.ShortStmtRef idx) (rows : list ShortLeftDecisionData) (e : Est s) :
  In e (short_rows_adds br st rows) -> est_vstart e = Index.node_extent (Index.sh_node st).
Proof.
  unfold short_rows_adds. intro Hin. apply in_flat_map in Hin. destruct Hin as [x [_ Hin]].
  destruct x as [i ed]. destruct (nth_error rows i) as [row|]; try (exact (match Hin with end)).
  destruct row; try (exact (match Hin with end)).
  destruct Hin as [<-|F]; [| destruct F ]. apply new_est_vstart.
Qed.

(* within the short statement, its own additions are gated out of every use environment *)
Lemma short_cur_adds_empty {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.NodeRef idx) (tix cut : nat) (tr : TraceRow s)
  (st' : Index.ShortStmtRef idx) (rows : list ShortLeftDecisionData) :
  nth_error (bp_traces bp) tix = Some tr ->
  nth_error (trow_evs tr) cut = Some (BEvShort st' rows) ->
  Index.nr_pos u <= Index.node_extent (Index.sh_node st') ->
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
Record DeclarationGroupRef {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type
  := mk_decl_group {
  dg_scope   : ScopeId s ;
  dg_name    : Names.OrdinaryIdentifier ;
  dg_members : list (Est s)
}.
Arguments mk_decl_group {p idx s} _ _ _.
Arguments dg_scope {p idx s} _.
Arguments dg_name {p idx s} _.
Arguments dg_members {p idx s} _.

Definition group_view {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {sc : ScopeId s} {n : Names.OrdinaryIdentifier}
  (rr : RedeclarationRef bp sc n) : DeclarationGroupRef s :=
  mk_decl_group sc n (map es_est (bg_members (rr_group rr))).

Definition redecl_view {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {n : Names.OrdinaryIdentifier} (root : RedeclRoot bp n)
  : DeclarationGroupRef s := group_view (projT2 root).

(* one exact redeclared-group projection per canonical group, keyed at its exact first member *)
Definition redeclared_groups {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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
Definition group_at_use {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
  : list (EstablishmentRef bp) :=
  match ue_block (use_env bp u) with
  | Some bc => match bc_visible bc n with [] => pkg_named (use_env bp u) n | v => v end
  | None => pkg_named (use_env bp u) n
  end.

(* main status stays a projection over the exact retained package environment refs *)
Definition package_main {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pr : PI.PackageRef s) : MainStatus s pr :=
  main_status_of (map es_est (package_env_refs bp pr)) pr.

Theorem package_main_sound {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} (bp : BindingPhase s d) (pr : PI.PackageRef s) :
  main_status_ests (package_main bp pr) = main_ests_of (map es_est (package_env_refs bp pr)) pr.
Proof. unfold package_main. apply main_status_ests_of. Qed.

Lemma main_is_package_local {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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
Definition site_outer {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) : nat :=
  match site with PkgEventAt pix _ _ => pix | BlockEventAt tix _ _ => tix end.
Definition site_eix {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) : nat :=
  match site with PkgEventAt _ eix _ => eix | BlockEventAt _ eix _ => eix end.

Lemma refs_scan_keys {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) :
  forall l k (E : l = skipn k (event_adds site)),
  map (fun er => (es_site er, es_ix er)) (refs_scan site k l E)
  = map (fun ix => (site, ix)) (seq k (length l)).
Proof.
  induction l as [|e0 rest IH]; intros k E; [ reflexivity |].
  cbn. rewrite IH. reflexivity.
Qed.

Lemma refs_of_event_keys {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) :
  map (fun er => (es_site er, es_ix er)) (refs_of_event site)
  = map (fun ix => (site, ix)) (seq 0 (length (event_adds site))).
Proof. apply refs_scan_keys. Qed.

(* the keys of one event's refs are distinct: they share the site and carry distinct addition indices *)
Lemma event_keys_nodup {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} (site : EvSite bp) :
  NoDup (map (fun er => (es_site er, es_ix er)) (refs_of_event site)).
Proof.
  rewrite refs_of_event_keys. apply nodup_map_inj;
    [ intros x y H; congruence | apply seq_NoDup ].
Qed.

(* one ledger's establishment keys are distinct, every one carrying that ledger's package ordinal *)
Lemma ledger_keys_nodup {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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
Lemma trace_keys_nodup {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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
Theorem establishment_refs_once {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
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
Lemma short_lhs_blank {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (pre : BlockStateRef c) {st : Index.ShortStmtRef idx} {i : nat}
  (e : Index.ShortLhsEdge st i) (row : ShortLeftDecisionData) (f : ShortLhsFact pre e row) :
  match row with ShortBlankData => binder_ident (Index.sl_child e) = None | _ => True end.
Proof. destruct f; cbn; solve [ exact I | assumption ]. Qed.

Lemma short_lhs_duplicate {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (pre : BlockStateRef c) {st : Index.ShortStmtRef idx} {i : nat}
  (e : Index.ShortLhsEdge st i) (row : ShortLeftDecisionData) (f : ShortLhsFact pre e row) :
  match row with
  | ShortDuplicateData j => exists (n : Names.OrdinaryIdentifier) (ej : Index.ShortLhsEdge st j) (Hj : j < i),
      binder_ident (Index.sl_child e) = Some n /\ binder_ident (Index.sl_child ej) = Some n
      /\ find_dup i n (Index.short_lhs_edges st) = Some (existT _ j (ej, Hj))
  | _ => True end.
Proof.
  destruct f as [H | n j ej Hj Hb Hbej Hd | n Hb Hd Hm | n mr Hb Hd Hft Ho Hv
                | n mr Hb Hd Hft Ho Hv | n grp mr1 mr2 Hb Hd Hft Hlg Hs1 Hs2]; cbn; try exact I.
  exists n, ej, Hj. split; [ exact Hb | split; [ exact Hbej | exact Hd ] ].
Qed.

Lemma short_lhs_new {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (pre : BlockStateRef c) {st : Index.ShortStmtRef idx} {i : nat}
  (e : Index.ShortLhsEdge st i) (row : ShortLeftDecisionData) (f : ShortLhsFact pre e row) :
  match row with
  | ShortNewData n =>
      binder_ident (Index.sl_child e) = Some n
      /\ find_dup i n (Index.short_lhs_edges st) = None
      /\ (forall mr : BlockMemberRef pre, same_block_cand n (es_est (bm_ref mr)) = false)
  | _ => True end.
Proof.
  destruct f as [H | n j ej Hj Hb Hbej Hd | n Hb Hd Hm | n mr Hb Hd Hft Ho Hv
                | n mr Hb Hd Hft Ho Hv | n grp mr1 mr2 Hb Hd Hft Hlg Hs1 Hs2]; cbn; try exact I.
  split; [ exact Hb | split; [ exact Hd | exact Hm ] ].
Qed.

Lemma short_lhs_existing {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (pre : BlockStateRef c) {st : Index.ShortStmtRef idx} {i : nat}
  (e : Index.ShortLhsEdge st i) (row : ShortLeftDecisionData) (f : ShortLhsFact pre e row) :
  match row with
  | ShortExistingVariableData m => exists (n : Names.OrdinaryIdentifier) (mr : BlockMemberRef pre),
      bm_ord mr = m /\ binder_ident (Index.sl_child e) = Some n
      /\ find_dup i n (Index.short_lhs_edges st) = None
      /\ find_two_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = None
      /\ find_ord (same_block_cand n) 0 (map es_est (bs_members pre)) = Some (bm_ord mr, es_est (bm_ref mr))
      /\ is_variable_binder (est_node (es_est (bm_ref mr))) = true
  | ShortExistingNonVariableData m => exists (n : Names.OrdinaryIdentifier) (mr : BlockMemberRef pre),
      bm_ord mr = m /\ binder_ident (Index.sl_child e) = Some n
      /\ find_dup i n (Index.short_lhs_edges st) = None
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

Lemma short_lhs_ambiguous {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b : Index.NodeRef idx} {tr : BlockTraceRef bp b}
  {c : BlockCutRef tr} (pre : BlockStateRef c) {st : Index.ShortStmtRef idx} {i : nat}
  (e : Index.ShortLhsEdge st i) (row : ShortLeftDecisionData) (f : ShortLhsFact pre e row) :
  match row with
  | ShortAmbiguousData j k => exists (n : Names.OrdinaryIdentifier) (grp : LocalGroupRef pre n)
      (mr1 mr2 : BlockMemberRef pre),
      bm_ord mr1 = j /\ bm_ord mr2 = k /\ binder_ident (Index.sl_child e) = Some n
      /\ find_dup i n (Index.short_lhs_edges st) = None
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

(* the exact declaration-binder classification inverts: each constructor names its exact evidence (contract §9.4) *)
Lemma decl_lhs_blank {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b0 : Index.NodeRef idx} {tr : BlockTraceRef bp b0}
  {c : BlockCutRef tr} (pre : BlockStateRef c) (t : Index.NodeRef idx) (i : nat) (bd : Index.NodeRef idx) :
  binder_ident bd = None
  <-> match decl_lhs_class pre t i bd with DCBlank _ => True | _ => False end.
Proof.
  split.
  - intro Hn. destruct (decl_lhs_class pre t i bd) as
      [Hbl|n j bj Hb Hlt Hjn Hbj|n mr Hb Hfnd Hs|n grp mr1 mr2 Hb Hfnd Hlt Hs1 Hs2|n Hb Hfnd Hm];
      try exact I; rewrite Hn in Hb; discriminate Hb.
  - intro Hm. destruct (decl_lhs_class pre t i bd) as
      [Hbl|n j bj Hb Hlt Hjn Hbj|n mr Hb Hfnd Hs|n grp mr1 mr2 Hb Hfnd Hlt Hs1 Hs2|n Hb Hfnd Hm2];
      solve [ exact Hbl | destruct Hm ].
Qed.

Lemma decl_lhs_duplicate {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b0 : Index.NodeRef idx} {tr : BlockTraceRef bp b0}
  {c : BlockCutRef tr} (pre : BlockStateRef c) (t : Index.NodeRef idx) (i : nat) (bd : Index.NodeRef idx) :
  match decl_lhs_class pre t i bd with
  | DCDuplicateEarlier n j bj _ _ _ _ =>
      binder_ident bd = Some n /\ j < i /\ nth_error (decl_binders t) j = Some bj
      /\ binder_ident bj = Some n
  | _ => True end.
Proof.
  destruct (decl_lhs_class pre t i bd) as
    [Hbl|n j bj Hb Hlt Hjn Hbj|n mr Hb Hfnd Hs|n grp mr1 mr2 Hb Hfnd Hlt Hs1 Hs2|n Hb Hfnd Hm];
    try exact I. split; [exact Hb | split; [exact Hlt | split; [exact Hjn | exact Hbj]]].
Qed.

Lemma decl_lhs_redeclared {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b0 : Index.NodeRef idx} {tr : BlockTraceRef bp b0}
  {c : BlockCutRef tr} (pre : BlockStateRef c) (t : Index.NodeRef idx) (i : nat) (bd : Index.NodeRef idx) :
  match decl_lhs_class pre t i bd with
  | DCRedeclaredPrior n mr _ _ _ =>
      binder_ident bd = Some n /\ same_block_cand n (es_est (bm_ref mr)) = true
  | _ => True end.
Proof.
  destruct (decl_lhs_class pre t i bd) as
    [Hbl|n j bj Hb Hlt Hjn Hbj|n mr Hb Hfnd Hs|n grp mr1 mr2 Hb Hfnd Hlt Hs1 Hs2|n Hb Hfnd Hm];
    try exact I. split; [exact Hb | exact Hs].
Qed.

Lemma decl_lhs_ambiguous {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b0 : Index.NodeRef idx} {tr : BlockTraceRef bp b0}
  {c : BlockCutRef tr} (pre : BlockStateRef c) (t : Index.NodeRef idx) (i : nat) (bd : Index.NodeRef idx) :
  match decl_lhs_class pre t i bd with
  | DCAlreadyAmbiguous n grp mr1 mr2 _ _ _ _ _ =>
      binder_ident bd = Some n /\ bm_ord mr1 < bm_ord mr2
      /\ same_block_cand n (es_est (bm_ref mr1)) = true
      /\ same_block_cand n (es_est (bm_ref mr2)) = true
      /\ lg_members grp = local_group_refs pre n
  | _ => True end.
Proof.
  destruct (decl_lhs_class pre t i bd) as
    [Hbl|n j bj Hb Hlt Hjn Hbj|n mr Hb Hfnd Hs|n grp mr1 mr2 Hb Hfnd Hlt Hs1 Hs2|n Hb Hfnd Hm];
    try exact I.
  split; [exact Hb | split; [exact Hlt | split; [exact Hs1 | split; [exact Hs2 | exact (lg_ok grp)]]]].
Qed.

Lemma decl_lhs_fresh {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {d : PhaseData s} {bp : BindingPhase s d} {b0 : Index.NodeRef idx} {tr : BlockTraceRef bp b0}
  {c : BlockCutRef tr} (pre : BlockStateRef c) (t : Index.NodeRef idx) (i : nat) (bd : Index.NodeRef idx) :
  match decl_lhs_class pre t i bd with
  | DCFresh n _ _ _ =>
      binder_ident bd = Some n
      /\ find_ord (binder_name_matches n) 0 (firstn i (decl_binders t)) = None
      /\ (forall mr : BlockMemberRef pre, same_block_cand n (es_est (bm_ref mr)) = false)
  | _ => True end.
Proof.
  destruct (decl_lhs_class pre t i bd) as
    [Hbl|n j bj Hb Hlt Hjn Hbj|n mr Hb Hfnd Hs|n grp mr1 mr2 Hb Hfnd Hlt Hs1 Hs2|n Hb Hfnd Hm];
    try exact I. split; [exact Hb | split; [exact Hfnd | exact Hm]].
Qed.
