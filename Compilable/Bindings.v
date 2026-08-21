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

(* a package-scope function declaration: the fixed main establishes the name main at package scope *)
Definition make_main_est {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (b : Index.NodeRef idx) : option (Est s) :=
  (match Index.is_main_view (Index.node_view b) as m
     return Index.is_main_view (Index.node_view b) = m -> option (Est s) with
   | true => fun H => Some (mk_est (DOFunc (FixedMainFunction (Index.mkMainOccurrenceRef b H))) main_ident (PackageScope pr) (Index.nr_pos b))
   | false => fun _ => None
   end) eq_refl.

(* the package-scope establishments of one occurrence: a fixed main, or a top-level declaration's binders *)
Definition node_pkg_ests {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.NodeRef idx) : list (Est s) :=
  match Index.node_view r with
  | Index.VTop Index.TSMain => match make_main_est pr r with Some e => [e] | None => [] end
  | Index.VTop Index.TSTopDecl => stmt_decl_ests (PackageScope pr) r
  | _ => []
  end.

(* every package-scope establishment of the surface, in package, file, and position order *)
Definition pkg_ests {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : list (Est s) :=
  flat_map (fun pr => flat_map (fun fr =>
      flat_map (fun pos => match Index.mk_noderef fr (Pos.of_succ_nat pos) with
                           | Some r => node_pkg_ests pr r
                           | None => [] end)
               (seq 0 (Index.occ_count fr)))
    (PI.pkg_members pr)) (PI.packages s).

(* the package-scope seed of one block's environment: exactly its own package's establishments *)
Definition block_base {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
  (br : Index.BlockRef idx) : list (Est s) :=
  filter (fun e => match est_scope e with
                   | PackageScope pr =>
                       PI.packageref_eqb (PI.package_of_file s (Index.nr_file (Index.bl_node br))) pr
                   | BlockScope _ => false end)
         (pkg_ests s).

(* main multiplicity: a distinguished projection over the package-scope function declarations named main *)
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
Definition group_members_core {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (core : list (Est s)) (e : Est s) : list (Est s) := filter (same_group e) core.

(* a group's multiplicity; "ambiguous" (embedded-field/dot-import) is unrepresentable here, so absent by design *)
Inductive GroupStatus {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
| GUnique     : Est s -> GroupStatus s
| GRedeclared : Est s -> Est s -> list (Est s) -> GroupStatus s.
Arguments GUnique {p idx s} _.
Arguments GRedeclared {p idx s} _ _ _.

Definition group_status {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (members : list (Est s)) : option (GroupStatus s) :=
  match members with
  | [] => None
  | m :: nil => Some (GUnique m)
  | a :: b :: rest => Some (GRedeclared a b rest)
  end.

(* a declaration establishment: a declaration binder or a function declaration; short origins are excluded *)
Definition is_decl_est {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} (e : Est s) : bool :=
  match est_origin e with DOShort _ => false | _ => true end.


(* the declaration members of e's group over an establishment list *)
Definition decl_group_core {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (core : list (Est s)) (e : Est s) : list (Est s) := filter is_decl_est (group_members_core core e).

(* a block-scoped establishment: its object lives in a block, not at package scope *)
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

(* an exact environment member: the ordinal and the exact retained member it indexes there *)
Record EnvEstRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) : Type := mk_env_ref {
  er_ord : nat ;
  er_est : Est s ;
  er_at  : nth_error env er_ord = Some er_est
}.
Arguments mk_env_ref {p idx s env} _ _ _.
Arguments er_ord {p idx s env} _.
Arguments er_est {p idx s env} _.
Arguments er_at {p idx s env} _.

(* the first environment member satisfying a predicate, as an exact member reference *)
Fixpoint env_scan {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) (pred : Est s -> bool) (k : nat) (l : list (Est s)) {struct l}
  : l = skipn k env -> option (EnvEstRef env) :=
  match l with
  | [] => fun _ => None
  | e :: rest => fun E =>
      if pred e
      then Some (mk_env_ref k e (Index.skipn_head_at env rest k e E))
      else env_scan env pred (S k) rest (Index.skipn_tail_at env rest k e E)
  end.

(* a refused scan means no member satisfies the predicate *)
Lemma env_scan_none {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) (pred : Est s -> bool) :
  forall l k (E : l = skipn k env),
  env_scan env pred k l E = None -> forall x, In x l -> pred x = false.
Proof.
  induction l as [|e rest IH]; intros k E Hs x Hin; [ destruct Hin |].
  cbn in Hs. destruct (pred e) eqn:Hp; [ discriminate Hs |].
  destruct Hin as [He|Hin]; [ subst x; exact Hp |].
  exact (IH (S k) (Index.skipn_tail_at env rest k e E) Hs x Hin).
Qed.

(* a found member satisfies the predicate, and every earlier in-range member refuses it *)
Lemma env_scan_found {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) (pred : Est s -> bool) :
  forall l k (E : l = skipn k env) (ref : EnvEstRef env),
  env_scan env pred k l E = Some ref ->
  pred (er_est ref) = true /\ k <= er_ord ref
  /\ (forall j x, k <= j -> j < er_ord ref -> nth_error env j = Some x -> pred x = false).
Proof.
  induction l as [|e rest IH]; intros k E ref Hs; [ discriminate Hs |].
  cbn in Hs. destruct (pred e) eqn:Hp.
  - injection Hs as <-. cbn. split; [ exact Hp | split; [ lia |] ].
    intros j x Hkj Hjk. lia.
  - destruct (IH (S k) (Index.skipn_tail_at env rest k e E) ref Hs) as [Hpred [Hle Hbefore]].
    split; [ exact Hpred | split; [ lia |] ].
    intros j x Hkj Hjord Hnth.
    destruct (Nat.eq_dec j k) as [->|Hne].
    + assert (Hhead : nth_error env k = Some e) by (exact (Index.skipn_head_at env rest k e E)).
      rewrite Hhead in Hnth. injection Hnth as <-. exact Hp.
    + apply (Hbefore j x); [ lia | exact Hjord | exact Hnth ].
Qed.

(* the same-block match test: a block-scoped environment member spelling this exact name *)
Definition same_block_cand {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (n : Names.OrdinaryIdentifier) (e : Est s) : bool :=
  andb (is_block_scoped e) (Names.ordinary_equalb (est_name e) n).

(* the exact left-side classification view; the judgment pins it to the one classification decision *)
Inductive ShortLhsView {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) : Type :=
| SVBlank : ShortLhsView env
| SVDuplicate : nat -> ShortLhsView env
| SVNew : Names.OrdinaryIdentifier -> ShortLhsView env
| SVExistingVariable : EnvEstRef env -> ShortLhsView env
| SVExistingNonVariable : EnvEstRef env -> ShortLhsView env
| SVAmbiguous : Est s -> Est s -> list (Est s) -> ShortLhsView env.
Arguments SVBlank {p idx s env}.
Arguments SVDuplicate {p idx s env} _.
Arguments SVNew {p idx s env} _.
Arguments SVExistingVariable {p idx s env} _.
Arguments SVExistingNonVariable {p idx s env} _.
Arguments SVAmbiguous {p idx s env} _ _ _.

(* the one deterministic left-side classification over the exact pre-statement environment *)
Definition short_lhs_decide {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) {st : Index.ShortStmtRef idx} {i : nat} (e : Index.ShortLhsEdge st i)
  : ShortLhsView env :=
  match binder_ident (Index.sl_child e) with
  | None => SVBlank
  | Some n =>
      match find_dup i n (Index.short_lhs_edges st) with
      | Some (existT _ j _) => SVDuplicate j
      | None =>
          match filter (fun e2 => andb (same_block_cand n e2) (is_decl_est e2)) env with
          | a :: c :: rest => SVAmbiguous a c rest
          | _ =>
              match env_scan env (same_block_cand n) 0 env eq_refl with
              | Some prior => if is_variable_binder (est_node (er_est prior))
                              then SVExistingVariable prior else SVExistingNonVariable prior
              | None => SVNew n
              end
          end
      end
  end.

(* the exact retained left judgment: the exact edge and the classification the one decision pins to it *)
Record ShortLhsJudgment {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) (st : Index.ShortStmtRef idx) (i : nat) : Type := mk_slj {
  slj_edge : Index.ShortLhsEdge st i ;
  slj_view : ShortLhsView env ;
  slj_ok   : slj_view = short_lhs_decide env slj_edge
}.
Arguments mk_slj {p idx s env st i} _ _ _.
Arguments slj_edge {p idx s env st i} _.
Arguments slj_view {p idx s env st i} _.
Arguments slj_ok {p idx s env st i} _.

(* the retained short judgment: one left judgment per exact index, all against the one pre-environment *)
Record ShortJudgment {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) (st : Index.ShortStmtRef idx) : Type := mk_short_judgment {
  sj_lefts : list { i : nat & ShortLhsJudgment env st i } ;
  sj_lefts_ok : map (@projT1 _ _) sj_lefts = seq 0 (Index.sh_names st)
}.
Arguments mk_short_judgment {p idx s env st} _ _.
Arguments sj_lefts {p idx s env st} _.
Arguments sj_lefts_ok {p idx s env st} _.

Lemma short_lefts_build_ok {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) (st : Index.ShortStmtRef idx) :
  map (@projT1 _ _)
      (map (fun x => match x with existT _ i e =>
                       existT _ i (mk_slj (env := env) e (short_lhs_decide env e) eq_refl) end)
           (Index.short_lhs_edges st))
  = seq 0 (Index.sh_names st).
Proof.
  rewrite map_map.
  rewrite (map_ext (fun x => projT1 (match x with existT _ i e =>
                      existT _ i (mk_slj (env := env) e (short_lhs_decide env e) eq_refl) end))
                   (@projT1 _ _));
    [ apply Index.short_lhs_edges_ords | intros [i e]; reflexivity ].
Qed.

(* the one canonical short-declaration judgment: every left edge judged by the one decision *)
Definition short_judgment_of {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) (st : Index.ShortStmtRef idx) : ShortJudgment env st :=
  mk_short_judgment
    (map (fun x => match x with existT _ i e =>
                     existT _ i (mk_slj (env := env) e (short_lhs_decide env e) eq_refl) end)
         (Index.short_lhs_edges st))
    (short_lefts_build_ok env st).

(* the exact new establishment a ShortNew left creates: its origin ties the statement, index, and edge *)
Definition new_est {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) {st : Index.ShortStmtRef idx} {i : nat}
  (e : Index.ShortLhsEdge st i) (n : Names.OrdinaryIdentifier) : Est s :=
  mk_est (DOShort (mk_short_new st i e)) n (BlockScope br) (vis_start (Index.sl_child e)).

(* a judgment's additions: all and only its ShortNew lefts, in left source order *)
Definition new_ests {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) {env : list (Est s)} {st : Index.ShortStmtRef idx}
  (sj : ShortJudgment env st) : list (Est s) :=
  flat_map (fun x => match slj_view (projT2 x) with
                     | SVNew n => [new_est br (slj_edge (projT2 x)) n]
                     | _ => [] end)
           (sj_lefts sj).

(* one exact source-order transition: the complete pre-environment judgment and its ShortNew extension *)
Record ShortTransition {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (st : Index.ShortStmtRef idx) : Type := mk_transition {
  tr_block    : Index.BlockRef idx ;
  tr_at       : Index.node_parent (Index.sh_node st) = Some (Index.bl_node tr_block) ;
  tr_pre      : list (Est s) ;
  tr_judgment : ShortJudgment tr_pre st ;
  tr_added    : list (Est s) ;
  tr_added_ok : tr_added = new_ests tr_block tr_judgment
}.
Arguments mk_transition {p idx s st} _ _ _ _ _ _.
Arguments tr_block {p idx s st} _.
Arguments tr_at {p idx s st} _.
Arguments tr_pre {p idx s st} _.
Arguments tr_judgment {p idx s st} _.
Arguments tr_added {p idx s st} _.
Arguments tr_added_ok {p idx s st} _.

(* the post environment is the exact monotonic extension: the pre members, then the News in left order *)
Definition tr_post {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {st : Index.ShortStmtRef idx} (t : ShortTransition (s := s) st) : list (Est s) :=
  tr_pre t ++ tr_added t.

(* every right-hand expression is associated with the exact pre-statement environment, never the post *)
Definition tr_rhs_env {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {st : Index.ShortStmtRef idx} (t : ShortTransition (s := s) st) : list (Est s) := tr_pre t.

(* the exact ordinal of a node under a parent, scanned over the canonical ordinal-edge rows *)
Fixpoint ordinal_scan {p} {idx : Index.ProgramIndex p} (par r : Index.NodeRef idx)
  (l : list { o : nat & Index.ChildAt par o }) {struct l} : option { o : nat & Index.ChildAt par o } :=
  match l with
  | [] => None
  | existT _ o e :: rest =>
      if noderef_eqb (Index.ca_child e) r then Some (existT _ o e) else ordinal_scan par r rest
  end.
Definition find_ordinal {p} {idx : Index.ProgramIndex p} (par r : Index.NodeRef idx)
  : option { o : nat & Index.ChildAt par o } :=
  ordinal_scan par r (Index.all_children par).

(* one block child's establishment contribution over the exact environment before it *)
Definition child_contrib {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) {k : nat} (e : Index.ChildAt (Index.bl_node br) k)
  (env : list (Est s)) (v : Index.NodeView) (Hv : Index.node_view (Index.ca_child e) = v)
  : list (Est s) :=
  match v as v0 return Index.node_view (Index.ca_child e) = v0 -> list (Est s) with
  | Index.VStmt Index.SSDecl => fun _ => stmt_decl_ests (BlockScope br) (Index.ca_child e)
  | Index.VStmt (Index.SSShort nn nv) => fun Hv0 =>
      new_ests br (short_judgment_of env (Index.mkShortStmtRef (Index.ca_child e) nn nv Hv0))
  | _ => fun _ => []
  end Hv.

(* the exact block environment below child ordinal k: the package seed plus every earlier binding event *)
Fixpoint block_env {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) (k : nat) {struct k} : list (Est s) :=
  match k with
  | O => block_base s br
  | S k' => let env := block_env br k' in
            env ++ match Index.child_at_opt (Index.bl_node br) k' with
                   | Some e => child_contrib br e env (Index.node_view (Index.ca_child e)) eq_refl
                   | None => [] end
  end.

(* a short statement is never parentless, its parent is its block, and its own ordinal is always found *)
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

Lemma ordinal_scan_finds {p} {idx : Index.ProgramIndex p} (par r : Index.NodeRef idx) :
  forall l, (exists x, In x l /\ Index.ca_child (projT2 x) = r) -> ordinal_scan par r l <> None.
Proof.
  induction l as [|[o e] rest IH]; intros [x [Hin Hc]]; [ destruct Hin |].
  cbn. destruct (noderef_eqb (Index.ca_child e) r) eqn:Hb; [ discriminate |].
  destruct Hin as [He|Hin].
  - exfalso. subst x. cbn in Hc.
    rewrite Hc in Hb. rewrite (proj2 (noderef_eqb_spec r r) eq_refl) in Hb. discriminate Hb.
  - apply IH. exists x. split; assumption.
Qed.

Lemma stmt_ordinal_found {p} {idx : Index.ProgramIndex p} (st : Index.ShortStmtRef idx)
  (par : Index.NodeRef idx) :
  Index.node_parent (Index.sh_node st) = Some par ->
  find_ordinal par (Index.sh_node st) = None -> False.
Proof.
  intros Hp Hf.
  destruct (Index.all_children_of_parent (Index.sh_node st) par Hp) as [o [e [Hrow Hchild]]].
  apply (ordinal_scan_finds par (Index.sh_node st) (Index.all_children par));
    [ exists (existT _ o e); split; [ exact Hrow | exact Hchild ] | exact Hf ].
Qed.

(* the canonical transition, staged so each stage's decision is a plain argument the laws invert exactly *)
Definition short_transition_fo {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (st : Index.ShortStmtRef idx) (par : Index.NodeRef idx)
  (Hp : Index.node_parent (Index.sh_node st) = Some par)
  (Hb : Index.is_block_view (Index.node_view par) = true)
  (fo : option { o : nat & Index.ChildAt par o })
  (Hf : find_ordinal par (Index.sh_node st) = fo) : ShortTransition (s := s) st :=
  match fo as fo0 return find_ordinal par (Index.sh_node st) = fo0 -> ShortTransition st with
  | Some (existT _ o _) => fun _ =>
      mk_transition (Index.mkBlockRef par Hb) Hp
        (block_env (Index.mkBlockRef par Hb) o)
        (short_judgment_of (block_env (Index.mkBlockRef par Hb) o) st)
        (new_ests (Index.mkBlockRef par Hb)
           (short_judgment_of (block_env (Index.mkBlockRef par Hb) o) st))
        eq_refl
  | None => fun Hf0 => False_rect _ (stmt_ordinal_found st par Hp Hf0)
  end Hf.

Definition short_transition_bv {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (st : Index.ShortStmtRef idx) (par : Index.NodeRef idx)
  (Hp : Index.node_parent (Index.sh_node st) = Some par)
  (bv : bool) (Hb : Index.is_block_view (Index.node_view par) = bv) : ShortTransition (s := s) st :=
  match bv as bv0 return Index.is_block_view (Index.node_view par) = bv0 -> ShortTransition st with
  | true => fun Hb0 => short_transition_fo st par Hp Hb0 (find_ordinal par (Index.sh_node st)) eq_refl
  | false => fun Hb0 => False_rect _ (stmt_parent_not_block st par Hp Hb0)
  end Hb.

Definition short_transition_at {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (st : Index.ShortStmtRef idx) (op : option (Index.NodeRef idx))
  (Hp : Index.node_parent (Index.sh_node st) = op) : ShortTransition (s := s) st :=
  match op as o return Index.node_parent (Index.sh_node st) = o -> ShortTransition st with
  | Some par => fun Hp0 =>
      short_transition_bv st par Hp0 (Index.is_block_view (Index.node_view par)) eq_refl
  | None => fun Hp0 => False_rect _ (stmt_has_parent st Hp0)
  end Hp.

Definition short_transition_of {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (st : Index.ShortStmtRef idx) : ShortTransition (s := s) st :=
  short_transition_at st (Index.node_parent (Index.sh_node st)) eq_refl.

(* the emitted transition rows of one occurrence: exactly the short statements, each with its transition *)
Definition short_row_emit {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (r : Index.NodeRef idx) (v : Index.NodeView) (Hv : Index.node_view r = v)
  : list { st : Index.ShortStmtRef idx & ShortTransition (s := s) st } :=
  match v as v0 return Index.node_view r = v0 -> _ with
  | Index.VStmt (Index.SSShort nn nv) => fun Hv0 =>
      [existT _ (Index.mkShortStmtRef r nn nv Hv0)
              (short_transition_of (Index.mkShortStmtRef r nn nv Hv0))]
  | _ => fun _ => []
  end Hv.

(* the retained source-order trace: every short transition, in package, file, and position order *)
Definition short_rows_of_file {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (fr : Index.FileRef idx) : list { st : Index.ShortStmtRef idx & ShortTransition (s := s) st } :=
  flat_map (fun pos => match Index.mk_noderef fr (Pos.of_succ_nat pos) with
                       | Some r => short_row_emit r (Index.node_view r) eq_refl
                       | None => []
                       end)
           (seq 0 (Index.occ_count fr)).
Definition short_trace {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
  : list { st : Index.ShortStmtRef idx & ShortTransition (s := s) st } :=
  flat_map (fun pr => flat_map short_rows_of_file (PI.pkg_members pr)) (PI.packages s).

(* the exact block scope of a parent occurrence, when it is a block *)
Definition block_scope_of {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (par : Index.NodeRef idx) : option (ScopeId s) :=
  (match Index.is_block_view (Index.node_view par) as bv
         return Index.is_block_view (Index.node_view par) = bv -> option (ScopeId s) with
   | true => fun Hb => Some (BlockScope (Index.mkBlockRef par Hb))
   | false => fun _ => None
   end) eq_refl.

Lemma block_scope_of_some {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (par : Index.NodeRef idx) (sc : ScopeId s) :
  block_scope_of par = Some sc -> exists br, sc = BlockScope br /\ Index.bl_node br = par.
Proof.
  unfold block_scope_of.
  generalize (@eq_refl bool (Index.is_block_view (Index.node_view par))).
  destruct (Index.is_block_view (Index.node_view par)) at 2 3; intro Hb;
    [ intro He; injection He as <-; eexists; split; reflexivity | discriminate ].
Qed.

Lemma block_scope_of_block {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (par : Index.NodeRef idx) :
  Index.node_view par = Index.VBlock -> block_scope_of (s := s) par <> None.
Proof.
  intro Hv. unfold block_scope_of.
  generalize (@eq_refl bool (Index.is_block_view (Index.node_view par))).
  destruct (Index.is_block_view (Index.node_view par)) at 2 3; intro Hb;
    [ discriminate | exfalso; rewrite Hv in Hb; discriminate Hb ].
Qed.

(* the actual establishments emitted at one occurrence: mains, declaration subtrees, and short News *)
Definition node_ests {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.NodeRef idx)
  (v : Index.NodeView) (Hv : Index.node_view r = v) : list (Est s) :=
  match v as v0 return Index.node_view r = v0 -> list (Est s) with
  | Index.VTop Index.TSMain => fun _ => match make_main_est pr r with Some e => [e] | None => [] end
  | Index.VTop Index.TSTopDecl => fun _ => stmt_decl_ests (PackageScope pr) r
  | Index.VStmt Index.SSDecl => fun _ =>
      match Index.node_parent r with
      | Some par =>
          match block_scope_of (s := s) par with
          | Some sc => stmt_decl_ests sc r
          | None => []
          end
      | None => []
      end
  | Index.VStmt (Index.SSShort nn nv) => fun Hv0 =>
      tr_added (short_transition_of (s := s) (Index.mkShortStmtRef r nn nv Hv0))
  | _ => fun _ => []
  end Hv.

(* every actual establishment of the surface, in package, file, and position order *)
Definition actual_ests_of_file {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (fr : Index.FileRef idx) : list (Est s) :=
  flat_map (fun pos => match Index.mk_noderef fr (Pos.of_succ_nat pos) with
                       | Some r => node_ests pr r (Index.node_view r) eq_refl
                       | None => []
                       end)
           (seq 0 (Index.occ_count fr)).
Definition actual_ests {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : list (Est s) :=
  flat_map (fun pr => flat_map (actual_ests_of_file pr) (PI.pkg_members pr)) (PI.packages s).

(* the retained binding phase, sealed to its one builder; main status is a projection over the establishments *)

Record RawBP {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type := mk_rawbp {
  rbp_ests   : list (Est s) ;
  rbp_consts : list { cs : Index.SpecRef idx Index.ConstSpecF & ConstJudgment cs } ;
  rbp_shorts : list { st : Index.ShortStmtRef idx & ShortTransition (s := s) st }
}.
Arguments mk_rawbp {p idx s} _ _ _.
Arguments rbp_ests {p idx s} _.
Arguments rbp_consts {p idx s} _.
Arguments rbp_shorts {p idx s} _.

Definition raw_bindings {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : RawBP s :=
  mk_rawbp (actual_ests s) (const_table s) (short_trace s).
Definition BindingPhase {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
  { b : RawBP s | b = raw_bindings s }.
Definition bindings {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : BindingPhase s :=
  exist _ (raw_bindings s) eq_refl.
Definition bp_ests {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} (bp : BindingPhase s) : list (Est s) :=
  rbp_ests (proj1_sig bp).
Definition bp_consts {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} (bp : BindingPhase s)
  : list { cs : Index.SpecRef idx Index.ConstSpecF & ConstJudgment cs } :=
  rbp_consts (proj1_sig bp).
Definition bp_shorts {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} (bp : BindingPhase s)
  : list { st : Index.ShortStmtRef idx & ShortTransition (s := s) st } :=
  rbp_shorts (proj1_sig bp).
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

(* every emitted transition row names its own occurrence *)
Lemma short_row_emit_node {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (r : Index.NodeRef idx) (v : Index.NodeView) (Hv : Index.node_view r = v)
  (row : { st : Index.ShortStmtRef idx & ShortTransition (s := s) st }) :
  In row (short_row_emit r v Hv) -> Index.sh_node (projT1 row) = r.
Proof.
  destruct v; cbn; try (intros F; exact (match F with end)).
  match goal with sh0 : Index.StmtShape |- _ =>
    destruct sh0; cbn; try (intros F; exact (match F with end)) end.
  intros [He|F]; [ rewrite <- He; reflexivity | destruct F ].
Qed.

Lemma short_row_emit_nodup {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (r : Index.NodeRef idx) (v : Index.NodeView) (Hv : Index.node_view r = v) :
  NoDup (short_row_emit (s := s) r v Hv).
Proof.
  destruct v; cbn; try (repeat constructor; intros F; destruct F).
  match goal with sh0 : Index.StmtShape |- _ =>
    destruct sh0; cbn; repeat constructor; intros F; destruct F end.
Qed.

Lemma short_row_emit_nodes_nodup {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (r : Index.NodeRef idx) (v : Index.NodeView) (Hv : Index.node_view r = v) :
  NoDup (map (fun row => Index.sh_node (projT1 row)) (short_row_emit (s := s) r v Hv)).
Proof.
  destruct v; cbn; try (repeat constructor; intros F; destruct F).
  match goal with sh0 : Index.StmtShape |- _ =>
    destruct sh0; cbn; repeat constructor; intros F; destruct F end.
Qed.

(* the emission fires for every short view: the row exists and names the statement's occurrence *)
Lemma short_row_emit_cover {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (r : Index.NodeRef idx) (v : Index.NodeView) (Hv : Index.node_view r = v) (nn nv : nat) :
  v = Index.VStmt (Index.SSShort nn nv) ->
  exists row, In row (short_row_emit (s := s) r v Hv) /\ Index.sh_node (projT1 row) = r.
Proof.
  intro E. revert Hv. subst v. intro Hv. cbn.
  eexists. split; [ left; reflexivity | reflexivity ].
Qed.

(* the trace covers every short statement *)
Lemma short_trace_cover {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
  (st : Index.ShortStmtRef idx) :
  exists row, In row (short_trace s) /\ Index.sh_node (projT1 row) = Index.sh_node st.
Proof.
  set (r := Index.sh_node st).
  assert (Hfile : In (Index.nr_file r) (PI.pkg_members (PI.package_of_file s (Index.nr_file r))))
    by apply PI.pkg_members_of_file.
  assert (Hentry : exists row, In row (short_rows_of_file (s := s) (Index.nr_file r))
                               /\ Index.sh_node (projT1 row) = r).
  { unfold short_rows_of_file.
    assert (Hmk : Index.mk_noderef (Index.nr_file r) (Pos.of_succ_nat (Index.nr_pos r)) = Some r)
      by (rewrite <- Index.nr_key_pos; apply Index.mk_noderef_self).
    destruct (short_row_emit_cover (s := s) r (Index.node_view r) eq_refl
                (Index.sh_names st) (Index.sh_values st) (Index.sh_ok st)) as [row [Hin' Hnode']].
    exists row. split; [| exact Hnode' ].
    apply in_flat_map. exists (Index.nr_pos r). split.
    - apply in_seq. pose proof (nr_pos_lt r). lia.
    - rewrite Hmk. exact Hin'. }
  destruct Hentry as [row [Hin' Hnode']].
  exists row. split; [| exact Hnode' ].
  unfold short_trace. apply in_flat_map.
  exists (PI.package_of_file s (Index.nr_file r)). split; [ apply PI.packages_complete |].
  apply in_flat_map. exists (Index.nr_file r). split; [ exact Hfile | exact Hin' ].
Qed.

(* the exact phase-owned const judgment ref: one exact retained table row for one exact phase and spec *)
Record ConstSpecJudgmentRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (cs : Index.SpecRef idx Index.ConstSpecF) : Type := mk_cjr {
  cjr_ord : nat ;
  cjr_row : { c : Index.SpecRef idx Index.ConstSpecF & ConstJudgment c } ;
  cjr_at  : nth_error (bp_consts bp) cjr_ord = Some cjr_row ;
  cjr_subject : projT1 cjr_row = cs
}.
Arguments mk_cjr {p idx s bp cs} _ _ _ _.
Arguments cjr_ord {p idx s bp cs} _.
Arguments cjr_row {p idx s bp cs} _.
Arguments cjr_at {p idx s bp cs} _.
Arguments cjr_subject {p idx s bp cs} _.

Lemma specref_of_nodes {p} {idx : Index.ProgramIndex p} {fl : Index.SpecFlavor}
  (a b : Index.SpecRef idx fl) : noderef_eqb (Index.sp_node a) (Index.sp_node b) = true -> a = b.
Proof. intro H. apply specref_positional. apply noderef_eqb_spec. exact H. Qed.

Fixpoint cjr_scan {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (cs : Index.SpecRef idx Index.ConstSpecF) (k : nat)
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
  (bp : BindingPhase s) (cs : Index.SpecRef idx Index.ConstSpecF) :
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
  (bp : BindingPhase s) :
  map (fun row => projT1 row) (bp_consts bp) = const_subjects s.
Proof.
  unfold bp_consts. rewrite (proj2_sig bp). cbn [rbp_consts raw_bindings].
  unfold const_table. rewrite map_map.
  etransitivity; [ apply map_ext; intro cs; reflexivity | apply map_id ].
Qed.

Lemma bp_consts_cover {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (cs : Index.SpecRef idx Index.ConstSpecF) :
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
  (bp : BindingPhase s) (cs : Index.SpecRef idx Index.ConstSpecF) : ConstSpecJudgmentRef bp cs :=
  (match cjr_scan bp cs 0 (bp_consts bp) eq_refl as o
         return cjr_scan bp cs 0 (bp_consts bp) eq_refl = o -> ConstSpecJudgmentRef bp cs with
   | Some r => fun _ => r
   | None => fun E =>
       False_rect _ (cjr_scan_finds bp cs (bp_consts bp) 0 eq_refl (bp_consts_cover bp cs) E)
   end) eq_refl.

(* the exact phase-owned transition ref: one exact retained trace row for one exact phase and statement *)
Record ShortTransitionRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (st : Index.ShortStmtRef idx) : Type := mk_str {
  str_ord : nat ;
  str_row : { st' : Index.ShortStmtRef idx & ShortTransition (s := s) st' } ;
  str_at  : nth_error (bp_shorts bp) str_ord = Some str_row ;
  str_subject : projT1 str_row = st
}.
Arguments mk_str {p idx s bp st} _ _ _ _.
Arguments str_ord {p idx s bp st} _.
Arguments str_row {p idx s bp st} _.
Arguments str_at {p idx s bp st} _.
Arguments str_subject {p idx s bp st} _.

Lemma shortref_of_nodes {p} {idx : Index.ProgramIndex p}
  (a b : Index.ShortStmtRef idx) : noderef_eqb (Index.sh_node a) (Index.sh_node b) = true -> a = b.
Proof. intro H. apply shortstmtref_positional. apply noderef_eqb_spec. exact H. Qed.

Fixpoint str_scan {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (st : Index.ShortStmtRef idx) (k : nat)
  (l : list { st' : Index.ShortStmtRef idx & ShortTransition (s := s) st' }) {struct l}
  : l = skipn k (bp_shorts bp) -> option (ShortTransitionRef bp st) :=
  match l with
  | [] => fun _ => None
  | row :: rest => fun E =>
      match Bool.bool_dec (noderef_eqb (Index.sh_node (projT1 row)) (Index.sh_node st)) true with
      | left Hb => Some (mk_str k row (Index.skipn_head_at (bp_shorts bp) rest k row E)
                                (shortref_of_nodes (projT1 row) st Hb))
      | right _ => str_scan bp st (S k) rest (Index.skipn_tail_at (bp_shorts bp) rest k row E)
      end
  end.

Lemma str_scan_finds {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (st : Index.ShortStmtRef idx) :
  forall l k (E : l = skipn k (bp_shorts bp)),
  (exists row, In row l /\ Index.sh_node (projT1 row) = Index.sh_node st) ->
  str_scan bp st k l E <> None.
Proof.
  induction l as [|row rest IH]; intros k E [row0 [Hin Hnode]]; [ destruct Hin |].
  cbn. destruct (Bool.bool_dec (noderef_eqb (Index.sh_node (projT1 row)) (Index.sh_node st)) true)
    as [|Hne]; [ discriminate |].
  destruct Hin as [Hhead|Hin].
  - exfalso. apply Hne. subst row0. apply noderef_eqb_spec. exact Hnode.
  - apply (IH (S k) (Index.skipn_tail_at (bp_shorts bp) rest k row E)).
    exists row0. split; [ exact Hin | exact Hnode ].
Qed.

(* the retained trace is exactly the canonical trace: the phase pin names the one builder *)
Lemma bp_shorts_trace {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) : bp_shorts bp = short_trace s.
Proof. unfold bp_shorts. rewrite (proj2_sig bp). reflexivity. Qed.

Lemma bp_shorts_cover {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (st : Index.ShortStmtRef idx) :
  exists row, In row (bp_shorts bp) /\ Index.sh_node (projT1 row) = Index.sh_node st.
Proof. rewrite bp_shorts_trace. exact (short_trace_cover s st). Qed.

(* the sole ordinary transition lookup: total, returning the exact retained phase row *)
Definition short_transition {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (st : Index.ShortStmtRef idx) : ShortTransitionRef bp st :=
  (match str_scan bp st 0 (bp_shorts bp) eq_refl as o
         return str_scan bp st 0 (bp_shorts bp) eq_refl = o -> ShortTransitionRef bp st with
   | Some r => fun _ => r
   | None => fun E =>
       False_rect _ (str_scan_finds bp st (bp_shorts bp) 0 eq_refl (bp_shorts_cover bp st) E)
   end) eq_refl.

(* the exact left-judgment lookup within a retained short judgment, total below the left count *)
Fixpoint slj_scan {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {env : list (Est s)} {st : Index.ShortStmtRef idx} (i : nat)
  (l : list { i0 : nat & ShortLhsJudgment env st i0 }) {struct l}
  : option (ShortLhsJudgment env st i) :=
  match l with
  | [] => None
  | existT _ i0 j :: rest =>
      match Nat.eq_dec i0 i with
      | left He => Some (eq_rect i0 (fun i1 => ShortLhsJudgment env st i1) j i He)
      | right _ => slj_scan i rest
      end
  end.

Lemma slj_scan_finds {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {env : list (Est s)} {st : Index.ShortStmtRef idx} (i : nat) :
  forall l, In i (map (@projT1 _ _) l) -> slj_scan (env := env) (st := st) i l <> None.
Proof.
  induction l as [|[i0 j] rest IH]; intro Hin; [ destruct Hin |].
  cbn. destruct (Nat.eq_dec i0 i) as [|Hne]; [ discriminate |].
  destruct Hin as [Hhead|Hin]; [ exfalso; apply Hne; exact Hhead | exact (IH Hin) ].
Qed.

Definition short_lhs_judgment {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {env : list (Est s)} {st : Index.ShortStmtRef idx} (sj : ShortJudgment env st)
  (i : nat) (H : i < Index.sh_names st) : ShortLhsJudgment env st i :=
  (match slj_scan i (sj_lefts sj) as o return slj_scan i (sj_lefts sj) = o -> _ with
   | Some j => fun _ => j
   | None => fun E =>
       False_rect _ (slj_scan_finds i (sj_lefts sj)
                       (eq_ind_r (fun m => In i m) (in_seq_intro i (Index.sh_names st) H) (sj_lefts_ok sj)) E)
   end) eq_refl.


Definition package_main {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (pr : PI.PackageRef s) : MainStatus s pr := main_status_of (bp_ests bp) pr.

(* the main status is exactly the projection of the retained establishments over that package *)
Theorem package_main_sound {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (pr : PI.PackageRef s) :
  main_status_ests (package_main bp pr) = main_ests_of (bp_ests bp) pr.
Proof. unfold package_main. apply main_status_ests_of. Qed.

(* every main declaration in the status is a package-scope function declaration of that package *)
Lemma main_is_package_local {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (pr : PI.PackageRef s) :
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

Definition contains_visible {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (e : Est s) (u : Index.NodeRef idx) : bool :=
  match est_scope e with
  | PackageScope pr => PI.packageref_eqb (PI.package_of_file s (Index.nr_file u)) pr
  | BlockScope br =>
      andb (Index.fileref_eqb (Index.nr_file (Index.bl_node br)) (Index.nr_file u))
      (andb (Nat.ltb (Index.nr_pos (Index.bl_node br)) (Index.nr_pos u))
      (andb (Nat.leb (Index.nr_pos u) (Index.node_extent (Index.bl_node br)))
            (Nat.ltb (est_vstart e) (Index.nr_pos u))))
  end.

Definition source_cands {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) : list (Est s) :=
  filter (fun e => andb (Names.ordinary_equalb (est_name e) n) (contains_visible e u)) (bp_ests bp).

(* prefer the innermost (block) binding; else any match; else no source binding *)
Definition pick_best {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (cands : list (Est s)) : option (Est s) :=
  match find is_block_scoped cands with Some e => Some e | None => hd_error cands end.

Lemma pick_best_in {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (l : list (Est s)) (e : Est s) : pick_best l = Some e -> In e l.
Proof.
  unfold pick_best. destruct (find is_block_scoped l) as [x|] eqn:Ef.
  - intro H; injection H as <-. apply find_some in Ef. destruct Ef as [Hin _]; exact Hin.
  - destruct l as [|y ys]; intro H; [ discriminate H | cbn in H; injection H as <-; left; reflexivity ].
Qed.
Lemma pick_best_none {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (l : list (Est s)) : pick_best l = None -> l = [].
Proof.
  unfold pick_best. destruct (find is_block_scoped l) eqn:Ef; [ discriminate |].
  destruct l as [|y ys]; [ reflexivity | cbn; discriminate ].
Qed.

(* the ordered members of e's group in the retained phase, in bp_ests source order *)
Definition group_members {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (e : Est s) : list (Est s) := group_members_core (bp_ests bp) e.

(* the declaration members of e's group; a redeclared declaration group is an ambiguous name *)
Definition decl_group {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (e : Est s) : list (Est s) := decl_group_core (bp_ests bp) e.
Definition decl_ambiguous {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (e : Est s) : bool :=
  andb (is_decl_est e)
       (match group_status (decl_group bp e) with Some (GRedeclared _ _ _) => true | _ => false end).

(* the exact canonical declaration group: its shared scope and spelling, and its ordered declaration members *)
Record DeclarationGroupRef {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type := mk_decl_group {
  dg_scope   : ScopeId s ;
  dg_name    : Names.OrdinaryIdentifier ;
  dg_members : list (Est s)
}.
Arguments mk_decl_group {p idx s} _ _ _.
Arguments dg_scope {p idx s} _.
Arguments dg_name {p idx s} _.
Arguments dg_members {p idx s} _.

Definition decl_group_ref {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (e : Est s) : DeclarationGroupRef s :=
  mk_decl_group (est_scope e) (est_name e) (decl_group bp e).

Inductive Resolved {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (use : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) : Type :=
| RBound      : ObjectRef idx -> Resolved bp use n
| RRedeclared : DeclarationGroupRef s -> Resolved bp use n
| RUnbound    : Resolved bp use n.
Arguments RBound {p idx s bp use n} _.
Arguments RRedeclared {p idx s bp use n} _.
Arguments RUnbound {p idx s bp use n}.

(* resolution: one group authority; nearest binding shadows; a redeclared group is ambiguous; main no special route *)
Definition resolve {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (use : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) : Resolved bp use n :=
  match pick_best (source_cands bp use n) with
  | Some e => if decl_ambiguous bp e then RRedeclared (decl_group_ref bp e) else RBound (SourceObject (est_origin e))
  | None =>
      match Names.classify_predeclared (Names.ordinary_spelling n) with
      | Some pn => RBound (PredeclaredObject pn)
      | None => RUnbound
      end
  end.

Definition resolved_query {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {bp : BindingPhase s} {use : Index.NodeRef idx} {n : Names.OrdinaryIdentifier}
  (_ : Resolved bp use n) : Index.NodeRef idx * Names.OrdinaryIdentifier := (use, n).

Lemma resolve_retains_query {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (use : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) :
  resolved_query (resolve bp use n) = (use, n).
Proof. reflexivity. Qed.

Theorem resolve_exact {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (use : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) :
  match resolve bp use n with
  | RBound (SourceObject o) =>
      exists e, In e (source_cands bp use n) /\ est_origin e = o /\ decl_ambiguous bp e = false
  | RBound (PredeclaredObject pn) =>
      source_cands bp use n = [] /\ Names.classify_predeclared (Names.ordinary_spelling n) = Some pn
  | RRedeclared g =>
      exists e, pick_best (source_cands bp use n) = Some e /\ decl_ambiguous bp e = true /\ g = decl_group_ref bp e
  | RUnbound =>
      source_cands bp use n = [] /\ Names.classify_predeclared (Names.ordinary_spelling n) = None
  end.
Proof.
  unfold resolve. destruct (pick_best (source_cands bp use n)) as [e|] eqn:E.
  - destruct (decl_ambiguous bp e) eqn:Ea.
    + exists e; split; [ reflexivity | split; [ exact Ea | reflexivity ] ].
    + exists e; split; [ apply pick_best_in; exact E | split; [ reflexivity | exact Ea ] ].
  - pose proof (pick_best_none _ E) as Hnil.
    destruct (Names.classify_predeclared (Names.ordinary_spelling n)) eqn:Ec; split; try exact Hnil; try reflexivity.
Qed.




(* the canonical complete new-nonblank summary: exactly the retained ShortNew left judgments, in order *)
Definition short_new_members {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {env : list (Est s)} {st : Index.ShortStmtRef idx} (sj : ShortJudgment env st)
  : list { i : nat & ShortLhsJudgment env st i } :=
  filter (fun x => match slj_view (projT2 x) with SVNew _ => true | _ => false end) (sj_lefts sj).

(* the first duplicate short-left name, projected from the exact retained judgment views *)
Definition sj_dup_name {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {env : list (Est s)} {st : Index.ShortStmtRef idx} (sj : ShortJudgment env st)
  : option Names.OrdinaryIdentifier :=
  fold_right (fun x acc =>
                match slj_view (projT2 x) with
                | SVDuplicate _ => binder_ident (Index.sl_child (slj_edge (projT2 x)))
                | _ => acc
                end)
             None (sj_lefts sj).

(* the exact pre-statement cutpoint: the statement's own retained position, projected from the ref *)
Definition sj_cutpoint {p} {idx : Index.ProgramIndex p} (st : Index.ShortStmtRef idx) : nat :=
  Index.nr_pos (Index.sh_node st).

(* the phase-level duplicate projection: the retained transition row's judgment, never a recomputation *)
Definition short_stmt_dup_name {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (st : Index.ShortStmtRef idx) : option Names.OrdinaryIdentifier :=
  sj_dup_name (tr_judgment (projT2 (str_row (short_transition bp st)))).

(* a Some binder identity pins the exact named binding view *)
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

(* the blank law: a blank classification pins exactly a blank identifier, in both directions *)
Lemma slj_blank_exact {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) {st : Index.ShortStmtRef idx} {i : nat} (e : Index.ShortLhsEdge st i) :
  short_lhs_decide env e = SVBlank <-> binder_ident (Index.sl_child e) = None.
Proof.
  unfold short_lhs_decide. split.
  - intro Hd.
    destruct (binder_ident (Index.sl_child e)) as [n|] eqn:Hb; [| reflexivity ].
    exfalso.
    destruct (find_dup i n (Index.short_lhs_edges st)) as [[j w]|]; [ discriminate Hd |].
    destruct (filter (fun e2 => andb (same_block_cand n e2) (is_decl_est e2)) env)
      as [|a [|c rest]]; [ | | discriminate Hd ];
      (destruct (env_scan env (same_block_cand n) 0 env eq_refl) as [prior|];
       [ destruct (is_variable_binder (est_node (er_est prior))); discriminate Hd | discriminate Hd ]).
  - intro Hb. rewrite Hb. reflexivity.
Qed.

(* the duplicate law: an exact same-name earlier left exists at the retained witness index *)
Lemma slj_dup_exact {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) {st : Index.ShortStmtRef idx} {i : nat} (e : Index.ShortLhsEdge st i)
  (j : nat) :
  short_lhs_decide env e = SVDuplicate j ->
  exists n w, binder_ident (Index.sl_child e) = Some n
              /\ find_dup i n (Index.short_lhs_edges st) = Some (existT _ j w).
Proof.
  intro Hd. unfold short_lhs_decide in Hd.
  destruct (binder_ident (Index.sl_child e)) as [n|] eqn:Hb; [| discriminate Hd ].
  destruct (find_dup i n (Index.short_lhs_edges st)) as [[j0 w]|] eqn:Hdup.
  - injection Hd as <-. exists n, w. split; [ reflexivity | exact Hdup ].
  - exfalso.
    destruct (filter (fun e2 => andb (same_block_cand n e2) (is_decl_est e2)) env)
      as [|a [|c rest]]; [ | | discriminate Hd ];
      (destruct (env_scan env (same_block_cand n) 0 env eq_refl) as [prior|];
       [ destruct (is_variable_binder (est_node (er_est prior))); discriminate Hd | discriminate Hd ]).
Qed.

(* the new law: named, no same-statement duplicate, and no same-block match in the pre-environment *)
Lemma slj_new_exact {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) {st : Index.ShortStmtRef idx} {i : nat} (e : Index.ShortLhsEdge st i)
  (n : Names.OrdinaryIdentifier) :
  short_lhs_decide env e = SVNew n ->
  binder_ident (Index.sl_child e) = Some n
  /\ find_dup i n (Index.short_lhs_edges st) = None
  /\ (forall x, In x env -> same_block_cand n x = false).
Proof.
  intro Hd. unfold short_lhs_decide in Hd.
  destruct (binder_ident (Index.sl_child e)) as [n0|] eqn:Hb; [| discriminate Hd ].
  destruct (find_dup i n0 (Index.short_lhs_edges st)) as [[j w]|] eqn:Hdup; [ discriminate Hd |].
  destruct (filter (fun e2 => andb (same_block_cand n0 e2) (is_decl_est e2)) env)
    as [|a [|c rest]] eqn:Hfil; [ | | discriminate Hd ];
    (destruct (env_scan env (same_block_cand n0) 0 env eq_refl) as [prior|] eqn:Hscan;
     [ destruct (is_variable_binder (est_node (er_est prior))); discriminate Hd |]);
    injection Hd as <-;
    (split; [ reflexivity | split; [ exact Hdup |] ]);
    intros x Hin; exact (env_scan_none env (same_block_cand n0) env 0 eq_refl Hscan x Hin).
Qed.

(* the existing laws: the prior is the exact earliest same-block member reference, of the exact kind *)
Lemma slj_existing_exact {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) {st : Index.ShortStmtRef idx} {i : nat} (e : Index.ShortLhsEdge st i)
  (prior : EnvEstRef env) (isvar : bool) :
  short_lhs_decide env e
  = (if isvar then SVExistingVariable prior else SVExistingNonVariable prior) ->
  exists n, binder_ident (Index.sl_child e) = Some n
  /\ find_dup i n (Index.short_lhs_edges st) = None
  /\ same_block_cand n (er_est prior) = true
  /\ (forall j x, j < er_ord prior -> nth_error env j = Some x -> same_block_cand n x = false)
  /\ is_variable_binder (est_node (er_est prior)) = isvar.
Proof.
  intro Hd. unfold short_lhs_decide in Hd.
  destruct (binder_ident (Index.sl_child e)) as [n|] eqn:Hb; [| destruct isvar; discriminate Hd ].
  destruct (find_dup i n (Index.short_lhs_edges st)) as [[j w]|] eqn:Hdup;
    [ destruct isvar; discriminate Hd |].
  destruct (filter (fun e2 => andb (same_block_cand n e2) (is_decl_est e2)) env)
    as [|a [|c rest]]; [ | | destruct isvar; discriminate Hd ];
    (destruct (env_scan env (same_block_cand n) 0 env eq_refl) as [prior0|] eqn:Hscan;
     [| destruct isvar; discriminate Hd ]);
    (destruct (env_scan_found env (same_block_cand n) env 0 eq_refl prior0 Hscan)
      as [Hcand [_ Hbefore]]);
    (destruct (is_variable_binder (est_node (er_est prior0))) eqn:Hvar; destruct isvar;
     try discriminate Hd; injection Hd as <-; exists n;
     (split; [ reflexivity |
       split; [ exact Hdup |
         split; [ exact Hcand |
           split; [ intros j x Hj Hnth; exact (Hbefore j x (Nat.le_0_l j) Hj Hnth)
                  | exact Hvar ] ] ] ])).
Qed.

(* the ambiguity law: the exact canonical redeclared declaration group over the pre-environment *)
Lemma slj_ambiguous_exact {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (env : list (Est s)) {st : Index.ShortStmtRef idx} {i : nat} (e : Index.ShortLhsEdge st i)
  (a c : Est s) (rest : list (Est s)) :
  short_lhs_decide env e = SVAmbiguous a c rest ->
  exists n, binder_ident (Index.sl_child e) = Some n
  /\ find_dup i n (Index.short_lhs_edges st) = None
  /\ filter (fun e2 => andb (same_block_cand n e2) (is_decl_est e2)) env = a :: c :: rest.
Proof.
  intro Hd. unfold short_lhs_decide in Hd.
  destruct (binder_ident (Index.sl_child e)) as [n|] eqn:Hb; [| discriminate Hd ].
  destruct (find_dup i n (Index.short_lhs_edges st)) as [[j w]|] eqn:Hdup; [ discriminate Hd |].
  destruct (filter (fun e2 => andb (same_block_cand n e2) (is_decl_est e2)) env)
    as [|a0 [|c0 rest0]] eqn:Hfil;
    try ((destruct (env_scan env (same_block_cand n) 0 env eq_refl) as [prior|];
          [ destruct (is_variable_binder (est_node (er_est prior))); discriminate Hd
          | discriminate Hd ])).
  injection Hd as <- <- <-. exists n. split; [ reflexivity | split; [ exact Hdup | exact Hfil ] ].
Qed.

(* find_dup selects the exact earliest matching earlier left: no smaller in-range index matches *)
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

(* no alternative classification can inhabit the same environment, statement, and left index *)
Lemma slj_canonical {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {env : list (Est s)} {st : Index.ShortStmtRef idx} {i : nat}
  (j1 j2 : ShortLhsJudgment env st i) :
  slj_edge j1 = slj_edge j2 /\ slj_view j1 = slj_view j2.
Proof.
  assert (E : slj_edge j1 = slj_edge j2) by apply shortlhsedge_unique.
  split; [ exact E |].
  rewrite (slj_ok j1), (slj_ok j2), E. reflexivity.
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

(* the trace's subject occurrences are duplicate-free: one exact transition per source statement *)
Lemma short_trace_nodes_nodup {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) :
  NoDup (map (fun row => Index.sh_node (projT1 row)) (short_trace s)).
Proof.
  unfold short_trace. rewrite map_flat_map.
  apply (flat_map_nodup _ (fun r0 => PI.package_of_file s (Index.nr_file r0)));
    [ apply packages_nodup | |].
  - intros pr _. rewrite map_flat_map.
    apply (flat_map_nodup _ (fun r0 => Index.nr_file r0));
      [ apply pkg_members_nodup | |].
    + intros fr _. unfold short_rows_of_file. rewrite map_flat_map.
      apply (flat_map_nodup _ (fun r0 => Index.nr_pos r0));
        [ apply seq_NoDup | |].
      * intros pos _. destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|]; [| constructor ].
        apply short_row_emit_nodes_nodup.
      * intros pos r0 _ Hin.
        destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
        apply in_map_iff in Hin. destruct Hin as [row [Hf Hrow]].
        rewrite <- Hf. rewrite (short_row_emit_node r _ _ row Hrow).
        exact (noderef_pos_of_key r pos (mk_noderef_key fr _ r Hmk)).
    + intros fr r0 _ Hin.
      apply in_map_iff in Hin. destruct Hin as [row [Hf Hrow]].
      unfold short_rows_of_file in Hrow. apply in_flat_map in Hrow.
      destruct Hrow as [pos [_ Hrow]].
      destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hrow ].
      rewrite <- Hf. rewrite (short_row_emit_node r _ _ row Hrow).
      exact (Index.mk_noderef_file fr _ r Hmk).
  - intros pr r0 Hpr Hin.
    apply in_map_iff in Hin. destruct Hin as [row [Hf Hrow]].
    apply in_flat_map in Hrow. destruct Hrow as [fr [Hfr Hrow]].
    unfold short_rows_of_file in Hrow. apply in_flat_map in Hrow.
    destruct Hrow as [pos [_ Hrow]].
    destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hrow ].
    rewrite <- Hf. rewrite (short_row_emit_node r _ _ row Hrow).
    rewrite (Index.mk_noderef_file fr _ r Hmk).
    exact (PI.package_of_file_member s pr fr Hfr).
Qed.

(* each const subject appears exactly once: two table rows sharing a subject share the ordinal *)
Lemma bp_consts_exactly_once {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (o1 o2 : nat)
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

(* each short subject appears exactly once: two trace rows sharing a subject share the ordinal *)
Lemma bp_shorts_exactly_once {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (o1 o2 : nat)
  (row1 row2 : { st : Index.ShortStmtRef idx & ShortTransition (s := s) st }) :
  nth_error (bp_shorts bp) o1 = Some row1 -> nth_error (bp_shorts bp) o2 = Some row2 ->
  projT1 row1 = projT1 row2 -> o1 = o2.
Proof.
  intros H1 H2 He.
  assert (Hnd : NoDup (map (fun row => Index.sh_node (projT1 row)) (bp_shorts bp)))
    by (rewrite bp_shorts_trace; apply short_trace_nodes_nodup).
  assert (Hm1 : nth_error (map (fun row => Index.sh_node (projT1 row)) (bp_shorts bp)) o1
                = Some (Index.sh_node (projT1 row1)))
    by (exact (map_nth_error _ o1 _ H1)).
  assert (Hm2 : nth_error (map (fun row => Index.sh_node (projT1 row)) (bp_shorts bp)) o2
                = Some (Index.sh_node (projT1 row2)))
    by (exact (map_nth_error _ o2 _ H2)).
  apply (proj1 (NoDup_nth_error _) Hnd o1 o2).
  - apply nth_error_Some. rewrite Hm1. discriminate.
  - rewrite Hm1, Hm2, He. reflexivity.
Qed.

(* a keyed disjoint flat_map of per-item duplicate-free blocks is duplicate-free *)
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

(* a judgment's additions: exactly one exact new establishment per ShortNew left *)
Lemma new_ests_member {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) {env : list (Est s)} {st : Index.ShortStmtRef idx}
  (sj : ShortJudgment env st) (e : Est s) :
  In e (new_ests br sj) ->
  exists x n, In x (sj_lefts sj) /\ slj_view (projT2 x) = SVNew n
              /\ e = new_est br (slj_edge (projT2 x)) n.
Proof.
  intro Hin. unfold new_ests in Hin. apply in_flat_map in Hin.
  destruct Hin as [x [Hx Hin]].
  destruct (slj_view (projT2 x)) as [| |n| | |] eqn:Hv; try (exact (match Hin with end)).
  destruct Hin as [He|F]; [| destruct F ].
  exists x, n. split; [ exact Hx |]. split; [ exact Hv | rewrite <- He; reflexivity ].
Qed.

Lemma new_ests_complete {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) {env : list (Est s)} {st : Index.ShortStmtRef idx}
  (sj : ShortJudgment env st) (x : { i : nat & ShortLhsJudgment env st i })
  (n : Names.OrdinaryIdentifier) :
  In x (sj_lefts sj) -> slj_view (projT2 x) = SVNew n ->
  In (new_est br (slj_edge (projT2 x)) n) (new_ests br sj).
Proof.
  intros Hx Hv. unfold new_ests. apply in_flat_map. exists x. split; [ exact Hx |].
  rewrite Hv. left. reflexivity.
Qed.

(* the transition's additions are duplicate-free, keyed by their exact left index *)
Lemma new_ests_nodup {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) {env : list (Est s)} {st : Index.ShortStmtRef idx}
  (sj : ShortJudgment env st) : NoDup (new_ests br sj).
Proof.
  unfold new_ests.
  apply (flat_map_nodup_key _ (fun e => match est_origin e with DOShort sn => snr_ix sn | _ => 0 end)
           (@projT1 _ _)).
  - rewrite (sj_lefts_ok sj). apply seq_NoDup.
  - intros x _. destruct (slj_view (projT2 x)); repeat constructor; intros F; destruct F.
  - intros x e _ Hin. destruct (slj_view (projT2 x)); try (exact (match Hin with end)).
    destruct Hin as [He|F]; [| destruct F ]. rewrite <- He. reflexivity.
Qed.

(* the establishments emitted at one occurrence name it as their exact governing site *)
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

Lemma tr_added_site {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {st : Index.ShortStmtRef idx} (t : ShortTransition (s := s) st) (e : Est s) :
  In e (tr_added t) -> est_site e = Some (Index.sh_node st).
Proof.
  intro Hin. rewrite (tr_added_ok t) in Hin.
  destruct (new_ests_member _ _ _ Hin) as [x [n [_ [_ He]]]].
  rewrite He. unfold est_site. cbn.
  exact (Index.sl_parent (slj_edge (projT2 x))).
Qed.

Lemma node_ests_site {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.NodeRef idx) (v : Index.NodeView)
  (Hv : Index.node_view r = v) (e : Est s) :
  In e (node_ests pr r v Hv) -> est_site e = Some r.
Proof.
  destruct v; cbn; try (intros F; exact (match F with end)).
  - match goal with sh0 : Index.StmtShape |- _ => destruct sh0 end;
      try (intros F; exact (match F with end)).
    + destruct (Index.node_parent r) as [par|]; [| intros F; exact (match F with end) ].
      destruct (block_scope_of (s := s) par) as [sc|];
        [| intros F; exact (match F with end) ].
      apply stmt_decl_ests_site.
    + intro Hin. exact (tr_added_site _ e Hin).
  -
    match goal with ts0 : Index.TopShape |- _ => destruct ts0 end.
    + apply stmt_decl_ests_site.
    + destruct (make_main_est pr r) as [e0|] eqn:Hm; [| intros F; exact (match F with end) ].
      intros [He|F]; [| destruct F ]. subst e0.
      destruct (make_main_est_some pr r e Hm) as [[f Hor] [Hnode _]].
      unfold est_site. rewrite Hor, Hnode. reflexivity.
Qed.

(* one occurrence's emission is duplicate-free *)
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

Lemma node_ests_nodup {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.NodeRef idx) (v : Index.NodeView)
  (Hv : Index.node_view r = v) : NoDup (node_ests pr r v Hv).
Proof.
  destruct v; cbn; try constructor.
  - match goal with sh0 : Index.StmtShape |- _ => destruct sh0 end; try constructor.
    + destruct (Index.node_parent r) as [par|]; [| constructor ].
      destruct (block_scope_of (s := s) par) as [sc|]; [ apply stmt_decl_ests_nodup | constructor ].
    + rewrite (tr_added_ok _). apply new_ests_nodup.
  - match goal with ts0 : Index.TopShape |- _ => destruct ts0 end.
    + apply stmt_decl_ests_nodup.
    + destruct (make_main_est pr r); repeat constructor; intros F; destruct F.
Qed.

(* the surface enumeration is duplicate-free: every establishment sits at one exact site *)
Lemma actual_ests_nodup {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) :
  NoDup (actual_ests s).
Proof.
  unfold actual_ests.
  apply (flat_map_nodup_key _
           (fun e => match est_site e with
                     | Some x => PI.package_of_file s (Index.nr_file x) | None => PI.package_of_file s (Index.nr_file (est_node e)) end)
           (fun pr => pr));
    [ rewrite map_id; apply packages_nodup | |].
  - intros pr _.
    apply (flat_map_nodup_key _
             (fun e => match est_site e with
                       | Some x => Index.nr_file x | None => Index.nr_file (est_node e) end)
             (fun fr => fr));
      [ rewrite map_id; apply pkg_members_nodup | |].
    + intros fr _. unfold actual_ests_of_file.
      apply (flat_map_nodup_key _
               (fun e => match est_site e with
                         | Some x => Index.nr_pos x | None => 0 end)
               (fun pos => pos));
        [ rewrite map_id; apply seq_NoDup | |].
      * intros pos _. destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|]; [| constructor ].
        apply node_ests_nodup.
      * intros pos e _ Hin.
        destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
        rewrite (node_ests_site pr r _ _ e Hin).
        exact (noderef_pos_of_key r pos (mk_noderef_key fr _ r Hmk)).
    + intros fr e _ Hin.
      unfold actual_ests_of_file in Hin. apply in_flat_map in Hin.
      destruct Hin as [pos [_ Hin]].
      destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
      rewrite (node_ests_site pr r _ _ e Hin).
      exact (Index.mk_noderef_file fr _ r Hmk).
  - intros pr e Hpr Hin.
    apply in_flat_map in Hin. destruct Hin as [fr [Hfr Hin]].
    unfold actual_ests_of_file in Hin. apply in_flat_map in Hin.
    destruct Hin as [pos [_ Hin]].
    destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
    rewrite (node_ests_site pr r _ _ e Hin).
    rewrite (Index.mk_noderef_file fr _ r Hmk).
    exact (PI.package_of_file_member s pr fr Hfr).
Qed.

(* the phase's establishments are exactly the canonical actual enumeration *)
Lemma bp_ests_actual {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) : bp_ests bp = actual_ests s.
Proof. unfold bp_ests. rewrite (proj2_sig bp). reflexivity. Qed.

Lemma bp_ests_nodup {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) : NoDup (bp_ests bp).
Proof. rewrite bp_ests_actual. apply actual_ests_nodup. Qed.

Lemma ordinal_scan_sound {p} {idx : Index.ProgramIndex p} (par r : Index.NodeRef idx) :
  forall l o (e : Index.ChildAt par o),
  ordinal_scan par r l = Some (existT _ o e) -> Index.ca_child e = r.
Proof.
  induction l as [|[o0 e0] rest IH]; intros o e Hs; [ discriminate Hs |].
  cbn in Hs. destruct (noderef_eqb (Index.ca_child e0) r) eqn:Hb.
  - injection Hs as He1 He2. subst o0.
    apply Eqdep_dec.inj_pair2_eq_dec in He2; [| exact Nat.eq_dec ]. subst e0.
    apply noderef_eqb_spec. exact Hb.
  - exact (IH o e Hs).
Qed.

(* the canonical transition's exact block, pre-environment, and additions, at the statement's ordinal *)
Lemma short_transition_fo_eval {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (st : Index.ShortStmtRef idx) (br : Index.BlockRef idx) (k : nat)
  (ek : Index.ChildAt (Index.bl_node br) k)
  (Hp : Index.node_parent (Index.sh_node st) = Some (Index.bl_node br))
  (Hb : Index.is_block_view (Index.node_view (Index.bl_node br)) = true) :
  Index.ca_child ek = Index.sh_node st ->
  forall fo (Hf : find_ordinal (Index.bl_node br) (Index.sh_node st) = fo),
  tr_block (short_transition_fo (s := s) st (Index.bl_node br) Hp Hb fo Hf) = br
  /\ tr_pre (short_transition_fo (s := s) st (Index.bl_node br) Hp Hb fo Hf) = block_env br k
  /\ tr_added (short_transition_fo (s := s) st (Index.bl_node br) Hp Hb fo Hf)
     = new_ests br (short_judgment_of (block_env br k) st).
Proof.
  intros Hc fo Hf. destruct fo as [[o eo]|].
  2:{ exact (match stmt_ordinal_found st (Index.bl_node br) Hp Hf with end). }
  assert (Ho : o = k).
  { apply (Index.ca_ord_unique eo ek).
    rewrite (ordinal_scan_sound (Index.bl_node br) (Index.sh_node st) _ o eo Hf), Hc.
    reflexivity. }
  subst o. cbn [tr_block tr_pre tr_added short_transition_fo].
  assert (Hbr : Index.mkBlockRef (Index.bl_node br) Hb = br)
    by (apply Index.blockref_positional; reflexivity).
  rewrite Hbr. split; [ reflexivity | split; reflexivity ].
Qed.

Lemma short_transition_of_eval {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (st : Index.ShortStmtRef idx) (br : Index.BlockRef idx) (k : nat)
  (ek : Index.ChildAt (Index.bl_node br) k) :
  Index.ca_child ek = Index.sh_node st ->
  tr_block (short_transition_of (s := s) st) = br
  /\ tr_pre (short_transition_of (s := s) st) = block_env br k
  /\ tr_added (short_transition_of (s := s) st)
     = new_ests br (short_judgment_of (block_env br k) st).
Proof.
  intro Hc.
  assert (Hp : Index.node_parent (Index.sh_node st) = Some (Index.bl_node br))
    by (rewrite <- Hc; apply Index.ca_node_parent).
  unfold short_transition_of.
  assert (Haux : forall op (Hop : Index.node_parent (Index.sh_node st) = op),
    tr_block (short_transition_at (s := s) st op Hop) = br
    /\ tr_pre (short_transition_at (s := s) st op Hop) = block_env br k
    /\ tr_added (short_transition_at (s := s) st op Hop)
       = new_ests br (short_judgment_of (block_env br k) st)).
  { intros op Hop. destruct op as [par|].
    2:{ exact (match stmt_has_parent st Hop with end). }
    assert (Hpar : par = Index.bl_node br)
      by (pose proof (eq_trans (eq_sym Hop) Hp) as He; injection He as He; exact He).
    subst par. cbn [short_transition_at].
    assert (Haux2 : forall bv (Hbv : Index.is_block_view (Index.node_view (Index.bl_node br)) = bv),
      tr_block (short_transition_bv (s := s) st (Index.bl_node br) Hop bv Hbv) = br
      /\ tr_pre (short_transition_bv (s := s) st (Index.bl_node br) Hop bv Hbv) = block_env br k
      /\ tr_added (short_transition_bv (s := s) st (Index.bl_node br) Hop bv Hbv)
         = new_ests br (short_judgment_of (block_env br k) st)).
    { intros bv Hbv. destruct bv.
      2:{ exact (match stmt_parent_not_block st (Index.bl_node br) Hop Hbv with end). }
      cbn [short_transition_bv].
      exact (short_transition_fo_eval st br k ek Hop Hbv Hc _ eq_refl). }
    exact (Haux2 _ eq_refl). }
  exact (Haux _ eq_refl).
Qed.

(* the short child's contribution is exactly its canonical transition's additions *)
Lemma child_contrib_short {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) {k : nat} (e : Index.ChildAt (Index.bl_node br) k)
  (env : list (Est s)) (nn nv : nat)
  (Hv : Index.node_view (Index.ca_child e) = Index.VStmt (Index.SSShort nn nv)) :
  child_contrib br e env _ Hv
  = new_ests br (short_judgment_of env (Index.mkShortStmtRef (Index.ca_child e) nn nv Hv)).
Proof. reflexivity. Qed.

Lemma block_env_step {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) (k : nat) :
  block_env (s := s) br (S k)
  = block_env br k
    ++ match Index.child_at_opt (Index.bl_node br) k with
       | Some e => child_contrib br e (block_env br k) (Index.node_view (Index.ca_child e)) eq_refl
       | None => [] end.
Proof. reflexivity. Qed.

(* the short-child contribution, evaluated at the exact known view *)
Lemma child_contrib_short_eval {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) {k : nat} (e : Index.ChildAt (Index.bl_node br) k)
  (env : list (Est s)) (v : Index.NodeView) (Hv : Index.node_view (Index.ca_child e) = v)
  (nn nv : nat) :
  v = Index.VStmt (Index.SSShort nn nv) ->
  exists Hv0 : Index.node_view (Index.ca_child e) = Index.VStmt (Index.SSShort nn nv),
    child_contrib br e env v Hv
    = new_ests br (short_judgment_of env (Index.mkShortStmtRef (Index.ca_child e) nn nv Hv0)).
Proof. intro E. revert Hv. subst v. intro Hv. exists Hv. reflexivity. Qed.

(* the exact one-step law for a short child: the next environment appends its transition's additions *)
Lemma block_env_step_short {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) (k : nat) (ek : Index.ChildAt (Index.bl_node br) k)
  (st : Index.ShortStmtRef idx) :
  Index.ca_child ek = Index.sh_node st ->
  block_env (s := s) br (S k) = block_env br k ++ tr_added (short_transition_of (s := s) st).
Proof.
  intro Hc. rewrite block_env_step.
  destruct (Index.child_at_opt (Index.bl_node br) k) as [e|] eqn:Ho;
    [| exact (match Index.child_at_opt_some _ _ ek Ho with end) ].
  assert (Hce : Index.ca_child e = Index.sh_node st)
    by (rewrite (Index.ca_det e ek); exact Hc).
  f_equal.
  assert (Hview : Index.node_view (Index.ca_child e)
                  = Index.VStmt (Index.SSShort (Index.sh_names st) (Index.sh_values st)))
    by (rewrite Hce; exact (Index.sh_ok st)).
  destruct (child_contrib_short_eval (s := s) br e (block_env br k) _ eq_refl
              (Index.sh_names st) (Index.sh_values st) Hview) as [Hv0 Hcc].
  rewrite Hcc.
  assert (Hst : Index.mkShortStmtRef (Index.ca_child e) (Index.sh_names st) (Index.sh_values st) Hv0 = st)
    by (apply shortstmtref_positional; exact Hce).
  rewrite Hst.
  destruct (short_transition_of_eval (s := s) st br k ek Hc) as [_ [_ Hadded]].
  rewrite Hadded. reflexivity.
Qed.

(* environment growth is monotone: earlier members keep their exact ordinals *)
Lemma block_env_grows {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) (k1 k2 : nat) :
  k1 <= k2 ->
  forall j x, nth_error (block_env (s := s) br k1) j = Some x ->
              nth_error (block_env br k2) j = Some x.
Proof.
  induction k2 as [|k2' IH]; intros Hle j x Hnth.
  - assert (k1 = 0) by lia. subst k1. exact Hnth.
  - destruct (Nat.eq_dec k1 (S k2')) as [->|Hne]; [ exact Hnth |].
    assert (Hle' : k1 <= k2') by lia.
    rewrite block_env_step. rewrite nth_error_app1; [ exact (IH Hle' j x Hnth) |].
    apply nth_error_Some. rewrite (IH Hle' j x Hnth). discriminate.
Qed.

Lemma block_env_incl {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) (k1 k2 : nat) :
  k1 <= k2 -> incl (block_env (s := s) br k1) (block_env br k2).
Proof.
  intros Hle x Hin.
  destruct (In_nth_error _ _ Hin) as [j Hj].
  exact (nth_error_In _ _ (block_env_grows br k1 k2 Hle j x Hj)).
Qed.

(* every prior short child's exact additions are members of every later environment *)
Lemma earlier_news_in_env {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) (k1 k2 : nat) (ek : Index.ChildAt (Index.bl_node br) k1)
  (st : Index.ShortStmtRef idx) :
  Index.ca_child ek = Index.sh_node st -> k1 < k2 ->
  incl (tr_added (short_transition_of (s := s) st)) (block_env br k2).
Proof.
  intros Hc Hlt x Hin.
  apply (block_env_incl br (S k1) k2 Hlt).
  rewrite (block_env_step_short br k1 ek st Hc).
  apply in_or_app. right. exact Hin.
Qed.

Lemma node_pkg_ests_member {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.NodeRef idx) (e : Est s) :
  In e (node_pkg_ests pr r) ->
  est_scope e = PackageScope pr
  /\ match est_origin e with DOShort _ => False | _ => True end.
Proof.
  unfold node_pkg_ests.
  destruct (Index.node_view r) as [| | | | | | | | | | | |ts|]; try (intros F; exact (match F with end)).
  destruct ts.
  - intro Hin. destruct (stmt_decl_ests_member _ _ _ Hin) as [Hsc [[b Hor] _]].
    split; [ exact Hsc | rewrite Hor; exact I ].
  - destruct (make_main_est pr r) as [e0|] eqn:Hm; [| intros F; exact (match F with end) ].
    intros [He|F]; [| destruct F ]. subst e0.
    destruct (make_main_est_some pr r e Hm) as [[f Hor] [_ [Hsc _]]].
    split; [ exact Hsc | rewrite Hor; exact I ].
Qed.

Lemma pkg_ests_member {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) (e : Est s) :
  In e (pkg_ests s) ->
  (exists pr, est_scope e = PackageScope pr)
  /\ match est_origin e with DOShort _ => False | _ => True end.
Proof.
  intro Hin. unfold pkg_ests in Hin.
  apply in_flat_map in Hin. destruct Hin as [pr [_ Hin]].
  apply in_flat_map in Hin. destruct Hin as [fr [_ Hin]].
  apply in_flat_map in Hin. destruct Hin as [pos [_ Hin]].
  destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|]; [| destruct Hin ].
  destruct (node_pkg_ests_member pr r e Hin) as [Hsc Hor].
  split; [ exists pr; exact Hsc | exact Hor ].
Qed.

Lemma block_base_member {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) (e : Est s) :
  In e (block_base s br) ->
  In e (pkg_ests s)
  /\ (exists pr, est_scope e = PackageScope pr
        /\ PI.packageref_eqb (PI.package_of_file s (Index.nr_file (Index.bl_node br))) pr = true).
Proof.
  intro Hin. unfold block_base in Hin. apply filter_In in Hin.
  destruct Hin as [Hin Hcond]. split; [ exact Hin |].
  destruct (est_scope e) as [pr0|] eqn:Hsc; [| discriminate Hcond ].
  exists pr0. split; [ reflexivity | exact Hcond ].
Qed.

Lemma child_contrib_member {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) {k : nat} (e0 : Index.ChildAt (Index.bl_node br) k)
  (env : list (Est s)) (v : Index.NodeView) (Hv : Index.node_view (Index.ca_child e0) = v)
  (e : Est s) :
  In e (child_contrib br e0 env v Hv) ->
  est_scope e = BlockScope br
  /\ ((exists b, est_origin e = DOBinder b)
      \/ (exists sn, est_origin e = DOShort sn
            /\ Index.sh_node (snr_stmt sn) = Index.ca_child e0)).
Proof.
  destruct v; cbv beta iota delta [child_contrib]; try (intros F; exact (match F with end)).
  match goal with sh0 : Index.StmtShape |- _ => destruct sh0 end;
    try (intros F; exact (match F with end)).
  - intro Hin. destruct (stmt_decl_ests_member _ _ _ Hin) as [Hsc [Hor _]].
    split; [ exact Hsc | left; exact Hor ].
  - intro Hin. destruct (new_ests_member _ _ _ Hin) as [x [n [_ [_ He]]]].
    subst e. cbn. split; [ reflexivity |]. right.
    eexists. split; [ reflexivity | reflexivity ].
Qed.

(* every environment member is a package member or an exact earlier event of this exact block *)
Lemma block_env_member {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) (k : nat) (e : Est s) :
  In e (block_env (s := s) br k) ->
  In e (block_base s br)
  \/ (est_scope e = BlockScope br
      /\ ((exists b, est_origin e = DOBinder b)
          \/ (exists sn k' (e0 : Index.ChildAt (Index.bl_node br) k'),
                k' < k /\ est_origin e = DOShort sn
                /\ Index.sh_node (snr_stmt sn) = Index.ca_child e0))).
Proof.
  induction k as [|k' IH]; intro Hin.
  - left. exact Hin.
  - rewrite block_env_step in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + destruct (IH Hin) as [Hb|[Hsc [Hor|[sn [k0 [e0 [Hk0 Hrest]]]]]]];
        [ left; exact Hb
        | right; split; [ exact Hsc | left; exact Hor ]
        | right; split; [ exact Hsc |]; right; exists sn, k0, e0;
          split; [ lia | exact Hrest ] ].
    + destruct (Index.child_at_opt (Index.bl_node br) k') as [e0|] eqn:Ho; [| destruct Hin ].
      destruct (child_contrib_member br e0 _ _ _ e Hin) as [Hsc [Hor|[sn [Hor Hnode]]]];
        [ right; split; [ exact Hsc | left; exact Hor ]
        | right; split; [ exact Hsc |]; right; exists sn, k', e0;
          split; [ lia | split; [ exact Hor | exact Hnode ] ] ].
Qed.

(* the current statement's objects are absent from its exact pre-environment *)
Lemma block_env_no_current {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (br : Index.BlockRef idx) (k : nat) (ek : Index.ChildAt (Index.bl_node br) k)
  (e : Est s) (sn : ShortNewRef idx) :
  In e (block_env (s := s) br k) -> est_origin e = DOShort sn ->
  Index.sh_node (snr_stmt sn) = Index.ca_child ek -> False.
Proof.
  intros Hin Hor Hnode.
  destruct (block_env_member br k e Hin) as [Hb|[_ [[b Hb]|[sn' [k' [e0 [Hk' [Hor' Hnode']]]]]]]].
  - destruct (block_base_member br e Hb) as [Hpkg _].
    destruct (pkg_ests_member s e Hpkg) as [_ Hno]. rewrite Hor in Hno. exact Hno.
  - rewrite Hor in Hb. discriminate Hb.
  - rewrite Hor in Hor'. injection Hor' as <-.
    assert (He : Index.ca_child e0 = Index.ca_child ek)
      by (rewrite <- Hnode', <- Hnode; reflexivity).
    pose proof (Index.ca_ord_unique e0 ek He) as Hko. lia.
Qed.

(* every retained trace row is the canonical transition of its exact statement *)
Lemma short_row_emit_canonical {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (r : Index.NodeRef idx) (v : Index.NodeView) (Hv : Index.node_view r = v)
  (row : { st : Index.ShortStmtRef idx & ShortTransition (s := s) st }) :
  In row (short_row_emit r v Hv) ->
  exists st', row = existT _ st' (short_transition_of (s := s) st').
Proof.
  destruct v; cbn; try (intros F; exact (match F with end)).
  match goal with sh0 : Index.StmtShape |- _ =>
    destruct sh0; cbn; try (intros F; exact (match F with end)) end.
  intros [He|F]; [| destruct F ].
  eexists. exact (eq_sym He).
Qed.

Lemma short_trace_canonical {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
  (row : { st : Index.ShortStmtRef idx & ShortTransition (s := s) st }) :
  In row (short_trace s) ->
  exists st', row = existT _ st' (short_transition_of (s := s) st').
Proof.
  intro Hin. unfold short_trace in Hin.
  apply in_flat_map in Hin. destruct Hin as [pr [_ Hin]].
  apply in_flat_map in Hin. destruct Hin as [fr [_ Hin]].
  unfold short_rows_of_file in Hin. apply in_flat_map in Hin.
  destruct Hin as [pos [_ Hin]].
  destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|]; [| destruct Hin ].
  exact (short_row_emit_canonical r _ _ row Hin).
Qed.

(* the establishment enumeration at a short statement is exactly its transition's additions *)
Lemma node_ests_short_eval {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.NodeRef idx) (v : Index.NodeView)
  (Hv : Index.node_view r = v) (nn nv : nat) :
  v = Index.VStmt (Index.SSShort nn nv) ->
  exists Hv0 : Index.node_view r = Index.VStmt (Index.SSShort nn nv),
    node_ests pr r v Hv
    = tr_added (short_transition_of (s := s) (Index.mkShortStmtRef r nn nv Hv0)).
Proof. intro E. revert Hv. subst v. intro Hv. exists Hv. reflexivity. Qed.

(* membership analysis of one occurrence's establishment emission *)
Lemma node_ests_member {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.NodeRef idx) (v : Index.NodeView)
  (Hv : Index.node_view r = v) (e : Est s) :
  In e (node_ests pr r v Hv) ->
  make_main_est pr r = Some e
  \/ (exists sc, In e (stmt_decl_ests sc r))
  \/ (exists nn nv0 (Hv0 : Index.node_view r = Index.VStmt (Index.SSShort nn nv0)),
        In e (tr_added (short_transition_of (s := s) (Index.mkShortStmtRef r nn nv0 Hv0)))).
Proof.
  destruct v; cbv beta iota delta [node_ests]; try (intros F; exact (match F with end)).
  - match goal with sh0 : Index.StmtShape |- _ => destruct sh0 end;
      try (intros F; exact (match F with end)).
    + destruct (Index.node_parent r) as [par|]; [| intros F; exact (match F with end) ].
      destruct (block_scope_of (s := s) par) as [sc|]; [| intros F; exact (match F with end) ].
      intro Hin. right. left. exists sc. exact Hin.
    + intro Hin. right. right. eexists. eexists. eexists. exact Hin.
  - match goal with ts0 : Index.TopShape |- _ => destruct ts0 end.
    + intro Hin. right. left. eexists. exact Hin.
    + destruct (make_main_est pr r) as [e0|] eqn:Hm; [| intros F; exact (match F with end) ].
      intros [He|F]; [| destruct F ]. subst e0. left. reflexivity.
Qed.

Lemma actual_ests_member {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) (e : Est s) :
  In e (actual_ests s) ->
  exists pr (r : Index.NodeRef idx),
    In pr (PI.packages s) /\ In e (node_ests pr r (Index.node_view r) eq_refl).
Proof.
  intro Hin. unfold actual_ests in Hin.
  apply in_flat_map in Hin. destruct Hin as [pr [Hpr Hin]].
  apply in_flat_map in Hin. destruct Hin as [fr [_ Hin]].
  unfold actual_ests_of_file in Hin. apply in_flat_map in Hin.
  destruct Hin as [pos [_ Hin]].
  destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|]; [| destruct Hin ].
  exists pr, r. split; [ exact Hpr | exact Hin ].
Qed.

(* a short-origin phase member is exactly a retained ShortNew of its exact statement's canonical judgment *)
Lemma bp_est_short_origin {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (e : Est s) (sn : ShortNewRef idx) :
  In e (bp_ests bp) -> est_origin e = DOShort sn ->
  exists x n,
    In x (sj_lefts (tr_judgment (short_transition_of (s := s) (snr_stmt sn))))
    /\ slj_view (projT2 x) = SVNew n
    /\ e = new_est (tr_block (short_transition_of (s := s) (snr_stmt sn))) (slj_edge (projT2 x)) n
    /\ projT1 x = snr_ix sn.
Proof.
  intros Hin Hor. rewrite bp_ests_actual in Hin.
  destruct (actual_ests_member s e Hin) as [pr [r [_ Hn]]].
  destruct (node_ests_member pr r _ _ e Hn) as [Hm|[[sc Hd]|[nn [nv0 [Hv0 Ht]]]]].
  - destruct (make_main_est_some pr r e Hm) as [[f Hf] _]. rewrite Hor in Hf. discriminate Hf.
  - destruct (stmt_decl_ests_member sc r e Hd) as [_ [[b Hb] _]]. rewrite Hor in Hb. discriminate Hb.
  - set (st0 := Index.mkShortStmtRef r nn nv0 Hv0) in *.
    rewrite (tr_added_ok _) in Ht.
    destruct (new_ests_member _ _ _ Ht) as [x [n [Hx [Hview He]]]].
    assert (Hsn : sn = mk_short_new st0 (projT1 x) (slj_edge (projT2 x)))
      by (rewrite He in Hor; cbn in Hor; injection Hor as Hor; exact (eq_sym Hor)).
    assert (Hst : snr_stmt sn = st0) by (rewrite Hsn; reflexivity).
    assert (Hix : snr_ix sn = projT1 x) by (rewrite Hsn; reflexivity).
    rewrite Hst.
    exists x, n. split; [ exact Hx |]. split; [ exact Hview |].
    split; [| exact (eq_sym Hix) ].
    rewrite He. reflexivity.
Qed.

(* every retained ShortNew is an actual phase establishment *)
Lemma trace_new_in_bp_ests {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (row : { st : Index.ShortStmtRef idx & ShortTransition (s := s) st })
  (x : { i : nat & ShortLhsJudgment (tr_pre (projT2 row)) (projT1 row) i })
  (n : Names.OrdinaryIdentifier) :
  In row (bp_shorts bp) ->
  In x (sj_lefts (tr_judgment (projT2 row))) ->
  slj_view (projT2 x) = SVNew n ->
  In (new_est (tr_block (projT2 row)) (slj_edge (projT2 x)) n) (bp_ests bp).
Proof.
  intros Hrow Hx Hview.
  pose proof (new_ests_complete (tr_block (projT2 row)) (tr_judgment (projT2 row)) x n Hx Hview)
    as Hmem.
  rewrite <- (tr_added_ok (projT2 row)) in Hmem.
  set (r := Index.sh_node (projT1 row)).
  rewrite bp_ests_actual. unfold actual_ests.
  apply in_flat_map.
  exists (PI.package_of_file s (Index.nr_file r)). split; [ apply PI.packages_complete |].
  apply in_flat_map. exists (Index.nr_file r). split; [ apply PI.pkg_members_of_file |].
  unfold actual_ests_of_file. apply in_flat_map.
  exists (Index.nr_pos r). split; [ apply in_seq; pose proof (nr_pos_lt r); lia |].
  assert (Hmk : Index.mk_noderef (Index.nr_file r) (Pos.of_succ_nat (Index.nr_pos r)) = Some r)
    by (rewrite <- Index.nr_key_pos; apply Index.mk_noderef_self).
  rewrite Hmk.
  destruct (node_ests_short_eval (PI.package_of_file s (Index.nr_file r)) r
              (Index.node_view r) eq_refl (Index.sh_names (projT1 row))
              (Index.sh_values (projT1 row)) (Index.sh_ok (projT1 row))) as [Hv0 Hne].
  rewrite Hne.
  assert (Hst : Index.mkShortStmtRef r (Index.sh_names (projT1 row)) (Index.sh_values (projT1 row)) Hv0
                = projT1 row)
    by (apply shortstmtref_positional; reflexivity).
  rewrite Hst.
  destruct (short_trace_canonical s row) as [st' Hcan];
    [ rewrite <- (bp_shorts_trace bp); exact Hrow |].
  assert (Hta : tr_added (short_transition_of (s := s) (projT1 row)) = tr_added (projT2 row))
    by (rewrite Hcan; reflexivity).
  rewrite Hta. exact Hmem.
Qed.

Lemma shortstmtref_eq_dec {p} {idx : Index.ProgramIndex p} :
  forall a b : Index.ShortStmtRef idx, {a = b} + {a <> b}.
Proof.
  intros a b.
  destruct (Bool.bool_dec (noderef_eqb (Index.sh_node a) (Index.sh_node b)) true) as [H|H].
  - left. apply shortstmtref_positional. apply noderef_eqb_spec. exact H.
  - right. intro E. apply H. subst b. apply noderef_eqb_spec. reflexivity.
Qed.

(* no ExistingVariable, ExistingNonVariable, Duplicate, Blank, or Ambiguous left has an establishment *)
Lemma non_new_position_no_est {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (st0 : Index.ShortStmtRef idx) (t0 : ShortTransition (s := s) st0)
  (i : nat) (j : ShortLhsJudgment (tr_pre t0) st0 i) :
  In (existT _ st0 t0) (bp_shorts bp) ->
  In (existT _ i j) (sj_lefts (tr_judgment t0)) ->
  (forall n, slj_view j <> SVNew n) ->
  forall (e : Est s) (sn : ShortNewRef idx),
    In e (bp_ests bp) -> est_origin e = DOShort sn ->
    snr_stmt sn = st0 -> snr_ix sn = i -> False.
Proof.
  intros Hrow Hj Hnn e sn Hin Hor Hstmt Hix.
  destruct (bp_est_short_origin bp e sn Hin Hor) as [x [n [Hx [Hview [_ Hxi]]]]].
  destruct (short_trace_canonical s (existT _ st0 t0)) as [st' Hcan];
    [ rewrite <- (bp_shorts_trace bp); exact Hrow |].
  assert (Hst0 : st0 = st') by (exact (f_equal (@projT1 _ _) Hcan)).
  cbn [projT1] in Hst0. subst st'.
  apply Eqdep_dec.inj_pair2_eq_dec in Hcan; [| exact shortstmtref_eq_dec ].
  subst t0.
  destruct sn as [st1 ix1 e1]. cbn [snr_stmt snr_ix] in Hstmt, Hix, Hx, Hxi.
  subst st1.
  destruct x as [i' j']. cbn [projT1 projT2] in Hview, Hxi.
  subst i'. subst ix1.
  destruct (slj_canonical j j') as [_ Hv].
  apply (Hnn n). rewrite Hv. exact Hview.
Qed.

(* the establishment enumeration at a fixed main, evaluated at the exact known view *)
Lemma node_ests_main_eval {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.NodeRef idx) (v : Index.NodeView)
  (Hv : Index.node_view r = v) :
  v = Index.VTop Index.TSMain ->
  node_ests pr r v Hv = match make_main_est pr r with Some e => [e] | None => [] end.
Proof. intro E. revert Hv. subst v. intro Hv. reflexivity. Qed.

(* declaration and function establishment coverage: every named spec binder establishes exactly *)
Lemma bp_ests_has_main {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (r : Index.NodeRef idx) :
  Index.is_main_view (Index.node_view r) = true ->
  exists e, In e (bp_ests bp) /\ est_node e = r /\ (exists f, est_origin e = DOFunc f).
Proof.
  intro Hm.
  set (pr := PI.package_of_file s (Index.nr_file r)).
  destruct (make_main_est pr r) as [e0|] eqn:He;
    [| exact (match make_main_est_fires pr r Hm He with end) ].
  destruct (make_main_est_some pr r e0 He) as [Hf [Hnode _]].
  exists e0.
  split; [| split; [ exact Hnode | exact Hf ] ].
  rewrite bp_ests_actual. unfold actual_ests.
  apply in_flat_map. exists pr. split; [ apply PI.packages_complete |].
  apply in_flat_map. exists (Index.nr_file r). split; [ apply PI.pkg_members_of_file |].
  unfold actual_ests_of_file. apply in_flat_map.
  exists (Index.nr_pos r). split; [ apply in_seq; pose proof (nr_pos_lt r); lia |].
  assert (Hmk : Index.mk_noderef (Index.nr_file r) (Pos.of_succ_nat (Index.nr_pos r)) = Some r)
    by (rewrite <- Index.nr_key_pos; apply Index.mk_noderef_self).
  rewrite Hmk.
  rewrite (node_ests_main_eval pr r (Index.node_view r) eq_refl (Index.is_main_view_eq _ Hm)).
  rewrite He. left. reflexivity.
Qed.

(* the spec emission, evaluated at the exact known spec view *)
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

(* the establishment enumerations at declaration statements and top declarations, evaluated *)
Lemma node_ests_topdecl_eval {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.NodeRef idx) (v : Index.NodeView)
  (Hv : Index.node_view r = v) :
  v = Index.VTop Index.TSTopDecl -> node_ests pr r v Hv = stmt_decl_ests (PackageScope pr) r.
Proof. intro E. revert Hv. subst v. intro Hv. reflexivity. Qed.

Lemma node_ests_ssdecl_eval {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (r : Index.NodeRef idx) (v : Index.NodeView)
  (Hv : Index.node_view r = v) :
  v = Index.VStmt Index.SSDecl ->
  node_ests pr r v Hv
  = match Index.node_parent r with
    | Some par => match block_scope_of (s := s) par with
                  | Some sc => stmt_decl_ests sc r
                  | None => [] end
    | None => [] end.
Proof. intro E. revert Hv. subst v. intro Hv. reflexivity. Qed.

(* a spec's named binder is covered by the spec's own emission at any scope *)
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

(* every named declaration binder of the surface establishes in the phase, on its exact occurrence *)
Lemma bp_ests_has_spec_binder {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (b : Index.NodeRef idx) (fl : Index.SpecFlavor)
  (n : Names.OrdinaryIdentifier) :
  Index.node_role b = Index.RSpecName fl -> binder_ident b = Some n ->
  exists e, In e (bp_ests bp) /\ est_node e = b.
Proof.
  intros Hr Hb.
  (* the binder's parent is its exact spec *)
  destruct (Index.node_parent b) as [sp|] eqn:Hpb.
  2:{ exfalso. pose proof (Index.parentless_view_file b Hpb) as Hv.
      rewrite (binder_ident_view b n Hb) in Hv. discriminate Hv. }
  destruct (Index.all_children_of_parent b sp Hpb) as [i [eb [_ Hcb]]].
  assert (Hrb : Index.node_role (Index.ca_child eb) = Index.RSpecName fl)
    by (rewrite Hcb; exact Hr).
  pose proof (Index.child_at_specname_spec eb fl Hrb) as Hspv.
  (* the spec's parent is its exact declaration *)
  destruct (Index.node_parent sp) as [d|] eqn:Hpsp.
  2:{ exfalso. pose proof (Index.parentless_view_file sp Hpsp) as Hv.
      rewrite Hv in Hspv. destruct fl; exact Hspv. }
  destruct (Index.all_children_of_parent sp d Hpsp) as [k2 [ed [_ Hcd]]].
  assert (Hdv : Index.node_view d = Index.VDecl fl)
    by (apply (Index.child_at_spec_decl ed fl); rewrite Hcd; exact Hspv).
  (* the declaration's parent is its exact statement or top declaration *)
  destruct (Index.node_parent d) as [t|] eqn:Hpd.
  2:{ exfalso. pose proof (Index.parentless_view_file d Hpd) as Hv.
      rewrite Hdv in Hv. discriminate Hv. }
  destruct (Index.all_children_of_parent d t Hpd) as [k3 [et [_ Hct]]].
  assert (Hdt : Index.node_view (Index.ca_child et) = Index.VDecl fl) by (rewrite Hct; exact Hdv).
  pose proof (Index.child_at_decl_parent et fl Hdt) as Htv.
  assert (Hk3 : k3 = 0).
  { apply (Index.singleton_child_ordinal et).
    destruct Htv as [Htv|Htv]; rewrite Htv; reflexivity. }
  subst k3.
  (* the spec reference and its exact name edge at the binder's ordinal *)
  assert (Hspv' : exists sh : Index.SpecShape fl, Index.node_view sp = Index.spec_view_of fl sh).
  { destruct fl; cbn in Hspv; destruct (Index.node_view sp); try (exact (match Hspv with end));
      eexists; reflexivity. }
  destruct Hspv' as [sh Hshv].
  assert (Hlt : i < Index.shape_names fl (Index.sp_shape (Index.mkSpecRef (fl := fl) sp sh Hshv)))
    by (exact (specname_ordinal_lt (Index.mkSpecRef (fl := fl) sp sh Hshv) i eb Hrb)).
  assert (Hbn : binder_ident
                  (Index.sn_child (Index.mkSpecName (sp := Index.mkSpecRef (fl := fl) sp sh Hshv) eb Hlt))
                = Some n)
    by (unfold Index.sn_child; cbn [Index.sn_at Index.sp_node]; rewrite Hcb; exact Hb).
  assert (Hpsp' : Index.node_parent (Index.sp_node (Index.mkSpecRef (fl := fl) sp sh Hshv))
                  = Some (Index.ca_child et))
    by (cbn [Index.sp_node]; rewrite <- Hct in Hpsp; exact Hpsp).
  destruct Htv as [Htv|Htv].
  - (* block-local declaration statement *)
    destruct (Index.node_parent t) as [par|] eqn:Hpt.
    2:{ exfalso. pose proof (Index.parentless_view_file t Hpt) as Hv.
        rewrite Htv in Hv. discriminate Hv. }
    assert (Hbv : Index.node_view par = Index.VBlock).
    { destruct (Index.all_children_of_parent t par Hpt) as [k4 [e4 [_ Hc4]]].
      apply (Index.child_at_stmt_block e4 Index.SSDecl). rewrite Hc4. exact Htv. }
    destruct (block_scope_of (s := s) par) as [sc|] eqn:Hbs;
      [| exact (match block_scope_of_block par Hbv Hbs with end) ].
    destruct (stmt_decl_ests_cover sc t et (Index.mkSpecRef (fl := fl) sp sh Hshv) i
                (Index.mkSpecName (sp := Index.mkSpecRef (fl := fl) sp sh Hshv) eb Hlt) n
                Hpsp' Hbn) as [e0 [Hin Hnode]].
    exists e0. split.
    2:{ rewrite Hnode. unfold Index.sn_child. cbn [Index.sn_at Index.sp_node]. exact Hcb. }
    rewrite bp_ests_actual. unfold actual_ests.
    apply in_flat_map.
    exists (PI.package_of_file s (Index.nr_file t)). split; [ apply PI.packages_complete |].
    apply in_flat_map. exists (Index.nr_file t). split; [ apply PI.pkg_members_of_file |].
    unfold actual_ests_of_file. apply in_flat_map.
    exists (Index.nr_pos t). split; [ apply in_seq; pose proof (nr_pos_lt t); lia |].
    assert (Hmk : Index.mk_noderef (Index.nr_file t) (Pos.of_succ_nat (Index.nr_pos t)) = Some t)
      by (rewrite <- Index.nr_key_pos; apply Index.mk_noderef_self).
    rewrite Hmk.
    rewrite (node_ests_ssdecl_eval (PI.package_of_file s (Index.nr_file t)) t
               (Index.node_view t) eq_refl Htv).
    rewrite Hpt, Hbs. exact Hin.
  - (* top-level declaration *)
    destruct (stmt_decl_ests_cover (PackageScope (PI.package_of_file s (Index.nr_file t)))
                t et (Index.mkSpecRef (fl := fl) sp sh Hshv) i
                (Index.mkSpecName (sp := Index.mkSpecRef (fl := fl) sp sh Hshv) eb Hlt) n
                Hpsp' Hbn)
      as [e0 [Hin Hnode]].
    exists e0. split.
    2:{ rewrite Hnode. unfold Index.sn_child. cbn [Index.sn_at Index.sp_node]. exact Hcb. }
    rewrite bp_ests_actual. unfold actual_ests.
    apply in_flat_map.
    exists (PI.package_of_file s (Index.nr_file t)). split; [ apply PI.packages_complete |].
    apply in_flat_map. exists (Index.nr_file t). split; [ apply PI.pkg_members_of_file |].
    unfold actual_ests_of_file. apply in_flat_map.
    exists (Index.nr_pos t). split; [ apply in_seq; pose proof (nr_pos_lt t); lia |].
    assert (Hmk : Index.mk_noderef (Index.nr_file t) (Pos.of_succ_nat (Index.nr_pos t)) = Some t)
      by (rewrite <- Index.nr_key_pos; apply Index.mk_noderef_self).
    rewrite Hmk.
    rewrite (node_ests_topdecl_eval (PI.package_of_file s (Index.nr_file t)) t
               (Index.node_view t) eq_refl Htv).
    exact Hin.
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

(* every pre-environment member embeds into the post environment at its exact ordinal *)
Definition embed_pre {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {st : Index.ShortStmtRef idx} (t : ShortTransition (s := s) st)
  (ref : EnvEstRef (tr_pre t)) : EnvEstRef (tr_post t) :=
  mk_env_ref (er_ord ref) (er_est ref) (pre_nth_post _ _ _ _ (er_at ref)).

Lemma embed_pre_exact {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {st : Index.ShortStmtRef idx} (t : ShortTransition (s := s) st) (ref : EnvEstRef (tr_pre t)) :
  er_ord (embed_pre t ref) = er_ord ref /\ er_est (embed_pre t ref) = er_est ref.
Proof. split; reflexivity. Qed.

(* every addition owns an exact post-environment reference past the pre members *)
Definition post_new_ref {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {st : Index.ShortStmtRef idx} (t : ShortTransition (s := s) st)
  (k : nat) (e : Est s) (H : nth_error (tr_added t) k = Some e) : EnvEstRef (tr_post t) :=
  mk_env_ref (length (tr_pre t) + k) e (post_nth _ _ _ _ H).

Lemma post_new_ref_exact {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {st : Index.ShortStmtRef idx} (t : ShortTransition (s := s) st)
  (k : nat) (e : Est s) (H : nth_error (tr_added t) k = Some e) :
  er_ord (post_new_ref t k e H) = length (tr_pre t) + k /\ er_est (post_new_ref t k e H) = e.
Proof. split; reflexivity. Qed.

(* the post environment adds exactly the News: no member is dropped, reconstructed, or smuggled in *)
Lemma tr_post_member {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {st : Index.ShortStmtRef idx} (t : ShortTransition (s := s) st) (x : Est s) :
  In x (tr_post t) <-> In x (tr_pre t) \/ In x (tr_added t).
Proof. unfold tr_post. split; [ apply in_app_or | apply in_or_app ]. Qed.

(* the RHS environment is definitionally the exact pre-statement environment *)
Lemma tr_rhs_pre {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {st : Index.ShortStmtRef idx} (t : ShortTransition (s := s) st) :
  tr_rhs_env t = tr_pre t.
Proof. reflexivity. Qed.

(* every addition becomes visible only after the statement's exact extent *)
Lemma tr_added_vstart {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {st : Index.ShortStmtRef idx} (t : ShortTransition (s := s) st) (e : Est s) :
  In e (tr_added t) -> est_vstart e = Index.node_extent (Index.sh_node st).
Proof.
  intro Hin. rewrite (tr_added_ok t) in Hin.
  destruct (new_ests_member _ _ _ Hin) as [x [n [_ [_ He]]]].
  subst e. cbn [new_est est_vstart].
  unfold vis_start. rewrite (Index.sl_role (slj_edge (projT2 x))).
  rewrite (Index.sl_parent (slj_edge (projT2 x))). reflexivity.
Qed.

(* no addition is visible at any occurrence inside the statement: RHS resolution cannot see it *)
Lemma tr_added_invisible_inside {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {st : Index.ShortStmtRef idx} (t : ShortTransition (s := s) st) (e : Est s)
  (u : Index.NodeRef idx) :
  In e (tr_added t) -> Index.nr_pos u <= Index.node_extent (Index.sh_node st) ->
  contains_visible e u = false.
Proof.
  intros Hin Hle.
  pose proof (tr_added_vstart t e Hin) as Hvs.
  assert (Hor : exists br0, est_scope e = BlockScope br0).
  { rewrite (tr_added_ok t) in Hin.
    destruct (new_ests_member _ _ _ Hin) as [x [n [_ [_ He]]]].
    subst e. eexists. reflexivity. }
  destruct Hor as [br0 Hsc].
  unfold contains_visible. rewrite Hsc.
  assert (Hltb : Nat.ltb (est_vstart e) (Index.nr_pos u) = false)
    by (apply Nat.ltb_ge; rewrite Hvs; exact Hle).
  rewrite Hltb. rewrite !Bool.andb_false_r. reflexivity.
Qed.

(* a right-hand child sits inside the statement, so no addition is visible to it *)
Lemma tr_added_invisible_rhs {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {st : Index.ShortStmtRef idx} (t : ShortTransition (s := s) st) (e : Est s)
  (j : nat) (re : Index.ShortRhsEdge st j) :
  In e (tr_added t) -> contains_visible e (Index.sr_child re) = false.
Proof.
  intro Hin. apply (tr_added_invisible_inside t e _ Hin).
  apply Index.child_le_extent. exact (Index.sr_parent re).
Qed.

Lemma source_cands_actual {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) (e : Est s) :
  In e (source_cands bp u n) -> In e (bp_ests bp).
Proof. intro Hin. unfold source_cands in Hin. apply filter_In in Hin. exact (proj1 Hin). Qed.

(* declaration groups never contain a short-origin object *)
Lemma decl_group_no_short {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (x e : Est s) (sn : ShortNewRef idx) :
  In e (decl_group bp x) -> est_origin e = DOShort sn -> False.
Proof.
  intros Hin Hor. unfold decl_group, decl_group_core in Hin.
  apply filter_In in Hin. destruct Hin as [_ Hd].
  unfold is_decl_est in Hd. rewrite Hor in Hd. discriminate Hd.
Qed.
