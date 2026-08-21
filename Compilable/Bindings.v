(* Bindings — binders, blocks, objects, scopes, ordinary-name resolution, and package-scope function declarations. *)

From Stdlib Require Import String List Bool Arith PeanoNat Lia Eqdep_dec PArith NArith.
From Fido Require Import Syntax Names Index Compilable.PackageIdentity.
Import ListNotations.

Module PI := Compilable.PackageIdentity.

Definition is_binder_role (r : Index.Role) : bool :=
  match r with Index.RSpecName _ => true | Index.RShortLhs => true | _ => false end.

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

(* a shallow block occurrence is the Index block reference; mk_blockref makes the check total *)
Definition mk_blockref {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx) : option (Index.BlockRef idx) :=
  (match Index.is_block_view (Index.node_view r) as b
     return Index.is_block_view (Index.node_view r) = b -> option (Index.BlockRef idx) with
   | true => fun H => Some (Index.mkBlockRef r H)
   | false => fun _ => None
   end) eq_refl.

Lemma mk_blockref_node {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx) (br : Index.BlockRef idx) :
  mk_blockref r = Some br -> Index.bl_node br = r.
Proof.
  unfold mk_blockref. generalize (@eq_refl bool (Index.is_block_view (Index.node_view r))).
  destruct (Index.is_block_view (Index.node_view r)) at 2 3; intro H;
    [ intro E; injection E as <-; reflexivity | discriminate ].
Qed.

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

(* a declaration origin: a name binder or a package-scope function declaration (fixed main today; C9 extends DOFunc) *)
Inductive DeclOrigin {p} (idx : Index.ProgramIndex p) : Type :=
| DOBinder : BinderRef idx -> DeclOrigin idx
| DOFunc   : FunctionDeclRef idx -> DeclOrigin idx.
Arguments DOBinder {p idx} _.
Arguments DOFunc {p idx} _.

(* the establishing source occurrence of a declaration origin: the binder token, or the function declaration *)
Definition do_node {p} {idx : Index.ProgramIndex p} (o : DeclOrigin idx) : Index.NodeRef idx :=
  match o with DOBinder b => binder_node b | DOFunc f => function_node f end.

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

(* the nearest enclosing block per node, from one ascending fold — parents first, no per-fact scan *)
Definition nearest_block_table {p} {idx : Index.ProgramIndex p} (fr : Index.FileRef idx)
  : Collections.NodeMap.t (option (Index.BlockRef idx)) :=
  fold_left (fun tbl pos =>
    match Index.mk_noderef fr (Pos.of_succ_nat pos) with
    | Some r =>
        Collections.NodeMap.add (Index.nr_key r)
          (match Index.node_parent r with
           | Some par =>
               match mk_blockref par with
               | Some br => Some br
               | None => match Collections.NodeMap.find (Index.nr_key par) tbl with Some x => x | None => None end
               end
           | None => None
           end) tbl
    | None => tbl
    end)
    (seq 0 (Index.occ_count fr)) (Collections.NodeMap.empty _).

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
Lemma short_binder {p} {idx : Index.ProgramIndex p} (b : Index.NodeRef idx) :
  Index.node_role b = Index.RShortLhs -> is_binder_role (Index.node_role b) = true.
Proof. intro H; rewrite H; reflexivity. Qed.

Definition est_scope_of {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (nbt : Collections.NodeMap.t (option (Index.BlockRef idx))) (b : Index.NodeRef idx) : ScopeId s :=
  match Collections.NodeMap.find (Index.nr_key b) nbt with
  | Some (Some br) => BlockScope br
  | _ => PackageScope pr
  end.

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

(* an ordinary name binder establishes its name at its scope *)
Definition make_est {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (nbt : Collections.NodeMap.t (option (Index.BlockRef idx))) (b : Index.NodeRef idx)
  : option (Est s) :=
  match binder_ident b with
  | Some n =>
      (match Index.node_role b as r return Index.node_role b = r -> option (Est s) with
       | Index.RSpecName fl => fun H => Some (mk_est (DOBinder (binder_ref b (spec_binder b fl H))) n (est_scope_of pr nbt b) (vis_start b))
       | Index.RShortLhs    => fun H => Some (mk_est (DOBinder (binder_ref b (short_binder b H))) n (est_scope_of pr nbt b) (vis_start b))
       | _ => fun _ => None
       end) eq_refl
  | None => None
  end.

(* a package-scope function declaration: the fixed main establishes the name main at package scope *)
Definition make_main_est {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (b : Index.NodeRef idx) : option (Est s) :=
  (match Index.is_main_view (Index.node_view b) as m
     return Index.is_main_view (Index.node_view b) = m -> option (Est s) with
   | true => fun H => Some (mk_est (DOFunc (FixedMainFunction (Index.mkMainOccurrenceRef b H))) main_ident (PackageScope pr) (Index.nr_pos b))
   | false => fun _ => None
   end) eq_refl.

(* one establishment per source occurrence: a function declaration, else a name binder, else none *)
Definition est_of_node {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (nbt : Collections.NodeMap.t (option (Index.BlockRef idx))) (b : Index.NodeRef idx)
  : option (Est s) :=
  match make_main_est pr b with Some e => Some e | None => make_est pr nbt b end.

(* establishments of a file in source order (ascending position); file_nodes is trie order, so iterate positions *)
Definition ests_of_file {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (fr : Index.FileRef idx) : list (Est s) :=
  let nbt := nearest_block_table fr in
  flat_map (fun pos => match Index.mk_noderef fr (Pos.of_succ_nat pos) with
                       | Some b => match est_of_node pr nbt b with Some e => [e] | None => [] end
                       | None => []
                       end)
           (seq 0 (Index.occ_count fr)).

Definition all_ests {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : list (Est s) :=
  flat_map (fun pr => flat_map (ests_of_file pr) (PI.pkg_members pr)) (PI.packages s).

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

(* a declaration establishment: a const/var/type spec name or a function declaration; short-lhs is excluded *)
Definition is_decl_est {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} (e : Est s) : bool :=
  match est_origin e with
  | DOBinder b => match Index.node_role (binder_node b) with Index.RSpecName _ => true | _ => false end
  | DOFunc _ => true
  end.


(* the declaration members of e's group over an establishment list *)
Definition decl_group_core {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (core : list (Est s)) (e : Est s) : list (Est s) := filter is_decl_est (group_members_core core e).

(* the establishment carried by a binder occurrence within an establishment list, when it establishes one *)
Definition est_of_binder_core {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (core : list (Est s)) (b : Index.NodeRef idx) : option (Est s) :=
  find (fun e => noderef_eqb (est_node e) b) core.

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

(* the exact left-side classification view; the judgment pins it to the one classification decision *)
Inductive ShortLhsView {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
| SVBlank : ShortLhsView s
| SVDuplicate : nat -> ShortLhsView s
| SVNew : Est s -> ShortLhsView s
| SVExistingVariable : Est s -> Est s -> ShortLhsView s
| SVExistingNonVariable : Est s -> Est s -> ShortLhsView s
| SVAmbiguous : Est s -> Est s -> list (Est s) -> ShortLhsView s.
Arguments SVBlank {p idx s}.
Arguments SVDuplicate {p idx s} _.
Arguments SVNew {p idx s} _.
Arguments SVExistingVariable {p idx s} _ _.
Arguments SVExistingNonVariable {p idx s} _ _.
Arguments SVAmbiguous {p idx s} _ _ _.

(* the one deterministic left-side classification over the exact pre-statement establishment core *)
Definition short_lhs_decide {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (core : list (Est s)) {st : Index.ShortStmtRef idx} {i : nat} (e : Index.ShortLhsEdge st i)
  : ShortLhsView s :=
  let b := Index.sl_child e in
  match binder_ident b with
  | None => SVBlank
  | Some n =>
      match find_dup i n (Index.short_lhs_edges st) with
      | Some (existT _ j _) => SVDuplicate j
      | None =>
          match est_of_binder_core core b with
          | Some eb =>
              match group_status (decl_group_core core eb) with
              | Some (GRedeclared a c rest) => SVAmbiguous a c rest
              | _ =>
                  match find (fun e2 => andb (negb (est_eqb e2 eb))
                                             (Nat.ltb (Index.nr_pos (est_node e2)) (Index.nr_pos b)))
                             (group_members_core core eb) with
                  | Some prior => if is_variable_binder (est_node prior)
                                  then SVExistingVariable eb prior else SVExistingNonVariable eb prior
                  | None => SVNew eb
                  end
              end
          | None => SVBlank
          end
      end
  end.

(* the exact retained left judgment: the exact edge and the classification the one decision pins to it *)
Record ShortLhsJudgment {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (core : list (Est s)) (st : Index.ShortStmtRef idx) (i : nat) : Type := mk_slj {
  slj_edge : Index.ShortLhsEdge st i ;
  slj_view : ShortLhsView s ;
  slj_ok   : slj_view = short_lhs_decide core slj_edge
}.
Arguments mk_slj {p idx s core st i} _ _ _.
Arguments slj_edge {p idx s core st i} _.
Arguments slj_view {p idx s core st i} _.
Arguments slj_ok {p idx s core st i} _.

(* the exact retained short-declaration judgment: one left judgment per exact left index, complete *)
Record ShortJudgment {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (core : list (Est s)) (st : Index.ShortStmtRef idx) : Type := mk_short_judgment {
  sj_lefts : list { i : nat & ShortLhsJudgment core st i } ;
  sj_lefts_ok : map (@projT1 _ _) sj_lefts = seq 0 (Index.sh_names st)
}.
Arguments mk_short_judgment {p idx s core st} _ _.
Arguments sj_lefts {p idx s core st} _.
Arguments sj_lefts_ok {p idx s core st} _.

Lemma short_lefts_build_ok {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (core : list (Est s)) (st : Index.ShortStmtRef idx) :
  map (@projT1 _ _)
      (map (fun x => match x with existT _ i e =>
                       existT _ i (mk_slj (core := core) e (short_lhs_decide core e) eq_refl) end)
           (Index.short_lhs_edges st))
  = seq 0 (Index.sh_names st).
Proof.
  rewrite map_map.
  rewrite (map_ext (fun x => projT1 (match x with existT _ i e =>
                      existT _ i (mk_slj (core := core) e (short_lhs_decide core e) eq_refl) end))
                   (@projT1 _ _));
    [ apply Index.short_lhs_edges_ords | intros [i e]; reflexivity ].
Qed.

(* the one canonical short-declaration judgment: every left edge judged by the one decision *)
Definition short_judgment_of {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (core : list (Est s)) (st : Index.ShortStmtRef idx) : ShortJudgment core st :=
  mk_short_judgment
    (map (fun x => match x with existT _ i e =>
                     existT _ i (mk_slj (core := core) e (short_lhs_decide core e) eq_refl) end)
         (Index.short_lhs_edges st))
    (short_lefts_build_ok core st).

(* the short-statement emission of one occurrence, factored over its view *)
Definition short_ref_emit {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx)
  (v : Index.NodeView) (Hv : Index.node_view r = v) : list (Index.ShortStmtRef idx) :=
  match v as v0 return Index.node_view r = v0 -> _ with
  | Index.VStmt (Index.SSShort nn nv) => fun Hv0 => [Index.mkShortStmtRef r nn nv Hv0]
  | _ => fun _ => []
  end Hv.

Lemma short_ref_emit_cover {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx)
  (v : Index.NodeView) (Hv : Index.node_view r = v) (nn nv : nat) :
  v = Index.VStmt (Index.SSShort nn nv) ->
  exists st', In st' (short_ref_emit r v Hv) /\ Index.sh_node st' = r.
Proof.
  intro E. revert Hv. subst v. intro Hv. cbn.
  eexists. split; [ left; reflexivity | reflexivity ].
Qed.

(* every represented short declaration of the surface, in exact source order *)
Definition short_stmts_of_file {p} {idx : Index.ProgramIndex p} (fr : Index.FileRef idx)
  : list (Index.ShortStmtRef idx) :=
  flat_map (fun pos => match Index.mk_noderef fr (Pos.of_succ_nat pos) with
                       | Some r => short_ref_emit r (Index.node_view r) eq_refl
                       | None => []
                       end)
           (seq 0 (Index.occ_count fr)).
Definition short_subjects {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
  : list (Index.ShortStmtRef idx) :=
  flat_map (fun pr => flat_map short_stmts_of_file (PI.pkg_members pr)) (PI.packages s).

(* the one canonical short-judgment table of the surface over an establishment core *)
Definition short_table {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (core : list (Est s)) : list { st : Index.ShortStmtRef idx & ShortJudgment core st } :=
  map (fun st => existT _ st (short_judgment_of core st)) (short_subjects s).

(* the retained binding phase, sealed to its one builder; main status is a projection over the establishments *)

Record RawBP {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type := mk_rawbp {
  rbp_ests   : list (Est s) ;
  rbp_consts : list { cs : Index.SpecRef idx Index.ConstSpecF & ConstJudgment cs } ;
  rbp_shorts : list { st : Index.ShortStmtRef idx & ShortJudgment rbp_ests st }
}.
Arguments mk_rawbp {p idx s} _ _ _.
Arguments rbp_ests {p idx s} _.
Arguments rbp_consts {p idx s} _.
Arguments rbp_shorts {p idx s} _.

Definition raw_bindings {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : RawBP s :=
  mk_rawbp (all_ests s) (const_table s) (short_table (all_ests s)).
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
  : list { st : Index.ShortStmtRef idx & ShortJudgment (bp_ests bp) st } :=
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

(* the subjects enumeration covers every short statement *)
Lemma short_subjects_cover {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
  (st : Index.ShortStmtRef idx) :
  exists st', In st' (short_subjects s) /\ Index.sh_node st' = Index.sh_node st.
Proof.
  set (r := Index.sh_node st).
  assert (Hfile : In (Index.nr_file r) (PI.pkg_members (PI.package_of_file s (Index.nr_file r))))
    by apply PI.pkg_members_of_file.
  assert (Hentry : exists st', In st' (short_stmts_of_file (Index.nr_file r))
                               /\ Index.sh_node st' = r).
  { unfold short_stmts_of_file.
    assert (Hmk : Index.mk_noderef (Index.nr_file r) (Pos.of_succ_nat (Index.nr_pos r)) = Some r)
      by (rewrite <- Index.nr_key_pos; apply Index.mk_noderef_self).
    assert (Hin : exists st', In st' (short_ref_emit r (Index.node_view r) eq_refl)
                  /\ Index.sh_node st' = r).
    { exact (short_ref_emit_cover r (Index.node_view r) eq_refl (Index.sh_names st) (Index.sh_values st)
               (Index.sh_ok st)). }
    destruct Hin as [st' [Hin' Hnode']].
    exists st'. split; [| exact Hnode' ].
    apply in_flat_map. exists (Index.nr_pos r). split.
    - apply in_seq. pose proof (nr_pos_lt r). lia.
    - rewrite Hmk. exact Hin'. }
  destruct Hentry as [st' [Hin' Hnode']].
  exists st'. split; [| exact Hnode' ].
  unfold short_subjects. apply in_flat_map.
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

(* the exact phase-owned short judgment ref *)
Record ShortDeclJudgmentRef {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (st : Index.ShortStmtRef idx) : Type := mk_sjr {
  sjr_ord : nat ;
  sjr_row : { st' : Index.ShortStmtRef idx & ShortJudgment (bp_ests bp) st' } ;
  sjr_at  : nth_error (bp_shorts bp) sjr_ord = Some sjr_row ;
  sjr_subject : projT1 sjr_row = st
}.
Arguments mk_sjr {p idx s bp st} _ _ _ _.
Arguments sjr_ord {p idx s bp st} _.
Arguments sjr_row {p idx s bp st} _.
Arguments sjr_at {p idx s bp st} _.
Arguments sjr_subject {p idx s bp st} _.

Lemma shortref_of_nodes {p} {idx : Index.ProgramIndex p}
  (a b : Index.ShortStmtRef idx) : noderef_eqb (Index.sh_node a) (Index.sh_node b) = true -> a = b.
Proof. intro H. apply shortstmtref_positional. apply noderef_eqb_spec. exact H. Qed.

Fixpoint sjr_scan {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (st : Index.ShortStmtRef idx) (k : nat)
  (l : list { st' : Index.ShortStmtRef idx & ShortJudgment (bp_ests bp) st' }) {struct l}
  : l = skipn k (bp_shorts bp) -> option (ShortDeclJudgmentRef bp st) :=
  match l with
  | [] => fun _ => None
  | row :: rest => fun E =>
      match Bool.bool_dec (noderef_eqb (Index.sh_node (projT1 row)) (Index.sh_node st)) true with
      | left Hb => Some (mk_sjr k row (Index.skipn_head_at (bp_shorts bp) rest k row E)
                                (shortref_of_nodes (projT1 row) st Hb))
      | right _ => sjr_scan bp st (S k) rest (Index.skipn_tail_at (bp_shorts bp) rest k row E)
      end
  end.

Lemma sjr_scan_finds {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (st : Index.ShortStmtRef idx) :
  forall l k (E : l = skipn k (bp_shorts bp)),
  (exists row, In row l /\ Index.sh_node (projT1 row) = Index.sh_node st) ->
  sjr_scan bp st k l E <> None.
Proof.
  induction l as [|row rest IH]; intros k E [row0 [Hin Hnode]]; [ destruct Hin |].
  cbn. destruct (Bool.bool_dec (noderef_eqb (Index.sh_node (projT1 row)) (Index.sh_node st)) true)
    as [|Hne]; [ discriminate |].
  destruct Hin as [Hhead|Hin].
  - exfalso. apply Hne. subst row0. apply noderef_eqb_spec. exact Hnode.
  - apply (IH (S k) (Index.skipn_tail_at (bp_shorts bp) rest k row E)).
    exists row0. split; [ exact Hin | exact Hnode ].
Qed.

Lemma bp_shorts_subjects {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) :
  map (fun row => projT1 row) (bp_shorts bp) = short_subjects s.
Proof.
  unfold bp_shorts, bp_ests. rewrite (proj2_sig bp). cbn [rbp_shorts rbp_ests raw_bindings].
  unfold short_table. rewrite map_map.
  etransitivity; [ apply map_ext; intro st; reflexivity | apply map_id ].
Qed.

Lemma bp_shorts_cover {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (st : Index.ShortStmtRef idx) :
  exists row, In row (bp_shorts bp) /\ Index.sh_node (projT1 row) = Index.sh_node st.
Proof.
  destruct (short_subjects_cover s st) as [st' [Hin Hnode]].
  assert (Hin' : In st' (map (fun row => projT1 row) (bp_shorts bp)))
    by (rewrite bp_shorts_subjects; exact Hin).
  apply in_map_iff in Hin'. destruct Hin' as [row [Hproj Hrow]].
  exists row. split; [ exact Hrow | rewrite Hproj; exact Hnode ].
Qed.

(* the sole ordinary short-judgment lookup: total, returning the exact retained phase row *)
Definition short_decl_judgment {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (st : Index.ShortStmtRef idx) : ShortDeclJudgmentRef bp st :=
  (match sjr_scan bp st 0 (bp_shorts bp) eq_refl as o
         return sjr_scan bp st 0 (bp_shorts bp) eq_refl = o -> ShortDeclJudgmentRef bp st with
   | Some r => fun _ => r
   | None => fun E =>
       False_rect _ (sjr_scan_finds bp st (bp_shorts bp) 0 eq_refl (bp_shorts_cover bp st) E)
   end) eq_refl.

(* the exact left-judgment lookup within a retained short judgment, total below the left count *)
Fixpoint slj_scan {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {core : list (Est s)} {st : Index.ShortStmtRef idx} (i : nat)
  (l : list { i0 : nat & ShortLhsJudgment core st i0 }) {struct l}
  : option (ShortLhsJudgment core st i) :=
  match l with
  | [] => None
  | existT _ i0 j :: rest =>
      match Nat.eq_dec i0 i with
      | left He => Some (eq_rect i0 (fun i1 => ShortLhsJudgment core st i1) j i He)
      | right _ => slj_scan i rest
      end
  end.

Lemma slj_scan_finds {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {core : list (Est s)} {st : Index.ShortStmtRef idx} (i : nat) :
  forall l, In i (map (@projT1 _ _) l) -> slj_scan (core := core) (st := st) i l <> None.
Proof.
  induction l as [|[i0 j] rest IH]; intro Hin; [ destruct Hin |].
  cbn. destruct (Nat.eq_dec i0 i) as [|Hne]; [ discriminate |].
  destruct Hin as [Hhead|Hin]; [ exfalso; apply Hne; exact Hhead | exact (IH Hin) ].
Qed.

Definition short_lhs_judgment {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {core : list (Est s)} {st : Index.ShortStmtRef idx} (sj : ShortJudgment core st)
  (i : nat) (H : i < Index.sh_names st) : ShortLhsJudgment core st i :=
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

Definition is_block_scoped {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} (e : Est s) : bool :=
  match est_scope e with BlockScope _ => true | PackageScope _ => false end.

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


(* the exact effective-origin object of a const spec: itself when explicit, else a preceding-sibling edge *)
Inductive ConstOrigin {p} {idx : Index.ProgramIndex p} (cs : Index.SpecRef idx Index.ConstSpecF) : Type :=
| OriginSelf : cs_explicit cs = true -> ConstOrigin cs
| OriginPred : forall i, Index.PrecedingSiblingEdge (Index.sp_node cs) i -> ConstOrigin cs.
Arguments OriginSelf {p idx cs} _.
Arguments OriginPred {p idx cs} _ _.

(* the one exact retained const-spec status: the exact edge objects, tied to the exact spec ref *)
Record ConstSpecStatus {p} {idx : Index.ProgramIndex p} (cs : Index.SpecRef idx Index.ConstSpecF) : Type
  := mk_const_status {
  cst_preds  : list { i : nat & Index.PrecedingSiblingEdge (Index.sp_node cs) i } ;
  cst_names  : list { i : nat & Index.SpecNameEdge cs i } ;
  cst_type   : Index.SpecTypePresence cs ;
  cst_values : list { j : nat & Index.SpecValueEdge cs j }
}.
Arguments mk_const_status {p idx cs} _ _ _ _.
Arguments cst_preds {p idx cs} _. Arguments cst_names {p idx cs} _.
Arguments cst_type {p idx cs} _. Arguments cst_values {p idx cs} _.

(* a spec heads its declaration exactly when its retained preceding-sibling edges are empty *)
Definition cst_first {p} {idx : Index.ProgramIndex p} {cs : Index.SpecRef idx Index.ConstSpecF}
  (st : ConstSpecStatus cs) : bool :=
  match cst_preds st with [] => true | _ => false end.

(* the exact predecessor: the last retained preceding-sibling edge, derived from the retained edges *)
Definition cst_predecessor {p} {idx : Index.ProgramIndex p} {cs : Index.SpecRef idx Index.ConstSpecF}
  (st : ConstSpecStatus cs) : option { i : nat & Index.PrecedingSiblingEdge (Index.sp_node cs) i } :=
  fold_left (fun _ pe => Some pe) (cst_preds st) None.

(* the exact effective origin, derived from the retained shape and preceding edges *)
Definition cst_origin {p} {idx : Index.ProgramIndex p} {cs : Index.SpecRef idx Index.ConstSpecF}
  (st : ConstSpecStatus cs) : option (ConstOrigin cs) :=
  match Bool.bool_dec (cs_explicit cs) true with
  | left H => Some (OriginSelf H)
  | right _ =>
      fold_left (fun acc pe =>
                   if is_explicit_const_spec (Index.ps_sibling (projT2 pe))
                   then Some (OriginPred (projT1 pe) (projT2 pe)) else acc)
                (cst_preds st) None
  end.

Definition const_spec_status {p} {idx : Index.ProgramIndex p} (cs : Index.SpecRef idx Index.ConstSpecF)
  : ConstSpecStatus cs :=
  mk_const_status (Index.preceding_edges (Index.sp_node cs)) (Index.spec_name_edges cs)
                  (Index.spec_type_status cs) (Index.spec_value_edges cs).



(* the establishment carried by a binder occurrence, when it establishes one *)
Definition est_of_binder {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (b : Index.NodeRef idx) : option (Est s) :=
  est_of_binder_core (bp_ests bp) b.

(* the exact left-side status of one short-declaration name, tied to the exact left edge it classifies *)
Inductive ShortLhsStatus {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
  (st : Index.ShortStmtRef idx) (i : nat) : Type :=
| ShortBlank               : Index.ShortLhsEdge st i -> ShortLhsStatus s st i
| ShortNew                 : Index.ShortLhsEdge st i -> Est s -> ShortLhsStatus s st i
| ShortExistingVariable    : Index.ShortLhsEdge st i -> Est s -> ShortLhsStatus s st i
| ShortExistingNonVariable : Index.ShortLhsEdge st i -> Est s -> ShortLhsStatus s st i
| ShortDuplicate           : Index.ShortLhsEdge st i ->
                             forall j, Index.ShortLhsEdge st j -> j < i -> ShortLhsStatus s st i
| ShortAmbiguous           : Index.ShortLhsEdge st i -> Est s -> Est s -> list (Est s) -> ShortLhsStatus s st i.
Arguments ShortBlank {p idx s st i} _.
Arguments ShortNew {p idx s st i} _ _.
Arguments ShortExistingVariable {p idx s st i} _ _.
Arguments ShortExistingNonVariable {p idx s st i} _ _.
Arguments ShortDuplicate {p idx s st i} _ _ _ _.
Arguments ShortAmbiguous {p idx s st i} _ _ _ _.

Definition short_lhs_status {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) {st : Index.ShortStmtRef idx} {i : nat} (e : Index.ShortLhsEdge st i)
  : ShortLhsStatus s st i :=
  let b := Index.sl_child e in
  match binder_ident b with
  | None => ShortBlank e
  | Some n =>
      match find_dup i n (Index.short_lhs_edges st) with
      | Some (existT _ j (pair e' Hj)) => ShortDuplicate e j e' Hj
      | None =>
          match est_of_binder bp b with
          | Some eb =>
              match group_status (decl_group bp eb) with
              | Some (GRedeclared a c rest) => ShortAmbiguous e a c rest
              | _ =>
                  match find (fun e2 => andb (negb (est_eqb e2 eb))
                                             (Nat.ltb (Index.nr_pos (est_node e2)) (Index.nr_pos b)))
                             (group_members bp eb) with
                  | Some prior =>
                      if is_variable_binder (est_node prior)
                      then ShortExistingVariable e prior else ShortExistingNonVariable e prior
                  | None => ShortNew e eb
                  end
              end
          | None => ShortBlank e
          end
      end
  end.

(* the exact ordered left-side statuses of a short statement, one per exact left edge, in source order *)
Definition short_lhs_statuses {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (st : Index.ShortStmtRef idx) : list { i : nat & ShortLhsStatus s st i } :=
  map (fun x => match x with existT _ i e => existT _ i (short_lhs_status bp e) end)
      (Index.short_lhs_edges st).

(* the exact new-nonblank evidence: the establishing left edge and its establishment, or a real absence *)
Inductive NewNonblank {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
  (st : Index.ShortStmtRef idx) : Type :=
| HasNewNonblank : forall i, Index.ShortLhsEdge st i -> Est s -> NewNonblank s st
| NoNewNonblank  : NewNonblank s st.
Arguments HasNewNonblank {p idx s st} _ _ _.
Arguments NoNewNonblank {p idx s st}.

Definition new_nonblank_of {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {st : Index.ShortStmtRef idx} (lefts : list { i : nat & ShortLhsStatus s st i }) : NewNonblank s st :=
  fold_right (fun x acc =>
                match x with existT _ i stx =>
                  match stx with ShortNew e est => HasNewNonblank i e est | _ => acc end
                end)
             NoNewNonblank lefts.

(* the one exact retained short-declaration status, tied to the exact statement ref *)
Record ShortDeclStatus {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
  (st : Index.ShortStmtRef idx) : Type := mk_short_status {
  sd_lefts : list { i : nat & ShortLhsStatus s st i } ;
  sd_newnb : NewNonblank s st ;
  sd_rhs   : list { j : nat & Index.ShortRhsEdge st j }
}.
Arguments mk_short_status {p idx s st} _ _ _.
Arguments sd_lefts {p idx s st} _.
Arguments sd_newnb {p idx s st} _.
Arguments sd_rhs {p idx s st} _.

(* the RHS cutpoint: the exact statement position, projected from the exact ref, never re-stored *)
Definition sd_cutpoint {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {st : Index.ShortStmtRef idx} (_ : ShortDeclStatus s st) : nat := Index.nr_pos (Index.sh_node st).

Definition short_decl_status {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (st : Index.ShortStmtRef idx) : ShortDeclStatus s st :=
  let lefts := short_lhs_statuses bp st in
  mk_short_status lefts (new_nonblank_of lefts) (Index.short_rhs_edges st).

(* the first duplicate short-left name, the exact short-declaration invalidity projected from the retained status *)
Definition short_stmt_dup_name {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (st : Index.ShortStmtRef idx) : option Names.OrdinaryIdentifier :=
  fold_right (fun x acc =>
                match x with existT _ i stx =>
                  match stx with ShortDuplicate self _ _ _ => binder_ident (Index.sl_child self) | _ => acc end
                end)
             None (sd_lefts (short_decl_status bp st)).
