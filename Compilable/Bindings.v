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

(* the binder emission of one occurrence, factored over its role so laws can invert it exactly *)
Definition make_est_emit {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (nbt : Collections.NodeMap.t (option (Index.BlockRef idx))) (b : Index.NodeRef idx)
  (n : Names.OrdinaryIdentifier) (ro : Index.Role) (H : Index.node_role b = ro) : option (Est s) :=
  match ro as r return Index.node_role b = r -> option (Est s) with
  | Index.RSpecName fl => fun H0 => Some (mk_est (DOBinder (binder_ref b (spec_binder b fl H0))) n (est_scope_of pr nbt b) (vis_start b))
  | Index.RShortLhs    => fun H0 => Some (mk_est (DOBinder (binder_ref b (short_binder b H0))) n (est_scope_of pr nbt b) (vis_start b))
  | _ => fun _ => None
  end H.

(* an ordinary name binder establishes its name at its scope *)
Definition make_est {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (nbt : Collections.NodeMap.t (option (Index.BlockRef idx))) (b : Index.NodeRef idx)
  : option (Est s) :=
  match binder_ident b with
  | Some n => make_est_emit pr nbt b n (Index.node_role b) eq_refl
  | None => None
  end.

Lemma make_est_emit_binder {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (nbt : Collections.NodeMap.t (option (Index.BlockRef idx))) (b : Index.NodeRef idx)
  (n : Names.OrdinaryIdentifier) (ro : Index.Role) (H : Index.node_role b = ro) :
  is_binder_role ro = true ->
  exists est, make_est_emit pr nbt b n ro H = Some est /\ est_node est = b.
Proof.
  intro Hb. revert H. destruct ro; try discriminate Hb; intro H;
    eexists; split; reflexivity.
Qed.

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




(* the canonical complete new-nonblank summary: exactly the retained ShortNew left judgments, in order *)
Definition short_new_members {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {core : list (Est s)} {st : Index.ShortStmtRef idx} (sj : ShortJudgment core st)
  : list { i : nat & ShortLhsJudgment core st i } :=
  filter (fun x => match slj_view (projT2 x) with SVNew _ => true | _ => false end) (sj_lefts sj).

(* the first duplicate short-left name, projected from the exact retained judgment views *)
Definition sj_dup_name {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {core : list (Est s)} {st : Index.ShortStmtRef idx} (sj : ShortJudgment core st)
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

(* the phase-level duplicate projection: the retained judgment row's views, never a recomputation *)
Definition short_stmt_dup_name {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (st : Index.ShortStmtRef idx) : option Names.OrdinaryIdentifier :=
  sj_dup_name (projT2 (sjr_row (short_decl_judgment bp st))).

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

(* est existence: every nonblank binder occurrence of the surface establishes in the retained core *)
Lemma all_ests_has_binder {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx)
  (b : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) :
  binder_ident b = Some n -> is_binder_role (Index.node_role b) = true ->
  exists est, In est (all_ests s) /\ est_node est = b.
Proof.
  intros Hb Hr.
  set (fr := Index.nr_file b).
  set (pr := PI.package_of_file s fr).
  set (nbt := nearest_block_table fr).
  assert (Hmk : Index.mk_noderef fr (Pos.of_succ_nat (Index.nr_pos b)) = Some b)
    by (rewrite <- Index.nr_key_pos; apply Index.mk_noderef_self).
  assert (Hmain : make_main_est pr b = None).
  { apply make_main_est_none. rewrite (binder_ident_view b n Hb). reflexivity. }
  destruct (make_est_emit_binder pr nbt b n (Index.node_role b) eq_refl Hr) as [est [Hemit Hnode]].
  assert (Hnodee : est_of_node pr nbt b = Some est).
  { unfold est_of_node. rewrite Hmain. unfold make_est. rewrite Hb. exact Hemit. }
  exists est. split; [| exact Hnode ].
  unfold all_ests. apply in_flat_map.
  exists pr. split; [ apply PI.packages_complete |].
  apply in_flat_map. exists fr. split; [ apply PI.pkg_members_of_file |].
  unfold ests_of_file. apply in_flat_map. exists (Index.nr_pos b). split.
  - apply in_seq. pose proof (nr_pos_lt b). unfold fr. lia.
  - rewrite Hmk. fold nbt. rewrite Hnodee. left. reflexivity.
Qed.

(* the retained-core lookup succeeds for every nonblank binder *)
Lemma est_of_binder_core_some {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (b : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) :
  binder_ident b = Some n -> is_binder_role (Index.node_role b) = true ->
  exists est, est_of_binder_core (bp_ests bp) b = Some est.
Proof.
  intros Hb Hr.
  assert (Hcore : bp_ests bp = all_ests s)
    by (unfold bp_ests; rewrite (proj2_sig bp); reflexivity).
  destruct (all_ests_has_binder s b n Hb Hr) as [est [Hin Hnode]].
  unfold est_of_binder_core.
  destruct (find (fun e => noderef_eqb (est_node e) b) (bp_ests bp)) as [e0|] eqn:Hf.
  - exists e0. reflexivity.
  - exfalso.
    pose proof (find_none _ _ Hf est) as Hno.
    rewrite Hcore in Hno. specialize (Hno Hin).
    rewrite Hnode in Hno. rewrite (proj2 (noderef_eqb_spec b b) eq_refl) in Hno. discriminate Hno.
Qed.

(* the blank law: a retained-core blank classification pins a genuinely blank identifier *)
Lemma slj_blank_exact {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) {st : Index.ShortStmtRef idx} {i : nat} (e : Index.ShortLhsEdge st i) :
  short_lhs_decide (bp_ests bp) e = SVBlank -> binder_ident (Index.sl_child e) = None.
Proof.
  intro Hd. unfold short_lhs_decide in Hd.
  destruct (binder_ident (Index.sl_child e)) as [n|] eqn:Hb; [| reflexivity ].
  exfalso.
  destruct (find_dup i n (Index.short_lhs_edges st)) as [[j w]|]; [ discriminate Hd |].
  destruct (est_of_binder_core (bp_ests bp) (Index.sl_child e)) as [eb|] eqn:He.
  - destruct (group_status (decl_group_core (bp_ests bp) eb)) as [[?|? ? ?]|];
      [ | discriminate Hd | ];
      (destruct (find (fun e2 => andb (negb (est_eqb e2 eb))
                                      (Nat.ltb (Index.nr_pos (est_node e2))
                                               (Index.nr_pos (Index.sl_child e))))
                      (group_members_core (bp_ests bp) eb)) as [prior|];
       [ destruct (is_variable_binder (est_node prior)); discriminate Hd | discriminate Hd ]).
  - assert (Hrole : is_binder_role (Index.node_role (Index.sl_child e)) = true)
      by (rewrite (Index.sl_role e); reflexivity).
    destruct (est_of_binder_core_some bp (Index.sl_child e) n Hb Hrole) as [est Hs].
    rewrite He in Hs. discriminate Hs.
Qed.

(* the new law: the establishment is a retained-core member whose exact source origin is this edge *)
Lemma slj_new_exact {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) {st : Index.ShortStmtRef idx} {i : nat} (e : Index.ShortLhsEdge st i)
  (eb : Est s) :
  short_lhs_decide (bp_ests bp) e = SVNew eb ->
  In eb (bp_ests bp) /\ est_node eb = Index.sl_child e
  /\ exists n, binder_ident (Index.sl_child e) = Some n
               /\ find_dup i n (Index.short_lhs_edges st) = None.
Proof.
  intro Hd. unfold short_lhs_decide in Hd.
  destruct (binder_ident (Index.sl_child e)) as [n|] eqn:Hb; [| discriminate Hd ].
  destruct (find_dup i n (Index.short_lhs_edges st)) as [[j w]|] eqn:Hdup; [ discriminate Hd |].
  destruct (est_of_binder_core (bp_ests bp) (Index.sl_child e)) as [eb0|] eqn:He; [| discriminate Hd ].
  unfold est_of_binder_core in He.
  pose proof (find_some _ _ He) as [Hin Heqb].
  apply noderef_eqb_spec in Heqb.
  destruct (group_status (decl_group_core (bp_ests bp) eb0)) as [[?|? ? ?]|];
    try discriminate Hd;
    (destruct (find (fun e2 => andb (negb (est_eqb e2 eb0))
                                    (Nat.ltb (Index.nr_pos (est_node e2))
                                             (Index.nr_pos (Index.sl_child e))))
                    (group_members_core (bp_ests bp) eb0)) as [prior|];
     [ destruct (is_variable_binder (est_node prior)); discriminate Hd
     | injection Hd as <-; split; [ exact Hin | split; [ exact Heqb | exists n; split; [ reflexivity | exact Hdup ] ] ] ]).
Qed.

(* the existing laws: the prior is a same-group retained member, strictly earlier, of the exact kind *)
Lemma slj_existing_exact {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) {st : Index.ShortStmtRef idx} {i : nat} (e : Index.ShortLhsEdge st i)
  (eb prior : Est s) (isvar : bool) :
  short_lhs_decide (bp_ests bp) e
  = (if isvar then SVExistingVariable eb prior else SVExistingNonVariable eb prior) ->
  In prior (group_members_core (bp_ests bp) eb)
  /\ Nat.ltb (Index.nr_pos (est_node prior)) (Index.nr_pos (Index.sl_child e)) = true
  /\ est_eqb prior eb = false
  /\ is_variable_binder (est_node prior) = isvar.
Proof.
  intro Hd. unfold short_lhs_decide in Hd.
  destruct (binder_ident (Index.sl_child e)) as [n|] eqn:Hb; [| destruct isvar; discriminate Hd ].
  destruct (find_dup i n (Index.short_lhs_edges st)) as [[j w]|]; [ destruct isvar; discriminate Hd |].
  destruct (est_of_binder_core (bp_ests bp) (Index.sl_child e)) as [eb0|] eqn:He;
    [| destruct isvar; discriminate Hd ].
  destruct (group_status (decl_group_core (bp_ests bp) eb0)) as [[?|? ? ?]|];
    try (destruct isvar; discriminate Hd);
    (destruct (find (fun e2 => andb (negb (est_eqb e2 eb0))
                                    (Nat.ltb (Index.nr_pos (est_node e2))
                                             (Index.nr_pos (Index.sl_child e))))
                    (group_members_core (bp_ests bp) eb0)) as [prior0|] eqn:Hfind;
    try (destruct isvar; discriminate Hd);
    (pose proof (find_some _ _ Hfind) as [Hin Hcond];
     apply Bool.andb_true_iff in Hcond; destruct Hcond as [Hne Hlt];
     destruct (is_variable_binder (est_node prior0)) eqn:Hvar; destruct isvar;
     try discriminate Hd;
     injection Hd as <- <-;
     (split; [ exact Hin
             | split; [ exact Hlt
                      | split; [ apply Bool.negb_true_iff in Hne; exact Hne | exact Hvar ] ] ]))).
Qed.

(* the ambiguity law: the exact redeclared declaration group of the resolved establishment *)
Lemma slj_ambiguous_exact {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) {st : Index.ShortStmtRef idx} {i : nat} (e : Index.ShortLhsEdge st i)
  (a c : Est s) (rest : list (Est s)) :
  short_lhs_decide (bp_ests bp) e = SVAmbiguous a c rest ->
  exists eb, est_of_binder_core (bp_ests bp) (Index.sl_child e) = Some eb
             /\ group_status (decl_group_core (bp_ests bp) eb) = Some (GRedeclared a c rest).
Proof.
  intro Hd. unfold short_lhs_decide in Hd.
  destruct (binder_ident (Index.sl_child e)) as [n|] eqn:Hb; [| discriminate Hd ].
  destruct (find_dup i n (Index.short_lhs_edges st)) as [[j w]|]; [ discriminate Hd |].
  destruct (est_of_binder_core (bp_ests bp) (Index.sl_child e)) as [eb0|] eqn:He; [| discriminate Hd ].
  destruct (group_status (decl_group_core (bp_ests bp) eb0)) as [[?|a0 c0 rest0]|] eqn:Hg;
    try (destruct (find (fun e2 => andb (negb (est_eqb e2 eb0))
                                        (Nat.ltb (Index.nr_pos (est_node e2))
                                                 (Index.nr_pos (Index.sl_child e))))
                        (group_members_core (bp_ests bp) eb0)) as [prior|];
         [ destruct (is_variable_binder (est_node prior)); discriminate Hd | discriminate Hd ]).
  injection Hd as <- <- <-. exists eb0. split; [ reflexivity | exact Hg ].
Qed.

(* the duplicate law: an exact same-name earlier left exists at the retained witness index *)
Lemma slj_dup_exact {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) {st : Index.ShortStmtRef idx} {i : nat} (e : Index.ShortLhsEdge st i)
  (j : nat) :
  short_lhs_decide (bp_ests bp) e = SVDuplicate j ->
  exists n w, binder_ident (Index.sl_child e) = Some n
              /\ find_dup i n (Index.short_lhs_edges st) = Some (existT _ j w).
Proof.
  intro Hd. unfold short_lhs_decide in Hd.
  destruct (binder_ident (Index.sl_child e)) as [n|] eqn:Hb; [| discriminate Hd ].
  destruct (find_dup i n (Index.short_lhs_edges st)) as [[j0 w]|] eqn:Hdup.
  - injection Hd as <-. exists n, w. split; [ reflexivity | exact Hdup ].
  - destruct (est_of_binder_core (bp_ests bp) (Index.sl_child e)) as [eb0|]; [| discriminate Hd ].
    destruct (group_status (decl_group_core (bp_ests bp) eb0)) as [[?|? ? ?]|];
      try (destruct (find (fun e2 => andb (negb (est_eqb e2 eb0))
                                          (Nat.ltb (Index.nr_pos (est_node e2))
                                                   (Index.nr_pos (Index.sl_child e))))
                          (group_members_core (bp_ests bp) eb0)) as [prior|];
           [ destruct (is_variable_binder (est_node prior)); discriminate Hd | discriminate Hd ]).
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

(* no alternative classification can inhabit the same core, statement, and left index *)
Lemma slj_canonical {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  {core : list (Est s)} {st : Index.ShortStmtRef idx} {i : nat}
  (j1 j2 : ShortLhsJudgment core st i) :
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

Lemma short_ref_emit_node {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx)
  (v : Index.NodeView) (Hv : Index.node_view r = v) (st : Index.ShortStmtRef idx) :
  In st (short_ref_emit r v Hv) -> Index.sh_node st = r.
Proof.
  destruct v; cbn; try (intros F; exact (match F with end)).
  match goal with sh0 : Index.StmtShape |- _ =>
    destruct sh0; cbn; try (intros F; exact (match F with end)) end.
  intros [He|F]; [ rewrite <- He; reflexivity | destruct F ].
Qed.

Lemma const_ref_emit_nodup {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx)
  (v : Index.NodeView) (Hv : Index.node_view r = v) : NoDup (const_ref_emit r v Hv).
Proof. destruct v; cbn; repeat constructor; intros F; destruct F. Qed.

Lemma short_ref_emit_nodup {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx)
  (v : Index.NodeView) (Hv : Index.node_view r = v) : NoDup (short_ref_emit r v Hv).
Proof.
  destruct v; cbn; try (repeat constructor; intros F; destruct F).
  match goal with sh0 : Index.StmtShape |- _ =>
    destruct sh0; cbn; repeat constructor; intros F; destruct F end.
Qed.

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

(* the short subjects are duplicate-free: one exact subject per source statement *)
Lemma short_subjects_nodup {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) :
  NoDup (short_subjects s).
Proof.
  unfold short_subjects.
  apply (flat_map_nodup _ (fun st => PI.package_of_file s (Index.nr_file (Index.sh_node st))));
    [ apply packages_nodup | |].
  - intros pr _.
    apply (flat_map_nodup _ (fun st => Index.nr_file (Index.sh_node st)));
      [ apply pkg_members_nodup | |].
    + intros fr _. unfold short_stmts_of_file.
      apply (flat_map_nodup _ (fun st => Index.nr_pos (Index.sh_node st)));
        [ apply seq_NoDup | |].
      * intros pos _. destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|]; [| constructor ].
        apply short_ref_emit_nodup.
      * intros pos st _ Hin.
        destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
        rewrite (short_ref_emit_node r _ _ st Hin).
        exact (noderef_pos_of_key r pos (mk_noderef_key fr _ r Hmk)).
    + intros fr st _ Hin.
      unfold short_stmts_of_file in Hin. apply in_flat_map in Hin.
      destruct Hin as [pos [_ Hin]].
      destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
      rewrite (short_ref_emit_node r _ _ st Hin).
      exact (Index.mk_noderef_file fr _ r Hmk).
  - intros pr st Hpr Hin.
    apply in_flat_map in Hin. destruct Hin as [fr [Hfr Hin]].
    unfold short_stmts_of_file in Hin. apply in_flat_map in Hin.
    destruct Hin as [pos [_ Hin]].
    destruct (Index.mk_noderef fr (Pos.of_succ_nat pos)) as [r|] eqn:Hmk; [| destruct Hin ].
    rewrite (short_ref_emit_node r _ _ st Hin).
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

(* each short subject appears exactly once *)
Lemma bp_shorts_exactly_once {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (o1 o2 : nat)
  (row1 row2 : { st : Index.ShortStmtRef idx & ShortJudgment (bp_ests bp) st }) :
  nth_error (bp_shorts bp) o1 = Some row1 -> nth_error (bp_shorts bp) o2 = Some row2 ->
  projT1 row1 = projT1 row2 -> o1 = o2.
Proof.
  intros H1 H2 He.
  assert (Hnd : NoDup (map (fun row => projT1 row) (bp_shorts bp)))
    by (rewrite bp_shorts_subjects; apply short_subjects_nodup).
  assert (Hm1 : nth_error (map (fun row => projT1 row) (bp_shorts bp)) o1 = Some (projT1 row1))
    by (exact (map_nth_error _ o1 _ H1)).
  assert (Hm2 : nth_error (map (fun row => projT1 row) (bp_shorts bp)) o2 = Some (projT1 row2))
    by (exact (map_nth_error _ o2 _ H2)).
  apply (proj1 (NoDup_nth_error _) Hnd o1 o2).
  - apply nth_error_Some. rewrite Hm1. discriminate.
  - rewrite Hm1, Hm2, He. reflexivity.
Qed.
