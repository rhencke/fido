(* Bindings — binders, blocks, objects, scopes, ordinary-name resolution, and package-scope function declarations. *)

From Stdlib Require Import String List Bool Arith PeanoNat Lia Eqdep_dec PArith.
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

(* the retained binding phase, sealed to its one builder; main status is a projection over the establishments *)

Record RawBP {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type := mk_rawbp {
  rbp_ests : list (Est s)
}.
Arguments mk_rawbp {p idx s} _.
Arguments rbp_ests {p idx s} _.

Definition raw_bindings {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : RawBP s :=
  mk_rawbp (all_ests s).
Definition BindingPhase {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
  { b : RawBP s | b = raw_bindings s }.
Definition bindings {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : BindingPhase s :=
  exist _ (raw_bindings s) eq_refl.
Definition bp_ests {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} (bp : BindingPhase s) : list (Est s) :=
  rbp_ests (proj1_sig bp).

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

(* the ordered members of e's group: every establishment sharing e's scope and spelling, in bp_ests source order *)
Definition group_members {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (e : Est s) : list (Est s) := filter (same_group e) (bp_ests bp).

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

(* the declaration members of e's group; a redeclared declaration group is an ambiguous name *)
Definition decl_group {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (e : Est s) : list (Est s) := filter is_decl_est (group_members bp e).
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

(* the immediately-preceding sibling spec of a declaration spec, in source order — its inheritance predecessor *)
Definition spec_predecessor {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx) : option (Index.NodeRef idx) :=
  match Index.node_parent r with
  | Some par => fold_left (fun acc c => if Nat.ltb (Index.nr_pos c) (Index.nr_pos r) then Some c else acc)
                          (Index.node_children par) None
  | None => None
  end.

(* a spec heads its declaration exactly when it has no predecessor; a first inherited const spec is invalid *)
Definition spec_is_first {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx) : bool :=
  match spec_predecessor r with Some _ => false | None => true end.

Definition is_explicit_const_spec {p} {idx : Index.ProgramIndex p} (c : Index.NodeRef idx) : bool :=
  match Index.node_view c with Index.VConstSpec (Index.CSExplicit _ _ _) => true | _ => false end.

(* the effective explicit origin of a const spec: itself if explicit, else the nearest preceding explicit spec *)
Definition const_effective_origin {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx) : option (Index.NodeRef idx) :=
  if is_explicit_const_spec r then Some r
  else match Index.node_parent r with
       | Some par =>
           fold_left (fun acc c => if andb (Nat.ltb (Index.nr_pos c) (Index.nr_pos r)) (is_explicit_const_spec c)
                                   then Some c else acc) (Index.node_children par) None
       | None => None
       end.

(* a spec's ordered binding-name children: the exact names it declares, in source order *)
Definition spec_name_binders {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx) : list (Index.NodeRef idx) :=
  filter (fun c => match Index.node_role c with Index.RSpecName _ => true | _ => false end) (Index.node_children r).

(* a spec's optional type-use child; genuine absence (no type) is a real None, not a degraded edge *)
Definition spec_type_ref {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx) : option (Index.NodeRef idx) :=
  find (fun c => match Index.node_role c with Index.RTypeUse => true | _ => false end) (Index.node_children r).

(* a spec's ordered value-expression children, in source order *)
Definition spec_value_refs {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx) : list (Index.NodeRef idx) :=
  filter (fun c => match Index.node_role c with Index.RPlain => true | _ => false end) (Index.node_children r).

(* the ordered chain of preceding sibling specs; with no effective explicit origin this is the invalid chain *)
Definition const_predecessor_chain {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx) : list (Index.NodeRef idx) :=
  match Index.node_parent r with
  | Some par => filter (fun c => Nat.ltb (Index.nr_pos c) (Index.nr_pos r)) (Index.node_children par)
  | None => []
  end.

(* the one exact retained const-spec status: shape, effective origin, invalid chain, and name/type/value refs *)
Record ConstSpecStatus {p} (idx : Index.ProgramIndex p) : Type := mk_const_status {
  cs_explicit  : bool ;
  cs_first     : bool ;
  cs_origin    : option (Index.NodeRef idx) ;
  cs_predchain : list (Index.NodeRef idx) ;
  cs_names     : list (Index.NodeRef idx) ;
  cs_type      : option (Index.NodeRef idx) ;
  cs_values    : list (Index.NodeRef idx)
}.
Arguments mk_const_status {p idx} _ _ _ _ _ _ _.
Arguments cs_explicit {p idx} _. Arguments cs_first {p idx} _. Arguments cs_origin {p idx} _.
Arguments cs_predchain {p idx} _. Arguments cs_names {p idx} _. Arguments cs_type {p idx} _. Arguments cs_values {p idx} _.

Definition const_spec_status {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx) : ConstSpecStatus idx :=
  mk_const_status (is_explicit_const_spec r) (spec_is_first r) (const_effective_origin r)
                  (const_predecessor_chain r) (spec_name_binders r) (spec_type_ref r) (spec_value_refs r).

(* a binder introduces a variable object exactly when it is a short-lhs or var-spec name *)
Definition is_variable_binder {p} {idx : Index.ProgramIndex p} (b : Index.NodeRef idx) : bool :=
  match Index.node_role b with Index.RShortLhs | Index.RSpecName Index.VarSpecF => true | _ => false end.

(* the first earlier same-statement short-lhs binder repeating this name, in source order *)
Definition short_first_dup {p} {idx : Index.ProgramIndex p}
  (b : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) : option (Index.NodeRef idx) :=
  match Index.node_parent b with
  | Some stmt =>
      find (fun c => andb (Nat.ltb (Index.nr_pos c) (Index.nr_pos b))
                          (match binder_ident c with Some m => Names.ordinary_equalb m n | None => false end))
           (filter (fun c => match Index.node_role c with Index.RShortLhs => true | _ => false end)
                   (Index.node_children stmt))
  | None => None
  end.

(* the establishment carried by a binder occurrence, when it establishes one *)
Definition est_of_binder {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (b : Index.NodeRef idx) : option (Est s) :=
  find (fun e => noderef_eqb (est_node e) b) (bp_ests bp).

(* the exact ordered left-side status of one short-declaration name *)
Inductive ShortLhsStatus {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
| ShortBlank               : Index.NodeRef idx -> ShortLhsStatus s
| ShortNew                 : Est s -> ShortLhsStatus s
| ShortExistingVariable    : Est s -> ShortLhsStatus s
| ShortExistingNonVariable : Est s -> ShortLhsStatus s
| ShortDuplicate           : Index.NodeRef idx -> Index.NodeRef idx -> ShortLhsStatus s
| ShortAmbiguous           : Est s -> Est s -> list (Est s) -> ShortLhsStatus s.
Arguments ShortBlank {p idx s} _.
Arguments ShortNew {p idx s} _.
Arguments ShortExistingVariable {p idx s} _.
Arguments ShortExistingNonVariable {p idx s} _.
Arguments ShortDuplicate {p idx s} _ _.
Arguments ShortAmbiguous {p idx s} _ _ _.

Definition short_lhs_status {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (b : Index.NodeRef idx) : ShortLhsStatus s :=
  match binder_ident b with
  | None => ShortBlank b
  | Some n =>
      match short_first_dup b n with
      | Some first => ShortDuplicate first b
      | None =>
          match est_of_binder bp b with
          | Some eb =>
              match group_status (decl_group bp eb) with
              | Some (GRedeclared a c rest) => ShortAmbiguous a c rest
              | _ =>
                  match find (fun e => andb (negb (est_eqb e eb))
                                            (Nat.ltb (Index.nr_pos (est_node e)) (Index.nr_pos b)))
                             (group_members bp eb) with
                  | Some prior =>
                      if is_variable_binder (est_node prior)
                      then ShortExistingVariable prior else ShortExistingNonVariable prior
                  | None => ShortNew eb
                  end
              end
          | None => ShortBlank b
          end
      end
  end.

(* the exact ordered left-side statuses of a short declaration statement, in source order *)
Definition short_lhs_statuses {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (stmt : Index.NodeRef idx) : list (ShortLhsStatus s) :=
  map (short_lhs_status bp)
      (filter (fun c => match Index.node_role c with Index.RShortLhs => true | _ => false end)
              (Index.node_children stmt)).

(* the exact new-nonblank evidence of a short declaration: the first ShortNew establishment, or its absence *)
Inductive NewNonblank {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
| HasNewNonblank : Est s -> NewNonblank s
| NoNewNonblank  : NewNonblank s.
Arguments HasNewNonblank {p idx s} _.
Arguments NoNewNonblank {p idx s}.

Definition new_nonblank_of {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (lefts : list (ShortLhsStatus s)) : NewNonblank s :=
  fold_right (fun st acc => match st with ShortNew e => HasNewNonblank e | _ => acc end) NoNewNonblank lefts.

(* the one exact retained short-declaration status: ordered left statuses, new-nonblank evidence, RHS refs, cutpoint *)
Record ShortDeclStatus {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type := mk_short_status {
  sd_lefts    : list (ShortLhsStatus s) ;
  sd_newnb    : NewNonblank s ;
  sd_rhs      : list (Index.NodeRef idx) ;
  sd_cutpoint : nat
}.
Arguments mk_short_status {p idx s} _ _ _ _.
Arguments sd_lefts {p idx s} _.
Arguments sd_newnb {p idx s} _.
Arguments sd_rhs {p idx s} _.
Arguments sd_cutpoint {p idx s} _.

(* the RHS is evaluated at the cutpoint, before the new left objects become visible past the statement extent *)
Definition short_decl_status {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (stmt : Index.NodeRef idx) : ShortDeclStatus s :=
  let lefts := short_lhs_statuses bp stmt in
  mk_short_status lefts (new_nonblank_of lefts) (spec_value_refs stmt) (Index.nr_pos stmt).

(* the first duplicate short-left name, the exact short-declaration invalidity projected from the retained status *)
Definition short_stmt_dup_name {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (stmt : Index.NodeRef idx) : option Names.OrdinaryIdentifier :=
  fold_right (fun st acc => match st with ShortDuplicate _ later => binder_ident later | _ => acc end)
             None (sd_lefts (short_decl_status bp stmt)).
