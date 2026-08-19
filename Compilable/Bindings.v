(* Bindings — binders, blocks, objects, scopes, ordinary-name resolution, and the per-package fixed main. *)

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

Definition is_main_node {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx) : bool :=
  Index.is_main_view (Index.node_view r).

(* a fixed main declaration: an Index main occurrence qualified into its exact package *)
Record MainDeclRef {p} {idx : Index.ProgramIndex p}
  (s : PI.PackageSurface idx) (pr : PI.PackageRef s) : Type := main_decl_ref {
  main_occ : Index.MainOccurrenceRef idx ;
  main_pkg : PI.package_of_file s (Index.nr_file (Index.mo_node main_occ)) = pr
}.
Arguments main_decl_ref {p idx s pr} _ _.
Arguments main_occ {p idx s pr} _.
Arguments main_pkg {p idx s pr} _.

Definition main_node {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {pr : PI.PackageRef s}
  (m : MainDeclRef s pr) : Index.NodeRef idx := Index.mo_node (main_occ m).

Lemma main_declref_positional {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {pr : PI.PackageRef s}
  (a b : MainDeclRef s pr) : main_node a = main_node b -> a = b.
Proof.
  destruct a as [oa Pa], b as [ob Pb]; unfold main_node; cbn; intro E.
  assert (oa = ob) as Eo by (apply Index.mainocc_positional; exact E). subst ob.
  f_equal; apply (UIP_dec PI.packageref_eq_dec).
Qed.

(* the fixed main spelling is fixed by the source Main constructor, so a main is never a named binder *)
Lemma main_not_binder_view {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {pr : PI.PackageRef s}
  (m : MainDeclRef s pr) : forall bn, Index.node_view (main_node m) <> Index.VBindingName bn.
Proof.
  intros bn Heq. pose proof (Index.mo_ok (main_occ m)) as Hmo. unfold main_node in Heq.
  rewrite Heq in Hmo. discriminate Hmo.
Qed.

(* main multiplicity, independent of any ordinary declaration group keyed by main *)
Inductive MainStatus {p} {idx : Index.ProgramIndex p}
  (s : PI.PackageSurface idx) (pr : PI.PackageRef s) : Type :=
| MainMissing : MainStatus s pr
| MainOne : MainDeclRef s pr -> MainStatus s pr
| MainMultiple : MainDeclRef s pr -> MainDeclRef s pr -> list (MainDeclRef s pr) -> MainStatus s pr.
Arguments MainMissing {p idx s pr}.
Arguments MainOne {p idx s pr} _.
Arguments MainMultiple {p idx s pr} _ _ _.

Definition main_status_decls {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {pr : PI.PackageRef s}
  (st : MainStatus s pr) : list (MainDeclRef s pr) :=
  match st with
  | MainMissing => []
  | MainOne m => [m]
  | MainMultiple m1 m2 rest => m1 :: m2 :: rest
  end.

Inductive ObjectRef {p} (idx : Index.ProgramIndex p) : Type :=
| PredeclaredObject : Names.PredeclaredName -> ObjectRef idx
| SourceObject      : BinderRef idx -> ObjectRef idx
| MainObject        : Index.MainOccurrenceRef idx -> ObjectRef idx.
Arguments PredeclaredObject {p idx} _.
Arguments SourceObject {p idx} _.
Arguments MainObject {p idx} _.

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

Record Est {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type := mk_est {
  est_binder : BinderRef idx ;
  est_name   : Names.OrdinaryIdentifier ;
  est_scope  : ScopeId s ;
  est_vstart : nat
}.
Arguments mk_est {p idx s} _ _ _ _.
Arguments est_binder {p idx s} _.
Arguments est_name {p idx s} _.
Arguments est_scope {p idx s} _.
Arguments est_vstart {p idx s} _.

Definition make_est {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (nbt : Collections.NodeMap.t (option (Index.BlockRef idx))) (b : Index.NodeRef idx)
  : option (Est s) :=
  match binder_ident b with
  | Some n =>
      (match Index.node_role b as r return Index.node_role b = r -> option (Est s) with
       | Index.RSpecName fl => fun H => Some (mk_est (binder_ref b (spec_binder b fl H)) n (est_scope_of pr nbt b) (vis_start b))
       | Index.RShortLhs    => fun H => Some (mk_est (binder_ref b (short_binder b H)) n (est_scope_of pr nbt b) (vis_start b))
       | _ => fun _ => None
       end) eq_refl
  | None => None
  end.

(* establishments of a file in source order (ascending position); file_nodes is trie order, so iterate positions *)
Definition ests_of_file {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (fr : Index.FileRef idx) : list (Est s) :=
  let nbt := nearest_block_table fr in
  flat_map (fun pos => match Index.mk_noderef fr (Pos.of_succ_nat pos) with
                       | Some b => match make_est pr nbt b with Some e => [e] | None => [] end
                       | None => []
                       end)
           (seq 0 (Index.occ_count fr)).

Definition all_ests {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : list (Est s) :=
  flat_map (fun pr => flat_map (ests_of_file pr) (PI.pkg_members pr)) (PI.packages s).

Definition main_nodes_of {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) : list (Index.NodeRef idx) :=
  filter is_main_node (flat_map Index.file_nodes (PI.pkg_members pr)).

Lemma main_nodes_of_ok {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) : forall r, In r (main_nodes_of pr) ->
  is_main_node r = true /\ PI.package_of_file s (Index.nr_file r) = pr.
Proof.
  intros r Hin. unfold main_nodes_of in Hin. apply filter_In in Hin. destruct Hin as [Hin Hmain].
  split; [exact Hmain|]. apply in_flat_map in Hin. destruct Hin as [fr [Hfr Hrfn]].
  rewrite (Index.file_nodes_file fr r Hrfn). apply PI.package_of_file_member; exact Hfr.
Qed.

Fixpoint build_main_decls {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (nodes : list (Index.NodeRef idx))
  : (forall r, In r nodes -> is_main_node r = true /\ PI.package_of_file s (Index.nr_file r) = pr)
    -> list (MainDeclRef s pr) :=
  match nodes with
  | [] => fun _ => []
  | r :: rest => fun H =>
      main_decl_ref (Index.mkMainOccurrenceRef r (proj1 (H r (or_introl eq_refl)))) (proj2 (H r (or_introl eq_refl)))
      :: build_main_decls pr rest (fun r' Hr' => H r' (or_intror Hr'))
  end.

Lemma build_main_decls_nodes {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) : forall nodes H, map main_node (build_main_decls pr nodes H) = nodes.
Proof. induction nodes as [|r rest IH]; intro H; [reflexivity | cbn; f_equal; apply IH]. Qed.

Definition main_decls_of {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) : list (MainDeclRef s pr) :=
  build_main_decls pr (main_nodes_of pr) (main_nodes_of_ok pr).

Definition main_status_from {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {pr : PI.PackageRef s}
  (decls : list (MainDeclRef s pr)) : MainStatus s pr :=
  match decls with
  | [] => MainMissing
  | m :: nil => MainOne m
  | m1 :: m2 :: rest => MainMultiple m1 m2 rest
  end.

Lemma main_status_decls_from {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {pr : PI.PackageRef s}
  (decls : list (MainDeclRef s pr)) : main_status_decls (main_status_from decls) = decls.
Proof. destruct decls as [|m1 [|m2 rest]]; reflexivity. Qed.

Definition main_status_of {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) : MainStatus s pr := main_status_from (main_decls_of pr).

(* the retained binding phase, sealed to its one builder *)

Record RawBP {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type := mk_rawbp {
  rbp_ests : list (Est s) ;
  rbp_main : forall pr : PI.PackageRef s, MainStatus s pr
}.
Arguments mk_rawbp {p idx s} _ _.
Arguments rbp_ests {p idx s} _.
Arguments rbp_main {p idx s} _ _.

Definition raw_bindings {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : RawBP s :=
  mk_rawbp (all_ests s) (fun pr => main_status_of pr).
Definition BindingPhase {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
  { b : RawBP s | b = raw_bindings s }.
Definition bindings {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : BindingPhase s :=
  exist _ (raw_bindings s) eq_refl.
Definition bp_ests {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} (bp : BindingPhase s) : list (Est s) :=
  rbp_ests (proj1_sig bp).
Definition package_main {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (pr : PI.PackageRef s) : MainStatus s pr := rbp_main (proj1_sig bp) pr.

Theorem package_main_sound {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (pr : PI.PackageRef s) :
  map main_node (main_status_decls (package_main bp pr))
  = filter is_main_node (flat_map Index.file_nodes (PI.pkg_members pr)).
Proof.
  unfold package_main. rewrite (proj2_sig bp). cbn [rbp_main raw_bindings].
  unfold main_status_of. rewrite main_status_decls_from. unfold main_decls_of.
  rewrite build_main_decls_nodes. reflexivity.
Qed.

Lemma main_is_package_local {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (pr : PI.PackageRef s) :
  forall m, In m (main_status_decls (package_main bp pr)) -> PI.package_of_file s (Index.nr_file (main_node m)) = pr.
Proof. intros m _; exact (main_pkg m). Qed.

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

Inductive Resolved {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (use : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) : Type :=
| RBound   : ObjectRef idx -> Resolved bp use n
| RUnbound : Resolved bp use n.
Arguments RBound {p idx s bp use n} _.
Arguments RUnbound {p idx s bp use n}.

(* the source identifier "main"; the fixed package-scope main function resolves under this ordinary name *)
Definition main_ident : Names.OrdinaryIdentifier :=
  Names.MakeOrdinary (Names.MakeIdentifier "main"%string eq_refl) eq_refl.

(* the resolvable main object of a package: its first main occurrence, or none when the package has no main *)
Definition package_main_occ {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (pr : PI.PackageRef s) : option (Index.MainOccurrenceRef idx) :=
  match package_main bp pr with
  | MainMissing => None
  | MainOne m => Some (main_occ m)
  | MainMultiple m _ _ => Some (main_occ m)
  end.

(* ordinary resolution: nearest source binding (a local main shadows), then the package main, then predeclared *)
Definition resolve {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (use : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) : Resolved bp use n :=
  match pick_best (source_cands bp use n) with
  | Some e => RBound (SourceObject (est_binder e))
  | None =>
      match (if Names.ordinary_equalb n main_ident
             then package_main_occ bp (PI.package_of_file s (Index.nr_file use)) else None) with
      | Some m => RBound (MainObject m)
      | None =>
          match Names.classify_predeclared (Names.ordinary_spelling n) with
          | Some pn => RBound (PredeclaredObject pn)
          | None => RUnbound
          end
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
  | RBound (SourceObject b) => exists e, In e (source_cands bp use n) /\ est_binder e = b
  | RBound (MainObject m) =>
      source_cands bp use n = [] /\ Names.ordinary_equalb n main_ident = true
      /\ package_main_occ bp (PI.package_of_file s (Index.nr_file use)) = Some m
  | RBound (PredeclaredObject pn) =>
      source_cands bp use n = [] /\ Names.classify_predeclared (Names.ordinary_spelling n) = Some pn
  | RUnbound =>
      source_cands bp use n = [] /\ Names.classify_predeclared (Names.ordinary_spelling n) = None
  end.
Proof.
  unfold resolve. destruct (pick_best (source_cands bp use n)) as [e|] eqn:E.
  - exists e; split; [ apply pick_best_in; exact E | reflexivity ].
  - pose proof (pick_best_none _ E) as Hnil.
    destruct (if Names.ordinary_equalb n main_ident
              then package_main_occ bp (PI.package_of_file s (Index.nr_file use)) else None) as [m|] eqn:Em.
    + destruct (Names.ordinary_equalb n main_ident) eqn:Eq; [ split; [exact Hnil | split; [reflexivity | exact Em]] | discriminate Em ].
    + destruct (Names.classify_predeclared (Names.ordinary_spelling n)) eqn:Ec; split; try exact Hnil; try reflexivity.
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

(* two establishments are the same establishment iff they share their exact binder occurrence *)
Definition est_eqb {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} (a b : Est s) : bool :=
  noderef_eqb (binder_node (est_binder a)) (binder_node (est_binder b)).

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
  match Index.node_view c with Index.VConstSpec (Index.CSExplicit _) => true | _ => false end.

(* the effective explicit origin of a const spec: itself if explicit, else the nearest preceding explicit spec *)
Definition const_effective_origin {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx) : option (Index.NodeRef idx) :=
  if is_explicit_const_spec r then Some r
  else match Index.node_parent r with
       | Some par =>
           fold_left (fun acc c => if andb (Nat.ltb (Index.nr_pos c) (Index.nr_pos r)) (is_explicit_const_spec c)
                                   then Some c else acc) (Index.node_children par) None
       | None => None
       end.

(* a short left-hand name repeated earlier in the same short statement is an exact duplicate (invalid) left status *)
Definition short_lhs_duplicate {p} {idx : Index.ProgramIndex p}
  (r : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) : bool :=
  match Index.node_parent r with
  | Some stmt =>
      existsb (fun c => andb (Nat.ltb (Index.nr_pos c) (Index.nr_pos r))
                             (match binder_ident c with Some m => Names.ordinary_equalb m n | None => false end))
              (filter (fun c => match Index.node_role c with Index.RShortLhs => true | _ => false end)
                      (Index.node_children stmt))
  | None => false
  end.
