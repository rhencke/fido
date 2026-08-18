(* Bindings — binders, blocks, objects, scopes, ordinary-name resolution, and the per-package fixed main. *)

From Stdlib Require Import List Bool Arith PeanoNat Lia Eqdep_dec.
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
| SourceObject      : BinderRef idx -> ObjectRef idx.
Arguments PredeclaredObject {p idx} _.
Arguments SourceObject {p idx} _.

Inductive ScopeId {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
| PackageScope : PI.PackageRef s -> ScopeId s
| BlockScope   : Index.BlockRef idx -> ScopeId s.
Arguments PackageScope {p idx s} _.
Arguments BlockScope {p idx s} _.

Definition is_spec_kind (k : Index.Kind) : bool := match k with Index.SpecKind _ => true | _ => false end.
Definition is_stmt_kind (k : Index.Kind) : bool := match k with Index.StmtKind => true | _ => false end.

(* the nearest block enclosing [b] (largest start position among containing blocks), carrying its reference *)
Definition nearest_block {p} {idx : Index.ProgramIndex p}
  (nodes : list (Index.NodeRef idx)) (b : Index.NodeRef idx) : option (Index.BlockRef idx) :=
  fold_right (fun a acc =>
    match mk_blockref a with
    | Some br =>
        if andb (Nat.ltb (Index.nr_pos a) (Index.nr_pos b)) (Nat.leb (Index.nr_pos b) (Index.node_extent a))
        then match acc with
             | Some br' => if Nat.ltb (Index.nr_pos (Index.bl_node br')) (Index.nr_pos a) then Some br else acc
             | None => Some br
             end
        else acc
    | None => acc
    end) None nodes.

(* the extent of the nearest ancestor of [b] whose kind passes [kb], or [b]'s own position if none *)
Definition nearest_kind_extent {p} {idx : Index.ProgramIndex p}
  (kb : Index.Kind -> bool) (nodes : list (Index.NodeRef idx)) (b : Index.NodeRef idx) : nat :=
  match fold_right (fun a acc =>
    if andb (kb (Index.node_kind a))
            (andb (Nat.ltb (Index.nr_pos a) (Index.nr_pos b)) (Nat.leb (Index.nr_pos b) (Index.node_extent a)))
    then match acc with Some a' => if Nat.ltb (Index.nr_pos a') (Index.nr_pos a) then Some a else acc | None => Some a end
    else acc) None nodes
  with Some a => Index.node_extent a | None => Index.nr_pos b end.

(* where a block-scoped binder becomes visible: type at its identifier, const/var at spec end, short at statement end *)
Definition vis_start {p} {idx : Index.ProgramIndex p} (b : Index.NodeRef idx) : nat :=
  let nodes := Index.file_nodes (Index.nr_file b) in
  match Index.node_role b with
  | Index.RSpecName Index.TypeSpecF => Index.nr_pos b
  | Index.RSpecName _ => nearest_kind_extent is_spec_kind nodes b
  | Index.RShortLhs   => nearest_kind_extent is_stmt_kind nodes b
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
  (pr : PI.PackageRef s) (b : Index.NodeRef idx) : ScopeId s :=
  match nearest_block (Index.file_nodes (Index.nr_file b)) b with
  | Some br => BlockScope br
  | None => PackageScope pr
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
  (pr : PI.PackageRef s) (b : Index.NodeRef idx) : option (Est s) :=
  match binder_ident b with
  | Some n =>
      (match Index.node_role b as r return Index.node_role b = r -> option (Est s) with
       | Index.RSpecName fl => fun H => Some (mk_est (binder_ref b (spec_binder b fl H)) n (est_scope_of pr b) (vis_start b))
       | Index.RShortLhs    => fun H => Some (mk_est (binder_ref b (short_binder b H)) n (est_scope_of pr b) (vis_start b))
       | _ => fun _ => None
       end) eq_refl
  | None => None
  end.

Definition ests_of_file {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) (fr : Index.FileRef idx) : list (Est s) :=
  fold_right (fun b acc => match make_est pr b with Some e => e :: acc | None => acc end) [] (Index.file_nodes fr).

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

Definition resolve {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (use : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) : Resolved bp use n :=
  match pick_best (source_cands bp use n) with
  | Some e => RBound (SourceObject (est_binder e))
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
  | RBound (SourceObject b) => exists e, In e (source_cands bp use n) /\ est_binder e = b
  | RBound (PredeclaredObject pn) =>
      source_cands bp use n = [] /\ Names.classify_predeclared (Names.ordinary_spelling n) = Some pn
  | RUnbound =>
      source_cands bp use n = [] /\ Names.classify_predeclared (Names.ordinary_spelling n) = None
  end.
Proof.
  unfold resolve. destruct (pick_best (source_cands bp use n)) as [e|] eqn:E.
  - exists e; split; [ apply pick_best_in; exact E | reflexivity ].
  - pose proof (pick_best_none _ E) as Hnil.
    destruct (Names.classify_predeclared (Names.ordinary_spelling n)) eqn:Ec; split; try exact Hnil; try reflexivity.
Qed.

Lemma typespec_visible_after_identifier {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx) :
  Index.node_role r = Index.RSpecName Index.TypeSpecF -> vis_start r = Index.nr_pos r.
Proof. intro H; unfold vis_start; rewrite H; reflexivity. Qed.

Lemma const_var_spec_end_visibility {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx) :
  (Index.node_role r = Index.RSpecName Index.ConstSpecF \/ Index.node_role r = Index.RSpecName Index.VarSpecF) ->
  vis_start r = nearest_kind_extent is_spec_kind (Index.file_nodes (Index.nr_file r)) r.
Proof. intros [H|H]; unfold vis_start; rewrite H; reflexivity. Qed.

Lemma short_decl_statement_end_visibility {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx) :
  Index.node_role r = Index.RShortLhs ->
  vis_start r = nearest_kind_extent is_stmt_kind (Index.file_nodes (Index.nr_file r)) r.
Proof. intro H; unfold vis_start; rewrite H; reflexivity. Qed.

(* a type name is visible inside its own scope after its identifier, so it shadows an outer name there *)
Lemma typespec_self_outer_shadow {p} {idx : Index.ProgramIndex p} (r u : Index.NodeRef idx) :
  Index.node_role r = Index.RSpecName Index.TypeSpecF -> Index.nr_pos r < Index.nr_pos u ->
  vis_start r < Index.nr_pos u.
Proof. intros Hr Hlt; rewrite (typespec_visible_after_identifier r Hr); exact Hlt. Qed.
