(* Bindings — binders, blocks, objects, scopes, ordinary-name resolution with visibility, and the
   package-indexed reference to the anonymous top-level main declaration. *)

From Stdlib Require Import List Bool Arith PeanoNat Lia Eqdep_dec.
From Fido Require Import Syntax Names Index Compilable.PackageIdentity.
Import ListNotations.

Module PI := Compilable.PackageIdentity.

(* ---- binder and block references (name-binding occurrences) ---- *)

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

Definition kind_eq_dec (a b : Index.Kind) : {a = b} + {a <> b}.
Proof. decide equality; decide equality. Defined.

Record BlockRef {p} (idx : Index.ProgramIndex p) : Type := block_ref {
  block_node : Index.NodeRef idx ;
  block_ok   : Index.node_kind block_node = Index.BlockKind
}.
Arguments block_ref {p idx} _ _.
Arguments block_node {p idx} _.
Arguments block_ok {p idx} _.

Lemma blockref_positional {p} {idx : Index.ProgramIndex p} (a b : BlockRef idx) :
  block_node a = block_node b -> a = b.
Proof. destruct a as [na Ha], b as [nb Hb]; cbn; intro E; subst nb; f_equal; apply (UIP_dec kind_eq_dec). Qed.

(* ---- the anonymous top-level main declaration, referenced per package ---- *)

Definition is_main_view (v : Index.NodeView) : bool :=
  match v with Index.VTop (Syntax.Main _) => true | _ => false end.
Definition is_main_node {p} {idx : Index.ProgramIndex p} (r : Index.NodeRef idx) : bool :=
  is_main_view (Index.node_view r).

Definition body_of_view (v : Index.NodeView) : is_main_view v = true -> Syntax.Block :=
  match v return is_main_view v = true -> Syntax.Block with
  | Index.VTop t =>
      match t return is_main_view (Index.VTop t) = true -> Syntax.Block with
      | Syntax.Main body        => fun _ => body
      | Syntax.TopDeclaration _ => fun H => False_rect _ (Bool.diff_false_true H)
      end
  | _ => fun H => False_rect _ (Bool.diff_false_true H)
  end.

Lemma body_of_view_spec : forall v H, v = Index.VTop (Syntax.Main (body_of_view v H)).
Proof.
  intro v; destruct v as [e|te|bn|cs|vs|ts|d|st|blk|t|f]; intro H; try discriminate H.
  destruct t as [d|body]; [ discriminate H | reflexivity ].
Qed.

Record MainDeclRef {p} {idx : Index.ProgramIndex p}
  (s : PI.PackageSurface idx) (pr : PI.PackageRef s) : Type := main_decl_ref {
  main_node : Index.NodeRef idx ;
  main_ok   : is_main_node main_node = true ;
  main_pkg  : PI.package_of_file s (Index.nr_file main_node) = pr
}.
Arguments main_decl_ref {p idx s pr} _ _ _.
Arguments main_node {p idx s pr} _.
Arguments main_ok {p idx s pr} _.
Arguments main_pkg {p idx s pr} _.

Definition main_body {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {pr : PI.PackageRef s}
  (m : MainDeclRef s pr) : Syntax.Block :=
  body_of_view (Index.node_view (main_node m)) (main_ok m).

Lemma main_body_exact {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {pr : PI.PackageRef s}
  (m : MainDeclRef s pr) : Index.node_view (main_node m) = Index.VTop (Syntax.Main (main_body m)).
Proof. exact (body_of_view_spec (Index.node_view (main_node m)) (main_ok m)). Qed.

Lemma main_declref_positional {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {pr : PI.PackageRef s}
  (a b : MainDeclRef s pr) : main_node a = main_node b -> a = b.
Proof.
  destruct a as [na Ha Pa], b as [nb Hb Pb]; cbn; intro E; subst nb.
  f_equal; [ apply (UIP_dec Bool.bool_dec) | apply (UIP_dec PI.packageref_eq_dec) ].
Qed.

Lemma main_declref_not_binder {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {pr : PI.PackageRef s}
  (m : MainDeclRef s pr) : is_binder_role (Index.node_role (main_node m)) = false.
Proof.
  rewrite (Index.main_role_plain (main_node m) (main_body m) (main_body_exact m)); reflexivity.
Qed.

Inductive MainStatus {p} {idx : Index.ProgramIndex p}
  (s : PI.PackageSurface idx) (pr : PI.PackageRef s) : Type :=
| MainMissing : MainStatus s pr
| MainUnique : MainDeclRef s pr -> MainStatus s pr
| MainRedeclared : MainDeclRef s pr -> MainDeclRef s pr -> list (MainDeclRef s pr) -> MainStatus s pr.
Arguments MainMissing {p idx s pr}.
Arguments MainUnique {p idx s pr} _.
Arguments MainRedeclared {p idx s pr} _ _ _.

Definition main_status_decls {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {pr : PI.PackageRef s}
  (st : MainStatus s pr) : list (MainDeclRef s pr) :=
  match st with
  | MainMissing => []
  | MainUnique m => [m]
  | MainRedeclared m1 m2 rest => m1 :: m2 :: rest
  end.

(* ---- objects and scopes ---- *)

Inductive ObjectRef {p} (idx : Index.ProgramIndex p) : Type :=
| PredeclaredObject : Names.PredeclaredName -> ObjectRef idx
| SourceObject      : BinderRef idx -> ObjectRef idx.
Arguments PredeclaredObject {p idx} _.
Arguments SourceObject {p idx} _.

Inductive ScopeId {p} {idx : Index.ProgramIndex p} (s : PI.PackageSurface idx) : Type :=
| PackageScope : PI.PackageRef s -> ScopeId s
| BlockScope   : BlockRef idx -> ScopeId s.
Arguments PackageScope {p idx s} _.
Arguments BlockScope {p idx s} _.

(* ---- scope discovery and declaration-kind visibility ---- *)

Definition is_spec_kind (k : Index.Kind) : bool := match k with Index.SpecKind _ => true | _ => false end.
Definition is_stmt_kind (k : Index.Kind) : bool := match k with Index.StmtKind => true | _ => false end.

(* the nearest block enclosing [b] (largest start position among containing blocks), carrying its reference *)
Definition nearest_block {p} {idx : Index.ProgramIndex p}
  (nodes : list (Index.NodeRef idx)) (b : Index.NodeRef idx) : option (BlockRef idx) :=
  fold_right (fun a acc =>
    (match Index.node_kind a as k return Index.node_kind a = k -> option (BlockRef idx) with
     | Index.BlockKind => fun H =>
         if andb (Nat.ltb (Index.nr_pos a) (Index.nr_pos b)) (Nat.leb (Index.nr_pos b) (Index.node_extent a))
         then match acc with
              | Some br => if Nat.ltb (Index.nr_pos (block_node br)) (Index.nr_pos a) then Some (block_ref a H) else acc
              | None => Some (block_ref a H)
              end
         else acc
     | _ => fun _ => acc
     end) eq_refl) None nodes.

(* the extent of the nearest ancestor of [b] whose kind passes [kb], or [b]'s own position if none *)
Definition nearest_kind_extent {p} {idx : Index.ProgramIndex p}
  (kb : Index.Kind -> bool) (nodes : list (Index.NodeRef idx)) (b : Index.NodeRef idx) : nat :=
  match fold_right (fun a acc =>
    if andb (kb (Index.node_kind a))
            (andb (Nat.ltb (Index.nr_pos a) (Index.nr_pos b)) (Nat.leb (Index.nr_pos b) (Index.node_extent a)))
    then match acc with Some a' => if Nat.ltb (Index.nr_pos a') (Index.nr_pos a) then Some a else acc | None => Some a end
    else acc) None nodes
  with Some a => Index.node_extent a | None => Index.nr_pos b end.

(* where a block-scoped binder becomes visible: a type name at its own identifier; a const/var name at the end
   of its spec; a short-declaration name at the end of its statement. *)
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

(* ---- per-package main status, computed once ---- *)

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
      main_decl_ref r (proj1 (H r (or_introl eq_refl))) (proj2 (H r (or_introl eq_refl)))
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
  | m :: nil => MainUnique m
  | m1 :: m2 :: rest => MainRedeclared m1 m2 rest
  end.

Lemma main_status_decls_from {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} {pr : PI.PackageRef s}
  (decls : list (MainDeclRef s pr)) : main_status_decls (main_status_from decls) = decls.
Proof. destruct decls as [|m1 [|m2 rest]]; reflexivity. Qed.

Definition main_status_of {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (pr : PI.PackageRef s) : MainStatus s pr := main_status_from (main_decls_of pr).

(* ---- the retained binding phase, sealed to its one builder ---- *)

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

(* ---- resolution ---- *)

Definition is_block_scoped {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx} (e : Est s) : bool :=
  match est_scope e with BlockScope _ => true | PackageScope _ => false end.

Definition contains_visible {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (e : Est s) (u : Index.NodeRef idx) : bool :=
  match est_scope e with
  | PackageScope pr => PI.packageref_eqb (PI.package_of_file s (Index.nr_file u)) pr
  | BlockScope br =>
      andb (Index.fileref_eqb (Index.nr_file (block_node br)) (Index.nr_file u))
      (andb (Nat.ltb (Index.nr_pos (block_node br)) (Index.nr_pos u))
      (andb (Nat.leb (Index.nr_pos u) (Index.node_extent (block_node br)))
            (Nat.ltb (est_vstart e) (Index.nr_pos u))))
  end.

Definition source_cands {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) : list (Est s) :=
  filter (fun e => andb (Names.ordinary_equalb (est_name e) n) (contains_visible e u)) (bp_ests bp).

(* prefer the innermost (block) candidate; else any candidate; else no source binding *)
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

Definition scope_of {p} {idx : Index.ProgramIndex p} {s : PI.PackageSurface idx}
  (bp : BindingPhase s) (r : Index.NodeRef idx) : ScopeId s :=
  match nearest_block (Index.file_nodes (Index.nr_file r)) r with
  | Some br => BlockScope br
  | None => PackageScope (PI.package_of_file s (Index.nr_file r))
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

(* ---- declaration-kind visibility laws ---- *)

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
