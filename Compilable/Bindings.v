(* Bindings — object identity, lexical scopes, establisher sites, and ordinary-name resolution with shadowing. *)

From Stdlib Require Import PArith NArith List Bool Lia String.
From Fido Require Import Collections FilePath Names Syntax Index.
Import ListNotations.
Local Open Scope positive_scope.

(* a binder reference: a node reference whose projected role is a binder — SpecName or ShortLhs, by proof *)
Definition is_binder_role (rl : Index.Role) : bool :=
  match rl with Index.SpecName _ => true | Index.ShortLhs _ => true | _ => false end.
Record BinderRef {p : Syntax.Program} (idx : Index.ProgramIndex p) : Type := MkBinderRef {
  binder_node : Index.Snapshot.NodeRef idx;
  binder_is   : is_binder_role (Index.Snapshot.node_ref_role binder_node) = true
}.
Arguments MkBinderRef {p idx}. Arguments binder_node {p idx}. Arguments binder_is {p idx}.
Definition binder_key {p} {idx : Index.ProgramIndex p} (b : BinderRef idx) : Index.Key :=
  Index.Snapshot.node_ref_key (binder_node b).
(* the role proof is a mere proposition, so a binder reference is exactly its node — the proof never splits it *)
Lemma binder_ext {p} {idx : Index.ProgramIndex p} (a b : BinderRef idx) : binder_node a = binder_node b -> a = b.
Proof. destruct a as [na ha], b as [nb hb]; cbn; intros ->; f_equal; apply Eqdep_dec.UIP_dec, Bool.bool_dec. Qed.

(* a block reference: a node reference whose projected kind is a block, by proof — no any-node block scope *)
Definition is_block_kind (k : Index.Kind) : bool := match k with Index.BlockKind => true | _ => false end.
Record BlockRef {p : Syntax.Program} (idx : Index.ProgramIndex p) : Type := MkBlockRef {
  block_node : Index.Snapshot.NodeRef idx;
  block_is   : is_block_kind (Index.Snapshot.node_ref_kind block_node) = true
}.
Arguments MkBlockRef {p idx}. Arguments block_node {p idx}. Arguments block_is {p idx}.
Definition block_key {p} {idx : Index.ProgramIndex p} (b : BlockRef idx) : Index.Key :=
  Index.Snapshot.node_ref_key (block_node b).
Lemma block_ext {p} {idx : Index.ProgramIndex p} (a b : BlockRef idx) : block_node a = block_node b -> a = b.
Proof. destruct a as [na ha], b as [nb hb]; cbn; intros ->; f_equal; apply Eqdep_dec.UIP_dec, Bool.bool_dec. Qed.

(* an object is a predeclared entity or a source object named by its establisher's exact binder occurrence *)
Inductive ObjectRef {p : Syntax.Program} (idx : Index.ProgramIndex p) : Type :=
| PredeclaredObject : Names.PredeclaredName -> ObjectRef idx
| SourceObject      : BinderRef idx -> ObjectRef idx.
Arguments PredeclaredObject {p idx}. Arguments SourceObject {p idx}.

Definition object_key {p} {idx : Index.ProgramIndex p} (o : ObjectRef idx) : option Index.Key :=
  match o with PredeclaredObject _ => None | SourceObject r => Some (binder_key r) end.

Definition object_eqb {p} {idx : Index.ProgramIndex p} (a b : ObjectRef idx) : bool :=
  match a, b with
  | PredeclaredObject na, PredeclaredObject nb => Names.predeclared_eqb na nb
  | SourceObject ra, SourceObject rb           => Index.key_equalb (binder_key ra) (binder_key rb)
  | _, _ => false
  end.

Lemma object_eqb_spec : forall p (idx : Index.ProgramIndex p) (a b : ObjectRef idx), object_eqb a b = true <-> a = b.
Proof.
  intros p idx [na|ra] [nb|rb]; cbn; split; try discriminate.
  - intros H. apply Names.predeclared_eqb_spec in H. subst. reflexivity.
  - intros H. injection H as <-. apply Names.predeclared_eqb_spec. reflexivity.
  - intros H. apply Index.key_equalb_spec in H. apply Index.Snapshot.node_ref_key_inj in H.
    apply binder_ext in H. subst. reflexivity.
  - intros H. injection H as <-. apply Index.key_equalb_spec. reflexivity.
Qed.

(* lexical scopes: the predeclared universe, a package directory, and a func body's retained block occurrence *)
Inductive ScopeId {p : Syntax.Program} (idx : Index.ProgramIndex p) : Type :=
| PredeclaredScope
| PackageScope : Index.Snapshot.FileRef p -> ScopeId idx
| BlockScope   : BlockRef idx -> ScopeId idx.
Arguments PredeclaredScope {p idx}. Arguments PackageScope {p idx}. Arguments BlockScope {p idx}.

(* a package is named by a canonical member file; its identity is that file's directory, no free string *)
Definition pkg_dir {p} (fr : Index.Snapshot.FileRef p) : string :=
  FilePath.parent (Index.Snapshot.file_ref_path fr).

Definition scope_eqb {p} {idx : Index.ProgramIndex p} (a b : ScopeId idx) : bool :=
  match a, b with
  | PredeclaredScope, PredeclaredScope => true
  | PackageScope fa, PackageScope fb   => String.eqb (pkg_dir fa) (pkg_dir fb)
  | BlockScope ra, BlockScope rb       => Index.key_equalb (block_key ra) (block_key rb)
  | _, _ => false
  end.

(* two scopes are one scope when they name the same package directory / block node / both predeclared *)
Definition same_scope {p} {idx : Index.ProgramIndex p} (a b : ScopeId idx) : Prop :=
  match a, b with
  | PredeclaredScope, PredeclaredScope => True
  | PackageScope fa, PackageScope fb   => pkg_dir fa = pkg_dir fb
  | BlockScope ra, BlockScope rb       => block_node ra = block_node rb
  | _, _ => False
  end.

Lemma scope_eqb_spec : forall p (idx : Index.ProgramIndex p) (a b : ScopeId idx), scope_eqb a b = true <-> same_scope a b.
Proof.
  intros p idx [|fa|ra] [|fb|rb]; cbn; split; intro H;
    try exact I; try discriminate H; try contradiction H; try reflexivity.
  - apply String.eqb_eq in H; exact H.
  - apply String.eqb_eq; exact H.
  - apply Index.key_equalb_spec in H; apply Index.Snapshot.node_ref_key_inj in H; exact H.
  - apply Index.key_equalb_spec; unfold block_key; rewrite H; reflexivity.
Qed.

Definition scope_parent {p} {idx : Index.ProgramIndex p} (s : ScopeId idx) : option (ScopeId idx) :=
  match s with
  | PredeclaredScope => None
  | PackageScope _   => Some PredeclaredScope
  | BlockScope r     => Some (PackageScope (Index.Snapshot.node_ref_file (block_node r)))
  end.

(* the enclosing scopes of a scope, innermost first — the exact, finite chain *)
Definition scope_chain {p} {idx : Index.ProgramIndex p} (s : ScopeId idx) : list (ScopeId idx) :=
  match s with
  | PredeclaredScope => [PredeclaredScope]
  | PackageScope d   => [PackageScope d; PredeclaredScope]
  | BlockScope r     => [BlockScope r; PackageScope (Index.Snapshot.node_ref_file (block_node r)); PredeclaredScope]
  end.

Definition Encloses {p} {idx : Index.ProgramIndex p} (outer inner : ScopeId idx) : Prop :=
  In outer (scope_chain inner).

Lemma encloses_self : forall p (idx : Index.ProgramIndex p) (s : ScopeId idx), Encloses s s.
Proof. intros p idx s; unfold Encloses; destruct s; simpl; left; reflexivity. Qed.

Lemma encloses_parent : forall p (idx : Index.ProgramIndex p) (outer inner par : ScopeId idx),
  scope_parent inner = Some par -> Encloses outer par -> Encloses outer inner.
Proof.
  intros p idx outer inner par Hp Hen. unfold Encloses in *.
  destruct inner as [|d|r]; cbn [scope_parent] in Hp; try discriminate;
    injection Hp as <-; cbn [scope_chain] in *; right; exact Hen.
Qed.

Section WithProgram.
Variable p : Syntax.Program.
Variable idx : Index.ProgramIndex p.

(* whenever a cursor is a block, its projected kind really is a block — the proof a BlockRef needs *)
Lemma block_kind_proof {f} (c : Index.CFile f) :
  Index.cfile_kind c = Index.BlockKind -> is_block_kind (Index.cfile_kind c) = true.
Proof. intros H. rewrite H. reflexivity. Qed.

(* the func-body block windows [id, subtree_end], each carrying the block-scope reference it names; built totally *)
Definition block_windows (fr : Index.Snapshot.FileRef p) : list (positive * positive * BlockRef idx) :=
  let occs := Index.Snapshot.local_index idx fr in
  fold_right (fun s acc =>
     let t := Index.nth_lt occs (proj1_sig s) (proj2_sig s) in
     match Index.cfile_kind (snd t) as k return Index.cfile_kind (snd t) = k -> list (positive * positive * BlockRef idx) with
     | Index.BlockKind => fun Heq =>
         (fst (fst t), snd (fst t),
          MkBlockRef (Index.Snapshot.MakeNodeRef fr (proj1_sig s) (proj2_sig s)) (block_kind_proof (snd t) Heq)) :: acc
     | _ => fun _ => acc
     end eq_refl)
   [] (Index.indexed_lt occs).

Definition stmt_windows {f} (occs : list (positive * positive * Index.CFile f)) : list (positive * positive) :=
  fold_right (fun t acc =>
     match Index.cfile_role (snd t) with
     | Index.BlockStatement _ => (fst (fst t), snd (fst t)) :: acc
     | _ => acc end) [] occs.

(* the const/var/type spec windows [id, subtree_end] — a spec-name's Go scope starts at the end of its own spec *)
Definition spec_windows {f} (occs : list (positive * positive * Index.CFile f)) : list (positive * positive) :=
  fold_right (fun t acc =>
     match Index.cfile_kind (snd t) with
     | Index.SpecKind => (fst (fst t), snd (fst t)) :: acc
     | _ => acc end) [] occs.

(* the innermost block window strictly containing [id], with its reference; ties to the latest-starting block *)
Definition nearest_block (bw : list (positive * positive * BlockRef idx)) (id : positive)
  : option (positive * positive * BlockRef idx) :=
  fold_right (fun w acc =>
     let '(bid, bend, _) := w in
     if andb (Pos.ltb bid id) (Pos.leb id bend)
     then match acc with Some (a, _, _) => if Pos.ltb a bid then Some w else acc | None => Some w end
     else acc)
   None bw.

Definition scope_of_id (bw : list (positive * positive * BlockRef idx)) (fr : Index.Snapshot.FileRef p) (id : positive) : ScopeId idx :=
  match nearest_block bw id with
  | Some (_, _, br) => BlockScope br
  | None => PackageScope fr
  end.

(* the end of the block statement enclosing [id]; [id] itself when [id] is not inside a block statement *)
Definition stmt_end_of (sw : list (positive * positive)) (id : positive) : positive :=
  fold_right (fun w acc =>
     let '(sid, send) := w in if andb (Pos.leb sid id) (Pos.leb id send) then send else acc)
   id sw.

(* an object-establisher: a BNamed binder in a spec-name or short-lhs position; a blank establishes nothing *)
Definition binder_spelling {f} (c : Index.CFile f) : option (string * bool) :=
  match Index.cfile_view_binding_name c with
  | Some (Syntax.BNamed n) =>
      match Index.cfile_role c with
      | Index.SpecName _ => Some (Names.ordinary_spelling n, false)
      | Index.ShortLhs _ => Some (Names.ordinary_spelling n, true)
      | _ => None
      end
  | _ => None
  end.

(* whenever a cursor spells a binder, its role really is a binder role — the proof a BinderRef needs *)
Lemma binder_spelling_role {f} (c : Index.CFile f) x :
  binder_spelling c = Some x -> is_binder_role (Index.cfile_role c) = true.
Proof.
  intros H. unfold is_binder_role. unfold binder_spelling in H.
  destruct (Index.cfile_view_binding_name c) as [[n|]|]; try discriminate H;
    destruct (Index.cfile_role c); try discriminate H; reflexivity.
Qed.

Record Establisher := MkEst {
  est_ref      : BinderRef idx;
  est_spelling : string;
  est_scope    : ScopeId idx;
  est_short    : bool;
  est_vis_start : positive;   (* decl-kind-specific: a block-scoped binder is visible only after this position *)
  est_block    : option (positive * positive)   (* the containing block window, for O(1) use-containment *)
}.

Definition est_key (e : Establisher) : Index.Key := binder_key (est_ref e).

Definition file_establishers (fr : Index.Snapshot.FileRef p) : list Establisher :=
  let occs := Index.Snapshot.local_index idx fr in
  let bw   := block_windows fr in
  let sw   := stmt_windows occs in
  let spw  := spec_windows occs in
  fold_right (fun s acc =>
     let t := Index.nth_lt occs (proj1_sig s) (proj2_sig s) in
     match binder_spelling (snd t) as bo return binder_spelling (snd t) = bo -> list Establisher with
     | Some x => fun Heq =>
         MkEst (MkBinderRef (Index.Snapshot.MakeNodeRef fr (proj1_sig s) (proj2_sig s))
                            (binder_spelling_role (snd t) x Heq))
               (fst x) (scope_of_id bw fr (fst (fst t))) (snd x)
               (if snd x then stmt_end_of sw (fst (fst t)) else stmt_end_of spw (fst (fst t)))
               (option_map (fun w => (fst (fst w), snd (fst w))) (nearest_block bw (fst (fst t)))) :: acc
     | None => fun _ => acc
     end eq_refl)
   [] (Index.indexed_lt occs).

Definition establishers : list Establisher :=
  flat_map file_establishers (Index.Snapshot.file_refs p).

(* a block-scoped establisher is visible only after its decl-kind visibility start (spec-end vs statement-end) *)
Definition visible_to (e : Establisher) (use_id : positive) : bool :=
  match est_block e with Some _ => Pos.ltb (est_vis_start e) use_id | None => true end.

(* does [e]'s scope contain a use? block = same file within the block window; package = same directory *)
Definition scope_contains (e : Establisher) (use_path : FilePath.T) (use_id : positive) : bool :=
  match est_block e with
  | Some (lo, hi) =>
      andb (FilePath.equalb (Index.key_path (est_key e)) use_path) (andb (Pos.leb lo use_id) (Pos.leb use_id hi))
  | None => String.eqb (FilePath.parent (Index.key_path (est_key e))) (FilePath.parent use_path)
  end.

Definition block_scoped (e : Establisher) : bool := match est_block e with Some _ => true | None => false end.

(* the establishers of a spelling whose scope contains and is visible to a use *)
Definition visible_here (es : list Establisher) (n : string) (use_path : FilePath.T) (use_id : positive)
  : list Establisher :=
  filter (fun e => andb (andb (String.eqb (est_spelling e) n) (scope_contains e use_path use_id)) (visible_to e use_id)) es.

(* the earliest establisher by local id — the definite binder when a scope holds exactly one of a spelling *)
Definition earliest (es : list Establisher) : option Establisher :=
  fold_right (fun e acc =>
     match acc with
     | None => Some e
     | Some a => if Pos.ltb (Index.key_local (est_key e)) (Index.key_local (est_key a)) then Some e else acc
     end) None es.

(* a use resolves to the nearest visible enclosing source object of its spelling, else the predeclared one *)
Definition resolve (es : list Establisher) (use_path : FilePath.T) (use_id : positive) (n : string)
  : option (ObjectRef idx) :=
  let cands := visible_here es n use_path use_id in
  match earliest (filter block_scoped cands) with
  | Some e => Some (SourceObject (est_ref e))
  | None =>
      match earliest (filter (fun e => negb (block_scoped e)) cands) with
      | Some e => Some (SourceObject (est_ref e))
      | None =>
          match Names.classify_predeclared n with
          | Some pn => Some (PredeclaredObject pn)
          | None    => None
          end
      end
  end.

(* the short-declaration disposition of a left occurrence: a blank, a new object, or a reuse of an earlier one *)
Inductive ShortDisposition : Type :=
| ShortBlank
| ShortNew
| ShortReuse : BinderRef idx -> ShortDisposition.

(* the establishers of a spelling in one scope, other than [self], declared strictly before [self] *)
Definition prior_establishers (es : list Establisher) (sc : ScopeId idx) (n : string) (self : Establisher)
  : list Establisher :=
  filter (fun e => andb (andb (String.eqb (est_spelling e) n) (scope_eqb (est_scope e) sc))
                        (Pos.ltb (Index.key_local (est_key e)) (Index.key_local (est_key self)))) es.

(* is [e] a short-lhs establisher that reuses an earlier binder of its spelling in the same scope? *)
Definition short_disposition (es : list Establisher) (e : Establisher) : ShortDisposition :=
  if est_short e then
     match earliest (prior_establishers es (est_scope e) (est_spelling e) e) with
     | Some prior => ShortReuse (est_ref prior)
     | None       => ShortNew
     end
  else ShortNew.

(* a full (non-short) establisher redeclared where an earlier binder of its spelling already stands *)
Definition redeclares (es : list Establisher) (e : Establisher) : bool :=
  andb (negb (est_short e))
       (negb (match prior_establishers es (est_scope e) (est_spelling e) e with [] => true | _ => false end)).

End WithProgram.

Arguments MkEst {p idx}. Arguments est_ref {p idx}. Arguments est_spelling {p idx}. Arguments est_scope {p idx}.
Arguments est_short {p idx}. Arguments est_vis_start {p idx}. Arguments est_key {p idx}.
Arguments ShortBlank {p idx}. Arguments ShortNew {p idx}. Arguments ShortReuse {p idx}.
Arguments Establisher {p} idx.
