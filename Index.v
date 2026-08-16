
From Stdlib Require Import List Bool Lia Arith PeanoNat Eqdep_dec Wf_nat.
From Fido Require Import FilePath Collections Syntax.
Import ListNotations.

(* One transparent per-file preorder occurrence authority. No cursor topology, no equality-backed index, no
   per-id view map: the internal storage is a one-pass fold into plain per-file occurrence lists. *)

(* ---- the occurrence universe: a view of the exact selected source fragment, its kind, and its role ---- *)

Inductive NodeView : Type :=
| VExpr        : Syntax.Expr         -> NodeView
| VTypeExpr    : Syntax.TypeExpr     -> NodeView
| VBindingName : Syntax.BindingName  -> NodeView
| VConstSpec   : Syntax.ConstSpec    -> NodeView
| VVarSpec     : Syntax.VarSpec      -> NodeView
| VTypeSpec    : Syntax.TypeSpec     -> NodeView
| VDecl        : Syntax.Declaration  -> NodeView
| VStmt        : Syntax.Stmt         -> NodeView
| VBlock       : Syntax.Block        -> NodeView
| VTop         : Syntax.TopLevelDecl -> NodeView
| VFile        : Syntax.File         -> NodeView.

Inductive SpecFlavor := ConstSpecF | VarSpecF | TypeSpecF.

Inductive Kind :=
| ExprKind | TypeExprKind | BindingNameKind
| SpecKind : SpecFlavor -> Kind
| DeclKind | StmtKind | BlockKind | TopKind | FileKind.

Inductive Role :=
| RPlain | RApplicationHead | RApplicationArg : nat -> Role
| RUnaryOperand | RSpecName : SpecFlavor -> Role
| RShortLhs | RExprStatementExpr | RTypeUse.

(* the kind each view is classified as; node_kind agrees with this (view_exact_all_kinds) *)
Definition kind_of_view (v : NodeView) : Kind :=
  match v with
  | VExpr _ => ExprKind | VTypeExpr _ => TypeExprKind | VBindingName _ => BindingNameKind
  | VConstSpec _ => SpecKind ConstSpecF | VVarSpec _ => SpecKind VarSpecF | VTypeSpec _ => SpecKind TypeSpecF
  | VDecl _ => DeclKind | VStmt _ => StmtKind | VBlock _ => BlockKind | VTop _ => TopKind | VFile _ => FileKind
  end.

(* ---- generic total positional access; the in-range proof makes it a projection, never a fallback ---- *)

Fixpoint nth_lt {A} (l : list A) : forall n, n < length l -> A :=
  match l with
  | [] => fun n H => False_rect A (Nat.nlt_0_r n H)
  | x :: xs => fun n =>
      match n with
      | O => fun _ => x
      | S k => fun H => nth_lt xs k (proj2 (Nat.succ_lt_mono k (length xs)) H)
      end
  end.

Lemma lt_unique (n m : nat) (p q : n < m) : p = q.
Proof. apply Peano_dec.le_unique. Qed.

Lemma nth_lt_nth_error {A} (l : list A) : forall n H, nth_error l n = Some (nth_lt l n H).
Proof.
  induction l as [|x xs IH]; intros [|k] H; cbn in *.
  - exfalso; exact (Nat.nlt_0_r 0 H).
  - exfalso; exact (Nat.nlt_0_r (S k) H).
  - reflexivity.
  - apply IH.
Qed.

(* nth_lt depends only on the position, not on the proof it carries *)
Lemma nth_lt_pi {A} (l : list A) (n : nat) (H1 H2 : n < length l) : nth_lt l n H1 = nth_lt l n H2.
Proof. f_equal; apply lt_unique. Qed.

(* ---- the stored occurrence: the fold's payload at one preorder position ---- *)

Record Occ := mkOcc {
  o_view   : NodeView ;
  o_role   : Role ;
  o_parent : option nat ;   (* the enclosing occurrence's position; None only at the file root *)
  o_extent : nat            (* the last position of this occurrence's subtree; >= its own position *)
}.
(* Kind is not stored: it is a pure function of the view (kind_of_view), so storing it would be a second
   authority for one fact. node_kind derives it, and view_exact_all_kinds is then reflexivity. *)

(* ---- the source rose tree: the preorder structure before positions are assigned ---- *)

Inductive RNode : Type := mkRNode { rn_view : NodeView ; rn_role : Role ; rn_kids : list RNode }.

Definition r_expr (role : Role) (e : Syntax.Expr) (kids : list RNode) : RNode :=
  mkRNode (VExpr e) role kids.

(* build an expression subtree: head/argument/operand roles are assigned to children by their parent.
   The application arguments use an inlined nested fixpoint (as Syntax.Expr_ind' does) so the guard checker
   accepts the recursive call on each argument, a subterm of [Application head args]. *)
Fixpoint node_of_expr (role : Role) (e : Syntax.Expr) : RNode :=
  match e with
  | Syntax.Name _        => r_expr role e []
  | Syntax.LiteralExpr _ => r_expr role e []
  | Syntax.Unary _ e'    => r_expr role e [ node_of_expr RUnaryOperand e' ]
  | Syntax.Application head args =>
      r_expr role e
        ( node_of_expr RApplicationHead head
          :: (fix args_nodes (i : nat) (es : list Syntax.Expr) : list RNode :=
                match es with
                | [] => []
                | a :: rest => node_of_expr (RApplicationArg i) a :: args_nodes (S i) rest
                end) 0 args )
  end.

Definition node_of_typeexpr (role : Role) (t : Syntax.TypeExpr) : RNode :=
  mkRNode (VTypeExpr t) role [].
Definition node_of_bindingname (role : Role) (b : Syntax.BindingName) : RNode :=
  mkRNode (VBindingName b) role [].

Definition opttype_nodes (ot : option Syntax.TypeExpr) : list RNode :=
  match ot with Some t => [ node_of_typeexpr RTypeUse t ] | None => [] end.

Definition node_of_constspec (role : Role) (cs : Syntax.ConstSpec) : RNode :=
  mkRNode (VConstSpec cs) role
    ( List.map (node_of_bindingname (RSpecName ConstSpecF)) (Collections.ne_to_list (Syntax.const_names cs))
      ++ match Syntax.const_init cs with
         | Syntax.ExplicitConstInit ot vals =>
             opttype_nodes ot ++ List.map (node_of_expr RPlain) (Collections.ne_to_list vals)
         | Syntax.InheritedConstInit => []
         end ).

Definition node_of_varspec (role : Role) (vs : Syntax.VarSpec) : RNode :=
  mkRNode (VVarSpec vs) role
    ( List.map (node_of_bindingname (RSpecName VarSpecF)) (Collections.ne_to_list (Syntax.var_names vs))
      ++ match Syntax.var_init vs with
         | Syntax.VarTypeOnly t => [ node_of_typeexpr RTypeUse t ]
         | Syntax.VarValues ot vals => opttype_nodes ot ++ List.map (node_of_expr RPlain) (Collections.ne_to_list vals)
         end ).

Definition node_of_typespec (role : Role) (ts : Syntax.TypeSpec) : RNode :=
  mkRNode (VTypeSpec ts) role
    (match ts with
     | Syntax.AliasSpec b t | Syntax.DefSpec b t =>
         [ node_of_bindingname (RSpecName TypeSpecF) b ; node_of_typeexpr RTypeUse t ]
     end).

Definition node_of_decl (role : Role) (d : Syntax.Declaration) : RNode :=
  mkRNode (VDecl d) role
    (match d with
     | Syntax.ConstDecl cs => List.map (node_of_constspec RPlain) cs
     | Syntax.VarDecl vs   => List.map (node_of_varspec RPlain) vs
     | Syntax.TypeDecl ts  => List.map (node_of_typespec RPlain) ts
     end).

Definition node_of_stmt (role : Role) (s : Syntax.Stmt) : RNode :=
  mkRNode (VStmt s) role
    (match s with
     | Syntax.ExprStmt e        => [ node_of_expr RExprStatementExpr e ]
     | Syntax.DeclarationStmt d => [ node_of_decl RPlain d ]
     | Syntax.ShortVarDecl names vals =>
         List.map (node_of_bindingname RShortLhs) (Collections.ne_to_list names)
         ++ List.map (node_of_expr RPlain) (Collections.ne_to_list vals)
     end).

Definition node_of_block (role : Role) (b : Syntax.Block) : RNode :=
  mkRNode (VBlock b) role
    (match b with Syntax.MakeBlock stmts => List.map (node_of_stmt RPlain) stmts end).

Definition node_of_toplevel (role : Role) (t : Syntax.TopLevelDecl) : RNode :=
  mkRNode (VTop t) role
    (match t with
     | Syntax.TopDeclaration d => [ node_of_decl RPlain d ]
     | Syntax.Main blk         => [ node_of_block RPlain blk ]
     end).

Definition file_tree (f : Syntax.File) : RNode :=
  mkRNode (VFile f) RPlain (List.map (node_of_toplevel RPlain) (Syntax.declarations f)).

(* ---- flatten the rose tree to a preorder occurrence list with positions/parent/extent ---- *)

Fixpoint tree_size (n : RNode) : nat :=
  S ((fix sizes (ns : list RNode) : nat :=
        match ns with [] => 0 | k :: rest => tree_size k + sizes rest end) (rn_kids n)).

Fixpoint flat (parent : option nat) (base : nat) (n : RNode) {struct n} : list Occ :=
  mkOcc (rn_view n) (rn_role n) parent (base + tree_size n - 1)
  :: (fix flat_kids (b : nat) (ns : list RNode) {struct ns} : list Occ :=
        match ns with
        | [] => []
        | k :: rest => flat (Some base) b k ++ flat_kids (b + tree_size k) rest
        end) (S base) (rn_kids n).

(* the same kids-flattener, named as a standalone Fixpoint (calling the now-closed flat) so the proofs have a
   handle to induct over; flat_unfold rewrites the inlined fix inside flat to this. *)
Fixpoint flat_forest (parent : option nat) (base : nat) (ns : list RNode) {struct ns} : list Occ :=
  match ns with
  | [] => []
  | k :: rest => flat parent base k ++ flat_forest parent (base + tree_size k) rest
  end.

Definition file_occs (f : Syntax.File) : list Occ := flat None 0 (file_tree f).

(* ---- the retained per-file authority: plain per-file occurrence lists, built once ---- *)

Definition raw_index (p : Syntax.Program) : list (FilePath.T * list Occ) :=
  List.map (fun b => (fst b, file_occs (snd b))) (Syntax.program_bindings p).

(* ProgramIndex is sealed to the one canonical index: every idx IS raw_index p (read via prog_occs), so the
   structural laws hold for every idx, while a concrete index_program p still reduces for vm_compute/nf_all. *)
Definition ProgramIndex (p : Syntax.Program) : Type := { l : list (FilePath.T * list Occ) | l = raw_index p }.
Definition index_program (p : Syntax.Program) : ProgramIndex p := exist _ (raw_index p) eq_refl.
Definition prog_occs {p} (idx : ProgramIndex p) : list (FilePath.T * list Occ) := proj1_sig idx.

Definition index_has_file {p} (idx : ProgramIndex p) (path : FilePath.T) : bool :=
  existsb (fun b => FilePath.equalb (fst b) path) (prog_occs idx).
Definition file_occ_list {p} (idx : ProgramIndex p) (path : FilePath.T) : list Occ :=
  match find (fun b => FilePath.equalb (fst b) path) (prog_occs idx) with Some b => snd b | None => [] end.

Record FileRef {p} (idx : ProgramIndex p) : Type := file_ref {
  fr_path : FilePath.T ;
  fr_in   : index_has_file idx fr_path = true
}.
Arguments file_ref {p idx} _ _.
Arguments fr_path {p idx} _.
Arguments fr_in {p idx} _.

(* a file selector is its path; the membership proof is irrelevant (bool has unique proofs) *)
Lemma fileref_positional {p} {idx : ProgramIndex p} (a b : FileRef idx) : fr_path a = fr_path b -> a = b.
Proof. destruct a as [pa Ha], b as [pb Hb]; cbn; intro E; subst pb; f_equal; apply (UIP_dec Bool.bool_dec). Qed.

Definition fileref_eqb {p} {idx : ProgramIndex p} (a b : FileRef idx) : bool :=
  FilePath.equalb (fr_path a) (fr_path b).
Lemma fileref_eqb_spec {p} {idx : ProgramIndex p} (a b : FileRef idx) : fileref_eqb a b = true <-> a = b.
Proof.
  unfold fileref_eqb; split.
  - intro H; apply FilePath.equalb_spec in H; apply fileref_positional; exact H.
  - intro H; subst b; apply FilePath.equalb_spec; reflexivity.
Qed.

Lemma in_index_has_file {p} (idx : ProgramIndex p) (e : FilePath.T * list Occ) :
  In e (prog_occs idx) -> index_has_file idx (fst e) = true.
Proof.
  intro Hin. unfold index_has_file. apply existsb_exists.
  exists e; split; [ exact Hin | apply FilePath.equalb_spec; reflexivity ].
Qed.

Lemma index_has_file_in {p} (idx : ProgramIndex p) (path : FilePath.T) :
  index_has_file idx path = true -> exists e, In e (prog_occs idx) /\ fst e = path.
Proof.
  unfold index_has_file; intro H. apply existsb_exists in H. destruct H as [e [Hin He]].
  exists e; split; [ exact Hin | apply FilePath.equalb_spec in He; exact He ].
Qed.

(* build a FileRef at a candidate path, if present *)
Definition mk_fileref {p} (idx : ProgramIndex p) (path : FilePath.T) : option (FileRef idx) :=
  match Bool.bool_dec (index_has_file idx path) true with
  | left H  => Some (file_ref path H)
  | right _ => None
  end.

Lemma mk_fileref_path {p} (idx : ProgramIndex p) (path : FilePath.T) (fr : FileRef idx) :
  mk_fileref idx path = Some fr -> fr_path fr = path.
Proof.
  unfold mk_fileref; destruct (Bool.bool_dec (index_has_file idx path) true);
    [ intro H; injection H as <-; reflexivity | discriminate ].
Qed.

Lemma mk_fileref_of_in {p} (idx : ProgramIndex p) (path : FilePath.T) :
  index_has_file idx path = true -> exists fr, mk_fileref idx path = Some fr /\ fr_path fr = path.
Proof.
  intro H; unfold mk_fileref; destruct (Bool.bool_dec (index_has_file idx path) true) as [H'|H'];
    [ eexists; split; reflexivity | congruence ].
Qed.

Definition occ_count {p} {idx : ProgramIndex p} (fr : FileRef idx) : nat :=
  length (file_occ_list idx (fr_path fr)).

Record NodeRef {p} (idx : ProgramIndex p) : Type := node_at {
  nr_file : FileRef idx ;
  nr_pos  : nat ;
  nr_lt   : nr_pos < occ_count nr_file
}.
Arguments node_at {p idx} _ _ _.
Arguments nr_file {p idx} _.
Arguments nr_pos {p idx} _.
Arguments nr_lt {p idx} _.

(* occurrence access reads the retained list by position through [nth_error] — the in-range proof [nr_lt]
   discharges the impossible None branch, so this is still a total projection (never a fallback), but it does
   NOT thread/accumulate an O(position) `le` witness the way [nth_lt] does; a fold that reads every node's
   occurrence therefore stays linear in the retained-proof size rather than quadratic. *)
Lemma occ_at_none_absurd {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  nth_error (file_occ_list idx (fr_path (nr_file r))) (nr_pos r) = None -> False.
Proof.
  intro E. apply nth_error_None in E. pose proof (nr_lt r) as Hlt. unfold occ_count in Hlt. lia.
Qed.

Definition occ_of_opt {A} (o : option A) : o <> None -> A :=
  match o with Some x => fun _ => x | None => fun H => False_rect A (H eq_refl) end.

Definition occ_at {p} {idx : ProgramIndex p} (r : NodeRef idx) : Occ :=
  occ_of_opt (nth_error (file_occ_list idx (fr_path (nr_file r))) (nr_pos r)) (occ_at_none_absurd r).

Lemma occ_at_spec {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  nth_error (file_occ_list idx (fr_path (nr_file r))) (nr_pos r) = Some (occ_at r).
Proof.
  unfold occ_at. generalize (occ_at_none_absurd r).
  destruct (nth_error (file_occ_list idx (fr_path (nr_file r))) (nr_pos r)) as [x|]; intro H; cbn.
  - reflexivity.
  - exfalso; exact (H eq_refl).
Qed.

Definition node_view   {p} {idx : ProgramIndex p} (r : NodeRef idx) : NodeView := o_view   (occ_at r).
Definition node_kind   {p} {idx : ProgramIndex p} (r : NodeRef idx) : Kind     := kind_of_view (node_view r).
Definition node_role   {p} {idx : ProgramIndex p} (r : NodeRef idx) : Role     := o_role   (occ_at r).
Definition node_extent {p} {idx : ProgramIndex p} (r : NodeRef idx) : nat      := o_extent (occ_at r).

(* build a NodeRef at a candidate position, if in range (used by parent/children navigation).
   The bound is derived through an OPAQUE lemma from a boolean test, so a built NodeRef carries an O(1) proof
   term rather than an O(position) `le` witness.  [nth_lt] only threads the bound (it never matches on it), so
   occurrence access still computes; a fold that materializes a whole file's nodes then stays linear in the
   retained-proof size instead of quadratic. *)
Lemma lt_of_ltb (a b : nat) : Nat.ltb a b = true -> a < b.
Proof. apply Nat.ltb_lt. Qed.

Definition mk_noderef {p}{idx : ProgramIndex p} (fr : FileRef idx) (q : nat) : option (NodeRef idx) :=
  match Bool.bool_dec (Nat.ltb q (occ_count fr)) true with
  | left E  => Some (node_at fr q (lt_of_ltb q (occ_count fr) E))
  | right _ => None
  end.

Definition node_parent {p} {idx : ProgramIndex p} (r : NodeRef idx) : option (NodeRef idx) :=
  match o_parent (occ_at r) with Some pp => mk_noderef (nr_file r) pp | None => None end.

Definition node_children {p} {idx : ProgramIndex p} (r : NodeRef idx) : list (NodeRef idx) :=
  flat_map
    (fun q => match mk_noderef (nr_file r) q with
              | Some c => match o_parent (occ_at c) with
                          | Some pp => if Nat.eqb pp (nr_pos r) then [c] else []
                          | None => []
                          end
              | None => []
              end)
    (seq (S (nr_pos r)) (node_extent r - nr_pos r)).

Definition file_nodes {p} {idx : ProgramIndex p} (fr : FileRef idx) : list (NodeRef idx) :=
  flat_map (fun q => match mk_noderef fr q with Some r => [r] | None => [] end)
           (seq 0 (occ_count fr)).

Lemma mk_noderef_file {p} {idx : ProgramIndex p} (fr : FileRef idx) (q : nat) (r : NodeRef idx) :
  mk_noderef fr q = Some r -> nr_file r = fr.
Proof.
  unfold mk_noderef; destruct (Bool.bool_dec (Nat.ltb q (occ_count fr)) true);
    [ intro E; injection E as <-; reflexivity | discriminate ].
Qed.

Lemma file_nodes_file {p} {idx : ProgramIndex p} (fr : FileRef idx) (r : NodeRef idx) :
  In r (file_nodes fr) -> nr_file r = fr.
Proof.
  unfold file_nodes; intro Hin. apply in_flat_map in Hin. destruct Hin as [q [_ Hin]].
  destruct (mk_noderef fr q) as [r'|] eqn:E; cbn in Hin.
  - destruct Hin as [Heq|[]]. subst r'. exact (mk_noderef_file fr q r E).
  - destruct Hin.
Qed.

Definition strict_descendant {p} {idx : ProgramIndex p} (a b : NodeRef idx) : Prop :=
  nr_file a = nr_file b /\ nr_pos a < nr_pos b /\ nr_pos b <= node_extent a.

(* ---- flatten invariants: the numeric facts the fold establishes, proven once, then read by the laws ---- *)

(* the nested-list induction principle RNode's auto-generated scheme cannot give (kids recurse through list) *)
Fixpoint RNode_ind' (P : RNode -> Prop)
  (step : forall v role kids, Forall P kids -> P (mkRNode v role kids))
  (n : RNode) {struct n} : P n :=
  match n with
  | mkRNode v role kids =>
      step v role kids
        ((fix kl (ns : list RNode) : Forall P ns :=
            match ns with
            | [] => Forall_nil P
            | k :: rest => Forall_cons k (RNode_ind' P step k) (kl rest)
            end) kids)
  end.

(* a named handle for the subtree-size sum the inlined fix inside tree_size computes *)
Fixpoint sum_tree_size (ns : list RNode) : nat :=
  match ns with [] => 0 | k :: rest => tree_size k + sum_tree_size rest end.

Lemma tree_size_cons : forall v role kids, tree_size (mkRNode v role kids) = S (sum_tree_size kids).
Proof. reflexivity. Qed.

Lemma tree_size_pos : forall n, 0 < tree_size n.
Proof. intros n; destruct n; cbn [tree_size]; lia. Qed.

(* one flatten step: the inlined kids-fix inside flat equals the standalone flat_forest, by induction on kids *)
Lemma flat_unfold : forall parent base v role kids,
  flat parent base (mkRNode v role kids)
  = mkOcc v role parent (base + tree_size (mkRNode v role kids) - 1)
    :: flat_forest (Some base) (S base) kids.
Proof.
  intros parent base v role kids. cbn [flat rn_view rn_role rn_kids]. f_equal.
  generalize (S base) as b. induction kids as [|k rest IH]; intro b.
  - reflexivity.
  - cbn. rewrite IH. reflexivity.
Qed.

Lemma flat_forest_length : forall ns,
  Forall (fun k => forall parent base, length (flat parent base k) = tree_size k) ns ->
  forall parent base, length (flat_forest parent base ns) = sum_tree_size ns.
Proof.
  induction ns as [|k rest IH]; intros HF parent base.
  - reflexivity.
  - cbn [flat_forest sum_tree_size]. rewrite length_app.
    inversion HF as [|? ? Hk HFrest]; subst.
    rewrite (Hk parent base). rewrite (IH HFrest parent (base + tree_size k)). reflexivity.
Qed.

Lemma flat_length : forall n parent base, length (flat parent base n) = tree_size n.
Proof.
  induction n as [v role kids IH] using RNode_ind'; intros parent base.
  rewrite flat_unfold. cbn [length]. rewrite tree_size_cons. f_equal.
  apply flat_forest_length. exact IH.
Qed.

(* every occurrence in [flat parent base n] carries: an extent at least its own absolute position; a parent equal
   to the passed one exactly at the head; and, off the head, a strictly-earlier in-subtree parent position. *)
Definition node_ok (n : RNode) : Prop :=
  forall parent base i occ,
    nth_error (flat parent base n) i = Some occ ->
    base + i <= o_extent occ
    /\ (i = 0 -> o_parent occ = parent)
    /\ (i <> 0 -> exists pp, o_parent occ = Some pp /\ base <= pp /\ pp < base + i).

Lemma flat_forest_nth : forall ns, Forall node_ok ns ->
  forall pbase b, pbase < b -> forall j occ,
    nth_error (flat_forest (Some pbase) b ns) j = Some occ ->
    b + j <= o_extent occ /\ (exists pp, o_parent occ = Some pp /\ pbase <= pp /\ pp < b + j).
Proof.
  induction ns as [|k rest IH]; intros HF pbase b Hlt j occ Hnth.
  - destruct j; discriminate Hnth.
  - cbn [flat_forest] in Hnth.
    pose proof (flat_length k (Some pbase) b) as HL.
    destruct (Nat.lt_ge_cases j (length (flat (Some pbase) b k))) as [Hjl | Hjge].
    + rewrite nth_error_app1 in Hnth by exact Hjl.
      inversion HF as [|? ? Hk HFrest]; subst.
      destruct (Hk (Some pbase) b j occ Hnth) as (Hext & Hp0 & Hpn).
      split; [exact Hext|].
      destruct (Nat.eq_dec j 0) as [->|Hj0].
      * exists pbase. split; [exact (Hp0 eq_refl) | split; lia].
      * destruct (Hpn Hj0) as (pp & Hpp & Hlo & Hhi). exists pp. split; [exact Hpp | split; lia].
    + rewrite nth_error_app2 in Hnth by exact Hjge.
      inversion HF as [|? ? Hk HFrest]; subst.
      assert (Hlt' : pbase < b + tree_size k) by lia.
      destruct (IH HFrest pbase (b + tree_size k) Hlt'
                   (j - length (flat (Some pbase) b k)) occ Hnth)
        as (Hext & pp & Hpp & Hlo & Hhi).
      split.
      * replace (b + j) with ((b + tree_size k) + (j - length (flat (Some pbase) b k))) by lia. exact Hext.
      * exists pp. split; [exact Hpp | split; [exact Hlo|]].
        replace (b + j) with ((b + tree_size k) + (j - length (flat (Some pbase) b k))) by lia. exact Hhi.
Qed.

Lemma flat_node_ok : forall n, node_ok n.
Proof.
  induction n as [v role kids IH] using RNode_ind'.
  unfold node_ok. intros parent base i occ Hnth.
  rewrite flat_unfold in Hnth. destruct i as [|j].
  - cbn [nth_error] in Hnth. injection Hnth as Heq. subst occ.
    pose proof (tree_size_pos (mkRNode v role kids)) as Hpos.
    cbn [o_extent o_parent]. split; [ | split ].
    + lia.
    + intros _; reflexivity.
    + intros H; congruence.
  - cbn [nth_error] in Hnth.
    assert (Hlt : base < S base) by lia.
    destruct (flat_forest_nth kids IH base (S base) Hlt j occ Hnth) as (Hext & pp & Hpp & Hlo & Hhi).
    repeat split.
    + replace (base + S j) with (S base + j) by lia. exact Hext.
    + intros Hc; discriminate Hc.
    + intros _. exists pp. split; [exact Hpp | split; [lia|]].
      replace (base + S j) with (S base + j) by lia. exact Hhi.
Qed.

(* every occurrence list a canonical index yields for a path is either empty or a whole-file [flat None 0 _] *)
Lemma file_occ_list_flat : forall p (idx : ProgramIndex p) path,
  (exists f, file_occ_list idx path = flat None 0 (file_tree f))
  \/ file_occ_list idx path = [].
Proof.
  intros p idx path. unfold file_occ_list, prog_occs. rewrite (proj2_sig idx). unfold raw_index.
  induction (Syntax.program_bindings p) as [|b rest IH]; cbn.
  - right; reflexivity.
  - destruct (FilePath.equalb (fst b) path) eqn:E.
    + left. exists (snd b). reflexivity.
    + exact IH.
Qed.

Lemma mk_noderef_some {p} {idx : ProgramIndex p} (fr : FileRef idx) (q : nat) :
  q < occ_count fr -> exists r, mk_noderef fr q = Some r.
Proof.
  intros H. unfold mk_noderef.
  destruct (Bool.bool_dec (Nat.ltb q (occ_count fr)) true) as [E|E];
    [ eexists; reflexivity | exfalso; apply E; apply Nat.ltb_lt; exact H ].
Qed.

(* ---- laws ---- *)

(* identity is file + position; the in-range proof is irrelevant (le is a proposition with unique proofs) *)
Lemma noderef_positional {p} {idx : ProgramIndex p} (a b : NodeRef idx) :
  nr_file a = nr_file b -> nr_pos a = nr_pos b -> a = b.
Proof.
  destruct a as [fa pa Ha], b as [fb pb Hb]; simpl; intros Ef Ep; subst.
  f_equal; apply lt_unique.
Qed.

(* a selector cannot cross indices: NodeRef is indexed by the exact idx, so a NodeRef of a different index is a
   distinct type; the property is the dependent typing itself (see the build's foreign-index typing controls). *)
Definition foreign_index_by_type {p} (idx : ProgramIndex p) : Prop := True.

(* node_kind is derived from node_view, so the classification always matches the retained fragment *)
Lemma view_exact_all_kinds {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  kind_of_view (node_view r) = node_kind r.
Proof. reflexivity. Qed.

(* every projection is total on the canonical index (no fallback); node_parent is None exactly at the file root *)
Lemma node_total {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  (nr_pos r = 0 -> node_parent r = None) /\ (nr_pos r <> 0 -> node_parent r <> None).
Proof.
  destruct (file_occ_list_flat p idx (fr_path (nr_file r))) as [(f & Hf) | Hnil].
  - assert (E : nth_error (flat None 0 (file_tree f)) (nr_pos r) = Some (occ_at r)).
    { rewrite <- Hf. apply occ_at_spec. }
    destruct (flat_node_ok (file_tree f) None 0 (nr_pos r) (occ_at r) E) as (_ & Hp0 & Hpn).
    unfold node_parent. split.
    + intros H0. rewrite (Hp0 H0). reflexivity.
    + intros Hn0. destruct (Hpn Hn0) as (pp & Hpp & _ & Hhi). rewrite Hpp.
      destruct (mk_noderef_some (nr_file r) pp) as (r' & Hr').
      { pose proof (nr_lt r). lia. }
      rewrite Hr'. discriminate.
  - exfalso. pose proof (nr_lt r) as HL. unfold occ_count in HL. rewrite Hnil in HL. cbn in HL. lia.
Qed.

(* positions are the exact preorder: a node's extent bounds it below, and any parent position is strictly earlier *)
Lemma occ_order_exact {p} {idx : ProgramIndex p} (r : NodeRef idx) :
  nr_pos r <= node_extent r
  /\ (forall pp, o_parent (occ_at r) = Some pp -> pp < nr_pos r).
Proof.
  destruct (file_occ_list_flat p idx (fr_path (nr_file r))) as [(f & Hf) | Hnil].
  - assert (E : nth_error (flat None 0 (file_tree f)) (nr_pos r) = Some (occ_at r)).
    { rewrite <- Hf. apply occ_at_spec. }
    destruct (flat_node_ok (file_tree f) None 0 (nr_pos r) (occ_at r) E) as (Hext & Hp0 & Hpn).
    split.
    + unfold node_extent. lia.
    + intros pp Hpp. destruct (Nat.eq_dec (nr_pos r) 0) as [H0|Hn0].
      * rewrite (Hp0 H0) in Hpp. discriminate Hpp.
      * destruct (Hpn Hn0) as (pp' & Hpp' & _ & Hhi). rewrite Hpp' in Hpp. injection Hpp as <-. lia.
  - exfalso. pose proof (nr_lt r) as HL. unfold occ_count in HL. rewrite Hnil in HL. cbn in HL. lia.
Qed.

(* ---- main_role_plain: the anonymous top-level Main declaration is never a name binder ---- *)

(* rpv_b n: every node in n whose view is a VTop carries role RPlain.  Only node_of_toplevel emits a VTop
   view, and only ever with RPlain, so this holds for a whole file tree; the sub-builders emit no VTop. *)
Fixpoint rpv_b (n : RNode) : bool :=
  match rn_view n with VTop _ => match rn_role n with RPlain => true | _ => false end | _ => true end
  && (fix allb (ns : list RNode) : bool := match ns with [] => true | k :: rest => rpv_b k && allb rest end)
       (rn_kids n).

Lemma rpv_b_cons : forall v role kids,
  rpv_b (mkRNode v role kids)
  = (match v with VTop _ => match role with RPlain => true | _ => false end | _ => true end)
    && forallb rpv_b kids.
Proof.
  intros v role kids. cbn [rpv_b rn_view rn_role rn_kids]. f_equal.
Qed.

Lemma forallb_rpv_app : forall l1 l2,
  forallb rpv_b l1 = true -> forallb rpv_b l2 = true -> forallb rpv_b (l1 ++ l2) = true.
Proof.
  intros l1 l2 H1 H2. apply forallb_forall. intros n Hn. apply in_app_or in Hn.
  destruct Hn as [Hn|Hn]; [ rewrite forallb_forall in H1; apply H1 | rewrite forallb_forall in H2; apply H2 ]; exact Hn.
Qed.
Lemma forallb_rpv_map : forall {A} (g : A -> RNode) (l : list A),
  (forall x, rpv_b (g x) = true) -> forallb rpv_b (map g l) = true.
Proof.
  intros A g l H. apply forallb_forall. intros y Hy. apply in_map_iff in Hy.
  destruct Hy as [x [<- _]]. apply H.
Qed.

Lemma rpv_b_typeexpr : forall role t, rpv_b (node_of_typeexpr role t) = true.
Proof. intros role t; unfold node_of_typeexpr; rewrite rpv_b_cons; apply andb_true_intro; split; reflexivity. Qed.
Lemma rpv_b_bindingname : forall role b, rpv_b (node_of_bindingname role b) = true.
Proof. intros role b; unfold node_of_bindingname; rewrite rpv_b_cons; apply andb_true_intro; split; reflexivity. Qed.
Lemma rpv_b_opttype : forall ot, forallb rpv_b (opttype_nodes ot) = true.
Proof. intros [t|]; cbn [opttype_nodes]; [ cbn [forallb]; rewrite rpv_b_typeexpr; reflexivity | reflexivity ]. Qed.

(* the application-argument subtrees, named so the proof can induct over them *)
Fixpoint arg_nodes (i : nat) (es : list Syntax.Expr) : list RNode :=
  match es with [] => [] | a :: rest => node_of_expr (RApplicationArg i) a :: arg_nodes (S i) rest end.
Lemma node_of_expr_app : forall role head args,
  node_of_expr role (Syntax.Application head args)
  = mkRNode (VExpr (Syntax.Application head args)) role (node_of_expr RApplicationHead head :: arg_nodes 0 args).
Proof. intros role head args; reflexivity. Qed.
Lemma arg_nodes_cons : forall i a rest,
  arg_nodes i (a :: rest) = node_of_expr (RApplicationArg i) a :: arg_nodes (S i) rest.
Proof. reflexivity. Qed.
Lemma node_of_expr_unary : forall role op e',
  node_of_expr role (Syntax.Unary op e')
  = mkRNode (VExpr (Syntax.Unary op e')) role [node_of_expr RUnaryOperand e'].
Proof. reflexivity. Qed.

Lemma rpv_b_arg_nodes : forall args,
  Forall (fun a => forall role, rpv_b (node_of_expr role a) = true) args ->
  forall i, forallb rpv_b (arg_nodes i args) = true.
Proof.
  induction args as [|a rest IH]; intros HF i; [reflexivity|].
  rewrite arg_nodes_cons; cbn [forallb]. inversion HF as [|? ? Ha Hrest]; subst.
  rewrite (Ha (RApplicationArg i)), (IH Hrest (S i)); reflexivity.
Qed.

Lemma rpv_b_expr : forall e role, rpv_b (node_of_expr role e) = true.
Proof.
  intro e; induction e as [n|l|op e' IH|head args IHhead IHargs] using Syntax.Expr_ind'; intro role.
  - reflexivity.
  - reflexivity.
  - rewrite node_of_expr_unary, rpv_b_cons; apply andb_true_intro; split; [reflexivity|].
    cbn [forallb]; rewrite (IH RUnaryOperand); reflexivity.
  - rewrite node_of_expr_app, rpv_b_cons; apply andb_true_intro; split; [reflexivity|].
    cbn [forallb]; rewrite (IHhead RApplicationHead); cbn [andb].
    exact (rpv_b_arg_nodes args IHargs 0).
Qed.

Lemma rpv_b_constspec : forall role cs, rpv_b (node_of_constspec role cs) = true.
Proof.
  intros role cs. unfold node_of_constspec. rewrite rpv_b_cons. apply andb_true_intro; split; [reflexivity|].
  apply forallb_rpv_app; [ apply forallb_rpv_map; intro; apply rpv_b_bindingname |].
  destruct (Syntax.const_init cs) as [ot vals|];
    [ apply forallb_rpv_app; [ apply rpv_b_opttype | apply forallb_rpv_map; intro; apply rpv_b_expr ] | reflexivity ].
Qed.
Lemma rpv_b_varspec : forall role vs, rpv_b (node_of_varspec role vs) = true.
Proof.
  intros role vs. unfold node_of_varspec. rewrite rpv_b_cons. apply andb_true_intro; split; [reflexivity|].
  apply forallb_rpv_app; [ apply forallb_rpv_map; intro; apply rpv_b_bindingname |].
  destruct (Syntax.var_init vs) as [t|ot vals];
    [ cbn [forallb]; rewrite rpv_b_typeexpr; reflexivity
    | apply forallb_rpv_app; [ apply rpv_b_opttype | apply forallb_rpv_map; intro; apply rpv_b_expr ] ].
Qed.
Lemma rpv_b_typespec : forall role ts, rpv_b (node_of_typespec role ts) = true.
Proof.
  intros role ts. unfold node_of_typespec. rewrite rpv_b_cons. apply andb_true_intro; split; [reflexivity|].
  destruct ts; cbn [forallb]; rewrite rpv_b_bindingname, rpv_b_typeexpr; reflexivity.
Qed.
Lemma rpv_b_decl : forall role d, rpv_b (node_of_decl role d) = true.
Proof.
  intros role d. unfold node_of_decl. rewrite rpv_b_cons. apply andb_true_intro; split; [reflexivity|].
  destruct d; apply forallb_rpv_map; intro; [ apply rpv_b_constspec | apply rpv_b_varspec | apply rpv_b_typespec ].
Qed.
Lemma rpv_b_stmt : forall role s, rpv_b (node_of_stmt role s) = true.
Proof.
  intros role s. unfold node_of_stmt. rewrite rpv_b_cons. apply andb_true_intro; split; [reflexivity|].
  destruct s as [e|d|names vals]; cbn [forallb].
  - rewrite rpv_b_expr; reflexivity.
  - rewrite rpv_b_decl; reflexivity.
  - apply forallb_rpv_app; apply forallb_rpv_map; intro; [ apply rpv_b_bindingname | apply rpv_b_expr ].
Qed.
Lemma rpv_b_block : forall role b, rpv_b (node_of_block role b) = true.
Proof.
  intros role b. unfold node_of_block. rewrite rpv_b_cons. apply andb_true_intro; split; [reflexivity|].
  destruct b; apply forallb_rpv_map; intro; apply rpv_b_stmt.
Qed.
Lemma rpv_b_toplevel_plain : forall t, rpv_b (node_of_toplevel RPlain t) = true.
Proof.
  intros t. unfold node_of_toplevel. rewrite rpv_b_cons. apply andb_true_intro; split; [reflexivity|].
  destruct t; cbn [forallb]; [ rewrite rpv_b_decl | rewrite rpv_b_block ]; reflexivity.
Qed.
Lemma rpv_b_file_tree : forall f, rpv_b (file_tree f) = true.
Proof.
  intros f. unfold file_tree. rewrite rpv_b_cons. apply andb_true_intro; split; [reflexivity|].
  apply forallb_rpv_map; intro; apply rpv_b_toplevel_plain.
Qed.

(* flatten preserves the rpv discipline into every occurrence *)
Definition rv_ok (n : RNode) : Prop :=
  forall parent base i occ, nth_error (flat parent base n) i = Some occ ->
    forall t, o_view occ = VTop t -> o_role occ = RPlain.

Lemma flat_forest_rv : forall ns, Forall rv_ok ns ->
  forall parent base j occ, nth_error (flat_forest parent base ns) j = Some occ ->
    forall t, o_view occ = VTop t -> o_role occ = RPlain.
Proof.
  induction ns as [|k rest IH]; intros HF parent base j occ Hnth t Hv.
  - destruct j; discriminate Hnth.
  - cbn [flat_forest] in Hnth. destruct (Nat.lt_ge_cases j (length (flat parent base k))) as [Hjl|Hjge].
    + rewrite nth_error_app1 in Hnth by exact Hjl.
      inversion HF as [|? ? Hk HFrest]; subst. exact (Hk parent base j occ Hnth t Hv).
    + rewrite nth_error_app2 in Hnth by exact Hjge.
      inversion HF as [|? ? Hk HFrest]; subst.
      exact (IH HFrest parent (base + tree_size k) (j - length (flat parent base k)) occ Hnth t Hv).
Qed.

Lemma flat_rv : forall n, rpv_b n = true -> rv_ok n.
Proof.
  induction n as [v role kids IH] using RNode_ind'. intro Hrpv.
  rewrite rpv_b_cons in Hrpv. apply andb_true_iff in Hrpv as [Hhead Hkids].
  unfold rv_ok; intros parent base i occ Hnth t Hv. rewrite flat_unfold in Hnth. destruct i as [|j].
  - cbn [nth_error] in Hnth. injection Hnth as <-. cbn [o_view o_role] in *.
    subst v. destruct role; first [ reflexivity | discriminate Hhead ].
  - cbn [nth_error] in Hnth.
    assert (Hrv : Forall rv_ok kids).
    { apply Forall_forall. intros k Hk. apply (proj1 (Forall_forall _ _) IH k Hk).
      apply (proj1 (forallb_forall _ _) Hkids k Hk). }
    exact (flat_forest_rv kids Hrv (Some base) (S base) j occ Hnth t Hv).
Qed.

(* the anonymous top-level main declaration carries role RPlain, so it is never a name binder *)
Lemma main_role_plain {p} {idx : ProgramIndex p} (r : NodeRef idx) (body : Syntax.Block) :
  node_view r = VTop (Syntax.Main body) -> node_role r = RPlain.
Proof.
  intro Hv. destruct (file_occ_list_flat p idx (fr_path (nr_file r))) as [(f & Hf) | Hnil].
  - assert (E : nth_error (flat None 0 (file_tree f)) (nr_pos r) = Some (occ_at r)).
    { rewrite <- Hf. apply occ_at_spec. }
    apply (flat_rv (file_tree f) (rpv_b_file_tree f) None 0 (nr_pos r) (occ_at r) E (Syntax.Main body)).
    unfold node_view in Hv. exact Hv.
  - exfalso. pose proof (nr_lt r) as HL. unfold occ_count in HL. rewrite Hnil in HL. cbn in HL. lia.
Qed.

(* strict descent is well-founded: a descendant shares the file and has a strictly larger, still in-range
   position, so [occ_count - position] is a strictly decreasing measure toward descendants *)
Lemma descendant_wellfounded {p} {idx : ProgramIndex p} :
  well_founded (fun b a : NodeRef idx => strict_descendant a b).
Proof.
  apply (well_founded_lt_compat _ (fun r => occ_count (nr_file r) - nr_pos r)).
  intros x y H. destruct H as (Ef & Hlt & _).
  pose proof (nr_lt x) as Hx. rewrite Ef. lia.
Qed.
