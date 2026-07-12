(** ============================================================================
    GoCompile — the EXACT static/compiler-admissibility authority for [GoAST].

    [GoCompile p] means precisely: this [GoFile], canonically rendered for the pinned
    TargetConfig, is accepted by the pinned Go compiler.  Nothing more (not safe, not
    panic-free, not terminating — those are GoSafe) and nothing less.  It is DECLARATIVE
    (a relation), with an executable checker [go_compile] proved SOUND and COMPLETE against
    it — never a bare [check = true].  Within the domain [GoAST] can represent it is EXACT
    (no conservative under-approximation): every rule the compiler would enforce for the
    admitted fragment is formalized here (package/func identity, builtin resolution of the
    callee, admissible primitive argument forms, target-int representability of constants).
    The pinned compiler stays a last-mile integration check, never a proof premise.

    Since the AST *is* the IR, GoCompile decorates nothing — a "compiled program" is a
    [GoFile] together with a [GoCompile] proof (GoSafe.[SafeProgram]).
    ============================================================================ *)
From Stdlib Require Import String NArith ZArith List Bool.
From Fido Require Import TargetConfig Literals GoIdent GoAST.
Import ListNotations.
Open Scope Z_scope.

(** ---- The declarative judgment ---- *)

Inductive ExprOk : GoExpr -> Prop :=
| OkTrue  : forall i, ident_str i = "true"%string  -> ExprOk (EIdent i)   (* predeclared bool *)
| OkFalse : forall i, ident_str i = "false"%string -> ExprOk (EIdent i)
| OkInt   : forall n, Z.of_N n <= int_max          -> ExprOk (EInt n)     (* fits the pinned int *)
| OkNeg   : forall n, Z.of_N n <= - int_min        -> ExprOk (ENeg n)
| OkStr   : forall s H, ExprOk (EStr s H).

Inductive StmtOk : GoStmt -> Prop :=
| OkCall : forall callee args,
    ident_str callee = "println"%string ->                                (* the resolved builtin *)
    Forall ExprOk args ->
    StmtOk (SCall callee args).

Definition GoCompile (p : GoFile) : Prop :=
  ident_str (file_pkg p) = "main"%string
  /\ ident_str (fn_name (file_func p)) = "main"%string
  /\ Forall StmtOk (fn_body (file_func p)).

(** ---- The executable checker ---- *)

Definition expr_ok (e : GoExpr) : bool :=
  match e with
  | EIdent i => String.eqb (ident_str i) "true" || String.eqb (ident_str i) "false"
  | EInt n   => Z.of_N n <=? int_max
  | ENeg n   => Z.of_N n <=? - int_min
  | EStr _ _ => true
  end.

Definition stmt_ok (s : GoStmt) : bool :=
  match s with
  | SCall callee args => String.eqb (ident_str callee) "println" && forallb expr_ok args
  end.

Definition go_compile (p : GoFile) : bool :=
  String.eqb (ident_str (file_pkg p)) "main"
  && String.eqb (ident_str (fn_name (file_func p))) "main"
  && forallb stmt_ok (fn_body (file_func p)).

(** ---- Soundness + completeness: checker and judgment coincide EXACTLY ---- *)

Lemma expr_ok_iff : forall e, expr_ok e = true <-> ExprOk e.
Proof.
  intro e. split.
  - intro H. destruct e as [ i | n | n | s Hs ]; simpl in H.
    + apply orb_true_iff in H as [H|H]; apply String.eqb_eq in H;
        [ apply OkTrue | apply OkFalse ]; exact H.
    + apply Z.leb_le in H. apply OkInt; exact H.
    + apply Z.leb_le in H. apply OkNeg; exact H.
    + apply OkStr.
  - intro H. destruct H as [ i He | i He | n Hn | n Hn | s Hs ]; simpl.
    + rewrite He. reflexivity.
    + rewrite He. rewrite orb_true_r. reflexivity.
    + apply Z.leb_le; exact Hn.
    + apply Z.leb_le; exact Hn.
    + reflexivity.
Qed.

Lemma forallb_expr_ok_iff : forall args, forallb expr_ok args = true <-> Forall ExprOk args.
Proof.
  induction args as [ | a args' IH ]; simpl.
  - split; [ intros _; constructor | reflexivity ].
  - rewrite andb_true_iff, expr_ok_iff, IH. split.
    + intros [Ha Hr]; constructor; assumption.
    + intro H; inversion H; subst; split; assumption.
Qed.

Lemma stmt_ok_iff : forall s, stmt_ok s = true <-> StmtOk s.
Proof.
  intros [callee args]. simpl. rewrite andb_true_iff, String.eqb_eq, forallb_expr_ok_iff.
  split.
  - intros [Hc Ha]. apply OkCall; assumption.
  - intro H; inversion H; subst; split; assumption.
Qed.

Lemma forallb_stmt_ok_iff : forall body, forallb stmt_ok body = true <-> Forall StmtOk body.
Proof.
  induction body as [ | s body' IH ]; simpl.
  - split; [ intros _; constructor | reflexivity ].
  - rewrite andb_true_iff, stmt_ok_iff, IH. split.
    + intros [Hs Hr]; constructor; assumption.
    + intro H; inversion H; subst; split; assumption.
Qed.

Theorem go_compile_sound : forall p, go_compile p = true -> GoCompile p.
Proof.
  intros p H. unfold go_compile in H. unfold GoCompile.
  apply andb_true_iff in H as [H1 H3].
  apply andb_true_iff in H1 as [Hp Hf].
  apply String.eqb_eq in Hp. apply String.eqb_eq in Hf.
  apply forallb_stmt_ok_iff in H3.
  repeat split; assumption.
Qed.

Theorem go_compile_complete : forall p, GoCompile p -> go_compile p = true.
Proof.
  intros p [Hp [Hf Hb]]. unfold go_compile.
  apply andb_true_iff. split; [ apply andb_true_iff; split | ].
  - apply String.eqb_eq; exact Hp.
  - apply String.eqb_eq; exact Hf.
  - apply forallb_stmt_ok_iff; exact Hb.
Qed.

Corollary go_compile_iff : forall p, go_compile p = true <-> GoCompile p.
Proof. intro p. split; [ apply go_compile_sound | apply go_compile_complete ]. Qed.

(** GoCompile is decidable (the checker decides it). *)
Corollary GoCompile_dec : forall p, {GoCompile p} + {~ GoCompile p}.
Proof.
  intro p. destruct (go_compile p) eqn:E.
  - left. apply go_compile_sound; exact E.
  - right. intro H. apply go_compile_complete in H. rewrite H in E. discriminate.
Qed.
