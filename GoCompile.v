(** ============================================================================
    GoCompile — static/compiler admissibility as EVIDENCE over the ONE [GoAST], never a
    second syntax tree.  Because package/function/println/bool are structural (GoAST), the
    ONLY thing the Go compiler could still reject in a representable program is an integer
    literal that does not fit the target [int].  So:

      GoCompile f  ==  every integer literal in f is representable for the pinned target.

    This is EXACT for the representable domain: every representable program the pinned Go
    compiler accepts is accepted here (all bool/in-range-int programs), and every program
    rejected here (an out-of-range magnitude) is a genuine Go constant-overflow error — not a
    supported-but-refused program.  [-(2^63)] is admitted (via [ENeg]); a bare [2^63] is not.

    A declarative judgment ([GoCompile]) plus an executable decision ([go_compile]) proved
    SOUND and COMPLETE against it — never a bare boolean, never completeness against a
    mirror-relation instead of the compiler.  [CompiledProgram] is a proof-bearing wrapper
    over the SAME [GoFile] (no copy, no erasure).
    ============================================================================ *)
From Stdlib Require Import NArith ZArith List Bool.
From Fido Require Import TargetConfig GoAST.
Import ListNotations.
Open Scope Z_scope.

(** ---- declarative admissibility (integer representability) ---- *)

Inductive ExprOk : GoExpr -> Prop :=
| OkBool : forall b, ExprOk (EBool b)
| OkInt  : forall n, Z.of_N n <= int_max     -> ExprOk (EInt n)
| OkNeg  : forall n, Z.of_N n <= - int_min   -> ExprOk (ENeg n).

Inductive StmtOk : GoStmt -> Prop :=
| OkPrintln : forall args, Forall ExprOk args -> StmtOk (SPrintln args).

Definition GoCompile (f : GoFile) : Prop :=
  match f with MainFile body => Forall StmtOk body end.

(** ---- executable decision ---- *)

Definition expr_ok (e : GoExpr) : bool :=
  match e with
  | EBool _ => true
  | EInt n  => Z.of_N n <=? int_max
  | ENeg n  => Z.of_N n <=? - int_min
  end.

Definition stmt_ok (s : GoStmt) : bool :=
  match s with SPrintln args => forallb expr_ok args end.

Definition go_compile (f : GoFile) : bool :=
  match f with MainFile body => forallb stmt_ok body end.

(** ---- soundness + completeness (checker ⇔ judgment) ---- *)

Lemma expr_ok_iff : forall e, expr_ok e = true <-> ExprOk e.
Proof.
  intro e; destruct e as [ b | n | n ]; simpl; split.
  - intros _; constructor.
  - reflexivity.
  - intro H; apply Z.leb_le in H; constructor; exact H.
  - intro H; inversion H; subst; apply Z.leb_le; assumption.
  - intro H; apply Z.leb_le in H; constructor; exact H.
  - intro H; inversion H; subst; apply Z.leb_le; assumption.
Qed.

Lemma forallb_expr_ok_iff : forall args, forallb expr_ok args = true <-> Forall ExprOk args.
Proof.
  induction args as [ | a args' IH ]; simpl.
  - split; [ constructor | reflexivity ].
  - rewrite andb_true_iff, expr_ok_iff, IH.
    split; [ intros [Ha Hr]; constructor; assumption
           | intro H; inversion H; subst; split; assumption ].
Qed.

Lemma stmt_ok_iff : forall s, stmt_ok s = true <-> StmtOk s.
Proof.
  intros [args]; simpl. rewrite forallb_expr_ok_iff.
  split; [ intro H; constructor; exact H | intro H; inversion H; subst; assumption ].
Qed.

Lemma forallb_stmt_ok_iff : forall body, forallb stmt_ok body = true <-> Forall StmtOk body.
Proof.
  induction body as [ | s body' IH ]; simpl.
  - split; [ constructor | reflexivity ].
  - rewrite andb_true_iff, stmt_ok_iff, IH.
    split; [ intros [Hs Hr]; constructor; assumption
           | intro H; inversion H; subst; split; assumption ].
Qed.

Theorem go_compile_sound : forall f, go_compile f = true -> GoCompile f.
Proof. intros [body] H; simpl in *. apply forallb_stmt_ok_iff; exact H. Qed.

Theorem go_compile_complete : forall f, GoCompile f -> go_compile f = true.
Proof. intros [body] H; simpl in *. apply forallb_stmt_ok_iff; exact H. Qed.

Corollary go_compile_iff : forall f, go_compile f = true <-> GoCompile f.
Proof. intro f; split; [ apply go_compile_sound | apply go_compile_complete ]. Qed.

Corollary GoCompile_dec : forall f, {GoCompile f} + {~ GoCompile f}.
Proof.
  intro f; destruct (go_compile f) eqn:E.
  - left; apply go_compile_sound; exact E.
  - right; intro H; apply go_compile_complete in H; rewrite H in E; discriminate.
Qed.

(** ---- the certificate: a proof-bearing wrapper over the SAME AST ---- *)

Record CompiledProgram : Type := mkCompiled {
  cp_ast : GoFile;
  cp_ok  : GoCompile cp_ast
}.
