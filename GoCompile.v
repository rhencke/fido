(** ============================================================================
    GoCompile — whole-PROGRAM static/compiler admissibility as EVIDENCE over the ONE raw AST (the
    finite-map [GoProgram]), never a second syntax tree.

    Responsibilities: accept/reject exactly as the Go compiler would for every program the current
    subset can represent, and (as the AST grows) derive the static meaning the compiler resolves —
    package grouping, imports, symbols, types, calls, entry point — as facts over the same program.
    Today the fragment is one file (structurally package main + func main) of admissible println
    statements, so [CompilationFacts] is empty (no symbol/type/package/entry table is needed yet) and
    the only obligation is integer representability for the 64-bit target.

    HONESTY — two distinct claims:
    A. KERNEL-internal exactness (PROVED): the executable checker succeeds exactly for the formal
       [GoCompile] judgment ([prog_ok_iff]; [go_compile] returns a [CompilableProgram] iff it holds).
    B. EXTERNAL Go-compiler adequacy (the GOAL, NOT a kernel theorem): every successful
       [CompilableProgram], rendered, is accepted by the real Go compiler (and eventually the converse).
       Exercised by the pinned e2e toolchain, not a proof about cmd/compile.  Do not overclaim
       "equivalent to go build".

    [CompilableProgram] wraps the SAME [GoProgram] + its facts + the compile proof — no copy.
    ============================================================================ *)
From Stdlib Require Import NArith ZArith List Bool String.
From Fido Require Import Ints FMap GoAST.
Import ListNotations.
Open Scope Z_scope.

(** ---- declarative admissibility (integer representability) ---- *)

Inductive ExprOk : GoExpr -> Prop :=
| OkBool : forall b, ExprOk (EBool b)
| OkInt  : forall n, Z.of_N n <= int_max     -> ExprOk (EInt n)
| OkNeg  : forall n, Z.of_N n <= - int_min   -> ExprOk (ENeg n).

Inductive StmtOk : GoStmt -> Prop :=
| OkPrintln : forall args, Forall ExprOk args -> StmtOk (SPrintln args).

(** ---- executable checker ---- *)

Definition expr_ok (e : GoExpr) : bool :=
  match e with
  | EBool _ => true
  | EInt n  => Z.of_N n <=? int_max
  | ENeg n  => Z.of_N n <=? - int_min
  end.

Definition stmt_ok (s : GoStmt) : bool :=
  match s with SPrintln args => forallb expr_ok args end.

Definition file_ok (f : GoFileAST) : bool :=
  match f with MainFile body => forallb stmt_ok body end.

(** The MVP closed-world checker: exactly one file, and it is admissible. *)
Definition prog_ok (p : GoProgram) : bool :=
  match fm_list p with [ (_, f) ] => file_ok f | _ => false end.

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

(** ---- the certificate: facts + proof over the SAME program ---- *)

(** The static facts GoCompile derives about a program.  EMPTY today — the one-file println fragment
    needs no symbol/type/package/entry table.  The permanent home for those facts when the AST grows;
    they will decorate this same [GoProgram], never a copied tree. *)
Inductive CompilationFacts (p : GoProgram) : Type := mkFacts.
Arguments mkFacts {p}.

(** MVP: exactly one file, at some path, a main file whose statements are all admissible. *)
Definition GoCompile (p : GoProgram) (_ : CompilationFacts p) : Prop :=
  exists path body,
    fm_keys p = [path]
    /\ fm_find path p = Some (MainFile body)
    /\ Forall StmtOk body.

Record CompilableProgram : Type := mkCompilable {
  cp_program : GoProgram;
  cp_facts   : CompilationFacts cp_program;
  cp_ok      : GoCompile cp_program cp_facts
}.

(** ---- (A) internal checker exactness ---- *)

Lemma prog_ok_iff : forall p, prog_ok p = true <-> GoCompile p mkFacts.
Proof.
  intro p. unfold prog_ok, GoCompile, fm_keys, fm_find.
  destruct (fm_list p) as [ | [k f] [ | e l ] ] eqn:E; simpl.
  - split; [ discriminate | intros [path [body [Hk _]]]; discriminate Hk ].
  - destruct f as [ body ]. split.
    + intro Hf. exists k, body. split; [ reflexivity | split ].
      * simpl. rewrite String.eqb_refl. reflexivity.
      * apply forallb_stmt_ok_iff; exact Hf.
    + intros [path [body' [Hk [Hfind Hbody]]]].
      injection Hk as Hkp; subst path.
      simpl in Hfind. rewrite String.eqb_refl in Hfind. injection Hfind as Hf; subst body'.
      apply forallb_stmt_ok_iff; exact Hbody.
  - split; [ discriminate | intros [path [body [Hk _]]]; discriminate Hk ].
Qed.

(** A boolean, reflected as a decision that remembers the witnessing equation. *)
Definition bool_sumbool (b : bool) : {b = true} + {b = false} :=
  match b with true => left eq_refl | false => right eq_refl end.

(** The executable compiler is proof-producing: it returns a CompilableProgram exactly when the
    program is admissible. *)
Definition go_compile (p : GoProgram) : option CompilableProgram :=
  match bool_sumbool (prog_ok p) with
  | left H  => Some (mkCompilable p mkFacts (proj1 (prog_ok_iff p) H))
  | right _ => None
  end.

Theorem go_compile_sound : forall p cp, go_compile p = Some cp -> cp_program cp = p.
Proof.
  intros p cp. unfold go_compile.
  destruct (bool_sumbool (prog_ok p)) as [ H | H ]; intro Heq;
    [ injection Heq as <-; reflexivity | discriminate ].
Qed.

Theorem go_compile_complete : forall p, GoCompile p mkFacts -> exists cp, go_compile p = Some cp.
Proof.
  intros p H. apply prog_ok_iff in H. unfold go_compile.
  destruct (bool_sumbool (prog_ok p)) as [ H' | H' ];
    [ eexists; reflexivity | rewrite H in H'; discriminate ].
Qed.

(** A rejected program yields no CompilableProgram (and hence no SafeProgram). *)
Lemma reject_no_compile : forall p, prog_ok p = false -> ~ GoCompile p mkFacts.
Proof. intros p E H; apply prog_ok_iff in H; rewrite H in E; discriminate. Qed.

(** ---- kernel-checked boundary + rejection facts ---- *)

Example accept_max_int :
  prog_ok (fm_singleton "main.go" (MainFile [SPrintln [EInt (Z.to_N int_max)]])) = true.
Proof. reflexivity. Qed.

Example accept_min_int :
  prog_ok (fm_singleton "main.go" (MainFile [SPrintln [ENeg (Z.to_N (- int_min))]])) = true.
Proof. reflexivity. Qed.

Example reject_pos_overflow :
  prog_ok (fm_singleton "main.go" (MainFile [SPrintln [EInt (Z.to_N (int_max + 1))]])) = false.
Proof. reflexivity. Qed.

Example reject_neg_overflow :
  prog_ok (fm_singleton "main.go" (MainFile [SPrintln [ENeg (Z.to_N (- int_min + 1))]])) = false.
Proof. reflexivity. Qed.

(** Duplicate relative paths are unrepresentable: lookup is a function, so a path never maps to two
    files ([FMap.fm_MapsTo_fun]); the finite map carries a NoDup-keys proof by construction. *)
Definition path_unique : forall (p : GoProgram) k f1 f2,
  fm_MapsTo k f1 p -> fm_MapsTo k f2 p -> f1 = f2 :=
  fun p k f1 f2 => fm_MapsTo_fun k f1 f2 p.
