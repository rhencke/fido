(** ============================================================================
    GoCompile — whole-PROGRAM static/compiler admissibility as EVIDENCE over the ONE raw AST (the
    finite-map [GoProgram]), never a second syntax tree.

    Responsibilities: accept/reject exactly as the Go compiler would for every program the current
    subset can represent, and (as the AST grows) derive the static meaning the compiler resolves —
    package grouping, imports, symbols, types, calls, entry point — as facts over the same program.
    Today the fragment is one file (structurally package main + func main) of admissible println
    statements at the canonical build path [main.go], so the obligations are exactly: the single key is
    [main.go] (a build-participating source path) and every integer is representable on the 64-bit
    target.  No static facts are derived yet, so there is no facts record — an empty one would be
    scaffolding; when real facts appear they decorate this same program.

    HONESTY — two distinct claims:
    A. KERNEL-internal exactness (PROVED): the executable checker succeeds exactly for the formal
       [GoCompile] judgment ([prog_ok_iff]; [go_compile] returns a [CompilableProgram] iff it holds).
    B. EXTERNAL Go-compiler adequacy (the GOAL, NOT a kernel theorem): every successful
       [CompilableProgram], rendered, is accepted by the real Go compiler (and eventually the converse).
       Exercised by the pinned e2e toolchain, not a proof about cmd/compile.  Do not overclaim
       "equivalent to go build".

    [CompilableProgram] wraps the SAME [GoProgram] + the compile proof — no copy, no second tree.
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

(** The canonical source path of the one-file fragment. *)
Definition main_path : string := "main.go".

(** The MVP closed-world checker: exactly one file, at the canonical build-participating path
    [main.go], and it is admissible.  The KEY is pinned, not ignored — the admitted fragment emits
    exactly one file that `go build` compiles, so any other key is not compile-admissible: a non-[.go]
    name the Go build ignores, a nested/absolute/traversing path, or a sink control name.  These are
    rejected IN Rocq (below), never left for the writer to catch.  A general certified [GoSourcePath]
    model (with the full Go source-selection rules) arrives with multi-file support; today the exact
    one-file obligation is "the single key is [main.go]". *)
Definition prog_ok (p : GoProgram) : bool :=
  match fm_list p with [ (k, f) ] => String.eqb k main_path && file_ok f | _ => false end.

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

(** ---- the certificate: a proof over the SAME program ---- *)

(** MVP: exactly one file, at the canonical [main.go] path, a main file whose statements are all
    admissible.  There is no facts record: the current fragment derives no symbol/type/package table,
    and an empty placeholder would be future scaffolding.  When compilation DOES derive static facts
    they will decorate this same [GoProgram] (never a copied tree), added then, carrying real data. *)
Definition GoCompile (p : GoProgram) : Prop :=
  exists body,
    fm_keys p = [main_path]
    /\ fm_find main_path p = Some (MainFile body)
    /\ Forall StmtOk body.

Record CompilableProgram : Type := mkCompilable {
  cp_program : GoProgram;
  cp_ok      : GoCompile cp_program
}.

(** ---- (A) internal checker exactness ---- *)

Lemma prog_ok_iff : forall p, prog_ok p = true <-> GoCompile p.
Proof.
  intro p. unfold prog_ok, GoCompile, fm_keys, fm_find.
  destruct (fm_list p) as [ | [k f] [ | e l ] ] eqn:E; simpl.
  - split; [ discriminate | intros [body [Hk _]]; discriminate Hk ].
  - destruct f as [ body ]. split.
    + intro H. apply andb_true_iff in H. destruct H as [ Hk Hf ].
      apply String.eqb_eq in Hk; subst k. exists body. split; [ reflexivity | split ].
      * reflexivity.
      * apply forallb_stmt_ok_iff; exact Hf.
    + intros [body' [Hk [Hfind Hbody]]].
      injection Hk as Hkp; subst k.
      simpl in Hfind. injection Hfind as Hf; subst body'.
      apply andb_true_iff; split; [ reflexivity | apply forallb_stmt_ok_iff; exact Hbody ].
  - split; [ discriminate | intros [body [Hk _]]; discriminate Hk ].
Qed.

(** A boolean, reflected as a decision that remembers the witnessing equation. *)
Definition bool_sumbool (b : bool) : {b = true} + {b = false} :=
  match b with true => left eq_refl | false => right eq_refl end.

(** The executable compiler is proof-producing: it returns a CompilableProgram exactly when the
    program is admissible. *)
Definition go_compile (p : GoProgram) : option CompilableProgram :=
  match bool_sumbool (prog_ok p) with
  | left H  => Some (mkCompilable p (proj1 (prog_ok_iff p) H))
  | right _ => None
  end.

Theorem go_compile_sound : forall p cp, go_compile p = Some cp -> cp_program cp = p.
Proof.
  intros p cp. unfold go_compile.
  destruct (bool_sumbool (prog_ok p)) as [ H | H ]; intro Heq;
    [ injection Heq as <-; reflexivity | discriminate ].
Qed.

Theorem go_compile_complete : forall p, GoCompile p -> exists cp, go_compile p = Some cp.
Proof.
  intros p H. apply prog_ok_iff in H. unfold go_compile.
  destruct (bool_sumbool (prog_ok p)) as [ H' | H' ];
    [ eexists; reflexivity | rewrite H in H'; discriminate ].
Qed.

(** A rejected program yields no CompilableProgram (and hence no SafeProgram). *)
Lemma reject_no_compile : forall p, prog_ok p = false -> ~ GoCompile p.
Proof. intros p E H; apply prog_ok_iff in H; rewrite H in E; discriminate. Qed.

(** The one compiled file is at the canonical build path — so the emitted image key is [main.go],
    never an arbitrary/traversing/non-[.go] string.  Consumed by GoEmit. *)
Lemma compiled_main_go : forall cp : CompilableProgram, fm_keys (cp_program cp) = [main_path].
Proof. intros [ prog Hok ]; simpl. destruct Hok as [ body [ Hk _ ] ]. exact Hk. Qed.

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

(** Bad paths are rejected IN Rocq — an admissible body at an inadmissible key is not compile-
    admissible (no CompilableProgram, no SafeProgram, no image), so the writer never has to reject a
    certified program.  A non-[.go] name Go ignores, a traversing/absolute/nested path, and a sink
    control name are all rejected. *)
Example reject_non_go_ext :
  prog_ok (fm_singleton "main.txt" (MainFile [SPrintln []])) = false.
Proof. reflexivity. Qed.

Example reject_traversal_path :
  prog_ok (fm_singleton "../main.go" (MainFile [SPrintln []])) = false.
Proof. reflexivity. Qed.

Example reject_absolute_path :
  prog_ok (fm_singleton "/main.go" (MainFile [SPrintln []])) = false.
Proof. reflexivity. Qed.

Example reject_nested_path :
  prog_ok (fm_singleton "sub/main.go" (MainFile [SPrintln []])) = false.
Proof. reflexivity. Qed.

Example reject_control_name :
  prog_ok (fm_singleton ".fido-staging/x.go" (MainFile [SPrintln []])) = false.
Proof. reflexivity. Qed.
