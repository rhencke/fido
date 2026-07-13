(** ============================================================================
    GoCompile — EXACT whole-PROGRAM static/compiler admissibility as EVIDENCE over the ONE raw program
    (the [GoProgram]: a [ModuleSpec] + a possibly-EMPTY finite map of files), plus the derived
    [CompilationFacts] over that same program.  The empty program is accepted (no packages, one go.mod).

    Whole-program package policy (a deliberate exact GENERATOR-language subset — not a model of arbitrary
    human package clauses).  Because raw package clauses and imports are absent:
      - files are grouped by parent directory ([fp_parent]); each directory is one package;
      - the compiler-derived package name is `main`;
      - every package must contain EXACTLY ONE admissible `main` declaration across all its files
        (zero rejects the whole program; more than one rejects the whole program);
      - every declaration's statements must be integer-representable;
      - one invalid package rejects the WHOLE program (all-or-nothing; no per-file partial acceptance);
      - multiple valid main packages in different directories are accepted, matching `go build ./...`;
      - an empty file is accepted when its package's single `main` is elsewhere;
      - imports are impossible (no import syntax), so the derived import set is empty for every file.

    HONESTY — two distinct claims:
    A. KERNEL-internal exactness (PROVED here): [go_compile] succeeds exactly for the declarative
       [GoCompile] judgment ([prog_ok_iff]; sound + complete).
    B. EXTERNAL adequacy (the GOAL, attacked by differential `go build ./...` experiments, NOT a kernel
       theorem): the declarative judgment matches `go build ./...` for every representable rendered
       program.  We do NOT invoke cmd/go from Rocq and claim no kernel theorem about it.
    ============================================================================ *)
From Stdlib Require Import NArith ZArith List Bool String Arith.
From Fido Require Import Ints FilePath FMap GoAST.
Import ListNotations.
Open Scope Z_scope.

(** ---- statement/expression admissibility (integer representability) ---- *)

Inductive ExprOk : GoExpr -> Prop :=
| OkBool : forall b, ExprOk (EBool b)
| OkInt  : forall n, Z.of_N n <= int_max     -> ExprOk (EInt n)
| OkNeg  : forall n, Z.of_N n <= - int_min   -> ExprOk (ENeg n).

Inductive StmtOk : GoStmt -> Prop :=
| OkPrintln : forall args, Forall ExprOk args -> StmtOk (SPrintln args).

Inductive DeclOk : GoDecl -> Prop :=
| OkDMain : forall body, Forall StmtOk body -> DeclOk (DMain body).

Definition FileOk (f : GoFileAST) : Prop := Forall DeclOk f.

Definition expr_ok (e : GoExpr) : bool :=
  match e with
  | EBool _ => true
  | EInt n  => Z.of_N n <=? int_max
  | ENeg n  => Z.of_N n <=? - int_min
  end.

Definition stmt_ok (s : GoStmt) : bool := match s with SPrintln args => forallb expr_ok args end.
Definition decl_ok (d : GoDecl) : bool := match d with DMain body => forallb stmt_ok body end.
Definition file_ok (f : GoFileAST) : bool := forallb decl_ok f.

(** ---- main-declaration counting (entry-point status is a compilation result) ---- *)

Definition decl_is_main (d : GoDecl) : bool := match d with DMain _ => true end.
Definition file_main_count (f : GoFileAST) : nat := List.length (List.filter decl_is_main f).

(** total `main` declarations in one package (directory) across all its files. *)
Definition main_count_in_dir (dir : string) (entries : list (FilePath * GoFileAST)) : nat :=
  fold_right (fun e acc =>
    ((if String.eqb (fp_parent (fst e)) dir then file_main_count (snd e) else 0) + acc)%nat)
    0%nat entries.

(** ---- reflection helpers ---- *)

Lemma forallb_Forall {X} : forall (f : X -> bool) (P : X -> Prop) (l : list X),
  (forall x, f x = true <-> P x) -> (forallb f l = true <-> Forall P l).
Proof.
  intros f P l Hpt; induction l as [ | x l' IH ]; simpl.
  - split; [ constructor | reflexivity ].
  - rewrite Bool.andb_true_iff, Hpt, IH.
    split; [ intros [Hx Hl]; constructor; assumption
           | intro H; inversion H; subst; split; assumption ].
Qed.

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

Lemma stmt_ok_iff : forall s, stmt_ok s = true <-> StmtOk s.
Proof.
  intros [args]; simpl. rewrite (forallb_Forall expr_ok ExprOk args expr_ok_iff).
  split; [ intro H; constructor; exact H | intro H; inversion H; subst; assumption ].
Qed.

Lemma decl_ok_iff : forall d, decl_ok d = true <-> DeclOk d.
Proof.
  intros [body]; simpl. rewrite (forallb_Forall stmt_ok StmtOk body stmt_ok_iff).
  split; [ intro H; constructor; exact H | intro H; inversion H; subst; assumption ].
Qed.

Lemma file_ok_iff : forall f, file_ok f = true <-> FileOk f.
Proof. intro f; unfold file_ok, FileOk; apply forallb_Forall; exact decl_ok_iff. Qed.

(** ---- the declarative validity of the whole program ---- *)

(** Every file's declarations are admissible. *)
Definition AllFilesOk (p : GoProgram) : Prop :=
  Forall (fun e => FileOk (snd e)) (prog_entries p).

(** Every package (directory) has exactly one `main` declaration. *)
Definition AllPackagesOneMain (p : GoProgram) : Prop :=
  Forall (fun e => main_count_in_dir (fp_parent (fst e)) (prog_entries p) = 1%nat) (prog_entries p).

Definition ProgValid (p : GoProgram) : Prop := AllFilesOk p /\ AllPackagesOneMain p.

Definition prog_ok (p : GoProgram) : bool :=
  forallb (fun e => file_ok (snd e)) (prog_entries p)
  && forallb (fun e => Nat.eqb (main_count_in_dir (fp_parent (fst e)) (prog_entries p)) 1%nat)
             (prog_entries p).

Lemma prog_ok_iff : forall p, prog_ok p = true <-> ProgValid p.
Proof.
  intro p; unfold prog_ok, ProgValid, AllFilesOk, AllPackagesOneMain.
  rewrite Bool.andb_true_iff.
  rewrite (forallb_Forall (fun e => file_ok (snd e)) (fun e => FileOk (snd e)) (prog_entries p)
             (fun e => file_ok_iff (snd e))).
  rewrite (forallb_Forall
             (fun e => Nat.eqb (main_count_in_dir (fp_parent (fst e)) (prog_entries p)) 1%nat)
             (fun e => main_count_in_dir (fp_parent (fst e)) (prog_entries p) = 1%nat)
             (prog_entries p)
             (fun e => Nat.eqb_eq _ 1%nat)).
  reflexivity.
Qed.

(** ---- compilation facts over the SAME program ---- *)

(** The compiler-derived facts a downstream stage consumes.  Today: the derived package clause name the
    renderer emits (uniformly `main` under the current policy — a compilation RESULT, not raw metadata,
    since raw files carry no package clause).  Indexed by [p] so richer per-program facts (symbol/type
    tables) decorate this same program later without a second AST. *)
Record CompilationFacts (p : GoProgram) : Type := mkFacts {
  cf_pkg_name : string
}.
Arguments mkFacts {p}.
Arguments cf_pkg_name {p}.

Definition GoCompile (p : GoProgram) (facts : CompilationFacts p) : Prop :=
  cf_pkg_name facts = "main"%string /\ ProgValid p.

Record CompilableProgram : Type := mkCompilable {
  cp_program : GoProgram;
  cp_facts   : CompilationFacts cp_program;
  cp_ok      : GoCompile cp_program cp_facts
}.

(** ---- the proof-producing executable compiler ---- *)

Inductive CompileError : Type :=
| ErrIntOverflow      (* some declaration has an out-of-range integer literal *)
| ErrPackageMainCount (* some package has zero or multiple `main` declarations *).

Inductive result (E A : Type) : Type := Ok : A -> result E A | Err : E -> result E A.
Arguments Ok {E A}. Arguments Err {E A}.

Definition bool_sumbool (b : bool) : {b = true} + {b = false} :=
  match b with true => left eq_refl | false => right eq_refl end.

Definition go_compile (p : GoProgram) : result CompileError CompilableProgram :=
  match bool_sumbool (prog_ok p) with
  | left H  => Ok (mkCompilable p (mkFacts "main"%string) (conj eq_refl (proj1 (prog_ok_iff p) H)))
  | right _ =>
      if forallb (fun e => file_ok (snd e)) (prog_entries p)
      then Err ErrPackageMainCount else Err ErrIntOverflow
  end.

(** (A) internal exactness: [go_compile] accepts exactly the admissible programs, whole-program. *)
Theorem go_compile_sound : forall p cp,
  go_compile p = Ok cp -> cp_program cp = p /\ GoCompile (cp_program cp) (cp_facts cp).
Proof.
  intros p cp Heq. split; [ | exact (cp_ok cp) ].
  revert Heq. unfold go_compile.
  destruct (bool_sumbool (prog_ok p)) as [ H | H ].
  - intro Heq; injection Heq as <-; reflexivity.
  - destruct (forallb (fun e => file_ok (snd e)) (prog_entries p)); discriminate.
Qed.

Theorem go_compile_complete : forall p facts,
  GoCompile p facts -> exists cp, go_compile p = Ok cp.
Proof.
  intros p facts [ _ Hvalid ]. apply (proj2 (prog_ok_iff p)) in Hvalid. unfold go_compile.
  destruct (bool_sumbool (prog_ok p)) as [ H' | H' ]; [ eexists; reflexivity | ].
  rewrite Hvalid in H'; discriminate.
Qed.

(** A rejected program yields no CompilableProgram (and hence no SafeProgram, no image). *)
Lemma reject_no_compile : forall p facts, prog_ok p = false -> ~ GoCompile p facts.
Proof.
  intros p facts E [ _ Hvalid ]. apply (proj2 (prog_ok_iff p)) in Hvalid.
  rewrite Hvalid in E; discriminate.
Qed.
