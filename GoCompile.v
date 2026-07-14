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
      - the whole program is TYPED through [GoTypes] ([ProgramTyped] — every `println` argument resolves to a
        [GoType]; today the only typing failure is an integer literal outside the 64-bit range);
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
From Fido Require Import Ints FilePath FMap GoAST GoTypes.
Import ListNotations.
Open Scope Z_scope.

(** ---- static admissibility is TYPING (GoTypes, the one type authority) ----

    Per-file/decl/statement/expression admissibility is [GoTypes.ProgramTyped]/[program_typedb] over the
    SAME raw AST: every [println] argument must RESOLVE under [UsePrintlnArg] to a [GoType] (the current
    fragment's only failure is an integer literal outside the 64-bit range — bools always resolve).  There
    is no separate GoCompile static-admissibility family; the deleted [ExprOk]/[StmtOk]/[DeclOk]/[FileOk]
    are subsumed by the type judgment. *)

(** ---- main-declaration counting (entry-point status is a compilation result) ---- *)

Definition decl_is_main (d : GoDecl) : bool := match d with DMain _ => true end.
Definition file_main_count (f : GoFileAST) : nat := List.length (List.filter decl_is_main f).

(** total `main` declarations in one package (directory) across all its files. *)
Definition main_count_in_dir (dir : string) (entries : list (FilePath * GoFileAST)) : nat :=
  fold_right (fun e acc =>
    ((if String.eqb (fp_parent (fst e)) dir then file_main_count (snd e) else 0) + acc)%nat)
    0%nat entries.

(** ---- the declarative validity of the whole program ---- *)

(** Every package (directory) has exactly one `main` declaration. *)
Definition AllPackagesOneMain (p : GoProgram) : Prop :=
  Forall (fun e => main_count_in_dir (fp_parent (fst e)) (prog_entries p) = 1%nat) (prog_entries p).

(** A program is valid iff it is TYPED (every argument resolves through [GoTypes]) AND every package has
    exactly one `main`.  [ProgramTyped] is the one static-typing foundation; there is no parallel
    admissibility family. *)
Definition ProgValid (p : GoProgram) : Prop := ProgramTyped p /\ AllPackagesOneMain p.

Definition prog_ok (p : GoProgram) : bool :=
  program_typedb p
  && forallb (fun e => Nat.eqb (main_count_in_dir (fp_parent (fst e)) (prog_entries p)) 1%nat)
             (prog_entries p).

Lemma prog_ok_iff : forall p, prog_ok p = true <-> ProgValid p.
Proof.
  intro p; unfold prog_ok, ProgValid, AllPackagesOneMain.
  rewrite Bool.andb_true_iff, program_typedb_iff.
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
    tables) decorate this same program later without a second AST.  The static TYPING evidence over the
    same [p] is NOT stored as a redundant field — it is a canonical projection from the compiled evidence
    ([compile_program_typed]/[compilable_program_typed] below), since [GoCompile] already carries
    [ProgValid p] whose first conjunct is [ProgramTyped p]. *)
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

(** The compiled evidence EXPOSES that the same program is typed through [GoTypes] (§17): an immediate
    canonical projection, not a stored second copy of the typing proof. *)
Theorem compile_program_typed : forall p facts, GoCompile p facts -> ProgramTyped p.
Proof. intros p facts H; exact (proj1 (proj2 H)). Qed.

Theorem compilable_program_typed : forall cp : CompilableProgram, ProgramTyped (cp_program cp).
Proof. intro cp; exact (compile_program_typed _ _ (cp_ok cp)). Qed.

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
      (* the whole program is typed but some package's `main` count is wrong, vs. a typing failure
         (today the only typing failure is an integer literal outside the 64-bit range). *)
      if program_typedb p then Err ErrPackageMainCount else Err ErrIntOverflow
  end.

(** (A) internal exactness: [go_compile] accepts exactly the admissible programs, whole-program. *)
Theorem go_compile_sound : forall p cp,
  go_compile p = Ok cp -> cp_program cp = p /\ GoCompile (cp_program cp) (cp_facts cp).
Proof.
  intros p cp Heq. split; [ | exact (cp_ok cp) ].
  revert Heq. unfold go_compile.
  destruct (bool_sumbool (prog_ok p)) as [ H | H ].
  - intro Heq; injection Heq as <-; reflexivity.
  - destruct (program_typedb p); discriminate.
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

(** The empty program (empty file map) is accepted under the new typing authority: no package to type
    and no `main` to count, so [prog_ok] holds vacuously. *)
Lemma prog_ok_empty : forall p, prog_entries p = [] -> prog_ok p = true.
Proof. intros p H; unfold prog_ok, program_typedb; rewrite H; reflexivity. Qed.

(** ---- boundary fixture: an out-of-range argument rejects the WHOLE program BEFORE any emission ---- *)

(** A single-file program whose only `println` argument is [int_max + 1] (one past the one [Ints] upper
    bound; NOT a duplicated numeric literal) — unrepresentable as [TInt] through the [GoTypes] authority. *)
Definition over_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EInt (Z.to_N (int_max + 1)) ] ] ].

(* the whole program fails typing, so [prog_ok] rejects it and [go_compile] returns the EXACT integer
   error — and there is NO [CompilableProgram] for it (hence no [SafeProgram], no [DirectoryImage], no
   rendering/emission): rejection happens strictly in Rocq, before any bytes. *)
Example over_program_untyped   : program_typedb over_program = false.        Proof. reflexivity. Qed.
Example over_program_not_ok    : prog_ok over_program = false.               Proof. reflexivity. Qed.
Example over_program_rejected  : go_compile over_program = Err ErrIntOverflow. Proof. reflexivity. Qed.
Example over_program_no_compile : forall facts, ~ GoCompile over_program facts.
Proof. intro facts; exact (reject_no_compile over_program facts over_program_not_ok). Qed.
