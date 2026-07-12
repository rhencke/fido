(** ============================================================================
    GoAST — the ONE raw program representation.  The permanent root is a nonempty verified finite map:

      GoProgram := nonempty (fmap FilePath GoFileAST)   (one raw file AST per intrinsic path)

    A [GoFileAST] is RAW top-level declarations only — nothing compiled.  It does NOT carry a package
    clause, a package identity, an entry-point flag, imports, symbols, or types: those are COMPILATION
    RESULTS derived by GoCompile over the whole path-indexed program.  There is no raw GoPackage tree.

    The one raw declaration today is [DMain body]: syntactically a `func main() { body }` declaration
    (zero parameters, no results) whose body is the existing [SPrintln] statements.  Whether that
    declaration is the UNIQUE entry point of its package is decided by GoCompile — MULTIPLE [DMain] in a
    file are representable precisely so GoCompile can reject a duplicate `main` exactly as Go would.  A
    file with NO declarations is representable (a valid file in a package whose `main` is elsewhere).

    No identifiers, calls, parameters, results, imports, arbitrary expressions/statements, user types,
    concurrency, or package clauses.  Anything else is UNREPRESENTABLE.
    ============================================================================ *)
From Stdlib Require Import NArith List.
From Fido Require Import FilePath FMap.
Import ListNotations.

Inductive GoExpr : Type :=
| EBool : bool -> GoExpr
| EInt  : N -> GoExpr
| ENeg  : N -> GoExpr.

Inductive GoStmt : Type :=
| SPrintln : list GoExpr -> GoStmt.

(** A raw top-level declaration.  Today: a `func main()` declaration with a statement body. *)
Inductive GoDecl : Type :=
| DMain : list GoStmt -> GoDecl.

(** The raw AST of one source file: its top-level declarations, in order. *)
Definition GoFileAST := list GoDecl.

(** ---- the nonempty program map ---- *)

Lemma cons_neq_nil {X : Type} : forall (e : X) r, e :: r <> [].
Proof. discriminate. Qed.

Lemma nonempty_from_eq {X : Type} : forall (fl : list X) e r, fl = e :: r -> fl <> [].
Proof. intros fl e r ->; discriminate. Qed.

Record GoProgram : Type := mkProgram {
  prog_files    : fmap FilePath GoFileAST;
  prog_nonempty : fm_list prog_files <> []
}.

Definition prog_entries (p : GoProgram) : list (FilePath * GoFileAST) := fm_list (prog_files p).
Definition prog_keys (p : GoProgram) : list FilePath := fm_keys (prog_files p).
Definition prog_find (path : FilePath) (p : GoProgram) : option GoFileAST :=
  fm_find fp_eqb path (prog_files p).

(** ---- builders (keys unique + nonempty, both intrinsic) ---- *)

(** A single-file program. *)
Definition singleton_program (path : FilePath) (f : GoFileAST) : GoProgram :=
  mkProgram (fm_singleton path f) (cons_neq_nil (path, f) []).

(** From a list of (path, file): [None] on duplicate paths OR an empty list; otherwise a program whose
    key-uniqueness and nonemptiness proofs are intrinsic. *)
Definition build_program (l : list (FilePath * GoFileAST)) : option GoProgram :=
  match fm_of_list fp_eqb fp_eqb_eq l with
  | None => None
  | Some m =>
      (match fm_list m as fl return fm_list m = fl -> option GoProgram with
       | [] => fun _ => None
       | e :: r => fun H => Some (mkProgram m (nonempty_from_eq (fm_list m) e r H))
       end) eq_refl
  end.
