(** A differential witness: a WHOLE-PROGRAM with TWO main packages in different directories (root
    `main.go` and `sub/main.go`, each with exactly one `main`) plus a THIRD file in the root package that
    has no declarations (an empty file, valid because the root package's single `main` is elsewhere).
    GoCompile accepts it (prog_ok = true, checked below); the emitted tree must be accepted by
    `go build ./...` — the differential alarm that the whole-program directory/package rules match Go. *)
From Stdlib Require Import List NArith String.
From Fido Require Import FilePath FMap GoAST GoCompile GoSafe GoRender GoEmit.
Import ListNotations.

Definition m_root  : FilePath := mkFP "main.go" eq_refl.
Definition m_extra : FilePath := mkFP "extra.go" eq_refl.          (* same (root) package, no main *)
Definition m_sub   : FilePath := mkFP "sub/main.go" eq_refl.       (* a second main package *)

Definition multi_entries : list (FilePath * GoFileAST) :=
  [ (m_root,  [ DMain [ SPrintln [ EBool true; EInt 1 ] ] ])
  ; (m_extra, [])
  ; (m_sub,   [ DMain [ SPrintln [ ENeg 5 ] ] ]) ].

Definition multi_program : GoProgram :=
  match build_program multi_entries with Some p => p | None => singleton_program m_root [] end.

Lemma multi_valid : ProgValid multi_program.
Proof. apply prog_ok_iff. vm_compute. reflexivity. Qed.

Definition multi_compiled : CompilableProgram :=
  mkCompilable multi_program (mkFacts "main"%string) (conj eq_refl multi_valid).
Definition multi_safe : SafeProgram := certify multi_compiled.

Declare ML Module "fido.emit".
Fido Emit (render_program multi_safe) To "/workspace/e2e-multi".
