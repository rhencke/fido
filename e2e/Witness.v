(** The e2e witness, emitted by the GENERAL Fido Emit transport command (no witness-specific
    executable, no extraction).  A proved [SafeProgram] is rendered to a [DirectoryImage] via
    [render_program], so its provenance proof is CLOSED (assumption-free); the command typechecks the
    image and finds its assumption closure empty (even though it descends the Qed lemma [demo_valid]),
    then decodes only the final (path, bytes) data and synchronizes the tree.  A candidate that is not
    compile-admissible has no [SafeProgram] and so cannot even be built into an image.

    This file is compiled EXPLICITLY (rocq c) after the cached theory/plugin build — the emission is not
    a dune .vo side effect.  It exercises every admitted primitive: bool, positive int, negative int,
    the exact min-int boundary [-(2^63)], the empty argument list, and multiple statements. *)
From Stdlib Require Import List NArith String.
From Fido Require Import FilePath FMap GoAST GoCompile GoSafe GoRender GoEmit.
Import ListNotations.

Definition demo_file : GoFileAST :=
  [ DMain [ SPrintln [ EBool true; EInt 42; ENeg 1; ENeg ((2 ^ 63)%N) ]
          ; SPrintln []
          ; SPrintln [ EBool false ] ] ].

Definition main_go : FilePath := mkFP "main.go" eq_refl.
Definition demo_program : GoProgram := singleton_program main_go demo_file.

Lemma demo_valid : ProgValid demo_program.
Proof. apply prog_ok_iff. reflexivity. Qed.

Definition demo_compiled : CompilableProgram :=
  mkCompilable demo_program (mkFacts "main"%string) (conj eq_refl demo_valid).
Definition demo_safe : SafeProgram := certify demo_compiled.

Declare ML Module "fido.emit".
Fido Emit (render_program demo_safe) To "/workspace/e2e-out".
