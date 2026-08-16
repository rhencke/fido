(* The boundary-byte witness: one println of the control and high byte boundaries, checked against hex. *)
From Stdlib Require Import List NArith String Ascii.
From Fido Require Import FilePath ModulePath Version Names Syntax Compilable Safe Render Emit.
Import ListNotations.

Definition boundary_bytes : string :=
  String (ascii_of_nat 0)   (String (ascii_of_nat 31)
 (String (ascii_of_nat 127) (String (ascii_of_nat 128)
 (String (ascii_of_nat 255) EmptyString)))).

Definition bytes_file : list Syntax.TopLevelDecl :=
  [ Syntax.Main (Syntax.MakeBlock
    [ Syntax.ExprStmt (Syntax.Application (Syntax.Name (Names.predeclared_ordinary Names.PPrintln))
        [ Syntax.LiteralExpr (Syntax.StringLiteral boundary_bytes) ]) ]) ].
Definition bytes_module : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Go1_23.
Definition bytes_program : Syntax.Program := singleton_program bytes_module (FilePath.Make "main.go" eq_refl) bytes_file.

Definition bytes_valid : Compilable.Admissible (Compilable.elaborate bytes_program).
Proof. split; apply Compilable.list_is_nilb_true; vm_compute; reflexivity. Qed.

(* carry the exact compilation and its capability into the certified image *)
Definition bytes_cap : Compilable.Prog.Program (Compilable.elaborate bytes_program) :=
  Compilable.Prog.issue (Compilable.elaborate bytes_program) bytes_valid.
Definition bytes_safe : Safe.Program := Safe.certify bytes_program (Compilable.elaborate bytes_program) bytes_cap I.
Definition bytes_image : Emit.Image := Emit.of_safe bytes_safe.

Declare ML Module "fido.emit".
Fido Materialize bytes_image To "/workspace/generated-bytes".
(* the witness materializes only, and never publishes *)
