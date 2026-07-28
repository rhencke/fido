(* The boundary-byte witness: one println of the control and high byte boundaries, checked against hex. *)
From Stdlib Require Import List NArith String Ascii.
From Fido Require Import FilePath ModulePath Version Syntax Compilable Safe Render Emit.
Import ListNotations.

Definition boundary_bytes : string :=
  String (ascii_of_nat 0)   (String (ascii_of_nat 31)
 (String (ascii_of_nat 127) (String (ascii_of_nat 128)
 (String (ascii_of_nat 255) EmptyString)))).

Definition bytes_file : list Syntax.Decl := [ Syntax.Main [ Syntax.Println [ Syntax.StringLiteral boundary_bytes ] ] ].
Definition bytes_module : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Go1_23.
Definition bytes_program : Syntax.Program := singleton_program bytes_module (FilePath.Make "main.go" eq_refl) bytes_file.

Lemma bytes_valid : Admissible bytes_program.
Proof. apply Compilable.admissible_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

Definition bytes_compiled : Compilable.Program :=
  Compilable.capability_of_admissible bytes_program bytes_valid.

(* the artifact comes from the successful elaboration, not from a second decision *)
Example bytes_compiles : exists cp Hcp, Compilable.compile bytes_program = Compilable.Compiled cp Hcp.
Proof. exact (Compilable.compile_complete bytes_program bytes_valid). Qed.
Definition bytes_safe : Safe.Program := certify bytes_compiled.

(* formed from the source the capability was minted for, so the transport forces no rediscovery *)
Definition bytes_image : Emit.Image :=
  Emit.of_safe_at bytes_safe bytes_program (eq_trans (Safe.certify_source bytes_compiled)
                          (Compilable.capability_source bytes_program bytes_valid)).

Declare ML Module "fido.emit".
Fido Materialize bytes_image To "/workspace/generated-bytes".
(* the witness materializes only, and never publishes *)
