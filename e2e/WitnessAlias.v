(* The byte and rune alias differential: the accepted conversions, rendered in their source spellings. *)
From Stdlib Require Import List NArith String Ascii.
From Fido Require Import FilePath ModulePath Version Names Syntax Compilable Safe Render Emit.
Import ListNotations.

Definition alias_file : list Syntax.Decl :=
  [ Syntax.Main [ Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Byte)  (Syntax.IntegerLiteral 0)
                     ; Syntax.Convert (Syntax.type_expr_of_name Names.Byte)  (Syntax.IntegerLiteral 255)
                     ; Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 255)
                     ; Syntax.Convert (Syntax.type_expr_of_name Names.Rune)  (Syntax.NegatedIntegerLiteral 2147483648)
                     ; Syntax.Convert (Syntax.type_expr_of_name Names.Rune)  (Syntax.IntegerLiteral 2147483647)
                     ; Syntax.Convert (Syntax.type_expr_of_name Names.Int32) (Syntax.NegatedIntegerLiteral 2147483648)
                     ; Syntax.Convert (Syntax.type_expr_of_name Names.Int32) (Syntax.IntegerLiteral 2147483647) ] ] ].
Definition alias_module : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Go1_23.
Definition alias_program : Syntax.Program := singleton_program alias_module (FilePath.Make "main.go" eq_refl) alias_file.

Lemma alias_valid : Admissible alias_program.
Proof. apply Compilable.admissible_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

Definition alias_compiled : Compilable.Program :=
  Compilable.capability_of_admissible alias_program alias_valid.

Example alias_compiles : exists cp Hcp, Compilable.compile alias_program = Compilable.Compiled cp Hcp.
Proof. exact (Compilable.compile_complete alias_program alias_valid). Qed.
Definition alias_safe : Safe.Program := certify alias_compiled.

(* formed from the source the capability was minted for, so the transport forces no rediscovery *)
Definition alias_image : Emit.Image :=
  Emit.of_safe_at alias_safe alias_program (eq_trans (Safe.certify_source alias_compiled)
                          (Compilable.capability_source alias_program alias_valid)).

Declare ML Module "fido.emit".
Fido Materialize alias_image To "/workspace/generated-alias".
(* the witness materializes only, and this tree is never the canonical published image *)
