(** The byte/rune SOURCE-ALIAS differential witness (C4, §12/§13): a single `println` of the ACCEPTED alias
    conversions across the full accept boundary — `byte(0)`, `byte(255)`, the matching `uint8(255)`, and the
    `rune`/`int32` endpoints `rune(-2147483648)`/`rune(2147483647)` with the matching `int32(...)`.  The renderer
    emits the SOURCE spellings `byte(...)`/`rune(...)` (never the resolved `uint8`/`int32`), Go compiles them
    under the pinned toolchain (`byte` IS `uint8`, `rune` IS `int32`), and the program prints the exact resolved
    values to stderr — the pinned-Go differential confirms the model's ACCEPT of the alias conversions matches
    real Go.

    This is a DISPOSABLE differential output (§13): it is materialized to a SEPARATE tree consumed only by the
    integration check and NEVER changes the canonical published module (`main.go`).  The REJECTED alias scars
    (`byte(-1)`, `byte(256)`, `rune(-2147483649)`, `rune(2147483648)`, and the matching `uint8`/`int32`) fail IN
    Rocq (`Typing.resolve = None`, the Admissible `scar_*_rejected` examples) so no Fido image exists for them; the
    e2e's `rej_conv` helper feeds the corresponding RAW Go to the SAME pinned toolchain and confirms it too
    REJECTS them with a conversion/type-check diagnostic — the accept AND reject halves are both pinned-Go. *)
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
Definition alias_module : ModuleSpec := Syntax.make_module_spec (ModulePath.make "fido.local/generated" eq_refl) Go1_23.
Definition alias_program : Syntax.Program := singleton_program alias_module (FilePath.make "main.go" eq_refl) alias_file.

Lemma alias_valid : Admissible alias_program.
Proof. apply Compilable.admissible_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

Definition alias_compiled : Compilable.Program :=
  Compilable.capability_of_admissible alias_program alias_valid.

Example alias_compiles : exists cp Hcp, Compilable.compile alias_program = Compilable.Compiled cp Hcp.
Proof. exact (Compilable.compile_complete alias_program alias_valid). Qed.
Definition alias_safe : Safe.Program := certify alias_compiled.

(* the image, formed from the source the capability was minted for: [capability_source] is the proof
   that this IS the certificate's own source, so the emitted bytes are the compiler-accepted program's
   and the transport never has to force the elaboration to rediscover a program it already has. *)
Definition alias_image : Emit.Image :=
  Emit.of_safe_at alias_safe alias_program (Compilable.capability_source alias_program alias_valid).

Declare ML Module "fido.emit".
Fido Materialize alias_image To "/workspace/generated-alias".
(* witness ONLY materializes the pristine (validated by the go-e2e fresh `go build`); no public
   sink/publish; DISPOSABLE — never the canonical published image. *)
