(** The boundary-byte string witness (contract): a single `println` of a string whose bytes are the
    control/high boundaries 0x00, 0x1f, 0x7f, 0x80, 0xff.  The renderer emits each as its canonical `\xhh`
    escape (the .go source stays ASCII + gofmt-clean), Go compiles it under the pinned toolchain, and the
    program prints the EXACT five bytes followed by a newline to stderr — the go-e2e byte-exact oracle
    compares that output (as hex, via `od`) against the reviewed golden `e2e/golden.bytes.hex`.

    This is NOT the canonical generated module (that is the primary `Witness.v`); it is emitted to a separate
    tree consumed only by the integration byte-exactness check.  `println` output is INTEGRATION EVIDENCE of
    real-Go byte fidelity, NOT the formal string semantics — the formal semantics are the exact byte value
    ([const_value]/[eval_expr]) and the independent canonical-literal decoder round-trip ([Render]). *)
From Stdlib Require Import List NArith String Ascii.
From Fido Require Import FilePath ModulePath Version Syntax Compilable Safe Render Emit.
Import ListNotations.

Definition boundary_bytes : string :=
  String (ascii_of_nat 0)   (String (ascii_of_nat 31)
 (String (ascii_of_nat 127) (String (ascii_of_nat 128)
 (String (ascii_of_nat 255) EmptyString)))).

Definition bytes_file (*decls*) : list Syntax.Decl := [ Syntax.Main [ Syntax.Println [ Syntax.StringLiteral boundary_bytes ] ] ].
Definition bytes_module : ModuleSpec := Syntax.make_module_spec (ModulePath.make "fido.local/generated" eq_refl) Go1_23.
Definition bytes_program : Syntax.Program := singleton_program bytes_module (FilePath.make "main.go" eq_refl) bytes_file.

Lemma bytes_valid : Admissible bytes_program.
Proof. apply Compilable.admissible_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

Definition bytes_compiled : Compilable.Program :=
  Compilable.capability_of_admissible bytes_program bytes_valid.

(* the compilation artifact IS obtained from the successful elaboration (the accepted decision, via Compilable.compile). *)
Example bytes_compiles : exists cp Hcp, Compilable.compile bytes_program = Compilable.Compiled cp Hcp.
Proof. exact (Compilable.compile_complete bytes_program bytes_valid). Qed.
Definition bytes_safe : Safe.Program := certify bytes_compiled.

(* the image, formed from the source the capability was minted for: [capability_source] is the proof
   that this IS the certificate's own source, so the emitted bytes are the compiler-accepted program's
   and the transport never has to force the elaboration to rediscover a program it already has. *)
Definition bytes_image : Emit.Image :=
  Emit.of_safe_at bytes_safe bytes_program (Compilable.capability_source bytes_program bytes_valid).

Declare ML Module "fido.emit".
Fido Materialize bytes_image To "/workspace/generated-bytes".
(* witness ONLY materializes the pristine (validated by the go-e2e fresh `go build`); no public
   sink/publish — the sink is exercised by e2e/sink_test.ml + the validated `make regenerate` workflow. *)
