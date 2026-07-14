(** The boundary-byte string witness (contract §22): a single `println` of a string whose bytes are the
    control/high boundaries 0x00, 0x1f, 0x7f, 0x80, 0xff.  The renderer emits each as its canonical `\xhh`
    escape (the .go source stays ASCII + gofmt-clean), Go compiles it under the pinned toolchain, and the
    program prints the EXACT five bytes followed by a newline to stderr — the go-e2e byte-exact oracle
    compares that output (as hex, via `od`) against the reviewed golden `e2e/golden.bytes.hex`.

    This is NOT the canonical generated module (that is the primary `Witness.v`); it is emitted to a separate
    tree consumed only by the integration byte-exactness check.  `println` output is INTEGRATION EVIDENCE of
    real-Go byte fidelity, NOT the formal string semantics — the formal semantics are the exact byte value
    ([const_value]/[eval_expr]) and the independent canonical-literal decoder round-trip ([GoRender]). *)
From Stdlib Require Import List NArith String Ascii.
From Fido Require Import FilePath FMap ModulePath GoVersion GoAST GoCompile GoSafe GoRender GoEmit.
Import ListNotations.

Definition boundary_bytes : string :=
  String (ascii_of_nat 0)   (String (ascii_of_nat 31)
 (String (ascii_of_nat 127) (String (ascii_of_nat 128)
 (String (ascii_of_nat 255) EmptyString)))).

Definition bytes_file : GoFileAST := [ DMain [ SPrintln [ EString boundary_bytes ] ] ].
Definition bytes_module : ModuleSpec := mkModuleSpec (mkMP "fido.local/generated" eq_refl) Go1_23.
Definition bytes_program : GoProgram := singleton_program bytes_module (mkFP "main.go" eq_refl) bytes_file.

Lemma bytes_valid : ProgValid bytes_program.
Proof. apply prog_ok_iff. reflexivity. Qed.

Definition bytes_compiled : CompilableProgram :=
  mkCompilable bytes_program (mkFacts "main"%string) (conj eq_refl bytes_valid).
Definition bytes_safe : SafeProgram := certify bytes_compiled.

Declare ML Module "fido.emit".
Fido Emit (render_program bytes_safe) To "/workspace/e2e-bytes".
