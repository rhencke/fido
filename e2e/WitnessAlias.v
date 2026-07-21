(** The byte/rune SOURCE-ALIAS differential witness (C4, §12/§13): a single `println` of the accepted alias
    conversions `byte(255)` and `rune(65)`.  The renderer emits the SOURCE spellings `byte(...)` / `rune(...)`
    (never the resolved `uint8`/`int32`), Go compiles them under the pinned toolchain (`byte` IS `uint8`,
    `rune` IS `int32`), and the program prints the exact resolved values `255 65` to stderr — the pinned-Go
    differential confirms the model's ACCEPT of the alias conversions matches real Go.

    This is a DISPOSABLE differential output (§13): it is materialized to a SEPARATE tree consumed only by the
    integration check and NEVER changes the canonical published module (`main.go`).  The rejected alias scars
    (`byte(256)`, `byte(-1)`, `rune(2^31)`, `rune(-2^31-1)`) fail IN Rocq (`const_info = None`, the
    GoCompile scar examples) and are never emitted — a Go build failure is never an expected test. *)
From Stdlib Require Import List NArith String Ascii.
From Fido Require Import FilePath ModulePath GoVersion GoNames GoAST GoCompile GoSafe GoRender GoEmit.
Import ListNotations.

Definition alias_file : list GoDecl :=
  [ DMain [ SPrintln [ EConvert (tsyn TNbyte) (EInt 255); EConvert (tsyn TNrune) (EInt 65) ] ] ].
Definition alias_module : ModuleSpec := mkModuleSpec (mkMP "fido.local/generated" eq_refl) Go1_23.
Definition alias_program : GoProgram := singleton_program alias_module (mkFP "main.go" eq_refl) alias_file.

Lemma alias_valid : GoCompile alias_program.
Proof. apply GoCompile_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

Definition alias_compiled : CompilableProgram :=
  compilable_of_valid alias_program alias_valid.

Example alias_compiles : exists cp Hcp, go_compile alias_program = CompiledOk cp Hcp.
Proof. exact (go_compile_complete alias_program alias_valid). Qed.
Definition alias_safe : SafeProgram := certify alias_compiled.

Declare ML Module "fido.emit".
Fido Materialize (render_program alias_safe) To "/workspace/generated-alias".
(* witness ONLY materializes the pristine (validated by the go-e2e fresh `go build`); no public
   sink/publish; DISPOSABLE — never the canonical published image. *)
