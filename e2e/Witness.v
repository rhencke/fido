(** The e2e witness, emitted by the GENERAL Fido Emit transport command (no witness-specific
    executable, no extraction).  A proved [SafeProgram] is rendered to a [DirectoryImage] via
    [render_program], so its provenance proof is CLOSED (assumption-free); the command typechecks the
    image and finds its assumption closure empty (even though it descends the Qed lemma [demo_valid]),
    then decodes only the final (go.mod bytes, entries) transport and synchronizes the tree.  A candidate that is not
    compile-admissible has no [SafeProgram] and so cannot even be built into an image.

    This file is compiled EXPLICITLY (rocq c) after the cached theory/plugin build — the emission is not
    a dune .vo side effect.  It exercises every admitted primitive: bool, positive int, negative int,
    the exact min-int boundary [-(2^63)], the empty argument list, multiple statements, readable Go
    strings — empty, ordinary ASCII, a lone double-quote, a lone backslash, and embedded tab / carriage
    return / newline bytes (the renderer emits each as its canonical escape; Go prints the exact bytes) —
    AND accepted explicit integer conversions across all ten integer types (signed/unsigned narrow +
    64-bit boundaries, platform int/uint, uint64(2^63), and a nested int8(int16(127))).  The pinned Go
    toolchain accepts every one and prints its exact value; the corresponding out-of-range / non-integer
    conversions are rejected by hand-written differential fixtures (Dockerfile go-e2e), exactly as
    GoTypes/GoCompile make impossible.  The rendered tree includes the certified [go.mod] (from the
    module spec) alongside the .go files. *)
From Stdlib Require Import List NArith String Ascii.
From Fido Require Import Ints FilePath FMap ModulePath GoVersion GoAST GoCompile GoSafe GoRender GoEmit.
Import ListNotations.

(* control-byte strings built by exact ascii code (0x09 TAB, 0x0d CR, 0x0a NL) between two letters. *)
Definition s_tab : string := String "a"%char (String (ascii_of_nat 9)  (String "b"%char EmptyString)).
Definition s_cr  : string := String "a"%char (String (ascii_of_nat 13) (String "b"%char EmptyString)).
Definition s_nl  : string := String "a"%char (String (ascii_of_nat 10) (String "b"%char EmptyString)).

Definition demo_file : GoFileAST :=
  [ DMain [ SPrintln [ EBool true; EInt 42; ENeg 1; ENeg ((2 ^ 63)%N) ]
          ; SPrintln []
          ; SPrintln [ EBool false ]
          ; SPrintln [ EString "hello, world" ]
          ; SPrintln [ EString EmptyString ]
          ; SPrintln [ EBool true; EInt 7; EString "mix" ]
          ; SPrintln [ EString (String (ascii_of_nat 34) EmptyString) ]   (* a lone double-quote *)
          ; SPrintln [ EString (String (ascii_of_nat 92) EmptyString) ]   (* a lone backslash *)
          ; SPrintln [ EString s_tab ]
          ; SPrintln [ EString s_cr ]
          ; SPrintln [ EString s_nl ]
          (* accepted integer conversions across all ten integer types (§18): signed narrow + 64-bit
             minima/maxima, unsigned maxima, platform int/uint, uint64(2^63), and a nested conversion. *)
          ; SPrintln [ EIntConvert IInt8  (ENeg 128); EIntConvert IInt8  (EInt 127) ]
          ; SPrintln [ EIntConvert IInt16 (ENeg 32768); EIntConvert IInt16 (EInt 32767) ]
          ; SPrintln [ EIntConvert IInt32 (ENeg 2147483648); EIntConvert IInt32 (EInt 2147483647) ]
          ; SPrintln [ EIntConvert IInt64 (ENeg ((2 ^ 63)%N)); EIntConvert IInt64 (EInt ((2 ^ 63 - 1)%N)) ]
          ; SPrintln [ EIntConvert IInt   (ENeg ((2 ^ 63)%N)); EIntConvert IInt   (EInt ((2 ^ 63 - 1)%N)) ]
          ; SPrintln [ EIntConvert IUint8 (EInt 255); EIntConvert IUint16 (EInt 65535)
                     ; EIntConvert IUint32 (EInt 4294967295) ]
          ; SPrintln [ EIntConvert IUint64 (EInt ((2 ^ 63)%N)); EIntConvert IUint64 (EInt 18446744073709551615) ]
          ; SPrintln [ EIntConvert IUint (EInt 18446744073709551615) ]
          ; SPrintln [ EIntConvert IInt8 (EIntConvert IInt16 (EInt 127)) ] ] ].

Definition demo_module : ModuleSpec := mkModuleSpec (mkMP "fido.local/generated" eq_refl) Go1_23.
Definition main_go : FilePath := mkFP "main.go" eq_refl.
Definition demo_program : GoProgram := singleton_program demo_module main_go demo_file.

Lemma demo_valid : ProgValid demo_program.
Proof. apply prog_ok_iff. reflexivity. Qed.

Definition demo_compiled : CompilableProgram :=
  mkCompilable demo_program (mkFacts "main"%string) (conj eq_refl demo_valid).
Definition demo_safe : SafeProgram := certify demo_compiled.

Declare ML Module "fido.emit".
Fido Emit (render_program demo_safe) To "/workspace/e2e-out".
