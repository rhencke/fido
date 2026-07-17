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
    64-bit boundaries, platform int/uint, uint64(2^63), and a nested int8(int16(127))), AND a readable
    FLOAT section — a bare default-float64 constant with its float32 conversion, an explicit float64, an
    exact float->int constant, an int->float constant, ★the direct-vs-nested double-rounding scar as an
    EXACT uint64 integer observation (uint64(float32(big)) vs uint64(float32(float64(big))), whose printed
    decimals differ), and an underflow to +0, AND a readable COMPLEX section — a bare complex128-default
    literal `complex(1.5, -2.5)`, its complex64/complex128 conversions, a zero-imaginary complex->int, a
    zero-imaginary complex->float32, and ★the component double-round scar as an EXACT uint64 observation
    through a zero-imaginary complex->uint64 (direct complex64 vs nested complex128-then-complex64).  The
    pinned Go toolchain accepts every one and prints its exact value (floats in Go's runtime %e format,
    complex as `(real+imagi)`, integration evidence only); the corresponding out-of-range / non-integer /
    nonzero-imaginary / wrong-type conversions are rejected by hand-written differential fixtures (Dockerfile
    go-e2e), exactly as GoTypes/GoCompile make impossible.  The rendered tree includes the certified [go.mod]
    (from the module spec) alongside the .go files. *)
From Stdlib Require Import List NArith ZArith String Ascii.
From Fido Require Import Ints Floats Complexes FilePath FMap ModulePath GoVersion GoAST GoCompile GoSafe GoRender GoEmit.
Import ListNotations.

(* control-byte strings built by exact ascii code (0x09 TAB, 0x0d CR, 0x0a NL) between two letters. *)
Definition s_tab : string := String "a"%char (String (ascii_of_nat 9)  (String "b"%char EmptyString)).
Definition s_cr  : string := String "a"%char (String (ascii_of_nat 13) (String "b"%char EmptyString)).
Definition s_nl  : string := String "a"%char (String (ascii_of_nat 10) (String "b"%char EmptyString)).

(* the readable float literals (§40) — DecimalFloat carries exact Z coefficient/exponent, so build under
   Z_scope; the rest of the witness uses N integer literals. *)
Definition dm_1p5  : DecimalFloat := mkDecimal 15 (-1) eq_refl.                    (* 1.5  -> 15.0e-1  *)
Definition dm_0p5  : DecimalFloat := mkDecimal 5 (-1) eq_refl.                     (* 0.5  -> 5.0e-1   *)
Definition dm_3    : DecimalFloat := mkDecimal 3 0 eq_refl.                        (* 3.0  -> 3.0e+0   *)
Definition dm_scar : DecimalFloat := mkDecimal 2305843146652647425 0 eq_refl.      (* 2^61+2^37+1      *)
Definition dm_tiny : DecimalFloat := mkDecimal 1 (-330) eq_refl.                   (* 1e-330 (underflow)*)
Definition dm_m2p5 : DecimalFloat := mkDecimal (-25) (-1) eq_refl.                 (* -2.5 -> -25.0e-1 *)
Definition dm_0    : DecimalFloat := mkDecimal 0 0 eq_refl.                        (* 0.0              *)

(* the readable complex literals (§51/§52): exact PAIRS of DecimalFloat components. *)
Definition dc_1p5_m2p5 : DecimalComplex := mkDC dm_1p5 dm_m2p5.   (* complex(1.5, -2.5) *)
Definition dc_1p5_0    : DecimalComplex := mkDC dm_1p5 dm_0.      (* complex(1.5, 0.0)  *)
Definition dc_3_0      : DecimalComplex := mkDC dm_3 dm_0.        (* complex(3.0, 0.0)  *)
Definition dc_scar_0   : DecimalComplex := mkDC dm_scar dm_0.     (* complex(scar, 0.0) *)

Definition demo_file (*decls*) : list GoDecl :=
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
          ; SPrintln [ EIntConvert IInt8 (EIntConvert IInt16 (EInt 127)) ]
          (* floats (§40): a bare default-float64 constant + its float32 conversion; explicit float64; an
             exact float->int constant; an int->float constant; ★the direct-vs-nested double-round scar as an
             EXACT uint64 integer observation (2^61+2^38 vs 2^61); and an underflow to +0. *)
          ; SPrintln [ EFloat dm_1p5; EFloatConvert F32 (EFloat dm_1p5) ]
          ; SPrintln [ EFloatConvert F64 (EFloat dm_0p5) ]
          ; SPrintln [ EIntConvert IInt (EFloat dm_3) ]
          ; SPrintln [ EFloatConvert F64 (EInt 7) ]
          ; SPrintln [ EIntConvert IUint64 (EFloatConvert F32 (EFloat dm_scar)) ]
          ; SPrintln [ EIntConvert IUint64 (EFloatConvert F32 (EFloatConvert F64 (EFloat dm_scar))) ]
          ; SPrintln [ EFloatConvert F64 (EFloat dm_tiny) ]
          (* complex (§51/§52): a bare complex128-default literal; its complex64/complex128 conversions; a
             zero-imaginary complex->int; a zero-imaginary complex->float32; and ★the component double-round
             scar via a zero-imaginary complex->uint64 (direct F32 vs nested F64-then-F32, decimals differ). *)
          ; SPrintln [ EComplex dc_1p5_m2p5 ]
          ; SPrintln [ EComplexConvert C64  (EComplex dc_1p5_m2p5) ]
          ; SPrintln [ EComplexConvert C128 (EComplex dc_1p5_m2p5) ]
          ; SPrintln [ EIntConvert IInt (EComplex dc_3_0) ]
          ; SPrintln [ EFloatConvert F32 (EComplex dc_1p5_0) ]
          ; SPrintln [ EIntConvert IUint64 (EComplexConvert C64 (EComplex dc_scar_0)) ]
          ; SPrintln [ EIntConvert IUint64 (EComplexConvert C64 (EComplexConvert C128 (EComplex dc_scar_0))) ]
          (* §53 remaining acceptance cases: integer -> complex64/complex128, float -> complex64/complex128,
             and a same-type nested complex conversion (all accepted by pinned Go). *)
          ; SPrintln [ EComplexConvert C64 (EInt 1); EComplexConvert C128 (EInt 1) ]
          ; SPrintln [ EComplexConvert C64 (EFloat dm_1p5); EComplexConvert C128 (EFloat dm_1p5) ]
          ; SPrintln [ EComplexConvert C64 (EComplexConvert C64 (EComplex dc_1p5_m2p5)) ] ] ].

Definition demo_module : ModuleSpec := mkModuleSpec (mkMP "fido.local/generated" eq_refl) Go1_23.
Definition main_go : FilePath := mkFP "main.go" eq_refl.
Definition demo_program : GoProgram := singleton_program demo_module main_go demo_file.

Lemma demo_valid : ProgValid demo_program.
Proof. apply prog_ok_iff. reflexivity. Qed.

Definition demo_compiled : CompilableProgram :=
  mkCompilable demo_program demo_valid.
Definition demo_safe : SafeProgram := certify demo_compiled.

Declare ML Module "fido.emit".
Fido Emit (render_program demo_safe) To "/workspace/e2e-out".
