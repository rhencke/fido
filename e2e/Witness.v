(** The e2e witness of the ONE validate-before-publish workflow — [Fido Materialize] (the sole Rocq transport
    vernac) writes the authoritative pristine image, which the go-e2e stage then validates with a fresh
    `go build ./...`.  The witness does NOT publish: there is no public [Fido Emit]; the sink is internal
    (exercised by sink_test, reached in production only through the validated `make regenerate`, which sinks
    the SAME validated pristine bytes).  No witness-specific executable, no extraction.  A proved [Safe.Program]
    is rendered to a [Emit.Image] via
    [Emit.of_safe], so its provenance proof is CLOSED (assumption-free); the command typechecks the
    image and finds its assumption closure empty (even though it descends the Qed lemma [demo_valid]),
    then decodes only the final (go.mod bytes, entries) transport and synchronizes the tree.  A candidate that is not
    compile-admissible has no [Safe.Program] and so cannot even be built into an image.

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
    go-e2e), exactly as Typing/Admissible make impossible.  The rendered tree includes the certified [go.mod]
    (from the module spec) alongside the .go files. *)
From Stdlib Require Import List NArith ZArith String Ascii.
From Fido Require Import Integer Float Complex FilePath ModulePath Version Syntax Compilable Safe Render Emit.
Import ListNotations.

(* control-byte strings built by exact ascii code (0x09 TAB, 0x0d CR, 0x0a NL) between two letters. *)
Definition s_tab : string := String "a"%char (String (ascii_of_nat 9)  (String "b"%char EmptyString)).
Definition s_cr  : string := String "a"%char (String (ascii_of_nat 13) (String "b"%char EmptyString)).
Definition s_nl  : string := String "a"%char (String (ascii_of_nat 10) (String "b"%char EmptyString)).

(* the readable float literals — Float.Decimal carries exact Z coefficient/exponent, so build under
   Z_scope; the rest of the witness uses N integer literals. *)
Definition decimal_1p5  : Float.Decimal := Float.MakeDecimal 15 (-1) eq_refl.                    (* 1.5  -> 15.0e-1  *)
Definition decimal_0p5  : Float.Decimal := Float.MakeDecimal 5 (-1) eq_refl.                     (* 0.5  -> 5.0e-1   *)
Definition decimal_3    : Float.Decimal := Float.MakeDecimal 3 0 eq_refl.                        (* 3.0  -> 3.0e+0   *)
Definition decimal_single_rounding : Float.Decimal := Float.MakeDecimal 2305843146652647425 0 eq_refl.      (* 2^61+2^37+1      *)
Definition decimal_tiny : Float.Decimal := Float.MakeDecimal 1 (-330) eq_refl.                   (* 1e-330 (underflow)*)
Definition decimal_m2p5 : Float.Decimal := Float.MakeDecimal (-25) (-1) eq_refl.                 (* -2.5 -> -25.0e-1 *)
Definition decimal_0    : Float.Decimal := Float.MakeDecimal 0 0 eq_refl.                        (* 0.0              *)

(* the readable complex literals: exact PAIRS of Float.Decimal components. *)
Definition decimal_complex_1p5_m2p5 : Complex.Decimal := Complex.MakeDecimal decimal_1p5 decimal_m2p5.   (* complex(1.5, -2.5) *)
Definition decimal_complex_1p5_0    : Complex.Decimal := Complex.MakeDecimal decimal_1p5 decimal_0.      (* complex(1.5, 0.0)  *)
Definition decimal_complex_3_0      : Complex.Decimal := Complex.MakeDecimal decimal_3 decimal_0.        (* complex(3.0, 0.0)  *)
Definition decimal_complex_single_rounding_0   : Complex.Decimal := Complex.MakeDecimal decimal_single_rounding decimal_0.     (* complex(scar, 0.0) *)

Definition demo_file (*decls*) : list Syntax.Decl :=
  [ Syntax.Main [ Syntax.Println [ Syntax.BoolLiteral true; Syntax.IntegerLiteral 42; Syntax.NegatedIntegerLiteral 1; Syntax.NegatedIntegerLiteral ((2 ^ 63)%N) ]
          ; Syntax.Println []
          ; Syntax.Println [ Syntax.BoolLiteral false ]
          ; Syntax.Println [ Syntax.StringLiteral "hello, world" ]
          ; Syntax.Println [ Syntax.StringLiteral EmptyString ]
          ; Syntax.Println [ Syntax.BoolLiteral true; Syntax.IntegerLiteral 7; Syntax.StringLiteral "mix" ]
          ; Syntax.Println [ Syntax.StringLiteral (String (ascii_of_nat 34) EmptyString) ]   (* a lone double-quote *)
          ; Syntax.Println [ Syntax.StringLiteral (String (ascii_of_nat 92) EmptyString) ]   (* a lone backslash *)
          ; Syntax.Println [ Syntax.StringLiteral s_tab ]
          ; Syntax.Println [ Syntax.StringLiteral s_cr ]
          ; Syntax.Println [ Syntax.StringLiteral s_nl ]
          (* accepted integer conversions across all ten integer types: signed narrow + 64-bit
             minima/maxima, unsigned maxima, platform int/uint, uint64(2^63), and a nested conversion. *)
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int8)  (Syntax.NegatedIntegerLiteral 128); Syntax.Convert (Syntax.type_expr_of_name Names.Int8)  (Syntax.IntegerLiteral 127) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.NegatedIntegerLiteral 32768); Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.IntegerLiteral 32767) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int32) (Syntax.NegatedIntegerLiteral 2147483648); Syntax.Convert (Syntax.type_expr_of_name Names.Int32) (Syntax.IntegerLiteral 2147483647) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int64) (Syntax.NegatedIntegerLiteral ((2 ^ 63)%N)); Syntax.Convert (Syntax.type_expr_of_name Names.Int64) (Syntax.IntegerLiteral ((2 ^ 63 - 1)%N)) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int)   (Syntax.NegatedIntegerLiteral ((2 ^ 63)%N)); Syntax.Convert (Syntax.type_expr_of_name Names.Int)   (Syntax.IntegerLiteral ((2 ^ 63 - 1)%N)) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Uint8) (Syntax.IntegerLiteral 255); Syntax.Convert (Syntax.type_expr_of_name Names.Uint16) (Syntax.IntegerLiteral 65535)
                     ; Syntax.Convert (Syntax.type_expr_of_name Names.Uint32) (Syntax.IntegerLiteral 4294967295) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.IntegerLiteral ((2 ^ 63)%N)); Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.IntegerLiteral 18446744073709551615) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Uint) (Syntax.IntegerLiteral 18446744073709551615) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.IntegerLiteral 127)) ]
          (* floats: a bare default-float64 constant + its float32 conversion; explicit float64; an
             exact float->int constant; an int->float constant; ★the direct-vs-nested double-round scar as an
             EXACT uint64 integer observation (2^61+2^38 vs 2^61); and an underflow to +0. *)
          ; Syntax.Println [ Syntax.FloatLiteral decimal_1p5; Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.FloatLiteral decimal_1p5) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Float64) (Syntax.FloatLiteral decimal_0p5) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int) (Syntax.FloatLiteral decimal_3) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Float64) (Syntax.IntegerLiteral 7) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.FloatLiteral decimal_single_rounding)) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.Convert (Syntax.type_expr_of_name Names.Float64) (Syntax.FloatLiteral decimal_single_rounding))) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Float64) (Syntax.FloatLiteral decimal_tiny) ]
          (* complex: a bare complex128-default literal; its complex64/complex128 conversions; a
             zero-imaginary complex->int; a zero-imaginary complex->float32; and ★the component double-round
             scar via a zero-imaginary complex->uint64 (direct F32 vs nested F64-then-F32, decimals differ). *)
          ; Syntax.Println [ Syntax.ComplexLiteral Typing.decimal_complex_1p5_m2p5 ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Complex64)  (Syntax.ComplexLiteral Typing.decimal_complex_1p5_m2p5) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Complex128) (Syntax.ComplexLiteral Typing.decimal_complex_1p5_m2p5) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int) (Syntax.ComplexLiteral decimal_complex_3_0) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.ComplexLiteral decimal_complex_1p5_0) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.ComplexLiteral decimal_complex_single_rounding_0)) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.Convert (Syntax.type_expr_of_name Names.Complex128) (Syntax.ComplexLiteral decimal_complex_single_rounding_0))) ]
          (* remaining acceptance cases: integer -> complex64/complex128, float -> complex64/complex128,
             and a same-type nested complex conversion (all accepted by pinned Go). *)
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.IntegerLiteral 1); Syntax.Convert (Syntax.type_expr_of_name Names.Complex128) (Syntax.IntegerLiteral 1) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.FloatLiteral decimal_1p5); Syntax.Convert (Syntax.type_expr_of_name Names.Complex128) (Syntax.FloatLiteral decimal_1p5) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.ComplexLiteral Typing.decimal_complex_1p5_m2p5)) ] ] ].

Definition demo_module : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Go1_23.
Definition main_go : FilePath.T := FilePath.Make "main.go" eq_refl.
Definition demo_program : Syntax.Program := singleton_program demo_module main_go demo_file.

Lemma demo_valid : Admissible demo_program.
Proof. apply Compilable.admissible_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

Definition demo_compiled : Compilable.Program :=
  Compilable.capability_of_admissible demo_program demo_valid.

(* the compilation artifact IS obtained from the successful elaboration (the accepted decision, via Compilable.compile). *)
Example demo_compiles : exists cp Hcp, Compilable.compile demo_program = Compilable.Compiled cp Hcp.
Proof. exact (Compilable.compile_complete demo_program demo_valid). Qed.
Definition demo_safe : Safe.Program := certify demo_compiled.

(* the image, formed from the source the capability was minted for: [capability_source] is the proof
   that this IS the certificate's own source, so the emitted bytes are the compiler-accepted program's
   and the transport never has to force the elaboration to rediscover a program it already has. *)
Definition demo_image : Emit.Image :=
  Emit.of_safe_at demo_safe demo_program (Compilable.capability_source demo_program demo_valid).

Declare ML Module "fido.emit".
(* AUTHORITATIVE pristine materialization (the pre-build image the pinned `go build ./...` validates and the
   committed canonical artifact is copied from) — written DIRECTLY from the decoded image, never from a sink
   directory. *)
Fido Materialize demo_image To "/workspace/generated".
(* the witness ONLY materializes the authoritative pristine image (which the go-e2e stage then validates
   with a fresh `go build ./...`).  It does NOT sink/publish: there is no public `Fido Emit` command, and the
   sink is exercised separately (e2e/sink_test.ml) and reached in production only through the validated
   `make regenerate` workflow, which sinks the SAME validated pristine bytes. *)
