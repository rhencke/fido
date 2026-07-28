(* The canonical witness: every admitted primitive, materialized pristine and validated by pinned Go. *)
From Stdlib Require Import List NArith ZArith String Ascii.
From Fido Require Import Integer Float Complex FilePath ModulePath Version Syntax Compilable Safe Render Emit.
Import ListNotations.

(* control-byte strings built by exact ascii code, each between two letters *)
Definition s_tab : string := String "a"%char (String (ascii_of_nat 9)  (String "b"%char EmptyString)).
Definition s_cr  : string := String "a"%char (String (ascii_of_nat 13) (String "b"%char EmptyString)).
Definition s_nl  : string := String "a"%char (String (ascii_of_nat 10) (String "b"%char EmptyString)).

(* these carry an exact Z coefficient and exponent, so they build under Z_scope *)
Definition decimal_1p5  : Float.Decimal := Float.MakeDecimal 15 (-1) eq_refl.                    (* 1.5  -> 15.0e-1  *)
Definition decimal_0p5  : Float.Decimal := Float.MakeDecimal 5 (-1) eq_refl.                     (* 0.5  -> 5.0e-1   *)
Definition decimal_3    : Float.Decimal := Float.MakeDecimal 3 0 eq_refl.                        (* 3.0  -> 3.0e+0   *)
Definition decimal_single_rounding : Float.Decimal := Float.MakeDecimal 2305843146652647425 0 eq_refl.      (* 2^61+2^37+1      *)
Definition decimal_tiny : Float.Decimal := Float.MakeDecimal 1 (-330) eq_refl.                   (* 1e-330 (underflow)*)
Definition decimal_m2p5 : Float.Decimal := Float.MakeDecimal (-25) (-1) eq_refl.                 (* -2.5 -> -25.0e-1 *)
Definition decimal_0    : Float.Decimal := Float.MakeDecimal 0 0 eq_refl.

(* the complex literals are exact pairs of the decimals above *)
Definition decimal_complex_1p5_m2p5 : Complex.Decimal := Complex.MakeDecimal decimal_1p5 decimal_m2p5.   (* complex(1.5, -2.5) *)
Definition decimal_complex_1p5_0    : Complex.Decimal := Complex.MakeDecimal decimal_1p5 decimal_0.      (* complex(1.5, 0.0)  *)
Definition decimal_complex_3_0      : Complex.Decimal := Complex.MakeDecimal decimal_3 decimal_0.        (* complex(3.0, 0.0)  *)
Definition decimal_complex_single_rounding_0   : Complex.Decimal := Complex.MakeDecimal decimal_single_rounding decimal_0.     (* complex(scar, 0.0) *)

Definition demo_file  : list Syntax.Decl :=
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
          (* accepted integer conversions across all ten integer types, at their boundaries *)
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
          (* floats, including the double-rounding scar as an exact uint64 observation *)
          ; Syntax.Println [ Syntax.FloatLiteral decimal_1p5; Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.FloatLiteral decimal_1p5) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Float64) (Syntax.FloatLiteral decimal_0p5) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int) (Syntax.FloatLiteral decimal_3) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Float64) (Syntax.IntegerLiteral 7) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.FloatLiteral decimal_single_rounding)) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.Convert (Syntax.type_expr_of_name Names.Float64) (Syntax.FloatLiteral decimal_single_rounding))) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Float64) (Syntax.FloatLiteral decimal_tiny) ]
          (* complex, including the same double rounding at the component level *)
          ; Syntax.Println [ Syntax.ComplexLiteral Typing.decimal_complex_1p5_m2p5 ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Complex64)  (Syntax.ComplexLiteral Typing.decimal_complex_1p5_m2p5) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Complex128) (Syntax.ComplexLiteral Typing.decimal_complex_1p5_m2p5) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Int) (Syntax.ComplexLiteral decimal_complex_3_0) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.ComplexLiteral decimal_complex_1p5_0) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.ComplexLiteral decimal_complex_single_rounding_0)) ]
          ; Syntax.Println [ Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.Convert (Syntax.type_expr_of_name Names.Complex128) (Syntax.ComplexLiteral decimal_complex_single_rounding_0))) ]
          (* the remaining acceptance cases, all accepted by pinned Go *)
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

(* the artifact comes from the successful elaboration, not from a second decision *)
Example demo_compiles : exists cp Hcp, Compilable.compile demo_program = Compilable.Compiled cp Hcp.
Proof. exact (Compilable.compile_complete demo_program demo_valid). Qed.
Definition demo_safe : Safe.Program := certify demo_compiled.

(* formed from the source the capability was minted for, so the transport forces no rediscovery *)
Definition demo_image : Emit.Image :=
  Emit.of_safe_at demo_safe demo_program (eq_trans (Safe.certify_source demo_compiled)
                          (Compilable.capability_source demo_program demo_valid)).

Declare ML Module "fido.emit".
Fido Materialize demo_image To "/workspace/generated".
(* the witness materializes only, and never publishes *)
