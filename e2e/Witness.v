(* The canonical witness: every admitted primitive, materialized pristine and validated by pinned Go. *)
From Stdlib Require Import List NArith ZArith String Ascii.
From Fido Require Import Integer Float Complex FilePath ModulePath Version Names Syntax Compilable Render Emit.
Import ListNotations.

(* control-byte strings built by exact ascii code, each between two letters *)
Definition s_tab : string := String "a"%char (String (ascii_of_nat 9)  (String "b"%char EmptyString)).
Definition s_cr  : string := String "a"%char (String (ascii_of_nat 13) (String "b"%char EmptyString)).
Definition s_nl  : string := String "a"%char (String (ascii_of_nat 10) (String "b"%char EmptyString)).

(* nonnegative magnitude literals; a negative source value is one unary-minus over its magnitude *)
Definition nnd_1p5  : Float.NonNegativeDecimal := Float.MakeNonNegDecimal (Float.MakeDecimal 15 (-1) eq_refl) eq_refl.
Definition nnd_0p5  : Float.NonNegativeDecimal := Float.MakeNonNegDecimal (Float.MakeDecimal 5 (-1) eq_refl) eq_refl.
Definition nnd_3    : Float.NonNegativeDecimal := Float.MakeNonNegDecimal (Float.MakeDecimal 3 0 eq_refl) eq_refl.
Definition nnd_2p5  : Float.NonNegativeDecimal := Float.MakeNonNegDecimal (Float.MakeDecimal 25 (-1) eq_refl) eq_refl.
Definition nnd_scar : Float.NonNegativeDecimal := Float.MakeNonNegDecimal (Float.MakeDecimal 2305843146652647425 0 eq_refl) eq_refl.
Definition nnd_tiny : Float.NonNegativeDecimal := Float.MakeNonNegDecimal (Float.MakeDecimal 1 (-330) eq_refl) eq_refl.
Definition nnd_0    : Float.NonNegativeDecimal := Float.MakeNonNegDecimal (Float.MakeDecimal 0 0 eq_refl) eq_refl.

Local Notation PL args := (Syntax.ExprStmt (Syntax.Application (Syntax.Name (Names.predeclared_ordinary Names.PPrintln)) args)).
Local Notation CONV t e := (Syntax.Application (Syntax.Name (Names.predeclared_ordinary t)) [e]).
Local Notation ILIT n := (Syntax.LiteralExpr (Syntax.IntegerLiteral n)).
Local Notation NEG e := (Syntax.Unary Syntax.UnaryMinus e).
Local Notation SLIT s := (Syntax.LiteralExpr (Syntax.StringLiteral s)).
Local Notation FLIT d := (Syntax.LiteralExpr (Syntax.FloatLiteral d)).
Local Notation CPLX re im := (Syntax.Application (Syntax.Name (Names.predeclared_ordinary Names.PComplex)) [re; im]).
Local Notation TT := (Syntax.Name (Names.predeclared_ordinary Names.PTrue)).
Local Notation FF := (Syntax.Name (Names.predeclared_ordinary Names.PFalse)).

Definition demo_file : list Syntax.TopLevelDecl :=
  [ Syntax.Main (Syntax.MakeBlock
    [ PL [ TT; ILIT 42; NEG (ILIT 1); NEG (ILIT ((2 ^ 63)%N)) ]
    ; PL []
    ; PL [ FF ]
    ; PL [ SLIT "hello, world" ]
    ; PL [ SLIT EmptyString ]
    ; PL [ TT; ILIT 7; SLIT "mix" ]
    ; PL [ SLIT (String (ascii_of_nat 34) EmptyString) ]
    ; PL [ SLIT (String (ascii_of_nat 92) EmptyString) ]
    ; PL [ SLIT s_tab ]
    ; PL [ SLIT s_cr ]
    ; PL [ SLIT s_nl ]
    ; PL [ CONV Names.PInt8  (NEG (ILIT 128)); CONV Names.PInt8  (ILIT 127) ]
    ; PL [ CONV Names.PInt16 (NEG (ILIT 32768)); CONV Names.PInt16 (ILIT 32767) ]
    ; PL [ CONV Names.PInt32 (NEG (ILIT 2147483648)); CONV Names.PInt32 (ILIT 2147483647) ]
    ; PL [ CONV Names.PInt64 (NEG (ILIT ((2 ^ 63)%N))); CONV Names.PInt64 (ILIT ((2 ^ 63 - 1)%N)) ]
    ; PL [ CONV Names.PInt   (NEG (ILIT ((2 ^ 63)%N))); CONV Names.PInt   (ILIT ((2 ^ 63 - 1)%N)) ]
    ; PL [ CONV Names.PUint8 (ILIT 255); CONV Names.PUint16 (ILIT 65535); CONV Names.PUint32 (ILIT 4294967295) ]
    ; PL [ CONV Names.PUint64 (ILIT ((2 ^ 63)%N)); CONV Names.PUint64 (ILIT 18446744073709551615) ]
    ; PL [ CONV Names.PUint (ILIT 18446744073709551615) ]
    ; PL [ CONV Names.PInt8 (CONV Names.PInt16 (ILIT 127)) ]
    ; PL [ FLIT nnd_1p5; CONV Names.PFloat32 (FLIT nnd_1p5) ]
    ; PL [ CONV Names.PFloat64 (FLIT nnd_0p5) ]
    ; PL [ CONV Names.PInt (FLIT nnd_3) ]
    ; PL [ CONV Names.PFloat64 (ILIT 7) ]
    ; PL [ CONV Names.PUint64 (CONV Names.PFloat32 (FLIT nnd_scar)) ]
    ; PL [ CONV Names.PUint64 (CONV Names.PFloat32 (CONV Names.PFloat64 (FLIT nnd_scar))) ]
    ; PL [ CONV Names.PFloat64 (FLIT nnd_tiny) ]
    ; PL [ CPLX (FLIT nnd_1p5) (NEG (FLIT nnd_2p5)) ]
    ; PL [ CONV Names.PComplex64  (CPLX (FLIT nnd_1p5) (NEG (FLIT nnd_2p5))) ]
    ; PL [ CONV Names.PComplex128 (CPLX (FLIT nnd_1p5) (NEG (FLIT nnd_2p5))) ]
    ; PL [ CONV Names.PInt (CPLX (FLIT nnd_3) (FLIT nnd_0)) ]
    ; PL [ CONV Names.PFloat32 (CPLX (FLIT nnd_1p5) (FLIT nnd_0)) ]
    ; PL [ CONV Names.PUint64 (CONV Names.PComplex64 (CPLX (FLIT nnd_scar) (FLIT nnd_0))) ]
    ; PL [ CONV Names.PUint64 (CONV Names.PComplex64 (CONV Names.PComplex128 (CPLX (FLIT nnd_scar) (FLIT nnd_0)))) ]
    ; PL [ CONV Names.PComplex64 (ILIT 1); CONV Names.PComplex128 (ILIT 1) ]
    ; PL [ CONV Names.PComplex64 (FLIT nnd_1p5); CONV Names.PComplex128 (FLIT nnd_1p5) ]
    ; PL [ CONV Names.PComplex64 (CONV Names.PComplex64 (CPLX (FLIT nnd_1p5) (NEG (FLIT nnd_2p5)))) ] ]) ].

Definition demo_module : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Go1_23.
Definition main_go : FilePath.T := FilePath.Make "main.go" eq_refl.
Definition demo_program : Syntax.Program := singleton_program demo_module main_go demo_file.

(* the compiled capability, from compile directly: for this concrete program disposition reduces to Compiled *)
Definition demo_prog : Compilable.Program demo_program :=
  Compilable.compiled_program demo_program (ltac:(rewrite Compilable.disposition_observe_data; vm_compute; reflexivity)).
Definition demo_image : Emit.Image demo_prog Emit.CompiledOnly tt := Emit.of_compiled demo_prog.

Declare ML Module "fido.emit".
Fido Materialize demo_image To "/workspace/generated".
(* the witness materializes only, and never publishes *)
