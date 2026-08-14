(* rejection controls: compile Rejects the §9.3 invalid-program matrix and Compiles the paired positive cases *)
From Stdlib Require Import List NArith ZArith String.
From Fido Require Import Integer Float FilePath ModulePath Version Names Syntax Compilable.
Import ListNotations.

Local Notation PL args := (Syntax.ExprStmt (Syntax.Application (Syntax.Name (Names.predeclared_ordinary Names.PPrintln)) args)).
Local Notation NEG e := (Syntax.Unary Syntax.UnaryMinus e).
Local Notation ILIT n := (Syntax.LiteralExpr (Syntax.IntegerLiteral n)).
Local Notation SLIT s := (Syntax.LiteralExpr (Syntax.StringLiteral s)).
Local Notation CONV t e := (Syntax.Application (Syntax.Name (Names.predeclared_ordinary t)) [e]).
Local Notation CPLX re im := (Syntax.Application (Syntax.Name (Names.predeclared_ordinary Names.PComplex)) [re; im]).
Local Notation APP h args := (Syntax.Application (Syntax.Name h) args).
Local Notation TT := (Syntax.Name (Names.predeclared_ordinary Names.PTrue)).
Local Notation FF := (Syntax.Name (Names.predeclared_ordinary Names.PFalse)).

Definition rmod : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Go1_23.
Definition rmain : FilePath.T := FilePath.Make "main.go" eq_refl.
Definition prog (body : list Syntax.Stmt) : Syntax.Program :=
  singleton_program rmod rmain [ Syntax.Main (Syntax.MakeBlock body) ].

Ltac reject    := apply Compilable.rejects_of_diags; vm_compute; discriminate.
Ltac compileok := apply Compilable.compiles_of_admissible; split; vm_compute; reflexivity.
Ltac outside   := apply Compilable.outsides_of_boundaries; [ vm_compute; reflexivity | vm_compute; discriminate ].

(* known type mismatches: unary minus over a nonnumeric or overflowing typed constant *)
Definition r_neg_string  : Compilable.rejects (prog [ PL [ NEG (SLIT "x") ] ]).                         Proof. reject. Qed.
Definition r_neg_bool    : Compilable.rejects (prog [ PL [ NEG TT ] ]).                                 Proof. reject. Qed.
Definition r_neg_uint8   : Compilable.rejects (prog [ PL [ NEG (CONV Names.PUint8 (ILIT 1)) ] ]).        Proof. reject. Qed.
Definition r_neg_int8min : Compilable.rejects (prog [ PL [ NEG (CONV Names.PInt8 (NEG (ILIT 128))) ] ]). Proof. reject. Qed.

(* known complex component errors: nonnumeric, string, typed-int, or mismatched-typed-float components *)
Definition r_cx_bool : Compilable.rejects (prog [ PL [ CPLX TT FF ] ]).                                 Proof. reject. Qed.
Definition r_cx_str  : Compilable.rejects (prog [ PL [ CPLX (ILIT 1) (SLIT "x") ] ]).                   Proof. reject. Qed.
Definition r_cx_int8 : Compilable.rejects (prog [ PL [ CPLX (CONV Names.PInt8 (ILIT 1)) (CONV Names.PInt8 (ILIT 2)) ] ]). Proof. reject. Qed.
Definition r_cx_mix  : Compilable.rejects (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat64 (ILIT 2)) ] ]). Proof. reject. Qed.

(* wrong arity: conversions take exactly one argument, the complex builtin exactly two *)
Definition r_conv0 : Compilable.rejects (prog [ PL [ APP (Names.predeclared_ordinary Names.PInt8) [] ] ]).              Proof. reject. Qed.
Definition r_conv2 : Compilable.rejects (prog [ PL [ APP (Names.predeclared_ordinary Names.PInt8) [ILIT 1; ILIT 2] ] ]). Proof. reject. Qed.
Definition r_cx1   : Compilable.rejects (prog [ PL [ APP (Names.predeclared_ordinary Names.PComplex) [ILIT 1] ] ]).   Proof. reject. Qed.
Definition r_cx3   : Compilable.rejects (prog [ PL [ APP (Names.predeclared_ordinary Names.PComplex) [ILIT 1; ILIT 2; ILIT 3] ] ]). Proof. reject. Qed.

(* no-value used as a value; a type used as a value; a non-function called *)
Definition r_println_val : Compilable.rejects (prog [ PL [ APP (Names.predeclared_ordinary Names.PPrintln) [] ] ]).  Proof. reject. Qed.
Definition r_type_value  : Compilable.rejects (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PInt8) ] ]).   Proof. reject. Qed.
Definition r_call_bool   : Compilable.rejects (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PTrue) []) ]). Proof. reject. Qed.
Definition r_call_lit    : Compilable.rejects (prog [ Syntax.ExprStmt (Syntax.Application (ILIT 1) []) ]).           Proof. reject. Qed.

(* illegal expression statements: a conversion or a bare literal cannot be a statement *)
Definition r_stmt_conv : Compilable.rejects (prog [ Syntax.ExprStmt (CONV Names.PInt8 (ILIT 1)) ]). Proof. reject. Qed.
Definition r_stmt_lit  : Compilable.rejects (prog [ Syntax.ExprStmt (ILIT 1) ]).                   Proof. reject. Qed.

(* positive controls: the same forms compile when the operand facts satisfy the rule *)
Definition c_neg_int8    : Compilable.compiles (prog [ PL [ NEG (CONV Names.PInt8 (ILIT 1)) ] ]). Proof. compileok. Qed.
Definition c_neg_untyped : Compilable.compiles (prog [ PL [ NEG (ILIT 1) ] ]).                   Proof. compileok. Qed.
Definition c_neg_complex : Compilable.compiles (prog [ PL [ NEG (CPLX (ILIT 1) (ILIT 2)) ] ]).    Proof. compileok. Qed.

(* a typed complex is valid Go but outside the implemented scope: not Compiled, not Rejected, but OutsideScope *)
Definition o_cx_typed : Compilable.outsides (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat32 (ILIT 2)) ] ]). Proof. outside. Qed.

(* iota and nil are known predeclared identities with no valid use in the active domain: definite invalidity *)
Definition r_iota : Compilable.rejects (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ] ]). Proof. reject. Qed.
Definition r_nil  : Compilable.rejects (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PNil) ] ]).  Proof. reject. Qed.
