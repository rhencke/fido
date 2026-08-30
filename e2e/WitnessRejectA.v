(* WitnessReject chunk A: one cost-balanced slice of the fixture matrix over the shared prelude *)

From Stdlib Require Import List NArith ZArith String.
From Fido Require Import Integer Float Collections FilePath ModulePath Version Names Syntax Index Compilable Compilable.PackageIdentity Compilable.Bindings Compilable.Analysis Compilable.Report Render Emit.
From Fido Require Import WitnessRejectPrelude.
Import ListNotations.

Definition r_neg_bool    : Compilable.rejects (prog [ PL [ NEG TT ] ]).                                 Proof. reject. Qed.

Definition r_neg_int8min : Compilable.rejects (prog [ PL [ NEG (CONV Names.PInt8 (NEG (ILIT 128))) ] ]). Proof. reject. Qed.

Definition r_cx_str  : Compilable.rejects (prog [ PL [ CPLX (ILIT 1) (SLIT "x") ] ]).                   Proof. reject. Qed.

Definition r_stmt_lit  : Compilable.rejects (prog [ Syntax.ExprStmt (ILIT 1) ]).                   Proof. reject. Qed.

(* an invalid conversion as a statement reports the arity once: the dependent illegal-statement is not duplicated *)
Definition r_stmt_conv0 : Compilable.rejects (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PInt8) []) ]). Proof. reject. Qed.

(* an unmodelled builtin application is a boundary (OutsideScope), not an illegal statement *)
Definition o_print : Compilable.outsides (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrint) [ILIT 1]) ]). Proof. outside. Qed.

Definition c_neg_untyped : Compilable.compiles (prog [ PL [ NEG (ILIT 1) ] ]).                   Proof. compileok. Qed.

(* a builtin used as a bare value (not called) is invalid Go — builtins are not first-class values *)
Definition r_append_val : Compilable.rejects (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PAppend) ] ]). Proof. reject. Qed.

Definition r_short_self : Compilable.rejects (prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "x"))) (NE1 (VNAME "x")) ]). Proof. reject. Qed.

Definition r_var_true : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarTypeOnly (Syntax.NamedType (Names.predeclared_ordinary Names.PTrue))) ]) ]). Proof. reject. Qed.

(* §16 RHS-negative and ambiguous are Fido-only rejections; the differential short cases are dp_short_* below *)
Definition r_short_rhsneg : Compilable.rejects (prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "x"))) (NE1 (VNAME "z")) ]). Proof. reject. Qed.

Definition d4_invalid_unsupported_coexist :
  map AN.issue_class (AN.result_issues (rres p_invalid_unsupported))
  = [ AN.ClassDiagnostic ; AN.ClassBoundary ].
Proof. obs_issue_classes p_invalid_unsupported. Qed.

Definition dr_neg_string  : Compilable.rejects dp_neg_string.  Proof. reject. Qed.

Definition dr_uint8_neg   : Compilable.rejects dp_uint8_neg.   Proof. reject. Qed.

Definition dr_type_value  : Compilable.rejects dp_type_value.  Proof. reject. Qed.
