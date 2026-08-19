(* controls: representable invalid/unimplemented cases Reject or bound; the paired positive cases Compile *)
From Stdlib Require Import List NArith ZArith String.
From Fido Require Import Integer Float Collections FilePath ModulePath Version Names Syntax Index Compilable Compilable.PackageIdentity Compilable.Bindings Compilable.Analysis Compilable.Report.
Import ListNotations.

Module PI := Compilable.PackageIdentity.
Module BN := Compilable.Bindings.
Module AN := Compilable.Analysis.
Module RP := Compilable.Report.

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

(* each branch is decided through the production authority: the transparent [disposition], reduced by computation *)
Ltac reject    := vm_compute; reflexivity.
Ltac compileok := vm_compute; reflexivity.
Ltac outside   := vm_compute; reflexivity.

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
(* a non-Name application head (a unary expression) is not callable: the exact head ref, never an invented nil *)
Definition r_call_neg    : Compilable.rejects (prog [ PL [ Syntax.Application (NEG (ILIT 1)) [] ] ]).                Proof. reject. Qed.

(* illegal expression statements: a conversion or a bare literal cannot be a statement *)
Definition r_stmt_conv : Compilable.rejects (prog [ Syntax.ExprStmt (CONV Names.PInt8 (ILIT 1)) ]). Proof. reject. Qed.
Definition r_stmt_lit  : Compilable.rejects (prog [ Syntax.ExprStmt (ILIT 1) ]).                   Proof. reject. Qed.
(* an invalid conversion as a statement reports the arity once: the dependent illegal-statement is not duplicated *)
Definition r_stmt_conv0 : Compilable.rejects (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PInt8) []) ]). Proof. reject. Qed.
(* an unmodelled builtin application is a boundary (OutsideScope), not an illegal statement *)
Definition o_print : Compilable.outsides (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrint) [ILIT 1]) ]). Proof. outside. Qed.

(* positive controls: the same forms compile when the operand facts satisfy the rule *)
Definition c_neg_int8    : Compilable.compiles (prog [ PL [ NEG (CONV Names.PInt8 (ILIT 1)) ] ]). Proof. compileok. Qed.
Definition c_neg_untyped : Compilable.compiles (prog [ PL [ NEG (ILIT 1) ] ]).                   Proof. compileok. Qed.
Definition c_neg_complex : Compilable.compiles (prog [ PL [ NEG (CPLX (ILIT 1) (ILIT 2)) ] ]).    Proof. compileok. Qed.

(* a typed complex is valid Go but outside the implemented scope: not Compiled, not Rejected, but OutsideScope *)
Definition o_cx_typed : Compilable.outsides (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat32 (ILIT 2)) ] ]). Proof. outside. Qed.

(* a bare integer literal that overflows the default int type is a definite default-overflow invalidity *)
Definition r_default_overflow : Compilable.rejects (prog [ PL [ ILIT ((2 ^ 63)%N) ] ]). Proof. reject. Qed.

(* iota and nil are known predeclared identities with no valid use in the active domain: definite invalidity *)
Definition r_iota : Compilable.rejects (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ] ]). Proof. reject. Qed.
Definition r_nil  : Compilable.rejects (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PNil) ] ]).  Proof. reject. Qed.

(* a builtin used as a bare value (not called) is invalid Go — builtins are not first-class values *)
Definition r_append_val : Compilable.rejects (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PAppend) ] ]). Proof. reject. Qed.

Local Notation OID s := (Names.MakeOrdinary (Names.MakeIdentifier s eq_refl) eq_refl).
Local Notation VNAME s := (Syntax.Name (OID s)).
Local Notation NE1 x := (Collections.MakeNonEmpty x nil).

(* visibility: a name is not visible inside its own spec, so a self-initializer is unresolved and Rejected *)
Definition r_var_self : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (VNAME "x"))) ]) ]). Proof. reject. Qed.
Definition r_const_self : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (VNAME "x"))) ]) ]). Proof. reject. Qed.
Definition r_short_self : Compilable.rejects (prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "x"))) (NE1 (VNAME "x")) ]). Proof. reject. Qed.

(* type uses: an unmodelled real type is a boundary; a value name used as a type is an exact invalidity *)
Definition o_var_uintptr : Compilable.outsides (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarTypeOnly (Syntax.NamedType (Names.predeclared_ordinary Names.PUintptr))) ]) ]). Proof. outside. Qed.
Definition r_var_true : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarTypeOnly (Syntax.NamedType (Names.predeclared_ordinary Names.PTrue))) ]) ]). Proof. reject. Qed.

(* visibility: a name IS visible after its spec, but a source value's meaning is a later root (OutsideScope) *)
Definition o_var_use : Compilable.outsides (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; PL [ VNAME "x" ] ]). Proof. outside. Qed.
Definition o_var_later : Compilable.outsides (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "a"))) (Syntax.VarValues None (NE1 (ILIT 1))) ; Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "b"))) (Syntax.VarValues None (NE1 (VNAME "a"))) ]) ]). Proof. outside. Qed.
Definition o_short_use : Compilable.outsides (prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "x"))) (NE1 (ILIT 1)) ; PL [ VNAME "x" ] ]). Proof. outside. Qed.
(* a short declaration does not compile merely because its later typing is absent: its meaning is a boundary *)
Definition o_short_new : Compilable.outsides (prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "x"))) (NE1 (ILIT 1)) ]). Proof. outside. Qed.
(* declaration invalidities: a first const spec omitting its initializer, a result-count mismatch, a short duplicate *)
Definition r_const_noinit : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) Syntax.InheritedConstInit ]) ]). Proof. reject. Qed.
Definition r_const_count : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (Collections.MakeNonEmpty (Syntax.BNamed (OID "x")) [Syntax.BNamed (OID "y")]) (Syntax.ExplicitConstInit None (NE1 (ILIT 1))) ]) ]). Proof. reject. Qed.
Definition r_short_dup : Compilable.rejects (prog [ Syntax.ShortVarDecl (Collections.MakeNonEmpty (Syntax.BNamed (OID "x")) [Syntax.BNamed (OID "x")]) (Collections.MakeNonEmpty (ILIT 1) [ILIT 2]) ]). Proof. reject. Qed.
(* a parent arity invalidity and an independent child requirement coexist: neither over-blocks the other *)
Definition r_complex_coexist : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; PL [ Syntax.Application (Syntax.Name (Names.predeclared_ordinary Names.PComplex)) [ VNAME "x" ] ] ]). Proof. reject. Qed.

(* the exact-payload catalogue: pin each cause / requirement of the one canonical Analysis issue table *)
Definition cbinds (p : Syntax.Program) := BN.bindings (PI.package_surface (Index.index_program p)).
Definition dcauses (p : Syntax.Program) :=
  map (AN.diag_cause (AN.facts (cbinds p)) (AN.package_facts (cbinds p)))
      (AN.diagnostics (AN.facts (cbinds p)) (AN.package_facts (cbinds p))).
Definition breqs (p : Syntax.Program) :=
  map (AN.bound_req (AN.facts (cbinds p)) (AN.package_facts (cbinds p)))
      (AN.boundaries (AN.facts (cbinds p)) (AN.package_facts (cbinds p))).
(* the boundary FACTS themselves; matching a fact's shape avoids the occ_req extraction that vm_computes a huge proof *)
Definition bfacts (p : Syntax.Program) :=
  map (AN.bound_fact (AN.facts (cbinds p)) (AN.package_facts (cbinds p)))
      (AN.boundaries (AN.facts (cbinds p)) (AN.package_facts (cbinds p))).
(* the diagnostic SITES; matching a site's shape avoids the diag_cause/group_cause extraction that blows up *)
Definition dsites (p : Syntax.Program) :=
  map (AN.diag_site (AN.facts (cbinds p)) (AN.package_facts (cbinds p)))
      (AN.diagnostics (AN.facts (cbinds p)) (AN.package_facts (cbinds p))).

Definition r_iota_cause :
  dcauses (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ] ]) = [ AN.OccCause (AN.InvalidIdentity Names.PIota) ].
Proof. vm_compute; reflexivity. Qed.
Definition r_type_value_cause :
  dcauses (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PInt8) ] ]) = [ AN.OccCause (AN.TypeAsValue (BN.PredeclaredObject Names.PInt8)) ].
Proof. vm_compute; reflexivity. Qed.
Definition r_cx_mix_cause : exists a b,
  dcauses (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat64 (ILIT 2)) ] ]) = [ AN.OccCause (AN.ComplexMismatch a b) ].
Proof. do 2 eexists; vm_compute; reflexivity. Qed.
Definition o_cx_typed_payload :
  dcauses (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat32 (ILIT 2)) ] ]) = []
  /\ exists r, breqs (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat32 (ILIT 2)) ] ]) = [ AN.ReqComplexType r ].
Proof. split; [ vm_compute; reflexivity | eexists; vm_compute; reflexivity ]. Qed.
Definition c_neg_int8_core :
  dcauses (prog [ PL [ NEG (CONV Names.PInt8 (ILIT 1)) ] ]) = [] /\ breqs (prog [ PL [ NEG (CONV Names.PInt8 (ILIT 1)) ] ]) = [].
Proof. split; vm_compute; reflexivity. Qed.

(* main-as-object: a use of the identifier main resolves to the package main function, or a shadowing local main *)
Definition o_main_recursive : Compilable.outsides (prog [ Syntax.ExprStmt (APP (OID "main") []) ]). Proof. outside. Qed.
Definition o_main_value : Compilable.outsides (prog [ PL [ VNAME "main" ] ]). Proof. outside. Qed.
Definition r_main_as_type : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarTypeOnly (Syntax.NamedType (OID "main"))) ]) ]). Proof. reject. Qed.
(* the recursive main call is the package main function object (a later-root boundary), never an unresolved name *)
Definition o_main_recursive_payload :
  (match bfacts (prog [ Syntax.ExprStmt (APP (OID "main") []) ]) with
   | [ AN.OFApp _ (AN.AUnmet (AN.ReqMainUse _)) ] => true | _ => false end) = true.
Proof. vm_compute; reflexivity. Qed.
(* a local main shadows the package main through the ordinary block rule *)
Definition o_main_shadowed : Compilable.outsides (prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "main"))) (NE1 (ILIT 1)) ; PL [ VNAME "main" ] ]). Proof. outside. Qed.

(* ordinary redeclaration: two var/const specs sharing one block scope and spelling is a redeclaration issue *)
Definition r_redecl_var : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ]). Proof. reject. Qed.
(* the one diagnostic is a group-redeclaration site over an establishment spelled "x" (cause OrdinaryRedeclared) *)
Definition r_redecl_payload :
  (match dsites (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ]) with
   | [ AN.AtGroup e ] => Names.ordinary_equalb (BN.est_name e) (OID "x")
   | _ => false
   end) = true.
Proof. vm_compute; reflexivity. Qed.

(* const inheritance: a non-first inherited const spec is valid Go outside the modelled scope (a boundary) *)
Definition o_const_inherited : Compilable.outsides (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (ILIT 1))) ; Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "y"))) Syntax.InheritedConstInit ]) ]). Proof. outside. Qed.

(* Rob's four fixed-main / declaration-group combinations: main participates in the ONE (scope, spelling) group *)
Definition prog_tops (tops : list Syntax.TopLevelDecl) : Syntax.Program := singleton_program rmod rmain tops.
Definition main0 : Syntax.TopLevelDecl := Syntax.Main (Syntax.MakeBlock []).
Definition tconstmain : Syntax.TopLevelDecl :=
  Syntax.TopDeclaration (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "main"))) (Syntax.ExplicitConstInit None (NE1 (ILIT 1))) ]).

(* (a) one fixed main, no competitor -> unique group + MainOne -> Compiled *)
Definition c_main_only : Compilable.compiles (prog_tops [ main0 ]). Proof. compileok. Qed.
(* (b) a fixed main plus a const main: a redeclared group, so main is an ordinary group member and it Rejects *)
Definition r_main_const_redecl : Compilable.rejects (prog_tops [ tconstmain ; main0 ]). Proof. reject. Qed.
Definition r_main_const_redecl_payload :
  (match dsites (prog_tops [ tconstmain ; main0 ]) with
   | [ AN.AtGroup e ] => Names.ordinary_equalb (BN.est_name e) (OID "main")
   | _ => false end) = true.
Proof. vm_compute; reflexivity. Qed.
(* (c) multiple fixed mains: a redeclared group through the one authority, no first-main pick, so Rejected *)
Definition r_main_multiple : Compilable.rejects (prog_tops [ main0 ; main0 ]). Proof. reject. Qed.
Definition r_main_multiple_payload :
  (match dsites (prog_tops [ main0 ; main0 ]) with
   | [ AN.AtGroup e ] => Names.ordinary_equalb (BN.est_name e) (OID "main")
   | _ => false end) = true.
Proof. vm_compute; reflexivity. Qed.
(* (d) no fixed main, an ordinary const main: MainMissing, so the missing-entry diagnostic Rejects *)
Definition r_main_missing : Compilable.rejects (prog_tops [ tconstmain ]). Proof. reject. Qed.
Definition r_main_missing_payload :
  (match dsites (prog_tops [ tconstmain ]) with
   | [ AN.AtPackage _ ] => true | _ => false end) = true.
Proof. vm_compute; reflexivity. Qed.
