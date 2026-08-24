(* controls: representable invalid/unimplemented cases Reject or bound; the paired positive cases Compile *)
From Stdlib Require Import List NArith ZArith String.
From Fido Require Import Integer Float Collections FilePath ModulePath Version Names Syntax Index Compilable Compilable.PackageIdentity Compilable.Bindings Compilable.Analysis Compilable.Report Render Emit.
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

(* the one retained Result these fixtures read: compile's stored object via analyze, not a peer rebuild *)
Definition rres (p : Syntax.Program) : AN.Result p := AN.analyze p.
(* the diagnostic ROWS themselves; each row already retains its exact subject, family, and cause at construction *)
Definition dsites (p : Syntax.Program) := AN.result_diagnostics (rres p).
(* the raw occurrence facts of a program, for the dependent-non-result checks *)
Definition pfacts (p : Syntax.Program) := AN.fact_list (AN.res_facts (rres p)).

(* provenance: whatever branch a program yields, its projected result IS the exact Result these fixtures read *)
Definition retained_via_program  {p} (cp : Compilable.Program p)   : Compilable.program_result cp  = rres p := Compilable.program_result_canonical cp.
Definition retained_via_rejection {p} (r  : Compilable.Rejection p) : Compilable.rejection_result r = rres p := Compilable.rejection_result_canonical r.
Definition retained_via_outside   {p} (o  : Compilable.Outside p)   : Compilable.outside_result o  = rres p := Compilable.outside_result_canonical o.
(* substitution-resistance: a rejected program admits no capability, so no rebuilt Result can back one *)
Definition no_program_for_rejected (p : Syntax.Program) (cp : Compilable.Program p) (Hrej : Compilable.rejects p) : False.
Proof. unfold Compilable.rejects in Hrej. rewrite (Compilable.program_forces_compiled cp) in Hrej. discriminate. Qed.

(* payload catalogue via the bp-free Report views: goal types carry no BindingPhase, so vm_compute stays cheap *)
Definition r_iota_cause :
  RP.result_cause_views (rres (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ] ])) = [ RP.CvInvalidIdentity Names.PIota ].
Proof. vm_compute; reflexivity. Qed.
Definition r_type_value_cause :
  RP.result_cause_views (rres (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PInt8) ] ])) = [ RP.CvTypeAsValue (Some Names.PInt8) ].
Proof. vm_compute; reflexivity. Qed.
Definition r_cx_mix_cause :
  RP.result_cause_views (rres (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat64 (ILIT 2)) ] ])) = [ RP.CvComplexMismatch ].
Proof. vm_compute; reflexivity. Qed.
Definition o_cx_typed_payload :
  RP.result_cause_views (rres (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat32 (ILIT 2)) ] ])) = []
  /\ RP.result_req_views (rres (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat32 (ILIT 2)) ] ])) = [ RP.RvComplexType ].
Proof. split; vm_compute; reflexivity. Qed.
Definition c_neg_int8_core :
  RP.result_cause_views (rres (prog [ PL [ NEG (CONV Names.PInt8 (ILIT 1)) ] ])) = [] /\ RP.result_req_views (rres (prog [ PL [ NEG (CONV Names.PInt8 (ILIT 1)) ] ])) = [].
Proof. split; vm_compute; reflexivity. Qed.

(* the fixed main is a zero-parameter function: a zero-argument main() call succeeds as a known zero-result call *)
Definition c_main_recursive : Compilable.compiles (prog [ Syntax.ExprStmt (APP (OID "main") []) ]). Proof. compileok. Qed.
(* main used as a bare value (not called) is a later-root boundary *)
Definition o_main_value : Compilable.outsides (prog [ PL [ VNAME "main" ] ]). Proof. outside. Qed.
Definition r_main_as_type : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarTypeOnly (Syntax.NamedType (OID "main"))) ]) ]). Proof. reject. Qed.
(* main(1) is an exact arity invalidity: the fixed main takes zero arguments *)
Definition r_main_arity : Compilable.rejects (prog [ Syntax.ExprStmt (APP (OID "main") [ILIT 1]) ]). Proof. reject. Qed.
(* the invalidity is the exact application-family MainArity cause carrying the function head *)
Definition r_main_arity_payload :
  (match dsites (prog [ Syntax.ExprStmt (APP (OID "main") [ILIT 1]) ]) with
   | [ AN.DOcc _ _ (AN.MainArity _ _ _ _ _) ] => true | _ => false end) = true.
Proof. vm_compute; reflexivity. Qed.
(* a local main shadows the package main through the ordinary block rule *)
Definition o_main_shadowed : Compilable.outsides (prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "main"))) (NE1 (ILIT 1)) ; PL [ VNAME "main" ] ]). Proof. outside. Qed.

(* ordinary redeclaration: two var/const specs sharing one block scope and spelling is a redeclaration issue *)
Definition r_redecl_var : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ]). Proof. reject. Qed.
(* the one diagnostic is a redeclared-group row over the group spelled "x" (cause RedeclaredGroupCause) *)
Definition r_redecl_payload :
  (match dsites (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ]) with
   | [ d ] => match RP.diag_group_name d with Some nm => Names.ordinary_equalb nm (OID "x") | None => false end
   | _ => false
   end) = true.
Proof. vm_compute; reflexivity. Qed.
(* an occurrence diagnostic retains its exact family, a value invalidity projecting as FamValue *)
Definition r_iota_family :
  (match dsites (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ] ]) with
   | [ d ] => match AN.diag_family d with Some AN.FamValue => true | _ => false end
   | _ => false end) = true.
Proof. vm_compute; reflexivity. Qed.
(* a boundary retains its own exact family too, projected from the one retained row *)
Definition o_cx_typed_family : exists f,
  map AN.bound_family (AN.result_boundaries (rres (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat32 (ILIT 2)) ] ]))) = [ f ].
Proof. eexists; vm_compute; reflexivity. Qed.
(* a use of the redeclared name folds into the one group row named "x"; exact contexts + soundness are §24.4 laws *)
Definition p_redecl_use : Syntax.Program :=
  prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ; Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "y"))) (NE1 (VNAME "x")) ].
Definition r_redecl_usecontext :
  map RP.diag_group_name (dsites p_redecl_use) = [ Some (OID "x") ].
Proof. vm_compute; reflexivity. Qed.

(* an unbound application head is a dependent non-result, never a successful application fact *)
Definition r_unbound_app_dep :
  existsb (fun f => match f with AN.OFApp _ (AN.ADependent (AN.DepUnboundName _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (OID "undefined") []) ])) = true.
Proof. vm_compute; reflexivity. Qed.
(* an invalid-identity application head (iota) is a dependent non-result, never a success *)
Definition r_invalidid_app_dep :
  existsb (fun f => match f with AN.OFApp _ (AN.ADependent (AN.DepInvalidId _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PIota) []) ])) = true.
Proof. vm_compute; reflexivity. Qed.
(* an expr-statement whose expr owns an issue is a dependent non-result, never a successful statement *)
Definition r_child_stmt_dep :
  existsb (fun f => match f with AN.OFStmt _ (AN.SDependent _) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PIota) []) ])) = true.
Proof. vm_compute; reflexivity. Qed.
(* a redeclared application head is a dependent non-result, never a successful application fact *)
Definition r_redecl_app_dep :
  existsb (fun f => match f with AN.OFApp _ (AN.ADependent (AN.DepRedeclaredName _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "f"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "f"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ; Syntax.ExprStmt (APP (OID "f") []) ])) = true.
Proof. vm_compute; reflexivity. Qed.
(* a redeclared name used as a type is a dependent non-result, never a fabricated Bool type *)
Definition r_redecl_type_dep :
  existsb (fun f => match f with AN.OFType _ (AN.TDependent _) => true | _ => false end)
          (pfacts (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "y"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "y"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "z"))) (Syntax.VarTypeOnly (Syntax.NamedType (OID "y"))) ]) ])) = true.
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
   | [ d ] => match RP.diag_group_name d with Some nm => Names.ordinary_equalb nm (OID "main") | None => false end
   | _ => false end) = true.
Proof. vm_compute; reflexivity. Qed.
(* (c) multiple fixed mains: a redeclared group through the one authority, no first-main pick, so Rejected *)
Definition r_main_multiple : Compilable.rejects (prog_tops [ main0 ; main0 ]). Proof. reject. Qed.
Definition r_main_multiple_payload :
  (match dsites (prog_tops [ main0 ; main0 ]) with
   | [ d ] => match RP.diag_group_name d with Some nm => Names.ordinary_equalb nm (OID "main") | None => false end
   | _ => false end) = true.
Proof. vm_compute; reflexivity. Qed.
(* (d) no fixed main, an ordinary const main: MainMissing, so the missing-entry diagnostic Rejects *)
Definition r_main_missing : Compilable.rejects (prog_tops [ tconstmain ]). Proof. reject. Qed.
Definition r_main_missing_payload :
  (match dsites (prog_tops [ tconstmain ]) with
   | [ AN.DMissingMain _ ] => true | _ => false end) = true.
Proof. vm_compute; reflexivity. Qed.

(* exact issue identity: the ordinal-indexed sequence never collapses distinct issues and partitions by class *)
Definition p_two_iota : Syntax.Program :=
  prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ]
       ; PL [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ] ].
(* two same-cause invalidities stay two distinct diagnostic-class issues in source order — no dedup, no collapse *)
Definition d4_two_iota_no_collapse :
  Datatypes.length (AN.result_issues (rres p_two_iota)) = 2%nat
  /\ map AN.issue_class (AN.result_issues (rres p_two_iota)) = [ AN.ClassDiagnostic ; AN.ClassDiagnostic ].
Proof. split; vm_compute; reflexivity. Qed.
(* the two issues carry the SAME cause yet occupy distinct ordinals: shared cause never merges them *)
Definition d4_two_iota_same_cause :
  RP.result_cause_views (rres p_two_iota)
  = [ RP.CvInvalidIdentity Names.PIota ; RP.CvInvalidIdentity Names.PIota ].
Proof. vm_compute; reflexivity. Qed.

(* an invalidity and an independent unsupported boundary coexist: one diagnostic-class and one boundary-class issue *)
Definition p_invalid_unsupported : Syntax.Program :=
  prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ]
       ; PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat32 (ILIT 2)) ] ].
Definition d4_invalid_unsupported_coexist :
  map AN.issue_class (AN.result_issues (rres p_invalid_unsupported))
  = [ AN.ClassDiagnostic ; AN.ClassBoundary ].
Proof. vm_compute; reflexivity. Qed.

(* ordinal 0 names an exact retained row: the first diagnostic, projecting its exact retained cause *)
Definition d4_ord0_is_first_diagnostic :
  match nth_error (AN.result_issues (rres p_two_iota)) 0%nat with
  | Some (AN.IDiag d) => RP.issuecause_view (AN.diag_cause d) = RP.CvInvalidIdentity Names.PIota
  | _ => False
  end.
Proof. vm_compute; reflexivity. Qed.

(* a default-output collision coexists with a missing main and with a redeclared group as distinct diagnostics *)
Definition cgen_path : FilePath.T := FilePath.Make "generated/x.go" eq_refl.
Definition cvar1 : Syntax.TopLevelDecl :=
  Syntax.TopDeclaration (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "v"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]).
Definition cvar2 : Syntax.TopLevelDecl :=
  Syntax.TopDeclaration (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "v"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]).
Definition p_collision : Syntax.Program :=
  match Syntax.build_program rmod
          [ Syntax.MakeFileNode rmain (Syntax.main_source [ cvar1 ])
          ; Syntax.MakeFileNode cgen_path (Syntax.MakeFile Syntax.MainPackage [] []) ] with
  | Some pp => pp | None => empty_program rmod end.
(* the output collision and the missing main are two distinct diagnostics; neither suppresses the other *)
Definition d4_collision_missing_main_coexist :
  andb (existsb (fun d => match d with AN.DOutputCollision _ _ => true | _ => false end) (dsites p_collision))
       (existsb (fun d => match d with AN.DMissingMain _ => true | _ => false end) (dsites p_collision)) = true.
Proof. vm_compute; reflexivity. Qed.
Definition p_collision_redecl : Syntax.Program :=
  match Syntax.build_program rmod
          [ Syntax.MakeFileNode rmain (Syntax.main_source [ cvar1 ; cvar2 ])
          ; Syntax.MakeFileNode cgen_path (Syntax.MakeFile Syntax.MainPackage [] []) ] with
  | Some pp => pp | None => empty_program rmod end.
(* the output collision and a redeclared group coexist as distinct diagnostics through the one authority *)
Definition d4_collision_redeclared_coexist :
  andb (existsb (fun d => match d with AN.DOutputCollision _ _ => true | _ => false end) (dsites p_collision_redecl))
       (existsb (fun d => match d with AN.DRedeclaredGroup _ => true | _ => false end) (dsites p_collision_redecl)) = true.
Proof. vm_compute; reflexivity. Qed.

(* the formal-vs-Go differential: one named program per case, proven to a disposition and exported for pinned Go *)
Definition otransport (pp : Syntax.Program) : string * list (string * string) :=
  (Emit.module_file_of pp, Emit.entries_of pp).

Definition dp_neg_string  : Syntax.Program := prog [ PL [ NEG (SLIT "x") ] ].
Definition dp_conv0       : Syntax.Program := prog [ PL [ APP (Names.predeclared_ordinary Names.PInt8) [] ] ].
Definition dp_conv2       : Syntax.Program := prog [ PL [ APP (Names.predeclared_ordinary Names.PInt8) [ILIT 1; ILIT 2] ] ].
Definition dp_uint8_neg   : Syntax.Program := prog [ PL [ NEG (CONV Names.PUint8 (ILIT 1)) ] ].
Definition dp_type_value  : Syntax.Program := prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PInt8) ] ].
Definition dp_stmt_lit    : Syntax.Program := prog [ Syntax.ExprStmt (ILIT 1) ].
Definition dp_default_ovf : Syntax.Program := prog [ PL [ ILIT ((2 ^ 63)%N) ] ].
Definition dp_no_main     : Syntax.Program := prog_tops [ tconstmain ].
Definition dp_multi_main  : Syntax.Program := prog_tops [ main0 ; main0 ].
Definition dp_ok          : Syntax.Program := prog [ PL [ NEG (CONV Names.PInt8 (ILIT 1)) ] ].

Definition dr_neg_string  : Compilable.rejects dp_neg_string.  Proof. reject. Qed.
Definition dr_conv0       : Compilable.rejects dp_conv0.       Proof. reject. Qed.
Definition dr_conv2       : Compilable.rejects dp_conv2.       Proof. reject. Qed.
Definition dr_uint8_neg   : Compilable.rejects dp_uint8_neg.   Proof. reject. Qed.
Definition dr_type_value  : Compilable.rejects dp_type_value.  Proof. reject. Qed.
Definition dr_stmt_lit    : Compilable.rejects dp_stmt_lit.    Proof. reject. Qed.
Definition dr_default_ovf : Compilable.rejects dp_default_ovf. Proof. reject. Qed.
Definition dr_no_main     : Compilable.rejects dp_no_main.     Proof. reject. Qed.
Definition dr_multi_main  : Compilable.rejects dp_multi_main.  Proof. reject. Qed.
Definition dc_ok          : Compilable.compiles dp_ok.         Proof. compileok. Qed.

Declare ML Module "fido.emit".
Fido OracleExport (otransport dp_neg_string)  To "/workspace/diff/reject/neg_string".
Fido OracleExport (otransport dp_conv0)       To "/workspace/diff/reject/conv0".
Fido OracleExport (otransport dp_conv2)       To "/workspace/diff/reject/conv2".
Fido OracleExport (otransport dp_uint8_neg)   To "/workspace/diff/reject/uint8_neg".
Fido OracleExport (otransport dp_type_value)  To "/workspace/diff/reject/type_value".
Fido OracleExport (otransport dp_stmt_lit)    To "/workspace/diff/reject/stmt_lit".
Fido OracleExport (otransport dp_default_ovf) To "/workspace/diff/reject/default_ovf".
Fido OracleExport (otransport dp_no_main)     To "/workspace/diff/reject/no_main".
Fido OracleExport (otransport dp_multi_main)  To "/workspace/diff/reject/multi_main".
Fido OracleExport (otransport dp_ok)          To "/workspace/diff/compiled/ok".
