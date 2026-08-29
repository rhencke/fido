(* WitnessReject chunk D: one cost-balanced slice of the fixture matrix over the shared prelude *)

From Stdlib Require Import List NArith ZArith String.
From Fido Require Import Integer Float Collections FilePath ModulePath Version Names Syntax Index Compilable Compilable.PackageIdentity Compilable.Bindings Compilable.Analysis Compilable.Report Render Emit.
From Fido Require Import WitnessRejectPrelude.
Import ListNotations.

(* known type mismatches: unary minus over a nonnumeric or overflowing typed constant *)
Definition r_neg_string  : Compilable.rejects (prog [ PL [ NEG (SLIT "x") ] ]).                         Proof. reject. Qed.

Definition r_neg_uint8   : Compilable.rejects (prog [ PL [ NEG (CONV Names.PUint8 (ILIT 1)) ] ]).        Proof. reject. Qed.

Definition r_cx_mix  : Compilable.rejects (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat64 (ILIT 2)) ] ]). Proof. reject. Qed.

Definition r_conv2 : Compilable.rejects (prog [ PL [ APP (Names.predeclared_ordinary Names.PInt8) [ILIT 1; ILIT 2] ] ]). Proof. reject. Qed.

Definition r_cx3   : Compilable.rejects (prog [ PL [ APP (Names.predeclared_ordinary Names.PComplex) [ILIT 1; ILIT 2; ILIT 3] ] ]). Proof. reject. Qed.

(* no-value used as a value; a type used as a value; a non-function called *)
Definition r_println_val : Compilable.rejects (prog [ PL [ APP (Names.predeclared_ordinary Names.PPrintln) [] ] ]).  Proof. reject. Qed.

Definition r_type_value  : Compilable.rejects (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PInt8) ] ]).   Proof. reject. Qed.

(* a bare integer literal that overflows the default int type is a definite default-overflow invalidity *)
Definition r_default_overflow : Compilable.rejects (prog [ PL [ ILIT ((2 ^ 63)%N) ] ]). Proof. reject. Qed.

Definition r_const_self : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (VNAME "x"))) ]) ]). Proof. reject. Qed.

(* §16 positive: x := 1 and _, x := 0, 1 stay OutsideScope: a positive SUnmet usage req, never SInvalid or SOK *)
Definition o_short_blank : Compilable.outsides (prog [ Syntax.ShortVarDecl (Collections.MakeNonEmpty Syntax.BBlank [Syntax.BNamed (OID "x")]) (Collections.MakeNonEmpty (ILIT 0) [ILIT 1]) ]). Proof. outside. Qed.

(* §15.3 two distinct short origins of different names; a use of y resolves to its exact origin, still Outside *)
Definition o_short_two_origins : Compilable.outsides (prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "x"))) (NE1 (ILIT 1)) ; Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "y"))) (NE1 (ILIT 2)) ; PL [ VNAME "y" ] ]). Proof. outside. Qed.

(* §15.4 invalid declaration coexistence: a duplicate short decl stays Rejected even with a following value use *)
Definition r_short_dup_use : Compilable.rejects (prog [ Syntax.ShortVarDecl (Collections.MakeNonEmpty (Syntax.BNamed (OID "x")) [Syntax.BNamed (OID "x")]) (Collections.MakeNonEmpty (ILIT 1) [ILIT 2]) ; PL [ VNAME "x" ] ]). Proof. reject. Qed.

Lemma reader_disp : Compilable.disposition rprobe = Compilable.Rejected.
Proof. vm_compute; reflexivity. Qed.

Lemma reader_disp_compiled : Compilable.disposition cprobe = Compilable.Compiled. Proof. vm_compute; reflexivity. Qed.

Lemma reader_index_compiled : AN.res_index (rres cprobe) = AN.res_index (AN.analyze cprobe). Proof. vm_compute; reflexivity. Qed.

Lemma reader_index_outside : AN.res_index (rres oprobe) = AN.res_index (AN.analyze oprobe). Proof. vm_compute; reflexivity. Qed.

(* payload catalogue via the bp-free Report views: goal types carry no BindingPhase, so vm_compute stays cheap *)
Definition r_iota_cause :
  RP.result_cause_views (rres (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ] ])) = [ RP.CvInvalidIdentity Names.PIota ].
Proof. vm_compute; reflexivity. Qed.

Definition o_cx_typed_payload :
  RP.result_cause_views (rres (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat32 (ILIT 2)) ] ])) = []
  /\ RP.result_req_views (rres (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat32 (ILIT 2)) ] ])) = [ RP.RvComplexType ].
Proof. split; vm_compute; reflexivity. Qed.

Definition r_main_as_type : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarTypeOnly (Syntax.NamedType (OID "main"))) ]) ]). Proof. reject. Qed.

(* a local main shadows the package main through the ordinary block rule *)
Definition o_main_shadowed : Compilable.outsides (prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "main"))) (NE1 (ILIT 1)) ; PL [ VNAME "main" ] ]). Proof. outside. Qed.

(* the one diagnostic is a redeclared-group row over the group spelled "x" (cause RedeclaredGroupCause) *)
Definition r_redecl_payload :
  (match dsites (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ]) with
   | [ d ] => match RP.diag_group_name d with Some nm => Names.ordinary_equalb nm (OID "x") | None => false end
   | _ => false
   end) = true.
Proof. vm_compute; reflexivity. Qed.

(* an unbound application head is a dependent non-result, never a successful application fact *)
Definition r_unbound_app_dep :
  existsb (fun f => match f with AN.OFApp _ (AN.ADependent (AN.DepUnboundNameA _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (OID "undefined") []) ])) = true.
Proof. vm_compute; reflexivity. Qed.

(* an expr-statement whose expr owns an issue is a dependent non-result, never a successful statement *)
Definition r_child_stmt_dep :
  existsb (fun f => match f with AN.OFStmt _ (AN.SDependent _) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PIota) []) ])) = true.
Proof. vm_compute; reflexivity. Qed.

(* a redeclared name used as a type is a dependent non-result, never a fabricated Bool type *)
Definition r_redecl_type_dep :
  existsb (fun f => match f with AN.OFType _ (AN.TDependent _) => true | _ => false end)
          (pfacts (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "y"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "y"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "z"))) (Syntax.VarTypeOnly (Syntax.NamedType (OID "y"))) ]) ])) = true.
Proof. vm_compute; reflexivity. Qed.

(* (a) one fixed main, no competitor -> unique group + MainOne -> Compiled *)
Definition c_main_only : Compilable.compiles (prog_tops [ main0 ]). Proof. compileok. Qed.

(* (c) multiple fixed mains: a redeclared group through the one authority, no first-main pick, so Rejected *)
Definition r_main_multiple : Compilable.rejects (prog_tops [ main0 ; main0 ]). Proof. reject. Qed.

Definition r_main_multiple_payload :
  (match dsites (prog_tops [ main0 ; main0 ]) with
   | [ d ] => match RP.diag_group_name d with Some nm => Names.ordinary_equalb nm (OID "main") | None => false end
   | _ => false end) = true.
Proof. vm_compute; reflexivity. Qed.

(* the output collision and a redeclared group coexist as distinct diagnostics through the one authority *)
Definition d4_collision_redeclared_coexist :
  andb (existsb (fun d => match d with AN.DOutputCollision _ => true | _ => false end) (dsites p_collision_redecl))
       (existsb (fun d => match d with AN.DRedeclaredGroup _ => true | _ => false end) (dsites p_collision_redecl)) = true.
Proof. vm_compute; reflexivity. Qed.

(* §17.2 a package with exactly one valid main has no missing-main case: the false missing-main cannot arise *)
Lemma mm17_2_main_one_none : pmissing (prog_tops [ main0 ]) = [].
Proof. vm_compute; reflexivity. Qed.

(* §17.3 a package with multiple mains is a group redeclaration, not a missing main: still no missing-main case *)
Lemma mm17_3_main_multiple_none : pmissing (prog_tops [ main0 ; main0 ]) = [].
Proof. vm_compute; reflexivity. Qed.

(* §17.4 an exact output collision retains the exact package+root: the collision view names the colliding entry *)
Lemma mm17_4_collision_view : option_map RP.cv_root (pcollision p_collision) = Some "generated"%string.
Proof. vm_compute; reflexivity. Qed.

Definition dr_default_ovf : Compilable.rejects dp_default_ovf. Proof. reject. Qed.

Definition dr_multi_main  : Compilable.rejects dp_multi_main.  Proof. reject. Qed.

Definition dc_ok          : Compilable.compiles dp_ok.         Proof. compileok. Qed.
