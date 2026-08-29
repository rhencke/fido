(* WitnessReject chunk C: one cost-balanced slice of the fixture matrix over the shared prelude *)

From Stdlib Require Import List NArith ZArith String.
From Fido Require Import Integer Float Collections FilePath ModulePath Version Names Syntax Index Compilable Compilable.PackageIdentity Compilable.Bindings Compilable.Analysis Compilable.Report Render Emit.
From Fido Require Import WitnessRejectPrelude.
Import ListNotations.

(* wrong arity: conversions take exactly one argument, the complex builtin exactly two *)
Definition r_conv0 : Compilable.rejects (prog [ PL [ APP (Names.predeclared_ordinary Names.PInt8) [] ] ]).              Proof. reject. Qed.

Definition r_call_bool   : Compilable.rejects (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PTrue) []) ]). Proof. reject. Qed.

Definition r_call_lit    : Compilable.rejects (prog [ Syntax.ExprStmt (Syntax.Application (ILIT 1) []) ]).           Proof. reject. Qed.

(* positive controls: the same forms compile when the operand facts satisfy the rule *)
Definition c_neg_int8    : Compilable.compiles (prog [ PL [ NEG (CONV Names.PInt8 (ILIT 1)) ] ]). Proof. compileok. Qed.

Definition r_nil  : Compilable.rejects (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PNil) ] ]).  Proof. reject. Qed.

(* visibility: a name is not visible inside its own spec, so a self-initializer is unresolved and Rejected *)
Definition r_var_self : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (VNAME "x"))) ]) ]). Proof. reject. Qed.

Definition o_var_later : Compilable.outsides (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "a"))) (Syntax.VarValues None (NE1 (ILIT 1))) ; Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "b"))) (Syntax.VarValues None (NE1 (VNAME "a"))) ]) ]). Proof. outside. Qed.

(* a short declaration does not compile merely because its later typing is absent: its meaning is a boundary *)
Definition o_short_new : Compilable.outsides (prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "x"))) (NE1 (ILIT 1)) ]). Proof. outside. Qed.

(* declaration invalidities: a first const spec omitting its initializer, a result-count mismatch, a short duplicate *)
Definition r_const_noinit : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) Syntax.InheritedConstInit ]) ]). Proof. reject. Qed.

Definition o_short_mixed : Compilable.outsides (prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "x"))) (NE1 (ILIT 1)) ; Syntax.ShortVarDecl (Collections.MakeNonEmpty (Syntax.BNamed (OID "x")) [Syntax.BNamed (OID "y")]) (Collections.MakeNonEmpty (ILIT 2) [ILIT 3]) ]). Proof. outside. Qed.

Lemma reader_disp_outside : Compilable.disposition oprobe = Compilable.OutsideScope. Proof. vm_compute; reflexivity. Qed.

(* §R.4 fact-row integration: the branch-carried Result carries the exact res_facts, so its rows ARE analyze's rows *)
Lemma reader_facts_kinds :
  map AN.fact_kind (pfacts rprobe) = map AN.fact_kind (AN.result_fact_list (AN.analyze rprobe)).
Proof. vm_compute; reflexivity. Qed.

Definition r_type_value_cause :
  RP.result_cause_views (rres (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PInt8) ] ])) = [ RP.CvTypeAsValue (Some Names.PInt8) ].
Proof. vm_compute; reflexivity. Qed.

Definition r_cx_mix_cause :
  RP.result_cause_views (rres (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat64 (ILIT 2)) ] ])) = [ RP.CvComplexMismatch ].
Proof. vm_compute; reflexivity. Qed.

(* main used as a bare value (not called) is a later-root boundary *)
Definition o_main_value : Compilable.outsides (prog [ PL [ VNAME "main" ] ]). Proof. outside. Qed.

(* main(1) is an exact arity invalidity: the fixed main takes zero arguments *)
Definition r_main_arity : Compilable.rejects (prog [ Syntax.ExprStmt (APP (OID "main") [ILIT 1]) ]). Proof. reject. Qed.

(* ordinary redeclaration: two var/const specs sharing one block scope and spelling is a redeclaration issue *)
Definition r_redecl_var : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ]). Proof. reject. Qed.

Definition r_redecl_usecontext :
  map RP.diag_group_name (dsites p_redecl_use) = [ Some (OID "x") ].
Proof. vm_compute; reflexivity. Qed.

(* an invalid-identity application head (iota) is a dependent non-result, never a success *)
Definition r_invalidid_app_dep :
  existsb (fun f => match f with AN.OFApp _ (AN.ADependent (AN.DepInvalidId _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PIota) []) ])) = true.
Proof. vm_compute; reflexivity. Qed.

(* a redeclared application head is a dependent non-result, never a successful application fact *)
Definition r_redecl_app_dep :
  existsb (fun f => match f with AN.OFApp _ (AN.ADependent (AN.DepRedeclaredNameA _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "f"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "f"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ; Syntax.ExprStmt (APP (OID "f") []) ])) = true.
Proof. vm_compute; reflexivity. Qed.

(* §22.3 a canonical invalid statement row: a bare literal is an illegal-statement invalidity in the statement family *)
Definition mf_stmt_lit_invalid_row :
  RP.result_cause_views (rres (prog [ Syntax.ExprStmt (ILIT 1) ])) = [ RP.CvOtherCause ]
  /\ RP.result_diag_families (rres (prog [ Syntax.ExprStmt (ILIT 1) ])) = [ AN.FamStatement ].
Proof. split; vm_compute; reflexivity. Qed.

(* §22.5 a dependent row yields no issue: only the unresolved child name is a cause, its app+stmt rows stay silent *)
Definition mf_dep_row_silent :
  RP.result_cause_views (rres (prog [ Syntax.ExprStmt (APP (OID "undefined") []) ])) = [ RP.CvUnresolvedName ]
  /\ RP.result_req_views (rres (prog [ Syntax.ExprStmt (APP (OID "undefined") []) ])) = [].
Proof. split; vm_compute; reflexivity. Qed.

Definition mf_app_two_families :
  (match filter (fun o => match AN.fact_kind o with AN.ApplicationKind => true | _ => false end) (pfacts p_app_multi) with
   | app :: _ => existsb (fun o => andb (match AN.fact_kind o with AN.ValueKind => true | _ => false end)
                                        (BN.noderef_eqb (AN.fact_site o) (AN.fact_site app))) (pfacts p_app_multi)
   | [] => false end) = true.
Proof. vm_compute; reflexivity. Qed.

(* const inheritance: a non-first inherited const spec is valid Go outside the modelled scope (a boundary) *)
Definition o_const_inherited : Compilable.outsides (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (ILIT 1))) ; Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "y"))) Syntax.InheritedConstInit ]) ]). Proof. outside. Qed.

(* (b) a fixed main plus a const main: a redeclared group, so main is an ordinary group member and it Rejects *)
Definition r_main_const_redecl : Compilable.rejects (prog_tops [ tconstmain ; main0 ]). Proof. reject. Qed.

Definition r_main_missing_payload :
  (match dsites (prog_tops [ tconstmain ]) with
   | [ AN.DMissingMain _ ] => true | _ => false end) = true.
Proof. vm_compute; reflexivity. Qed.

(* the output collision and the missing main are two distinct diagnostics; neither suppresses the other *)
Definition d4_collision_missing_main_coexist :
  andb (existsb (fun d => match d with AN.DOutputCollision _ => true | _ => false end) (dsites p_collision))
       (existsb (fun d => match d with AN.DMissingMain _ => true | _ => false end) (dsites p_collision)) = true.
Proof. vm_compute; reflexivity. Qed.

(* §17.1 a package with no fixed main has exactly one exact missing-main case for its own package *)
Lemma mm17_1_missing_len : Datatypes.length (AN.result_missing_main_refs (ppkg (prog_tops [ tconstmain ]))) = 1%nat.
Proof. vm_compute; reflexivity. Qed.

(* §17.5 a non-colliding program has no collision case: the false collision cannot arise *)
Lemma mm17_5_nocollision_none : pcollision (prog [ PL [ ILIT 1 ] ]) = None.
Proof. vm_compute; reflexivity. Qed.

Definition dr_conv0       : Compilable.rejects dp_conv0.       Proof. reject. Qed.

Definition dr_conv2       : Compilable.rejects dp_conv2.       Proof. reject. Qed.

Definition dr_no_main     : Compilable.rejects dp_no_main.     Proof. reject. Qed.

Definition dr_short_count    : Compilable.rejects dp_short_count.    Proof. reject. Qed.

Definition dr_short_nonvar   : Compilable.rejects dp_short_nonvar.   Proof. reject. Qed.

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
Fido OracleExport (otransport dp_short_dup)      To "/workspace/diff/reject/short_dup".
Fido OracleExport (otransport dp_short_count)    To "/workspace/diff/reject/short_count".
Fido OracleExport (otransport dp_short_nonew)    To "/workspace/diff/reject/short_nonew".
Fido OracleExport (otransport dp_short_allblank) To "/workspace/diff/reject/short_allblank".
Fido OracleExport (otransport dp_short_nonvar)   To "/workspace/diff/reject/short_nonvar".
Fido OracleExport (otransport dp_ok)          To "/workspace/diff/compiled/ok".
