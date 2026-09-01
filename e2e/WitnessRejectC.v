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

Lemma reader_disp_outside : Compilable.disposition oprobe = Compilable.OutsideScope. Proof. obs_disp. Qed.

(* §R.4 fact-row integration: the branch-carried Result carries the exact res_facts, so its rows ARE analyze's rows *)
Lemma reader_facts_kinds :
  map AN.fact_kind (pfacts rprobe) = map AN.fact_kind (AN.result_fact_list (AN.analyze rprobe)).
Proof. obs_eq rprobe. Qed.

Definition r_type_value_cause :
  RP.result_cause_views (rres (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PInt8) ] ])) = [ RP.CvTypeAsValue (Some Names.PInt8) ].
Proof. obs_direct (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PInt8) ] ]). Qed.

Definition r_cx_mix_cause :
  RP.result_cause_views (rres (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat64 (ILIT 2)) ] ])) = [ RP.CvComplexMismatch ].
Proof. obs_direct (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat64 (ILIT 2)) ] ]). Qed.

(* main used as a bare value (not called) is a later-root boundary *)
Definition o_main_value : Compilable.outsides (prog [ PL [ VNAME "main" ] ]). Proof. outside. Qed.

(* main(1) is an exact arity invalidity: the fixed main takes zero arguments *)
Definition r_main_arity : Compilable.rejects (prog [ Syntax.ExprStmt (APP (OID "main") [ILIT 1]) ]). Proof. reject. Qed.

(* ordinary redeclaration: two var/const specs sharing one block scope and spelling is a redeclaration issue *)
Definition r_redecl_var : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ]). Proof. reject. Qed.

Definition r_redecl_usecontext :
  map RP.diag_group_name (dsites p_redecl_use) = [ Some (OID "x") ].
Proof.
  unfold dsites.
  assert (Hc : AN.collision_rows (rres p_redecl_use) = []) by (apply (proj1 (AN.dnc_iff _)); obs_seal p_redecl_use).
  assert (Hm : AN.main_rows (rres p_redecl_use) = []) by (apply (proj1 (AN.dnm_iff _)); obs_seal p_redecl_use).
  assert (Ho : AN.occ_diags (rres p_redecl_use) = []) by (apply (proj1 (AN.dncause_iff _)); obs_seal p_redecl_use).
  rewrite (AN.diagnostics_order (rres p_redecl_use)), Hc, Hm, Ho. rewrite ?app_nil_l, ?app_nil_r.
  unfold AN.group_rows; rewrite map_map.
  erewrite (map_ext _ (fun rr => Some (projT1 rr))) by (intro rr; reflexivity).
  unfold rres, result_of_compile, AN.res_binds, AN.res_bind_data, AN.res_surface, AN.res_index.
  rewrite (Compilable.compile_observe_data p_redecl_use). vm_compute. reflexivity.
Qed.

(* §330 an iota application head is an invalid-application-identity on the app row, a diagnostic, never a success *)
Definition r_invalidid_app_dep :
  existsb (fun f => match f with AN.OFApp _ (AN.AInvalid (AN.InvalidApplicationIdentity _ _ _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PIota) []) ])) = true.
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PIota) []) ]). Qed.

(* a redeclared application head is a dependent non-result, never a successful application fact *)
Definition r_redecl_app_dep :
  existsb (fun f => match f with AN.OFApp _ (AN.ADependent (AN.DepRedeclaredNameA _ _ _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "f"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "f"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ; Syntax.ExprStmt (APP (OID "f") []) ])) = true.
Proof. obs_direct (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "f"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "f"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ; Syntax.ExprStmt (APP (OID "f") []) ]). Qed.

(* §22.3 a canonical invalid statement row: a bare literal is an illegal-statement invalidity in the statement family *)
Definition mf_stmt_lit_invalid_row :
  RP.result_cause_views (rres (prog [ Syntax.ExprStmt (ILIT 1) ])) = [ RP.CvIllegalStatement ]
  /\ RP.result_diag_families (rres (prog [ Syntax.ExprStmt (ILIT 1) ])) = [ AN.FamStatement ].
Proof. split; obs_direct (prog [ Syntax.ExprStmt (ILIT 1) ]). Qed.

(* §22.5 an unbound application head is the unresolved-name cause on the app row; stmt row silent, no requirement *)
Definition mf_dep_row_silent :
  RP.result_cause_views (rres (prog [ Syntax.ExprStmt (APP (OID "undefined") []) ])) = [ RP.CvUnresolvedName ]
  /\ RP.result_req_views (rres (prog [ Syntax.ExprStmt (APP (OID "undefined") []) ])) = [].
Proof. split; obs_direct (prog [ Syntax.ExprStmt (APP (OID "undefined") []) ]). Qed.

Definition mf_app_two_families :
  (match filter (fun o => match AN.fact_kind o with AN.ApplicationKind => true | _ => false end) (pfacts p_app_multi) with
   | app :: _ => existsb (fun o => andb (match AN.fact_kind o with AN.ValueKind => true | _ => false end)
                                        (BN.noderef_eqb (AN.fact_site o) (AN.fact_site app))) (pfacts p_app_multi)
   | [] => false end) = true.
Proof. obs_direct p_app_multi. Qed.

(* const inheritance: a non-first inherited const spec is valid Go outside the modelled scope (a boundary) *)
Definition o_const_inherited : Compilable.outsides (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (ILIT 1))) ; Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "y"))) Syntax.InheritedConstInit ]) ]). Proof. outside. Qed.

(* (b) a fixed main plus a const main: a redeclared group, so main is an ordinary group member and it Rejects *)
Definition r_main_const_redecl : Compilable.rejects (prog_tops [ tconstmain ; main0 ]). Proof. reject. Qed.

Definition r_main_missing_payload :
  (match dsites (prog_tops [ tconstmain ]) with
   | [ AN.DMissingMain _ ] => true | _ => false end) = true.
Proof.
  assert (Hlen : Datatypes.length (AN.result_missing_main_refs (rres (prog_tops [ tconstmain ]))) = 1%nat).
  { rewrite <- (length_map AN.mmr_package), AN.missing_main_packages.
    unfold rres, result_of_compile, AN.is_missing, AN.result_package_rule, AN.res_binds, AN.res_surface, AN.res_bind_data, AN.res_index.
    rewrite (Compilable.compile_observe_data (prog_tops [ tconstmain ])). vm_compute. reflexivity. }
  unfold dsites.
  assert (Hc : AN.collision_rows (rres (prog_tops [ tconstmain ])) = []) by (apply (proj1 (AN.dnc_iff _)); obs_seal (prog_tops [ tconstmain ])).
  assert (Hg : AN.group_rows (rres (prog_tops [ tconstmain ])) = []) by (apply (proj1 (AN.dnr_iff _)); obs_seal (prog_tops [ tconstmain ])).
  assert (Ho : AN.occ_diags (rres (prog_tops [ tconstmain ])) = []) by (apply (proj1 (AN.dncause_iff _)); obs_seal (prog_tops [ tconstmain ])).
  rewrite (AN.diagnostics_order (rres (prog_tops [ tconstmain ]))), Hc, Hg, Ho, ?app_nil_l, ?app_nil_r.
  unfold AN.main_rows.
  destruct (AN.result_missing_main_refs (rres (prog_tops [ tconstmain ]))) as [|ref0 [|ref1 rest]]; cbn in Hlen; try discriminate Hlen.
  reflexivity.
Qed.

(* the output collision and the missing main are two distinct diagnostics; neither suppresses the other *)
Definition d4_collision_missing_main_coexist :
  andb (existsb (fun d => match d with AN.DOutputCollision _ => true | _ => false end) (dsites p_collision))
       (existsb (fun d => match d with AN.DMissingMain _ => true | _ => false end) (dsites p_collision)) = true.
Proof.
  unfold dsites. rewrite (AN.diagnostics_order (rres p_collision)).
  assert (Hg : AN.group_rows (rres p_collision) = []) by (apply (proj1 (AN.dnr_iff _)); obs_seal p_collision).
  assert (Ho : AN.occ_diags (rres p_collision) = []) by (apply (proj1 (AN.dncause_iff _)); obs_seal p_collision).
  rewrite Hg, Ho, ?app_nil_r.
  destruct (AN.result_collision_ref (rres p_collision)) as [cr|] eqn:Hcr.
  2:{ exfalso. apply AN.collision_ref_none in Hcr. revert Hcr.
      unfold rres, result_of_compile, AN.result_preflight, AN.res_pkg, AN.res_binds, AN.res_bind_data, AN.res_surface, AN.res_index.
      rewrite (Compilable.compile_observe_data p_collision). vm_compute. discriminate. }
  assert (Hne : AN.result_missing_main_refs (rres p_collision) <> []).
  { intro Hnil. apply (f_equal (@Datatypes.length _)) in Hnil.
    rewrite <- (length_map AN.mmr_package), AN.missing_main_packages in Hnil. revert Hnil.
    unfold rres, result_of_compile, AN.is_missing, AN.result_package_rule, AN.res_binds, AN.res_surface, AN.res_bind_data, AN.res_index.
    rewrite (Compilable.compile_observe_data p_collision). vm_compute. discriminate. }
  unfold AN.collision_rows, AN.main_rows. rewrite Hcr.
  destruct (AN.result_missing_main_refs (rres p_collision)) as [|ref0 rest]; [ exfalso; exact (Hne eq_refl) | ].
  reflexivity.
Qed.

(* §17.1 a package with no fixed main has exactly one exact missing-main case for its own package *)
Lemma mm17_1_missing_len : Datatypes.length (AN.result_missing_main_refs (ppkg (prog_tops [ tconstmain ]))) = 1%nat.
Proof.
  unfold ppkg. rewrite <- (length_map AN.mmr_package), AN.missing_main_packages.
  unfold rres, result_of_compile, AN.is_missing, AN.result_package_rule, AN.res_binds, AN.res_surface, AN.res_bind_data, AN.res_index.
  rewrite (Compilable.compile_observe_data (prog_tops [ tconstmain ])). vm_compute. reflexivity.
Qed.

(* §17.5 a non-colliding program has no collision case: the false collision cannot arise *)
Lemma mm17_5_nocollision_none : pcollision (prog [ PL [ ILIT 1 ] ]) = None.
Proof.
  unfold pcollision, ppkg.
  assert (Hn : AN.result_collision_ref (rres (prog [ PL [ ILIT 1 ] ])) = None).
  { apply AN.collision_ref_none.
    unfold rres, result_of_compile, AN.result_preflight, AN.res_pkg, AN.res_binds, AN.res_bind_data, AN.res_surface, AN.res_index.
    rewrite (Compilable.compile_observe_data (prog [ PL [ ILIT 1 ] ])). vm_compute. reflexivity. }
  rewrite Hn. reflexivity.
Qed.

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
