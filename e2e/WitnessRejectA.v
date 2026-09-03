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

(* §17.2 a package with exactly one valid main has no missing-main case: the false missing-main cannot arise *)
Lemma mm17_2_main_one_none : pmissing (prog_tops [ main0 ]) = [].
Proof.
  unfold pmissing, ppkg.
  assert (Hnil : AN.result_missing_main_refs (rres (prog_tops [ main0 ])) = []).
  { apply (map_eq_nil AN.mmr_package). rewrite AN.missing_main_packages.
    unfold rres, result_of_compile, AN.is_missing, AN.result_package_rule, AN.res_binds, AN.res_surface, AN.res_bind_data, AN.res_index.
    rewrite (Compilable.compile_observe_data (prog_tops [ main0 ])). vm_compute. reflexivity. }
  rewrite Hnil. reflexivity.
Qed.

(* §17.3 a package with multiple mains is a group redeclaration, not a missing main: still no missing-main case *)
Lemma mm17_3_main_multiple_none : pmissing (prog_tops [ main0 ; main0 ]) = [].
Proof.
  unfold pmissing, ppkg.
  assert (Hnil : AN.result_missing_main_refs (rres (prog_tops [ main0 ; main0 ])) = []).
  { apply (map_eq_nil AN.mmr_package). rewrite AN.missing_main_packages.
    unfold rres, result_of_compile, AN.is_missing, AN.result_package_rule, AN.res_binds, AN.res_surface, AN.res_bind_data, AN.res_index.
    rewrite (Compilable.compile_observe_data (prog_tops [ main0 ; main0 ])). vm_compute. reflexivity. }
  rewrite Hnil. reflexivity.
Qed.

(* the one diagnostic is a redeclared-group row over the group spelled "x" (cause RedeclaredGroupCause) *)
Definition r_redecl_payload :
  (match dsites (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ]) with
   | [ d ] => match RP.diag_group_name d with Some nm => Names.ordinary_equalb nm (OID "x") | None => false end
   | _ => false
   end) = true.
Proof.
  set (pp := prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ]).
  assert (H : map RP.diag_group_name (dsites pp) = [ Some (OID "x") ]).
  { unfold dsites.
    obs_flags pp true true false true Hc Hm Hg Ho.
    apply (proj1 (AN.dnc_iff _)) in Hc. apply (proj1 (AN.dnm_iff _)) in Hm. apply (proj1 (AN.dncause_iff _)) in Ho.
    rewrite (AN.diagnostics_order (rres pp)), Hc, Hm, Ho. rewrite ?app_nil_l, ?app_nil_r.
    unfold AN.group_rows; rewrite map_map.
    erewrite (map_ext _ (fun rr => Some (projT1 rr))) by (intro rr; reflexivity).
    unfold rres, result_of_compile, AN.res_binds, AN.res_bind_data, AN.res_surface, AN.res_index.
    rewrite (Compilable.compile_observe_data pp). share_rd pp. vm_compute. reflexivity. }
  destruct (dsites pp) as [|d0 [|d1 r1]]; cbn in H; try discriminate H.
  injection H as Hd0. cbn. rewrite Hd0. reflexivity.
Qed.
