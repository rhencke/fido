(* WitnessReject chunk B: one cost-balanced slice of the fixture matrix over the shared prelude *)

From Stdlib Require Import List NArith ZArith String.
From Fido Require Import Integer Float Collections FilePath ModulePath Version Names Syntax Index Compilable Compilable.PackageIdentity Compilable.Bindings Compilable.Analysis Compilable.Report Render Emit.
From Fido Require Import WitnessRejectPrelude.
Import ListNotations.

(* known complex component errors: nonnumeric, string, typed-int, or mismatched-typed-float components *)
Definition r_cx_bool : Compilable.rejects (prog [ PL [ CPLX TT FF ] ]).                                 Proof. reject. Qed.

Definition r_cx_int8 : Compilable.rejects (prog [ PL [ CPLX (CONV Names.PInt8 (ILIT 1)) (CONV Names.PInt8 (ILIT 2)) ] ]). Proof. reject. Qed.

Definition r_cx1   : Compilable.rejects (prog [ PL [ APP (Names.predeclared_ordinary Names.PComplex) [ILIT 1] ] ]).   Proof. reject. Qed.

(* a non-Name application head (a unary expression) is not callable: the exact head ref, never an invented nil *)
Definition r_call_neg    : Compilable.rejects (prog [ PL [ Syntax.Application (NEG (ILIT 1)) [] ] ]).                Proof. reject. Qed.

(* illegal expression statements: a conversion or a bare literal cannot be a statement *)
Definition r_stmt_conv : Compilable.rejects (prog [ Syntax.ExprStmt (CONV Names.PInt8 (ILIT 1)) ]). Proof. reject. Qed.

Definition c_neg_complex : Compilable.compiles (prog [ PL [ NEG (CPLX (ILIT 1) (ILIT 2)) ] ]).    Proof. compileok. Qed.

(* a typed complex is valid Go but outside the implemented scope: not Compiled, not Rejected, but OutsideScope *)
Definition o_cx_typed : Compilable.outsides (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat32 (ILIT 2)) ] ]). Proof. outside. Qed.

(* iota and nil are known predeclared identities with no valid use in the active domain: definite invalidity *)
Definition r_iota : Compilable.rejects (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ] ]). Proof. reject. Qed.

(* type uses: an unmodelled real type is a boundary; a value name used as a type is an exact invalidity *)
Definition o_var_uintptr : Compilable.outsides (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarTypeOnly (Syntax.NamedType (Names.predeclared_ordinary Names.PUintptr))) ]) ]). Proof. outside. Qed.

(* visibility: a name IS visible after its spec, but a source value's meaning is a later root (OutsideScope) *)
Definition o_var_use : Compilable.outsides (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; PL [ VNAME "x" ] ]). Proof. outside. Qed.

Definition o_short_use : Compilable.outsides (prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "x"))) (NE1 (ILIT 1)) ; PL [ VNAME "x" ] ]). Proof. outside. Qed.

Definition r_const_count : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (Collections.MakeNonEmpty (Syntax.BNamed (OID "x")) [Syntax.BNamed (OID "y")]) (Syntax.ExplicitConstInit None (NE1 (ILIT 1))) ]) ]). Proof. reject. Qed.

Definition r_short_ambiguous : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ; Syntax.ShortVarDecl (Collections.MakeNonEmpty (Syntax.BNamed (OID "x")) [Syntax.BNamed (OID "y")]) (Collections.MakeNonEmpty (ILIT 3) [ILIT 4]) ]). Proof. reject. Qed.

Definition o_short_blank_new : Compilable.outsides (prog [ Syntax.ShortVarDecl (Collections.MakeNonEmpty Syntax.BBlank [Syntax.BNamed (OID "x")]) (Collections.MakeNonEmpty (ILIT 0) [ILIT 1]) ; PL [ VNAME "x" ] ]). Proof. outside. Qed.

(* §15.2 multiple new variables: x, y := 1, 2 then a use of y — the second short origin, whole program OutsideScope *)
Definition o_short_multi_use : Compilable.outsides (prog [ Syntax.ShortVarDecl (Collections.MakeNonEmpty (Syntax.BNamed (OID "x")) [Syntax.BNamed (OID "y")]) (Collections.MakeNonEmpty (ILIT 1) [ILIT 2]) ; PL [ VNAME "y" ] ]). Proof. outside. Qed.

(* a parent arity invalidity and an independent child requirement coexist: neither over-blocks the other *)
Definition r_complex_coexist : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; PL [ Syntax.Application (Syntax.Name (Names.predeclared_ordinary Names.PComplex)) [ VNAME "x" ] ] ]). Proof. reject. Qed.

Lemma reader_index : AN.res_index (rres rprobe) = AN.res_index (AN.analyze rprobe).
Proof. obs_eq rprobe. Qed.

Lemma reader_len :
  Datatypes.length (AN.result_fact_list (rres rprobe))
  = Datatypes.length (AN.result_fact_list (AN.analyze rprobe)).
Proof. obs_eq rprobe. Qed.

(* substitution-resistance: a rejected program admits no capability, so no rebuilt Result can back one *)
Definition no_program_for_rejected (p : Syntax.Program) (cp : Compilable.Program p) (Hrej : Compilable.rejects p) : False.
Proof. unfold Compilable.rejects in Hrej. rewrite (Compilable.program_forces_compiled cp) in Hrej. discriminate. Qed.

Definition c_neg_int8_core :
  RP.result_cause_views (rres (prog [ PL [ NEG (CONV Names.PInt8 (ILIT 1)) ] ])) = [] /\ RP.result_req_views (rres (prog [ PL [ NEG (CONV Names.PInt8 (ILIT 1)) ] ])) = [].
Proof. split; obs_direct (prog [ PL [ NEG (CONV Names.PInt8 (ILIT 1)) ] ]). Qed.

(* the fixed main is a zero-parameter function: a zero-argument main() call succeeds as a known zero-result call *)
Definition c_main_recursive : Compilable.compiles (prog [ Syntax.ExprStmt (APP (OID "main") []) ]). Proof. compileok. Qed.

(* the invalidity is the exact application-family MainArity cause, read via the bp-free cause view (vm-cheap) *)
Definition r_main_arity_payload :
  RP.result_cause_views (rres (prog [ Syntax.ExprStmt (APP (OID "main") [ILIT 1]) ])) = [ RP.CvMainArity ].
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (OID "main") [ILIT 1]) ]). Qed.

(* an occurrence diagnostic retains its exact family, a value invalidity projecting as FamValue (bp-free view) *)
Definition r_iota_family :
  RP.result_diag_families (rres (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ] ])) = [ AN.FamValue ].
Proof. obs_direct (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ] ]). Qed.

(* a boundary retains its own exact family too, projected bp-free from the one retained row *)
Definition o_cx_typed_family : exists f,
  RP.result_bound_families (rres (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat32 (ILIT 2)) ] ])) = [ f ].
Proof. eexists; obs_direct (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat32 (ILIT 2)) ] ]). Qed.

(* §22.1/22.2 a legal println application: its statement row is SOK and its application row is AOK — no invalid cause *)
Definition c_println_legal : Compilable.compiles (prog [ PL [ ILIT 1 ] ]). Proof. compileok. Qed.

Definition mf_println_legal_no_cause :
  RP.result_cause_views (rres (prog [ PL [ ILIT 1 ] ])) = [] /\ RP.result_req_views (rres (prog [ PL [ ILIT 1 ] ])) = [].
Proof. split; obs_direct (prog [ PL [ ILIT 1 ] ]). Qed.

Definition r_main_const_redecl_payload :
  (match dsites (prog_tops [ tconstmain ; main0 ]) with
   | [ d ] => match RP.diag_group_name d with Some nm => Names.ordinary_equalb nm (OID "main") | None => false end
   | _ => false end) = true.
Proof.
  assert (H : map RP.diag_group_name (dsites (prog_tops [ tconstmain ; main0 ])) = [ Some (OID "main") ]).
  { unfold dsites.
    assert (Hc : AN.collision_rows (rres (prog_tops [ tconstmain ; main0 ])) = []) by (apply (proj1 (AN.dnc_iff _)); obs_seal (prog_tops [ tconstmain ; main0 ])).
    assert (Hm : AN.main_rows (rres (prog_tops [ tconstmain ; main0 ])) = []) by (apply (proj1 (AN.dnm_iff _)); obs_seal (prog_tops [ tconstmain ; main0 ])).
    assert (Ho : AN.occ_diags (rres (prog_tops [ tconstmain ; main0 ])) = []) by (apply (proj1 (AN.dncause_iff _)); obs_seal (prog_tops [ tconstmain ; main0 ])).
    rewrite (AN.diagnostics_order (rres (prog_tops [ tconstmain ; main0 ]))), Hc, Hm, Ho. rewrite ?app_nil_l, ?app_nil_r.
    unfold AN.group_rows; rewrite map_map.
    erewrite (map_ext _ (fun rr => Some (projT1 rr))) by (intro rr; reflexivity).
    unfold rres, result_of_compile, AN.res_binds, AN.res_bind_data, AN.res_surface, AN.res_index.
    rewrite (Compilable.compile_observe_data (prog_tops [ tconstmain ; main0 ])). vm_compute. reflexivity. }
  destruct (dsites (prog_tops [ tconstmain ; main0 ])) as [|d0 [|d1 r1]]; cbn in H; try discriminate H.
  injection H as Hd0. cbn. rewrite Hd0. reflexivity.
Qed.

(* (d) no fixed main, an ordinary const main: MainMissing, so the missing-entry diagnostic Rejects *)
Definition r_main_missing : Compilable.rejects (prog_tops [ tconstmain ]). Proof. reject. Qed.

(* the one shared cluster computation: the issue list and view list of p_two_iota computed once, observed thrice *)
Definition two_iota_obs :
  (let is := AN.result_issues (rres p_two_iota) in
   let vs := RP.result_cause_views (rres p_two_iota) in
   (Datatypes.length is, map AN.issue_class is, vs))
  = (2%nat,
     [ AN.ClassDiagnostic ; AN.ClassDiagnostic ],
     [ RP.CvInvalidIdentity Names.PIota ; RP.CvInvalidIdentity Names.PIota ]).
Proof.
  assert (Hcls : map AN.issue_class (AN.result_issues (rres p_two_iota)) = [ AN.ClassDiagnostic ; AN.ClassDiagnostic ]) by (obs_issue_classes p_two_iota).
  assert (Hvs : RP.result_cause_views (rres p_two_iota) = [ RP.CvInvalidIdentity Names.PIota ; RP.CvInvalidIdentity Names.PIota ]) by (obs_direct p_two_iota).
  assert (Hlen : Datatypes.length (AN.result_issues (rres p_two_iota)) = 2%nat) by (rewrite <- (length_map AN.issue_class), Hcls; reflexivity).
  cbn zeta. rewrite Hlen, Hcls, Hvs. reflexivity.
Qed.
(* two same-cause invalidities stay two distinct diagnostic-class issues in source order — no dedup, no collapse *)
Definition d4_two_iota_no_collapse :
  Datatypes.length (AN.result_issues (rres p_two_iota)) = 2%nat
  /\ map AN.issue_class (AN.result_issues (rres p_two_iota)) = [ AN.ClassDiagnostic ; AN.ClassDiagnostic ].
Proof.
  split.
  - exact (f_equal (fun '(n, _, _) => n) two_iota_obs).
  - exact (f_equal (fun '(_, m, _) => m) two_iota_obs).
Qed.

(* the two issues carry the SAME cause yet occupy distinct ordinals: shared cause never merges them *)
Definition d4_two_iota_same_cause :
  RP.result_cause_views (rres p_two_iota)
  = [ RP.CvInvalidIdentity Names.PIota ; RP.CvInvalidIdentity Names.PIota ].
Proof. exact (f_equal (fun '(_, _, v) => v) two_iota_obs). Qed.

(* ordinal 0 names an exact retained row: the first issue is a diagnostic; its cause view is CvInvalidIdentity *)
Definition d4_ord0_is_first_diagnostic :
  (match nth_error (AN.result_issues (rres p_two_iota)) 0%nat with Some (AN.IDiag _) => True | _ => False end)
  /\ hd_error (RP.result_cause_views (rres p_two_iota)) = Some (RP.CvInvalidIdentity Names.PIota).
Proof.
  split.
  - pose proof (f_equal (fun '(_, m, _) => m) two_iota_obs) as Hm; cbv beta iota zeta in Hm.
    destruct (AN.result_issues (rres p_two_iota)) as [|i rest]; [ discriminate Hm | ].
    cbn in Hm |- *. injection Hm as Hc _.
    destruct i as [d|b]; [ exact I | ].
    cbn in Hc. discriminate Hc.
  - pose proof (f_equal (fun '(_, _, v) => v) two_iota_obs) as Hv; cbv beta iota zeta in Hv.
    rewrite Hv. reflexivity.
Qed.

Lemma mm17_1_missing_view : map RP.mmv_exec (pmissing (prog_tops [ tconstmain ])) = [ "generated"%string ].
Proof.
  unfold pmissing, ppkg. rewrite map_map.
  change (map (fun mmr => PI.default_exec_name (AN.mmr_package mmr)) (AN.result_missing_main_refs (rres (prog_tops [ tconstmain ]))) = [ "generated"%string ]).
  rewrite <- (map_map AN.mmr_package PI.default_exec_name), AN.missing_main_packages.
  unfold rres, result_of_compile, AN.is_missing, AN.result_package_rule, AN.res_binds, AN.res_surface, AN.res_bind_data, AN.res_index.
  rewrite (Compilable.compile_observe_data (prog_tops [ tconstmain ])). vm_compute. reflexivity.
Qed.

(* §17.6 coexistence: p_collision's package has both a collision AND no fixed main, as two distinct cases *)
Lemma mm17_6_coexist :
  andb (match AN.result_collision_ref (ppkg p_collision) with Some _ => true | None => false end)
       (Nat.ltb 0 (Datatypes.length (AN.result_missing_main_refs (ppkg p_collision)))) = true.
Proof.
  unfold ppkg. apply andb_true_intro. split.
  - destruct (AN.result_collision_ref (rres p_collision)) as [cr|] eqn:Hcr; [ reflexivity | ].
    exfalso. apply AN.collision_ref_none in Hcr. revert Hcr.
    unfold rres, result_of_compile, AN.result_preflight, AN.res_pkg, AN.res_binds, AN.res_bind_data, AN.res_surface, AN.res_index.
    rewrite (Compilable.compile_observe_data p_collision). discriminate.
  - rewrite <- (length_map AN.mmr_package), AN.missing_main_packages.
    unfold rres, result_of_compile, AN.is_missing, AN.result_package_rule, AN.res_binds, AN.res_surface, AN.res_bind_data, AN.res_index.
    rewrite (Compilable.compile_observe_data p_collision). vm_compute. reflexivity.
Qed.

Definition dr_stmt_lit    : Compilable.rejects dp_stmt_lit.    Proof. reject. Qed.

Definition dr_short_dup      : Compilable.rejects dp_short_dup.      Proof. reject. Qed.

Definition dr_short_nonew    : Compilable.rejects dp_short_nonew.    Proof. reject. Qed.

Definition dr_short_allblank : Compilable.rejects dp_short_allblank. Proof. reject. Qed.
