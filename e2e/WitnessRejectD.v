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
Proof. obs_disp. Qed.

Lemma reader_disp_compiled : Compilable.disposition cprobe = Compilable.Compiled. Proof. obs_disp. Qed.

Lemma reader_index_compiled : AN.res_index (rres cprobe) = AN.res_index (AN.analyze cprobe). Proof. obs_eq cprobe. Qed.

Lemma reader_index_outside : AN.res_index (rres oprobe) = AN.res_index (AN.analyze oprobe). Proof. obs_eq oprobe. Qed.

(* payload catalogue via the bp-free Report views: goal types carry no BindingPhase, so vm_compute stays cheap *)
Definition r_iota_cause :
  RP.result_cause_views (rres (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ] ])) = [ RP.CvInvalidIdentity Names.PIota ].
Proof. obs_direct (prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ] ]). Qed.

Definition o_cx_typed_payload :
  RP.result_cause_views (rres (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat32 (ILIT 2)) ] ])) = []
  /\ RP.result_req_views (rres (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat32 (ILIT 2)) ] ])) = [ RP.RvComplexType ].
Proof. split; obs_direct (prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat32 (ILIT 2)) ] ]). Qed.

Definition r_main_as_type : Compilable.rejects (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarTypeOnly (Syntax.NamedType (OID "main"))) ]) ]). Proof. reject. Qed.

(* a local main shadows the package main through the ordinary block rule *)
Definition o_main_shadowed : Compilable.outsides (prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "main"))) (NE1 (ILIT 1)) ; PL [ VNAME "main" ] ]). Proof. outside. Qed.

(* the one diagnostic is a redeclared-group row over the group spelled "x" (cause RedeclaredGroupCause) *)
Definition r_redecl_payload :
  (match dsites (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ]) with
   | [ d ] => match RP.diag_group_name d with Some nm => Names.ordinary_equalb nm (OID "x") | None => false end
   | _ => false
   end) = true.
Proof.
  assert (H : map RP.diag_group_name (dsites (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ])) = [ Some (OID "x") ]).
  { unfold dsites.
    assert (Hc : AN.collision_rows (rres (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ])) = []) by (apply (proj1 (AN.dnc_iff _)); obs_seal (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ])).
    assert (Hm : AN.main_rows (rres (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ])) = []) by (apply (proj1 (AN.dnm_iff _)); obs_seal (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ])).
    assert (Ho : AN.occ_diags (rres (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ])) = []) by (apply (proj1 (AN.dncause_iff _)); obs_seal (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ])).
    rewrite (AN.diagnostics_order (rres (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ]))), Hc, Hm, Ho. rewrite ?app_nil_l, ?app_nil_r.
    unfold AN.group_rows; rewrite map_map.
    erewrite (map_ext _ (fun rr => Some (projT1 rr))) by (intro rr; reflexivity).
    unfold rres, result_of_compile, AN.res_binds, AN.res_bind_data, AN.res_surface, AN.res_index.
    rewrite (Compilable.compile_observe_data (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ])). vm_compute. reflexivity. }
  destruct (dsites (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ])) as [|d0 [|d1 r1]]; cbn in H; try discriminate H.
  injection H as Hd0. cbn. rewrite Hd0. reflexivity.
Qed.

(* §332 an unbound application head is an unresolved-application-head on the app row, a diagnostic *)
Definition r_unbound_app_dep :
  existsb (fun f => match f with AN.OFApp _ (AN.AInvalid (AN.UnresolvedApplicationHead _ _ _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (OID "undefined") []) ])) = true.
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (OID "undefined") []) ]). Qed.

(* an expr-statement whose expr owns an issue is a dependent non-result, never a successful statement *)
Definition r_child_stmt_dep :
  existsb (fun f => match f with AN.OFStmt _ (AN.SDependent _) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PIota) []) ])) = true.
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PIota) []) ]). Qed.

(* a redeclared name used as a type is a dependent non-result, never a fabricated Bool type *)
Definition r_redecl_type_dep :
  existsb (fun f => match f with AN.OFType _ (AN.TDependent _) => true | _ => false end)
          (pfacts (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "y"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "y"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "z"))) (Syntax.VarTypeOnly (Syntax.NamedType (OID "y"))) ]) ])) = true.
Proof. obs_direct (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "y"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "y"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "z"))) (Syntax.VarTypeOnly (Syntax.NamedType (OID "y"))) ]) ]). Qed.

(* (a) one fixed main, no competitor -> unique group + MainOne -> Compiled *)
Definition c_main_only : Compilable.compiles (prog_tops [ main0 ]). Proof. compileok. Qed.

(* (c) multiple fixed mains: a redeclared group through the one authority, no first-main pick, so Rejected *)
Definition r_main_multiple : Compilable.rejects (prog_tops [ main0 ; main0 ]). Proof. reject. Qed.

Definition r_main_multiple_payload :
  (match dsites (prog_tops [ main0 ; main0 ]) with
   | [ d ] => match RP.diag_group_name d with Some nm => Names.ordinary_equalb nm (OID "main") | None => false end
   | _ => false end) = true.
Proof.
  assert (H : map RP.diag_group_name (dsites (prog_tops [ main0 ; main0 ])) = [ Some (OID "main") ]).
  { unfold dsites.
    assert (Hc : AN.collision_rows (rres (prog_tops [ main0 ; main0 ])) = []) by (apply (proj1 (AN.dnc_iff _)); obs_seal (prog_tops [ main0 ; main0 ])).
    assert (Hm : AN.main_rows (rres (prog_tops [ main0 ; main0 ])) = []) by (apply (proj1 (AN.dnm_iff _)); obs_seal (prog_tops [ main0 ; main0 ])).
    assert (Ho : AN.occ_diags (rres (prog_tops [ main0 ; main0 ])) = []) by (apply (proj1 (AN.dncause_iff _)); obs_seal (prog_tops [ main0 ; main0 ])).
    rewrite (AN.diagnostics_order (rres (prog_tops [ main0 ; main0 ]))), Hc, Hm, Ho. rewrite ?app_nil_l, ?app_nil_r.
    unfold AN.group_rows; rewrite map_map.
    erewrite (map_ext _ (fun rr => Some (projT1 rr))) by (intro rr; reflexivity).
    unfold rres, result_of_compile, AN.res_binds, AN.res_bind_data, AN.res_surface, AN.res_index.
    rewrite (Compilable.compile_observe_data (prog_tops [ main0 ; main0 ])). vm_compute. reflexivity. }
  destruct (dsites (prog_tops [ main0 ; main0 ])) as [|d0 [|d1 r1]]; cbn in H; try discriminate H.
  injection H as Hd0. cbn. rewrite Hd0. reflexivity.
Qed.

(* the output collision and a redeclared group coexist as distinct diagnostics through the one authority *)
Definition d4_collision_redeclared_coexist :
  andb (existsb (fun d => match d with AN.DOutputCollision _ => true | _ => false end) (dsites p_collision_redecl))
       (existsb (fun d => match d with AN.DRedeclaredGroup _ => true | _ => false end) (dsites p_collision_redecl)) = true.
Proof.
  apply andb_true_intro. split.
  - destruct (AN.result_collision_ref (rres p_collision_redecl)) as [cr|] eqn:Hcr.
    2:{ exfalso. apply AN.collision_ref_none in Hcr. revert Hcr.
        unfold rres, result_of_compile, AN.result_preflight, AN.res_pkg, AN.res_binds, AN.res_bind_data, AN.res_surface, AN.res_index.
        rewrite (Compilable.compile_observe_data p_collision_redecl). vm_compute. discriminate. }
    apply existsb_exists. exists (AN.DOutputCollision cr). split; [ | reflexivity ].
    unfold dsites. rewrite (AN.diagnostics_order (rres p_collision_redecl)).
    apply in_or_app. left. unfold AN.collision_rows. rewrite Hcr. left. reflexivity.
  - assert (Hgr : AN.group_rows (rres p_collision_redecl) <> []).
    { intro Hnil. apply (proj2 (AN.dnr_iff _)) in Hnil. revert Hnil.
      unfold rres, result_of_compile, AN.data_no_redecl, AN.res_binds, AN.res_bind_data, AN.res_surface, AN.res_index.
      rewrite (Compilable.compile_observe_data p_collision_redecl). vm_compute. discriminate. }
    destruct (AN.group_rows (rres p_collision_redecl)) as [|g0 grest] eqn:Hg; [ exfalso; exact (Hgr eq_refl) | ].
    apply existsb_exists. exists g0. split.
    + unfold dsites. rewrite (AN.diagnostics_order (rres p_collision_redecl)).
      apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. rewrite Hg. left. reflexivity.
    + revert Hg. unfold AN.group_rows.
      destruct (AN.BN.redeclaration_roots (AN.res_binds (rres p_collision_redecl))) as [|r0 rr]; [ discriminate | ].
      intro Hg. injection Hg as Hg0 _. subst g0. reflexivity.
Qed.

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

(* §17.4 an exact output collision retains the exact package+root: the collision view names the colliding entry *)
Lemma mm17_4_collision_view : option_map RP.cv_root (pcollision p_collision) = Some "generated"%string.
Proof.
  unfold pcollision, ppkg.
  destruct (AN.result_collision_ref (rres p_collision)) as [cr|] eqn:Hcr.
  - cbn [option_map]. f_equal.
    destruct (RP.collision_view_exact cr) as [_ Hcvr]. rewrite Hcvr.
    transitivity (match AN.result_preflight (rres p_collision) with
                  | AN.FreshCollision _ rr => PI.re_name rr | AN.FreshOk => ""%string end).
    + rewrite (AN.collision_case _ cr); reflexivity.
    + unfold rres, result_of_compile, AN.result_preflight, AN.res_pkg, AN.res_binds, AN.res_bind_data, AN.res_surface, AN.res_index;
      rewrite (Compilable.compile_observe_data p_collision); vm_compute; reflexivity.
  - exfalso. apply AN.collision_ref_none in Hcr. revert Hcr.
    unfold rres, result_of_compile, AN.result_preflight, AN.res_pkg, AN.res_binds, AN.res_bind_data, AN.res_surface, AN.res_index;
    rewrite (Compilable.compile_observe_data p_collision); vm_compute; discriminate.
Qed.

Definition dr_default_ovf : Compilable.rejects dp_default_ovf. Proof. reject. Qed.

Definition dr_multi_main  : Compilable.rejects dp_multi_main.  Proof. reject. Qed.

Definition dc_ok          : Compilable.compiles dp_ok.         Proof. compileok. Qed.
