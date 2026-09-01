(* WitnessReject shared basis: notations, programs, readers and tactics the chunks consume; no proofs live here. *)

From Stdlib Require Import List NArith ZArith String.

From Fido Require Import Integer Float Collections FilePath ModulePath Version Names Syntax Index Compilable Compilable.PackageIdentity Compilable.Bindings Compilable.Analysis Compilable.Report Render Emit.

Import ListNotations.

Module PI := Compilable.PackageIdentity.

Module BN := Compilable.Bindings.

Module AN := Compilable.Analysis.

Module RP := Compilable.Report.

Notation PL args := (Syntax.ExprStmt (Syntax.Application (Syntax.Name (Names.predeclared_ordinary Names.PPrintln)) args)).
Notation NEG e := (Syntax.Unary Syntax.UnaryMinus e).
Notation ILIT n := (Syntax.LiteralExpr (Syntax.IntegerLiteral n)).
Notation SLIT s := (Syntax.LiteralExpr (Syntax.StringLiteral s)).
Notation CONV t e := (Syntax.Application (Syntax.Name (Names.predeclared_ordinary t)) [e]).
Notation CPLX re im := (Syntax.Application (Syntax.Name (Names.predeclared_ordinary Names.PComplex)) [re; im]).
Notation APP h args := (Syntax.Application (Syntax.Name h) args).
Notation TT := (Syntax.Name (Names.predeclared_ordinary Names.PTrue)).
Notation FF := (Syntax.Name (Names.predeclared_ordinary Names.PFalse)).

Definition rmod : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Go1_23.

Definition rmain : FilePath.T := FilePath.Make "main.go" eq_refl.

Definition prog (body : list Syntax.Stmt) : Syntax.Program :=
  singleton_program rmod rmain [ Syntax.Main (Syntax.MakeBlock body) ].

(* each disposition crosses the seal via disposition_observe_data, then computes the transparent right side *)
Ltac reject    := unfold Compilable.rejects;  rewrite Compilable.disposition_observe_data; vm_compute; reflexivity.

Ltac compileok := unfold Compilable.compiles; rewrite Compilable.disposition_observe_data; vm_compute; reflexivity.

Ltac outside   := unfold Compilable.outsides; rewrite Compilable.disposition_observe_data; vm_compute; reflexivity.

Notation OID s := (Names.MakeOrdinary (Names.MakeIdentifier s eq_refl) eq_refl).
Notation VNAME s := (Syntax.Name (OID s)).
Notation NE1 x := (Collections.MakeNonEmpty x nil).

(* §19 the concrete reader IS compile's branch-carried Result: outcome_result reads compile's exact type index *)
Definition result_of_compile (p : Syntax.Program) : AN.Result p := Compilable.outcome_result (Compilable.compile p).

Definition rres (p : Syntax.Program) : AN.Result p := result_of_compile p.

(* §R.5 permanent VM controls: the branch-carried reader reduces to the exact data cheaply, like a direct analyze *)
Definition rprobe : Syntax.Program := prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ] ].

(* the diagnostic ROWS themselves; each row already retains its exact subject, family, and cause at construction *)
Definition dsites (p : Syntax.Program) := AN.result_diagnostics (rres p).

(* the raw occurrence facts of a program, for the dependent-non-result checks *)
Definition pfacts (p : Syntax.Program) := AN.result_fact_list (rres p).

(* §R.5 the public reader over the Compiled and OutsideScope branches too: the branch-carried index is exact, cheap *)
Definition cprobe : Syntax.Program := prog [ PL [ ILIT 1 ] ].

Definition oprobe : Syntax.Program := prog [ PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat32 (ILIT 2)) ] ].

(* observation-level provenance: the branch reader observes the one canonical analysis data, the sole bridge *)
Definition rres_observe (p : Syntax.Program) : AN.data_of_result (rres p) = AN.result_data p :=
  Compilable.compile_observe_data p.

(* direct data-level views: expose data_of_result through the view wrappers, cross the seal once, compute *)
Ltac obs_direct p := try unfold pfacts; try unfold dsites; unfold rres, result_of_compile;
  try unfold RP.result_cause_views; try unfold RP.result_req_views;
  try unfold RP.result_diag_families; try unfold RP.result_bound_families; try unfold RP.result_fact_views;
  unfold AN.result_fact_list, AN.res_facts, AN.res_binds, AN.res_bind_data, AN.res_surface, AN.res_index;
  rewrite (Compilable.compile_observe_data p); vm_compute; reflexivity.

(* a disposition equality via the sole disposition bridge *)
Ltac obs_disp := rewrite Compilable.disposition_observe_data; vm_compute; reflexivity.

(* the one canonical computed observation of a program: disposition + complete fact list + diagnostics + boundaries *)
Record UcObs := mk_uc_obs {
  uc_disp : Compilable.Disposition ;
  uc_facts : list RP.FactView ;
  uc_causes : list RP.CauseView ;
  uc_reqs : list RP.ReqView
}.
Definition uc_obs {p} (r : AN.Result p) : UcObs :=
  mk_uc_obs (Compilable.disposition_of r) (RP.result_fact_views r) (RP.result_cause_views r) (RP.result_req_views r).
(* prove one uc_obs record: cross the seal once, then compute the whole record in a single vm_compute *)
Ltac obs_uc p := unfold uc_obs, Compilable.disposition_of, Compilable.disposition_from_data,
  rres, result_of_compile, RP.result_fact_views, RP.result_cause_views, RP.result_req_views,
  AN.result_fact_list, AN.res_facts, AN.res_binds, AN.res_bind_data, AN.res_surface, AN.res_index;
  rewrite !(Compilable.compile_observe_data p); vm_compute; reflexivity.

(* a reader-vs-analyze equality: cross the seal on both sides, then reflexivity *)
Ltac obs_eq p := try unfold pfacts; unfold rres, result_of_compile;
  try unfold AN.result_fact_list; unfold AN.res_facts, AN.res_binds, AN.res_bind_data, AN.res_surface, AN.res_index;
  rewrite (Compilable.compile_observe_data p), (AN.analyze_observe_data p); vm_compute; reflexivity.

(* cross the seal on a data-level goal and compute, for the emptiness premises *)
Ltac obs_seal p := unfold rres, result_of_compile, AN.data_no_collision, AN.data_no_missing, AN.data_no_redecl,
  AN.data_no_cause, AN.data_no_req, AN.res_facts, AN.res_pkg, AN.res_binds, AN.res_bind_data, AN.res_surface, AN.res_index in *;
  rewrite (Compilable.compile_observe_data p); vm_compute; reflexivity.

(* collapse map over the occurrence rows to a data-level flat_map over result_fact_list via fact_rows_rows *)
Ltac occ_diag_collapse p := unfold AN.occ_diags;
  rewrite flat_map_concat_map, concat_map, map_map;
  set (gd := fun o : AN.OccFact (AN.res_binds (rres p)) => match AN.occ_cause o with Some _ => [AN.ClassDiagnostic] | None => (@nil AN.IssueClass) end);
  erewrite (map_ext _ (fun ref => gd (AN.frr_row ref)))
    by (let a := fresh "a" in intro a; subst gd; cbn beta; destruct (AN.occ_cause (AN.frr_row a)) as [c|] eqn:E;
        [ destruct (AN.occ_diag_complete _ _ _ E) as [ifr [Hr _]]; rewrite Hr; reflexivity
        | rewrite (AN.occ_diag_none _ _ E); reflexivity ]);
  rewrite <- (map_map AN.frr_row gd), AN.fact_rows_rows; subst gd.
Ltac occ_bound_collapse p := unfold AN.result_boundaries;
  rewrite flat_map_concat_map, concat_map, map_map;
  set (gb := fun o : AN.OccFact (AN.res_binds (rres p)) => match AN.occ_req o with Some _ => [AN.ClassBoundary] | None => (@nil AN.IssueClass) end);
  erewrite (map_ext _ (fun ref => gb (AN.frr_row ref)))
    by (let a := fresh "a" in intro a; subst gb; cbn beta; destruct (AN.occ_req (AN.frr_row a)) as [q|] eqn:E;
        [ destruct (AN.occ_bound_complete _ _ _ E) as [ufr [Hr _]]; rewrite Hr; reflexivity
        | rewrite (AN.occ_bound_none _ _ E); reflexivity ]);
  rewrite <- (map_map AN.frr_row gb), AN.fact_rows_rows; subst gb.

(* issue classes: class-split, kill package/collision/group rows via d*_iff, collapse occurrences, compute *)
Ltac obs_issue_classes p :=
  rewrite AN.result_issues_class_split, map_app, !map_map; cbn [AN.issue_class];
  assert (Hc : AN.collision_rows (rres p) = []) by (apply (proj1 (AN.dnc_iff _)); obs_seal p);
  assert (Hm : AN.main_rows (rres p) = []) by (apply (proj1 (AN.dnm_iff _)); obs_seal p);
  assert (Hg : AN.group_rows (rres p) = []) by (apply (proj1 (AN.dnr_iff _)); obs_seal p);
  rewrite (AN.diagnostics_order (rres p)), Hc, Hm, Hg; cbn [app];
  occ_diag_collapse p; occ_bound_collapse p;
  unfold rres, result_of_compile, AN.result_fact_list, AN.res_facts, AN.res_binds, AN.res_bind_data, AN.res_surface, AN.res_index;
  rewrite (Compilable.compile_observe_data p); vm_compute; reflexivity.

(* a use of the redeclared name folds into the one group row named "x"; exact contexts + soundness are §24.4 laws *)
Definition p_redecl_use : Syntax.Program :=
  prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ; Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "y"))) (NE1 (VNAME "x")) ].

(* §22.6 same-site multi-family: an application node owns both an Application-kind and a Value-kind fact at one site *)
Definition p_app_multi : Syntax.Program := prog [ Syntax.ExprStmt (APP (OID "main") []) ].

(* Rob's four fixed-main / declaration-group combinations: main participates in the ONE (scope, spelling) group *)
Definition prog_tops (tops : list Syntax.TopLevelDecl) : Syntax.Program := singleton_program rmod rmain tops.

Definition main0 : Syntax.TopLevelDecl := Syntax.Main (Syntax.MakeBlock []).

Definition tconstmain : Syntax.TopLevelDecl :=
  Syntax.TopDeclaration (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "main"))) (Syntax.ExplicitConstInit None (NE1 (ILIT 1))) ]).

(* exact issue identity: the ordinal-indexed sequence never collapses distinct issues and partitions by class *)
Definition p_two_iota : Syntax.Program :=
  prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ]
       ; PL [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ] ].

(* an invalidity and an independent unsupported boundary coexist: one diagnostic-class and one boundary-class issue *)
Definition p_invalid_unsupported : Syntax.Program :=
  prog [ PL [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ]
       ; PL [ CPLX (CONV Names.PFloat32 (ILIT 1)) (CONV Names.PFloat32 (ILIT 2)) ] ].

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

Definition p_collision_redecl : Syntax.Program :=
  match Syntax.build_program rmod
          [ Syntax.MakeFileNode rmain (Syntax.main_source [ cvar1 ; cvar2 ])
          ; Syntax.MakeFileNode cgen_path (Syntax.MakeFile Syntax.MainPackage [] []) ] with
  | Some pp => pp | None => empty_program rmod end.

(* §17 the exact package-case refs over the branch-carried pf are vm-cheap and exact, read through bp-free views *)
Definition ppkg (pp : Syntax.Program) := rres pp.

Definition pmissing (pp : Syntax.Program) := map RP.missing_main_view (AN.result_missing_main_refs (ppkg pp)).

Definition pcollision (pp : Syntax.Program) := option_map RP.collision_view (AN.result_collision_ref (ppkg pp)).

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

(* §17 the five newly-decided short-declaration rejections, each a whole program pinned Go also rejects *)
Definition dp_short_dup      : Syntax.Program := prog [ Syntax.ShortVarDecl (Collections.MakeNonEmpty (Syntax.BNamed (OID "x")) [Syntax.BNamed (OID "x")]) (Collections.MakeNonEmpty (ILIT 1) [ILIT 2]) ].

Definition dp_short_count    : Syntax.Program := prog [ Syntax.ShortVarDecl (Collections.MakeNonEmpty (Syntax.BNamed (OID "x")) [Syntax.BNamed (OID "y")]) (NE1 (ILIT 1)) ].

Definition dp_short_nonew    : Syntax.Program := prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "x"))) (NE1 (ILIT 1)) ; Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "x"))) (NE1 (ILIT 2)) ].

Definition dp_short_allblank : Syntax.Program := prog [ Syntax.ShortVarDecl (Collections.MakeNonEmpty Syntax.BBlank [Syntax.BBlank]) (Collections.MakeNonEmpty (ILIT 1) [ILIT 2]) ].

Definition dp_short_nonvar   : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (ILIT 1))) ]) ; Syntax.ShortVarDecl (Collections.MakeNonEmpty (Syntax.BNamed (OID "x")) [Syntax.BNamed (OID "y")]) (Collections.MakeNonEmpty (ILIT 2) [ILIT 3]) ].
