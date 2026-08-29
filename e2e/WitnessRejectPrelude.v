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

(* each branch is decided through the production authority: the transparent [disposition], reduced by computation *)
Ltac reject    := vm_compute; reflexivity.

Ltac compileok := vm_compute; reflexivity.

Ltac outside   := vm_compute; reflexivity.

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

(* provenance: whatever branch a program yields, its projected result IS the exact Result these fixtures read *)
Definition retained_via_program  {p} (cp : Compilable.Program p)   : Compilable.program_result cp  = rres p := Compilable.program_result_canonical cp.

Definition retained_via_rejection {p} (r  : Compilable.Rejection p) : Compilable.rejection_result r = rres p := Compilable.rejection_result_canonical r.

Definition retained_via_outside   {p} (o  : Compilable.Outside p)   : Compilable.outside_result o  = rres p := Compilable.outside_result_canonical o.

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
