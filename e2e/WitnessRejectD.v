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
(* uc_case_01 = primary matrix row 1: println(main()) is Rejected with NoValueUsed on the inner main app *)
Definition uc01_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ APP (OID "main") [] ]) ].
Definition uc_case_01 : uc_obs (rres uc01_prog) = mk_uc_obs Compilable.Rejected [ RP.FvOK AN.FamStatement; RP.FvOK AN.FamApplication; RP.FvNonconst AN.FamValue; RP.FvOK AN.FamApplication; RP.FvInvalid AN.FamValue RP.CvNoValueUsed ] [ RP.CvNoValueUsed ] [].
Proof. obs_uc uc01_prog. Qed.
Definition uc02_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (OID "main") []) ].
Definition uc03_prog : Syntax.Program := prog [ Syntax.ExprStmt (Syntax.Application (APP (OID "main") []) []) ].
Definition uc04_prog : Syntax.Program := prog [ Syntax.ExprStmt (Syntax.Application (APP (Names.predeclared_ordinary Names.PPrintln) []) []) ].
Definition uc05_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (APP (OID "main") []))) ]) ].
Definition uc06_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (APP (OID "main") []))) ]) ].
Definition uc07_prog : Syntax.Program := prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "x"))) (NE1 (APP (OID "main") [])) ].
Definition uc08_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (Syntax.Name (Names.predeclared_ordinary Names.PIota)))) ]) ].
Definition uc09_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (NEG (Syntax.Name (Names.predeclared_ordinary Names.PIota))))) ]) ].
Definition uc10_prog : Syntax.Program := prog [ Syntax.ExprStmt (Syntax.Name (Names.predeclared_ordinary Names.PIota)) ].
Definition uc11_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues (Some (Syntax.NamedType (Names.predeclared_ordinary Names.PInt))) (NE1 (Syntax.Name (Names.predeclared_ordinary Names.PIota)))) ]) ].
Definition uc12_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues (Some (Syntax.NamedType (Names.predeclared_ordinary Names.PAny))) (NE1 (Syntax.Name (Names.predeclared_ordinary Names.PNil)))) ]) ].
Definition uc13_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues (Some (Syntax.NamedType (Names.predeclared_ordinary Names.PInt))) (NE1 (Syntax.Name (Names.predeclared_ordinary Names.PNil)))) ]) ].
Definition uc_case_02 : uc_obs (rres uc02_prog) = mk_uc_obs Compilable.Compiled [ RP.FvOK AN.FamStatement; RP.FvOK AN.FamApplication; RP.FvNonconst AN.FamValue ] [] [].
Proof. obs_uc uc02_prog. Qed.
Definition uc_case_03 : uc_obs (rres uc03_prog) = mk_uc_obs Compilable.Rejected [ RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamApplication RP.CvNotCallableExpr; RP.FvNonconst AN.FamValue; RP.FvOK AN.FamApplication; RP.FvInvalid AN.FamValue RP.CvNoValueUsed ] [ RP.CvNotCallableExpr; RP.CvNoValueUsed ] [].
Proof. obs_uc uc03_prog. Qed.
Definition uc_case_04 : uc_obs (rres uc04_prog) = mk_uc_obs Compilable.Rejected [ RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamApplication RP.CvNotCallableExpr; RP.FvNonconst AN.FamValue; RP.FvOK AN.FamApplication; RP.FvInvalid AN.FamValue RP.CvNoValueUsed ] [ RP.CvNotCallableExpr; RP.CvNoValueUsed ] [].
Proof. obs_uc uc04_prog. Qed.
Definition uc_case_05 : uc_obs (rres uc05_prog) = mk_uc_obs Compilable.Rejected [ RP.FvUnmet AN.FamDeclaration RP.RvConstDecl; RP.FvOK AN.FamApplication; RP.FvInvalid AN.FamValue RP.CvNoValueUsed ] [ RP.CvNoValueUsed ] [ RP.RvConstDecl ].
Proof. obs_uc uc05_prog. Qed.
Definition uc_case_06 : uc_obs (rres uc06_prog) = mk_uc_obs Compilable.Rejected [ RP.FvUnmet AN.FamDeclaration RP.RvDeclMeaningV; RP.FvOK AN.FamApplication; RP.FvInvalid AN.FamValue RP.CvNoValueUsed ] [ RP.CvNoValueUsed ] [ RP.RvDeclMeaningV ].
Proof. obs_uc uc06_prog. Qed.
Definition uc_case_07 : uc_obs (rres uc07_prog) = mk_uc_obs Compilable.Rejected [ RP.FvDependent AN.FamDeclaration RP.DvChild; RP.FvOK AN.FamApplication; RP.FvInvalid AN.FamValue RP.CvNoValueUsed ] [ RP.CvNoValueUsed ] [].
Proof. obs_uc uc07_prog. Qed.
Definition uc_case_08 : uc_obs (rres uc08_prog) = mk_uc_obs Compilable.OutsideScope [ RP.FvUnmet AN.FamDeclaration RP.RvConstDecl; RP.FvUnmet AN.FamValue (RP.RvInitializerIdentity Names.PIota) ] [] [ RP.RvConstDecl; RP.RvInitializerIdentity Names.PIota ].
Proof. obs_uc uc08_prog. Qed.
Definition uc_case_09 : uc_obs (rres uc09_prog) = mk_uc_obs Compilable.OutsideScope [ RP.FvUnmet AN.FamDeclaration RP.RvConstDecl; RP.FvNonconst AN.FamValue; RP.FvUnmet AN.FamValue (RP.RvInitializerIdentity Names.PIota) ] [] [ RP.RvConstDecl; RP.RvInitializerIdentity Names.PIota ].
Proof. obs_uc uc09_prog. Qed.
Definition uc_case_10 : uc_obs (rres uc10_prog) = mk_uc_obs Compilable.Rejected [ RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamValue (RP.CvInvalidIdentity Names.PIota) ] [ RP.CvInvalidIdentity Names.PIota ] [].
Proof. obs_uc uc10_prog. Qed.
Definition uc_case_11 : uc_obs (rres uc11_prog) = mk_uc_obs Compilable.Rejected [ RP.FvUnmet AN.FamDeclaration RP.RvDeclMeaningV; RP.FvOK AN.FamTypeUse; RP.FvInvalid AN.FamValue (RP.CvInvalidIdentity Names.PIota) ] [ RP.CvInvalidIdentity Names.PIota ] [ RP.RvDeclMeaningV ].
Proof. obs_uc uc11_prog. Qed.
Definition uc_case_12 : uc_obs (rres uc12_prog) = mk_uc_obs Compilable.OutsideScope [ RP.FvUnmet AN.FamDeclaration RP.RvDeclMeaningV; RP.FvUnmet AN.FamTypeUse RP.RvTypeMeaning; RP.FvUnmet AN.FamValue (RP.RvTypedTargetIdentity Names.PNil) ] [] [ RP.RvDeclMeaningV; RP.RvTypeMeaning; RP.RvTypedTargetIdentity Names.PNil ].
Proof. obs_uc uc12_prog. Qed.
Definition uc_case_13 : uc_obs (rres uc13_prog) = mk_uc_obs Compilable.OutsideScope [ RP.FvUnmet AN.FamDeclaration RP.RvDeclMeaningV; RP.FvOK AN.FamTypeUse; RP.FvUnmet AN.FamValue (RP.RvTypedTargetIdentity Names.PNil) ] [] [ RP.RvDeclMeaningV; RP.RvTypedTargetIdentity Names.PNil ].
Proof. obs_uc uc13_prog. Qed.
Definition uc14_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (Syntax.Name (Names.predeclared_ordinary Names.PNil)))) ]) ].
Definition uc15_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (Syntax.Name (Names.predeclared_ordinary Names.PNil)))) ]) ].
Definition uc16_prog : Syntax.Program := prog [ Syntax.ExprStmt (Syntax.Name (Names.predeclared_ordinary Names.PNil)) ].
Definition uc17_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (ILIT ((2 ^ 63)%N)))) ]) ].
Definition uc18_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit (Some (Syntax.NamedType (Names.predeclared_ordinary Names.PUint64))) (NE1 (ILIT ((2 ^ 63)%N)))) ]) ].
Definition uc19_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues (Some (Syntax.NamedType (Names.predeclared_ordinary Names.PUint64))) (NE1 (ILIT ((2 ^ 63)%N)))) ]) ].
Definition uc20_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (ILIT ((2 ^ 63)%N)))) ]) ].
Definition uc21_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ ILIT ((2 ^ 63)%N) ]) ].
Definition uc22_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PInt) [ ILIT ((2 ^ 63)%N); ILIT ((2 ^ 63)%N) ]) ].
Definition uc23_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PInt) [ Syntax.Name (Names.predeclared_ordinary Names.PNil); Syntax.Name (Names.predeclared_ordinary Names.PNil) ]) ].
Definition uc24_prog : Syntax.Program := prog [ Syntax.ExprStmt (ILIT ((2 ^ 63)%N)) ].
Definition uc25_prog : Syntax.Program := prog [ Syntax.ExprStmt (Syntax.Application (ILIT ((2 ^ 63)%N)) []) ].
Definition uc_case_14 : uc_obs (rres uc14_prog) = mk_uc_obs Compilable.Rejected [ RP.FvUnmet AN.FamDeclaration RP.RvDeclMeaningV; RP.FvInvalid AN.FamValue (RP.CvInvalidIdentity Names.PNil) ] [ RP.CvInvalidIdentity Names.PNil ] [ RP.RvDeclMeaningV ].
Proof. obs_uc uc14_prog. Qed.
Definition uc_case_15 : uc_obs (rres uc15_prog) = mk_uc_obs Compilable.Rejected [ RP.FvUnmet AN.FamDeclaration RP.RvConstDecl; RP.FvInvalid AN.FamValue (RP.CvInvalidIdentity Names.PNil) ] [ RP.CvInvalidIdentity Names.PNil ] [ RP.RvConstDecl ].
Proof. obs_uc uc15_prog. Qed.
Definition uc_case_16 : uc_obs (rres uc16_prog) = mk_uc_obs Compilable.Rejected [ RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamValue (RP.CvInvalidIdentity Names.PNil) ] [ RP.CvInvalidIdentity Names.PNil ] [].
Proof. obs_uc uc16_prog. Qed.
Definition uc_case_17 : uc_obs (rres uc17_prog) = mk_uc_obs Compilable.OutsideScope [ RP.FvUnmet AN.FamDeclaration RP.RvConstDecl; RP.FvUnmet AN.FamValue RP.RvConstNoDefault ] [] [ RP.RvConstDecl; RP.RvConstNoDefault ].
Proof. obs_uc uc17_prog. Qed.
Definition uc_case_18 : uc_obs (rres uc18_prog) = mk_uc_obs Compilable.OutsideScope [ RP.FvUnmet AN.FamDeclaration RP.RvConstDecl; RP.FvOK AN.FamTypeUse; RP.FvUnmet AN.FamValue RP.RvTypedTargetConstant ] [] [ RP.RvConstDecl; RP.RvTypedTargetConstant ].
Proof. obs_uc uc18_prog. Qed.
Definition uc_case_19 : uc_obs (rres uc19_prog) = mk_uc_obs Compilable.OutsideScope [ RP.FvUnmet AN.FamDeclaration RP.RvDeclMeaningV; RP.FvOK AN.FamTypeUse; RP.FvUnmet AN.FamValue RP.RvTypedTargetConstant ] [] [ RP.RvDeclMeaningV; RP.RvTypedTargetConstant ].
Proof. obs_uc uc19_prog. Qed.
Definition uc_case_20 : uc_obs (rres uc20_prog) = mk_uc_obs Compilable.Rejected [ RP.FvUnmet AN.FamDeclaration RP.RvDeclMeaningV; RP.FvInvalid AN.FamValue RP.CvDefaultOverflow ] [ RP.CvDefaultOverflow ] [ RP.RvDeclMeaningV ].
Proof. obs_uc uc20_prog. Qed.
Definition uc_case_21 : uc_obs (rres uc21_prog) = mk_uc_obs Compilable.Rejected [ RP.FvOK AN.FamStatement; RP.FvOK AN.FamApplication; RP.FvNonconst AN.FamValue; RP.FvInvalid AN.FamValue RP.CvDefaultOverflow ] [ RP.CvDefaultOverflow ] [].
Proof. obs_uc uc21_prog. Qed.
Definition uc_case_22 : uc_obs (rres uc22_prog) = mk_uc_obs Compilable.Rejected [ RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamApplication RP.CvConversionArity; RP.FvNonconst AN.FamValue; RP.FvNonconst AN.FamValue; RP.FvNonconst AN.FamValue ] [ RP.CvConversionArity ] [].
Proof. obs_uc uc22_prog. Qed.
Definition uc_case_23 : uc_obs (rres uc23_prog) = mk_uc_obs Compilable.Rejected [ RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamApplication RP.CvConversionArity; RP.FvNonconst AN.FamValue; RP.FvInvalid AN.FamValue (RP.CvInvalidIdentity Names.PNil); RP.FvInvalid AN.FamValue (RP.CvInvalidIdentity Names.PNil) ] [ RP.CvConversionArity; RP.CvInvalidIdentity Names.PNil; RP.CvInvalidIdentity Names.PNil ] [].
Proof. obs_uc uc23_prog. Qed.
Definition uc_case_24 : uc_obs (rres uc24_prog) = mk_uc_obs Compilable.Rejected [ RP.FvInvalid AN.FamStatement RP.CvIllegalStatement; RP.FvNonconst AN.FamValue ] [ RP.CvIllegalStatement ] [].
Proof. obs_uc uc24_prog. Qed.
Definition uc_case_25 : uc_obs (rres uc25_prog) = mk_uc_obs Compilable.Rejected [ RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamApplication RP.CvNotCallableExpr; RP.FvNonconst AN.FamValue; RP.FvDependent AN.FamValue RP.DvHeadInvalid ] [ RP.CvNotCallableExpr ] [].
Proof. obs_uc uc25_prog. Qed.
Definition uc26_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.TypeDecl [ Syntax.AliasSpec (Syntax.BNamed (OID "T")) (Syntax.NamedType (Names.predeclared_ordinary Names.PInt)) ]) ; Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ APP (OID "T") [ ILIT 1 ] ]) ].
Definition uc27_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.TypeDecl [ Syntax.AliasSpec (Syntax.BNamed (OID "A")) (Syntax.NamedType (Names.predeclared_ordinary Names.PAny)) ]) ; Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ APP (OID "A") [ Syntax.Name (Names.predeclared_ordinary Names.PNil) ] ]) ].
Definition uc28_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.TypeDecl [ Syntax.AliasSpec (Syntax.BNamed (OID "U")) (Syntax.NamedType (Names.predeclared_ordinary Names.PUint64)) ]) ; Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ APP (OID "U") [ ILIT ((2 ^ 63)%N) ] ]) ].
Definition uc29_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ APP (Names.predeclared_ordinary Names.PAny) [ Syntax.Name (Names.predeclared_ordinary Names.PNil) ] ]) ].
Definition uc30_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "c"))) (Syntax.ExplicitConstInit None (NE1 (ILIT 1))) ]) ; Syntax.ExprStmt (APP (OID "c") []) ].
Definition uc31_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "c"))) (Syntax.ExplicitConstInit None (NE1 (ILIT 1))) ]) ; Syntax.ExprStmt (APP (OID "c") [ ILIT ((2 ^ 63)%N) ]) ].
Definition uc32_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "f"))) (Syntax.VarValues None (NE1 (VNAME "main"))) ]) ; Syntax.ExprStmt (APP (OID "f") []) ].
Definition uc33_prog : Syntax.Program := prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "f"))) (NE1 (VNAME "main")) ; Syntax.ExprStmt (APP (OID "f") []) ].
Definition uc34_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (OID "main") [ ILIT 1 ]) ].
Definition uc35_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (OID "main") [ ILIT ((2 ^ 63)%N) ]) ].
Definition uc36_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PTrue) []) ].
Definition uc37_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PTrue) [ ILIT ((2 ^ 63)%N) ]) ].
Definition uc38_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PIota) []) ].
Definition uc39_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PNil) []) ].
Definition uc40_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (OID "missingName") []) ].
Definition uc41_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (OID "missingName") [ ILIT ((2 ^ 63)%N) ]) ].
Definition uc_case_26 : uc_obs (rres uc26_prog) = mk_uc_obs Compilable.OutsideScope [ RP.FvUnmet AN.FamDeclaration RP.RvDeclMeaningV; RP.FvOK AN.FamTypeUse; RP.FvOK AN.FamStatement; RP.FvOK AN.FamApplication; RP.FvNonconst AN.FamValue; RP.FvUnmet AN.FamApplication RP.RvSourceTypeApp; RP.FvNonconst AN.FamValue; RP.FvDependent AN.FamValue (RP.DvArgUnmet 0) ] [] [ RP.RvDeclMeaningV; RP.RvSourceTypeApp ].
Proof. obs_uc uc26_prog. Qed.
Definition uc_case_27 : uc_obs (rres uc27_prog) = mk_uc_obs Compilable.OutsideScope [ RP.FvUnmet AN.FamDeclaration RP.RvDeclMeaningV; RP.FvUnmet AN.FamTypeUse RP.RvTypeMeaning; RP.FvOK AN.FamStatement; RP.FvOK AN.FamApplication; RP.FvNonconst AN.FamValue; RP.FvUnmet AN.FamApplication RP.RvSourceTypeApp; RP.FvNonconst AN.FamValue; RP.FvDependent AN.FamValue (RP.DvArgUnmet 0) ] [] [ RP.RvDeclMeaningV; RP.RvTypeMeaning; RP.RvSourceTypeApp ].
Proof. obs_uc uc27_prog. Qed.
Definition uc_case_28 : uc_obs (rres uc28_prog) = mk_uc_obs Compilable.OutsideScope [ RP.FvUnmet AN.FamDeclaration RP.RvDeclMeaningV; RP.FvOK AN.FamTypeUse; RP.FvOK AN.FamStatement; RP.FvOK AN.FamApplication; RP.FvNonconst AN.FamValue; RP.FvUnmet AN.FamApplication RP.RvSourceTypeApp; RP.FvNonconst AN.FamValue; RP.FvDependent AN.FamValue (RP.DvArgUnmet 0) ] [] [ RP.RvDeclMeaningV; RP.RvSourceTypeApp ].
Proof. obs_uc uc28_prog. Qed.
Definition uc_case_29 : uc_obs (rres uc29_prog) = mk_uc_obs Compilable.OutsideScope [ RP.FvOK AN.FamStatement; RP.FvOK AN.FamApplication; RP.FvNonconst AN.FamValue; RP.FvUnmet AN.FamApplication RP.RvApplication; RP.FvNonconst AN.FamValue; RP.FvDependent AN.FamValue (RP.DvArgUnmet 0) ] [] [ RP.RvApplication ].
Proof. obs_uc uc29_prog. Qed.
Definition uc_case_30 : uc_obs (rres uc30_prog) = mk_uc_obs Compilable.Rejected [ RP.FvUnmet AN.FamDeclaration RP.RvConstDecl; RP.FvOK AN.FamValue; RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamApplication RP.CvNotCallable; RP.FvNonconst AN.FamValue ] [ RP.CvNotCallable ] [ RP.RvConstDecl ].
Proof. obs_uc uc30_prog. Qed.
Definition uc_case_31 : uc_obs (rres uc31_prog) = mk_uc_obs Compilable.Rejected [ RP.FvUnmet AN.FamDeclaration RP.RvConstDecl; RP.FvOK AN.FamValue; RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamApplication RP.CvNotCallable; RP.FvNonconst AN.FamValue; RP.FvDependent AN.FamValue (RP.DvArgInvalid 0) ] [ RP.CvNotCallable ] [ RP.RvConstDecl ].
Proof. obs_uc uc31_prog. Qed.
Definition uc_case_32 : uc_obs (rres uc32_prog) = mk_uc_obs Compilable.OutsideScope [ RP.FvUnmet AN.FamDeclaration RP.RvDeclMeaningV; RP.FvUnmet AN.FamValue RP.RvMainUse; RP.FvDependent AN.FamStatement RP.DvChild; RP.FvUnmet AN.FamApplication RP.RvSourceValueApp; RP.FvNonconst AN.FamValue ] [] [ RP.RvDeclMeaningV; RP.RvMainUse; RP.RvSourceValueApp ].
Proof. obs_uc uc32_prog. Qed.
Definition uc_case_33 : uc_obs (rres uc33_prog) = mk_uc_obs Compilable.OutsideScope [ RP.FvDependent AN.FamDeclaration RP.DvChild; RP.FvUnmet AN.FamValue RP.RvMainUse; RP.FvDependent AN.FamStatement RP.DvChild; RP.FvUnmet AN.FamApplication RP.RvShortOriginApp; RP.FvNonconst AN.FamValue ] [] [ RP.RvMainUse; RP.RvShortOriginApp ].
Proof. obs_uc uc33_prog. Qed.
Definition uc_case_34 : uc_obs (rres uc34_prog) = mk_uc_obs Compilable.Rejected [ RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamApplication RP.CvMainArity; RP.FvNonconst AN.FamValue; RP.FvDependent AN.FamValue (RP.DvArgInvalid 0) ] [ RP.CvMainArity ] [].
Proof. obs_uc uc34_prog. Qed.
Definition uc_case_35 : uc_obs (rres uc35_prog) = mk_uc_obs Compilable.Rejected [ RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamApplication RP.CvMainArity; RP.FvNonconst AN.FamValue; RP.FvDependent AN.FamValue (RP.DvArgInvalid 0) ] [ RP.CvMainArity ] [].
Proof. obs_uc uc35_prog. Qed.
Definition uc_case_36 : uc_obs (rres uc36_prog) = mk_uc_obs Compilable.Rejected [ RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamApplication RP.CvNotCallable; RP.FvNonconst AN.FamValue ] [ RP.CvNotCallable ] [].
Proof. obs_uc uc36_prog. Qed.
Definition uc_case_37 : uc_obs (rres uc37_prog) = mk_uc_obs Compilable.Rejected [ RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamApplication RP.CvNotCallable; RP.FvNonconst AN.FamValue; RP.FvDependent AN.FamValue (RP.DvArgInvalid 0) ] [ RP.CvNotCallable ] [].
Proof. obs_uc uc37_prog. Qed.
Definition uc_case_38 : uc_obs (rres uc38_prog) = mk_uc_obs Compilable.Rejected [ RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamApplication (RP.CvInvalidAppIdentity Names.PIota); RP.FvNonconst AN.FamValue ] [ RP.CvInvalidAppIdentity Names.PIota ] [].
Proof. obs_uc uc38_prog. Qed.
Definition uc_case_39 : uc_obs (rres uc39_prog) = mk_uc_obs Compilable.Rejected [ RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamApplication (RP.CvInvalidAppIdentity Names.PNil); RP.FvNonconst AN.FamValue ] [ RP.CvInvalidAppIdentity Names.PNil ] [].
Proof. obs_uc uc39_prog. Qed.
Definition uc_case_40 : uc_obs (rres uc40_prog) = mk_uc_obs Compilable.Rejected [ RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamApplication RP.CvUnresolvedName; RP.FvDependent AN.FamValue RP.DvUnboundName ] [ RP.CvUnresolvedName ] [].
Proof. obs_uc uc40_prog. Qed.
Definition uc_case_41 : uc_obs (rres uc41_prog) = mk_uc_obs Compilable.Rejected [ RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamApplication RP.CvUnresolvedName; RP.FvDependent AN.FamValue RP.DvUnboundName; RP.FvDependent AN.FamValue (RP.DvArgInvalid 0) ] [ RP.CvUnresolvedName ] [].
Proof. obs_uc uc41_prog. Qed.
Definition uc43_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues (Some (Syntax.NamedType (Names.predeclared_ordinary Names.PInt))) (NE1 (NEG (Syntax.Name (Names.predeclared_ordinary Names.PNil))))) ]) ].
Definition uc44_prog : Syntax.Program := prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues (Some (Syntax.NamedType (Names.predeclared_ordinary Names.PAny))) (NE1 (APP (Names.predeclared_ordinary Names.PNil) []))) ]) ].
Definition uc45_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (OID "missingName") [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ]) ].
Definition uc46_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (OID "missingName") [ Syntax.Name (Names.predeclared_ordinary Names.PNil) ]) ].
Definition uc47_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ APP (Names.predeclared_ordinary Names.PInt) [ ILIT 1 ] ]) ].
Definition uc48_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PInt) [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ]) ].
Definition uc49_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PInt) [ Syntax.Name (Names.predeclared_ordinary Names.PNil) ]) ].
Definition uc50_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ APP (Names.predeclared_ordinary Names.PInt) [ Syntax.Name (Names.predeclared_ordinary Names.PNil) ] ]) ].
Definition uc53_prog : Syntax.Program := prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ NEG (ILIT ((2 ^ 63 + 1)%N)) ]) ].
Definition uc54_prog : Syntax.Program := prog [ Syntax.ExprStmt (NEG (ILIT ((2 ^ 63 + 1)%N))) ].
Definition uc55_prog : Syntax.Program := prog [ Syntax.ExprStmt (Syntax.Application (NEG (ILIT ((2 ^ 63 + 1)%N))) []) ].
Definition uc_case_43 : uc_obs (rres uc43_prog) = mk_uc_obs Compilable.Rejected [ RP.FvUnmet AN.FamDeclaration RP.RvDeclMeaningV; RP.FvOK AN.FamTypeUse; RP.FvNonconst AN.FamValue; RP.FvInvalid AN.FamValue (RP.CvInvalidIdentity Names.PNil) ] [ (RP.CvInvalidIdentity Names.PNil) ] [ RP.RvDeclMeaningV ].
Proof. obs_uc uc43_prog. Qed.
Definition uc_case_44 : uc_obs (rres uc44_prog) = mk_uc_obs Compilable.Rejected [ RP.FvUnmet AN.FamDeclaration RP.RvDeclMeaningV; RP.FvUnmet AN.FamTypeUse RP.RvTypeMeaning; RP.FvInvalid AN.FamApplication (RP.CvInvalidAppIdentity Names.PNil); RP.FvNonconst AN.FamValue ] [ (RP.CvInvalidAppIdentity Names.PNil) ] [ RP.RvDeclMeaningV; RP.RvTypeMeaning ].
Proof. obs_uc uc44_prog. Qed.
Definition uc_case_45 : uc_obs (rres uc45_prog) = mk_uc_obs Compilable.Rejected [ RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamApplication RP.CvUnresolvedName; RP.FvDependent AN.FamValue RP.DvUnboundName; RP.FvInvalid AN.FamValue (RP.CvInvalidIdentity Names.PIota) ] [ RP.CvUnresolvedName; (RP.CvInvalidIdentity Names.PIota) ] [].
Proof. obs_uc uc45_prog. Qed.
Definition uc_case_46 : uc_obs (rres uc46_prog) = mk_uc_obs Compilable.Rejected [ RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamApplication RP.CvUnresolvedName; RP.FvDependent AN.FamValue RP.DvUnboundName; RP.FvDependent AN.FamValue (RP.DvArgInvalid 0) ] [ RP.CvUnresolvedName ] [].
Proof. obs_uc uc46_prog. Qed.
Definition uc_case_47 : uc_obs (rres uc47_prog) = mk_uc_obs Compilable.Compiled [ RP.FvOK AN.FamStatement; RP.FvOK AN.FamApplication; RP.FvNonconst AN.FamValue; RP.FvOK AN.FamApplication; RP.FvOK AN.FamValue; RP.FvOK AN.FamValue ] [] [].
Proof. obs_uc uc47_prog. Qed.
Definition uc_case_48 : uc_obs (rres uc48_prog) = mk_uc_obs Compilable.Rejected [ RP.FvInvalid AN.FamStatement RP.CvIllegalStatement; RP.FvOK AN.FamApplication; RP.FvNonconst AN.FamValue; RP.FvInvalid AN.FamValue (RP.CvInvalidIdentity Names.PIota) ] [ RP.CvIllegalStatement; (RP.CvInvalidIdentity Names.PIota) ] [].
Proof. obs_uc uc48_prog. Qed.
Definition uc_case_49 : uc_obs (rres uc49_prog) = mk_uc_obs Compilable.Rejected [ RP.FvInvalid AN.FamStatement RP.CvIllegalStatement; RP.FvOK AN.FamApplication; RP.FvNonconst AN.FamValue; RP.FvInvalid AN.FamValue (RP.CvInvalidIdentity Names.PNil) ] [ RP.CvIllegalStatement; (RP.CvInvalidIdentity Names.PNil) ] [].
Proof. obs_uc uc49_prog. Qed.
Definition uc_case_50 : uc_obs (rres uc50_prog) = mk_uc_obs Compilable.Rejected [ RP.FvOK AN.FamStatement; RP.FvOK AN.FamApplication; RP.FvNonconst AN.FamValue; RP.FvOK AN.FamApplication; RP.FvNonconst AN.FamValue; RP.FvInvalid AN.FamValue (RP.CvInvalidIdentity Names.PNil) ] [ (RP.CvInvalidIdentity Names.PNil) ] [].
Proof. obs_uc uc50_prog. Qed.
Definition uc_case_53 : uc_obs (rres uc53_prog) = mk_uc_obs Compilable.Rejected [ RP.FvOK AN.FamStatement; RP.FvOK AN.FamApplication; RP.FvNonconst AN.FamValue; RP.FvInvalid AN.FamValue RP.CvDefaultOverflow; RP.FvNonconst AN.FamValue ] [ RP.CvDefaultOverflow ] [].
Proof. obs_uc uc53_prog. Qed.
Definition uc_case_54 : uc_obs (rres uc54_prog) = mk_uc_obs Compilable.Rejected [ RP.FvInvalid AN.FamStatement RP.CvIllegalStatement; RP.FvNonconst AN.FamValue; RP.FvNonconst AN.FamValue ] [ RP.CvIllegalStatement ] [].
Proof. obs_uc uc54_prog. Qed.
Definition uc_case_55 : uc_obs (rres uc55_prog) = mk_uc_obs Compilable.Rejected [ RP.FvDependent AN.FamStatement RP.DvChild; RP.FvInvalid AN.FamApplication RP.CvNotCallableExpr; RP.FvNonconst AN.FamValue; RP.FvDependent AN.FamValue RP.DvHeadInvalid; RP.FvNonconst AN.FamValue ] [ RP.CvNotCallableExpr ] [].
Proof. obs_uc uc55_prog. Qed.
Definition uc42_prog : Syntax.Program := prog_tops [ Syntax.TopDeclaration (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues (Some (Syntax.NamedType (Names.predeclared_ordinary Names.PAny))) (NE1 (APP (Names.predeclared_ordinary Names.PPrintln) [ Syntax.Name (Names.predeclared_ordinary Names.PNil) ]))) ]) ; main0 ].
Definition uc51_prog : Syntax.Program := prog_tops [ Syntax.TopDeclaration (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues (Some (Syntax.NamedType (Names.predeclared_ordinary Names.PInt))) (NE1 (NEG (ILIT ((2 ^ 63 + 1)%N))))) ]) ; main0 ].
Definition uc52_prog : Syntax.Program := prog_tops [ Syntax.TopDeclaration (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (NEG (ILIT ((2 ^ 63 + 1)%N))))) ]) ; main0 ].
Definition uc_case_42 : uc_obs (rres uc42_prog) = mk_uc_obs Compilable.Rejected [ RP.FvUnmet AN.FamDeclaration RP.RvDeclMeaningV; RP.FvUnmet AN.FamTypeUse RP.RvTypeMeaning; RP.FvOK AN.FamApplication; RP.FvInvalid AN.FamValue RP.CvNoValueUsed; RP.FvInvalid AN.FamValue (RP.CvInvalidIdentity Names.PNil) ] [ RP.CvNoValueUsed; (RP.CvInvalidIdentity Names.PNil) ] [ RP.RvDeclMeaningV; RP.RvTypeMeaning ].
Proof. obs_uc uc42_prog. Qed.
Definition uc_case_51 : uc_obs (rres uc51_prog) = mk_uc_obs Compilable.OutsideScope [ RP.FvUnmet AN.FamDeclaration RP.RvDeclMeaningV; RP.FvOK AN.FamTypeUse; RP.FvUnmet AN.FamValue RP.RvTypedTargetConstant; RP.FvNonconst AN.FamValue ] [] [ RP.RvDeclMeaningV; RP.RvTypedTargetConstant ].
Proof. obs_uc uc51_prog. Qed.
Definition uc_case_52 : uc_obs (rres uc52_prog) = mk_uc_obs Compilable.OutsideScope [ RP.FvUnmet AN.FamDeclaration RP.RvConstDecl; RP.FvUnmet AN.FamValue RP.RvConstNoDefault; RP.FvNonconst AN.FamValue ] [] [ RP.RvConstDecl; RP.RvConstNoDefault ].
Proof. obs_uc uc52_prog. Qed.

(* uc_path_total: every expression node has its exact use-path — use_path is total *)
Definition uc_path_total := @Index.Edges.use_path.
(* uc_path_progress: a use-path's root sits strictly before its subject, so the walk terminates *)
Definition uc_path_progress := @Index.Edges.up_root_lt.
(* uc_path_edge_roundtrip: the subject sits at its path's exact ordinal in its recorded parent *)
Definition uc_path_edge_roundtrip := @Index.Edges.up_iat.
(* uc_path_canonical_query: a subject's stored role is exactly the one its path implies *)
Definition uc_path_canonical_query := @Index.Edges.up_role_ok.
(* uc_path_root_exhaustive: a path's family is exactly the syntactic reading of its parent, over the eight families *)
Definition uc_path_root_exhaustive := @Index.Edges.up_family_ok.
(* uc_path_arbitrary_depth: the vm-safe root walk equals the path's root kind through any depth of fold links *)
Definition uc_path_arbitrary_depth := @Index.Edges.root_const_var_b_path.
(* uc_head_name_no_value: a name on the application-head edge contributes no occurrence fact, its value row deleted *)
Definition uc_head_name_no_value := @AN.occ_facts_va_name_head.
(* uc_nonname_head_value: a non-name application head retains its exact value fact *)
Definition uc_nonname_head_value := @AN.nonconst_value_fact_retained.
(* uc_application_row_retained: every application node keeps its exact application row in the fact list *)
Definition uc_application_row_retained := @AN.app_fact_retained.
(* uc_dep_ainvalid_roundtrip: a deferred argument's DepArgInvalid is recovered exactly by occ_dep *)
Definition ucdeep_prog : Syntax.Program := prog [ Syntax.ExprStmt (NEG (APP (Names.predeclared_ordinary Names.PInt) [ NEG (APP (Names.predeclared_ordinary Names.PInt) [ ILIT 1 ]) ])) ].
(* uc_deep_path_exact: a deep alternating unary/application program retains every intermediate fact *)
Definition uc_deep_path_exact : uc_obs (rres ucdeep_prog) = mk_uc_obs Compilable.Rejected [ RP.FvInvalid AN.FamStatement RP.CvIllegalStatement; RP.FvOK AN.FamValue; RP.FvOK AN.FamApplication; RP.FvOK AN.FamValue; RP.FvOK AN.FamValue; RP.FvOK AN.FamApplication; RP.FvOK AN.FamValue; RP.FvOK AN.FamValue ] [ RP.CvIllegalStatement ] [].
Proof. obs_uc ucdeep_prog. Qed.
(* uc_source_origin_exhaustive: every source-object declaration origin is a binder, a function, or a short new *)
Lemma uc_source_origin_exhaustive p (idx : Index.ProgramIndex p) (o : BN.DeclOrigin idx) :
  (exists b, o = BN.DOBinder b) \/ (exists f, o = BN.DOFunc f) \/ (exists sn, o = BN.DOShort sn).
Proof. destruct o as [b|f|sn]; [ left; exists b | right; left; exists f | right; right; exists sn ]; reflexivity. Qed.
(* uc_path_constructor_disjoint: the eight use-path families form a discrete, decidably-distinct enumeration *)
Lemma uc_path_constructor_disjoint (f1 f2 : Index.Edges.UseFamily) : {f1 = f2} + {f1 <> f2}.
Proof. decide equality. Qed.
(* uc_resolved_application_roundtrip: an application's observable negativity equals its own_app classification *)
Definition uc_resolved_application_roundtrip := @AN.app_neg_at_app.
(* uc_unresolved_head_on_app: an unresolved application head lands its issue on the application row *)
Definition uc_unresolved_head_on_app :
  existsb (fun f => match f with AN.OFApp _ (AN.AInvalid (AN.UnresolvedApplicationHead _ _ _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (OID "missingName") []) ])) = true.
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (OID "missingName") []) ]). Qed.
(* uc_invalid_identity_head_on_app: an iota or nil application head lands invalid-application-identity on the app row *)
Definition uc_invalid_identity_head_on_app :
  existsb (fun f => match f with AN.OFApp _ (AN.AInvalid (AN.InvalidApplicationIdentity _ _ _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PIota) []) ])) = true.
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PIota) []) ]). Qed.
(* uc_nonname_application_roundtrip: a non-name application head lands NotCallableExpr on the app row *)
Definition uc_nonname_application_roundtrip :
  existsb (fun f => match f with AN.OFApp _ (AN.AInvalid (AN.NotCallableExpr _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (Syntax.Application (ILIT ((2 ^ 63)%N)) []) ])) = true.
Proof. obs_direct (prog [ Syntax.ExprStmt (Syntax.Application (ILIT ((2 ^ 63)%N)) []) ]). Qed.
(* uc_head_folds_priority: a true fold keeps its iota argument InvalidIdentity, never a deferred DepArg *)
Definition uc_head_folds_priority :
  existsb (fun f => match f with AN.OFValue _ (AN.VInvalid (AN.InvalidIdentity _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PInt) [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ]) ])) = true
  /\ existsb (fun f => match f with AN.OFValue _ (AN.VDependent (AN.DepArgInvalid _ _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PInt) [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ]) ])) = false.
Proof. split; obs_direct (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PInt) [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ]) ]). Qed.
(* uc_nonfolded_aok_is_println: a nonfolded AOK application with an argument is println, which defaults that argument *)
Definition uc_nonfolded_aok_is_println :
  existsb (fun f => match f with AN.OFValue _ (AN.VInvalid (AN.DefaultOverflow _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ ILIT ((2 ^ 63)%N) ]) ])) = true.
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ ILIT ((2 ^ 63)%N) ]) ]). Qed.
(* uc_iota_policy_exhaustive: iota per context: init identity, standalone invalid, head invalid-app-id *)
Definition uc_iota_policy_exhaustive :
  existsb (fun f => match f with AN.OFValue _ (AN.VUnmet (AN.RInitializerIdentity _ _ _ _)) => true | _ => false end) (pfacts (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (Syntax.Name (Names.predeclared_ordinary Names.PIota)))) ]) ])) = true /\ existsb (fun f => match f with AN.OFValue _ (AN.VInvalid (AN.InvalidIdentity _ _ _)) => true | _ => false end) (pfacts (prog [ Syntax.ExprStmt (Syntax.Name (Names.predeclared_ordinary Names.PIota)) ])) = true /\ existsb (fun f => match f with AN.OFApp _ (AN.AInvalid (AN.InvalidApplicationIdentity _ _ _ _ _ _)) => true | _ => false end) (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PIota) []) ])) = true.
Proof. repeat split; first [ obs_direct (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (Syntax.Name (Names.predeclared_ordinary Names.PIota)))) ]) ]) | obs_direct (prog [ Syntax.ExprStmt (Syntax.Name (Names.predeclared_ordinary Names.PIota)) ]) | obs_direct (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PIota) []) ]) ]. Qed.
(* uc_nil_policy_exhaustive: nil per context: typed-target identity, standalone invalid, head invalid-app-id *)
Definition uc_nil_policy_exhaustive :
  existsb (fun f => match f with AN.OFValue _ (AN.VUnmet (AN.RTypedTargetIdentity _ _ _ _)) => true | _ => false end) (pfacts (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues (Some (Syntax.NamedType (Names.predeclared_ordinary Names.PAny))) (NE1 (Syntax.Name (Names.predeclared_ordinary Names.PNil)))) ]) ])) = true /\ existsb (fun f => match f with AN.OFValue _ (AN.VInvalid (AN.InvalidIdentity _ _ _)) => true | _ => false end) (pfacts (prog [ Syntax.ExprStmt (Syntax.Name (Names.predeclared_ordinary Names.PNil)) ])) = true /\ existsb (fun f => match f with AN.OFApp _ (AN.AInvalid (AN.InvalidApplicationIdentity _ _ _ _ _ _)) => true | _ => false end) (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PNil) []) ])) = true.
Proof. repeat split; first [ obs_direct (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues (Some (Syntax.NamedType (Names.predeclared_ordinary Names.PAny))) (NE1 (Syntax.Name (Names.predeclared_ordinary Names.PNil)))) ]) ]) | obs_direct (prog [ Syntax.ExprStmt (Syntax.Name (Names.predeclared_ordinary Names.PNil)) ]) | obs_direct (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PNil) []) ]) ]. Qed.
(* uc_default_policy_exhaustive: default per context: println overflow, const no-default, discarded illegal *)
Definition uc_default_policy_exhaustive :
  existsb (fun f => match f with AN.OFValue _ (AN.VInvalid (AN.DefaultOverflow _ _)) => true | _ => false end) (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ ILIT ((2 ^ 63)%N) ]) ])) = true /\ existsb (fun f => match f with AN.OFValue _ (AN.VUnmet (AN.RConstNoDefault _ _)) => true | _ => false end) (pfacts (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (ILIT ((2 ^ 63)%N)))) ]) ])) = true /\ existsb (fun f => match f with AN.OFStmt _ (AN.SInvalid (AN.IllegalStatement _)) => true | _ => false end) (pfacts (prog [ Syntax.ExprStmt (ILIT ((2 ^ 63)%N)) ])) = true.
Proof. repeat split; first [ obs_direct (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ ILIT ((2 ^ 63)%N) ]) ]) | obs_direct (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (ILIT ((2 ^ 63)%N)))) ]) ]) | obs_direct (prog [ Syntax.ExprStmt (ILIT ((2 ^ 63)%N)) ]) ]. Qed.
(* uc_fact_transform_exact: retained rows project to result_fact_list exactly, in retained order *)
Definition uc_fact_transform_exact := @AN.fact_rows_rows.
(* uc_issue_order_preserved: result_issues is exactly the diagnostics block then the boundaries block *)
Definition uc_issue_order_preserved := @AN.result_issues_class_split.
(* uc_compiled_admission_exact: over the full result domain, Compiled = exactly no diagnostics and no boundaries *)
Definition uc_compiled_admission_exact {p} (r : AN.Result p) :
  Compilable.disposition_of r = Compilable.Compiled <-> Compilable.AdmissibleData r.
Proof.
  split; [ apply Compilable.disposition_compiled | ].
  intros [Hd Hb]. unfold Compilable.disposition_of, Compilable.disposition_from_data.
  rewrite (proj2 (AN.data_diagnostics_empty_correct r) Hd), (proj2 (AN.data_boundaries_empty_correct r) Hb).
  reflexivity.
Qed.
(* uc_own_app_once: an application's own_app is one construction, the OFApp fact row, the cell its projection *)
Definition uc_own_app_once := @AN.own_app_once.
Definition uc_dep_ainvalid_roundtrip p (idx : Index.ProgramIndex p) (s : BN.PI.PackageSurface idx) (bd : BN.PhaseData s) (bp : BN.BindingPhase s bd)
  (r : Index.NodeRef idx) (ar : Index.Refs.AppRef idx) (i : nat)
  (Hpar : Index.node_parent r = Some (Index.Refs.app_node ar)) (Hrole : Index.node_role r = Index.Model.RApplicationArg i)
  (c : AN.Cause bp (Index.Refs.app_node ar) AN.ApplicationKind) :
  AN.occ_dep (AN.OFValue r (AN.VDependent (AN.DepArgInvalid ar i Hpar Hrole c))) = Some (AN.DepArgInvalid ar i Hpar Hrole c) := eq_refl.
(* uc_dep_aunmet_roundtrip: a deferred argument's DepArgUnmet is recovered exactly by occ_dep *)
Definition uc_dep_aunmet_roundtrip p (idx : Index.ProgramIndex p) (s : BN.PI.PackageSurface idx) (bd : BN.PhaseData s) (bp : BN.BindingPhase s bd)
  (r : Index.NodeRef idx) (ar : Index.Refs.AppRef idx) (i : nat)
  (Hpar : Index.node_parent r = Some (Index.Refs.app_node ar)) (Hrole : Index.node_role r = Index.Model.RApplicationArg i)
  (q : AN.Requirement bp (Index.Refs.app_node ar) AN.ApplicationKind) :
  AN.occ_dep (AN.OFValue r (AN.VDependent (AN.DepArgUnmet ar i Hpar Hrole q))) = Some (AN.DepArgUnmet ar i Hpar Hrole q) := eq_refl.
(* uc_dep_adependent_roundtrip: a deferred argument's DepArgDependent is recovered exactly by occ_dep *)
Definition uc_dep_adependent_roundtrip p (idx : Index.ProgramIndex p) (s : BN.PI.PackageSurface idx) (bd : BN.PhaseData s) (bp : BN.BindingPhase s bd)
  (r : Index.NodeRef idx) (ar : Index.Refs.AppRef idx) (i : nat)
  (Hpar : Index.node_parent r = Some (Index.Refs.app_node ar)) (Hrole : Index.node_role r = Index.Model.RApplicationArg i)
  (d : AN.Dependency bp (Index.Refs.app_node ar) AN.ApplicationKind) :
  AN.occ_dep (AN.OFValue r (AN.VDependent (AN.DepArgDependent ar i Hpar Hrole d))) = Some (AN.DepArgDependent ar i Hpar Hrole d) := eq_refl.

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

(* §8 an overflowing literal arg under an unresolved head defers to a DepArgInvalid, not a diagnostic *)
Definition r_arg_defers_unbound :
  existsb (fun f => match f with AN.OFValue _ (AN.VDependent (AN.DepArgInvalid _ _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (OID "undefined") [ ILIT ((2 ^ 63)%N) ]) ])) = true.
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (OID "undefined") [ ILIT ((2 ^ 63)%N) ]) ]). Qed.

(* §258 a folded conversion head keeps its nil arguments exact InvalidIdentity, never deferred — no DepArg row *)
Definition r_folded_nil_no_defer :
  existsb (fun f => match f with AN.OFValue _ (AN.VDependent (AN.DepArgInvalid _ _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PInt8)
                            [ Syntax.Name (Names.predeclared_ordinary Names.PNil)
                            ; Syntax.Name (Names.predeclared_ordinary Names.PNil) ]) ])) = false.
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PInt8) [ Syntax.Name (Names.predeclared_ordinary Names.PNil) ; Syntax.Name (Names.predeclared_ordinary Names.PNil) ]) ]). Qed.

(* §8 a nil argument under an unmodelled-conversion head defers to a DepArgUnmet on the head's ReqApplication *)
Definition r_arg_defers_unmet :
  existsb (fun f => match f with AN.OFValue _ (AN.VDependent (AN.DepArgUnmet _ _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PAny)
                            [ Syntax.Name (Names.predeclared_ordinary Names.PNil) ]) ])) = true.
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PAny) [ Syntax.Name (Names.predeclared_ordinary Names.PNil) ]) ]). Qed.

(* §271 a var-origin function-value call is a source-value-application requirement on the app row *)
Definition r_var_origin_app :
  existsb (fun f => match f with AN.OFApp _ (AN.AUnmet (AN.ReqSourceValueApp _ _ _ _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "f"))) (Syntax.VarValues None (NE1 (VNAME "main"))) ]) ; Syntax.ExprStmt (APP (OID "f") []) ])) = true.
Proof. obs_direct (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "f"))) (Syntax.VarValues None (NE1 (VNAME "main"))) ]) ; Syntax.ExprStmt (APP (OID "f") []) ]). Qed.

(* §271 a short-origin function-value call is a short-origin-application requirement on the app row *)
Definition r_short_origin_app :
  existsb (fun f => match f with AN.OFApp _ (AN.AUnmet (AN.ReqShortOriginApp _ _ _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "f"))) (NE1 (VNAME "main")) ; Syntax.ExprStmt (APP (OID "f") []) ])) = true.
Proof. obs_direct (prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "f"))) (NE1 (VNAME "main")) ; Syntax.ExprStmt (APP (OID "f") []) ]). Qed.

(* §271 a const-binder call is a known-noncallable cause on the app row, recovered from the spec flavor *)
Definition r_const_origin_app :
  existsb (fun f => match f with AN.OFApp _ (AN.AInvalid (AN.NotCallable _ _ _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "c"))) (Syntax.ExplicitConstInit None (NE1 (ILIT 1))) ]) ; Syntax.ExprStmt (APP (OID "c") []) ])) = true.
Proof. obs_direct (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "c"))) (Syntax.ExplicitConstInit None (NE1 (ILIT 1))) ]) ; Syntax.ExprStmt (APP (OID "c") []) ]). Qed.

(* §271 a type-alias-origin call is a source-type-application requirement on the app row *)
Definition r_type_origin_app :
  existsb (fun f => match f with AN.OFApp _ (AN.AUnmet (AN.ReqSourceTypeApp _ _ _ _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.DeclarationStmt (Syntax.TypeDecl [ Syntax.AliasSpec (Syntax.BNamed (OID "T")) (Syntax.NamedType (Names.predeclared_ordinary Names.PInt)) ]) ; Syntax.ExprStmt (APP (OID "T") [ ILIT 1 ]) ])) = true.
Proof. obs_direct (prog [ Syntax.DeclarationStmt (Syntax.TypeDecl [ Syntax.AliasSpec (Syntax.BNamed (OID "T")) (Syntax.NamedType (Names.predeclared_ordinary Names.PInt)) ]) ; Syntax.ExprStmt (APP (OID "T") [ ILIT 1 ]) ]). Qed.

(* §259 a literal argument under println (AOK) defaults, never defers — an exact DefaultOverflow value row *)
Definition r_arg_defaults_println :
  existsb (fun f => match f with AN.OFValue _ (AN.VInvalid (AN.DefaultOverflow _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ ILIT ((2 ^ 63)%N) ]) ])) = true.
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ ILIT ((2 ^ 63)%N) ]) ]). Qed.

(* §8 a literal argument under a redeclared head defers to a DepArgDependent on the redeclaration *)
Definition r_arg_defers_redecl :
  existsb (fun f => match f with AN.OFValue _ (AN.VDependent (AN.DepArgDependent _ _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "f"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "f"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ; Syntax.ExprStmt (APP (OID "f") [ ILIT ((2 ^ 63)%N) ]) ])) = true.
Proof. obs_direct (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "f"))) (Syntax.VarValues None (NE1 (ILIT 1))) ]) ; Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "f"))) (Syntax.VarValues None (NE1 (ILIT 2))) ]) ; Syntax.ExprStmt (APP (OID "f") [ ILIT ((2 ^ 63)%N) ]) ]). Qed.

(* §11 missingName(iota): the target-independent iota keeps its InvalidIdentity, the app is unresolved-head *)
Definition r_missingname_iota :
  RP.result_cause_views (rres (prog [ Syntax.ExprStmt (APP (OID "undefined") [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ]) ]))
  = [ RP.CvUnresolvedName ; RP.CvInvalidIdentity Names.PIota ].
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (OID "undefined") [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ]) ]). Qed.

(* §11 missingName(nil): the target-sensitive nil defers, leaving only the unresolved-application-head *)
Definition r_missingname_nil :
  RP.result_cause_views (rres (prog [ Syntax.ExprStmt (APP (OID "undefined") [ Syntax.Name (Names.predeclared_ordinary Names.PNil) ]) ]))
  = [ RP.CvUnresolvedName ].
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (OID "undefined") [ Syntax.Name (Names.predeclared_ordinary Names.PNil) ]) ]). Qed.

(* §11 arbitrary depth: iota under three unary links still roots at the const, an exact initializer-identity *)
Definition r_deep_unary_iota :
  existsb (fun f => match f with AN.OFValue _ (AN.VUnmet (AN.RInitializerIdentity _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (Syntax.Unary Syntax.UnaryMinus (Syntax.Unary Syntax.UnaryMinus (Syntax.Unary Syntax.UnaryMinus (Syntax.Name (Names.predeclared_ordinary Names.PIota))))))) ]) ])) = true.
Proof. obs_direct (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (Syntax.Unary Syntax.UnaryMinus (Syntax.Unary Syntax.UnaryMinus (Syntax.Unary Syntax.UnaryMinus (Syntax.Name (Names.predeclared_ordinary Names.PIota))))))) ]) ]). Qed.

(* §11 a folded conversion head keeps its iota argument exact InvalidIdentity, never deferred *)
Definition r_folded_iota_no_defer :
  existsb (fun f => match f with AN.OFValue _ (AN.VInvalid (AN.InvalidIdentity _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PInt8) [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ]) ])) = true.
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PInt8) [ Syntax.Name (Names.predeclared_ordinary Names.PIota) ]) ]). Qed.

(* §11 a nil in a folded conversion inside println stays exact InvalidIdentity, owned by the inner fold *)
Definition r_nested_fold_nil :
  existsb (fun f => match f with AN.OFValue _ (AN.VInvalid (AN.InvalidIdentity _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ APP (Names.predeclared_ordinary Names.PInt8) [ Syntax.Name (Names.predeclared_ordinary Names.PNil) ] ]) ])) = true.
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ APP (Names.predeclared_ordinary Names.PInt8) [ Syntax.Name (Names.predeclared_ordinary Names.PNil) ] ]) ]). Qed.

(* §286 iota() renders the exact invalid-application-identity cause view *)
Definition r_iota_app_view :
  RP.result_cause_views (rres (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PIota) []) ])) = [ RP.CvInvalidAppIdentity Names.PIota ].
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PIota) []) ]). Qed.

(* §286 a type-alias-origin call renders the source-type-application requirement view *)
Definition r_type_origin_view :
  existsb (fun v => match v with RP.RvSourceTypeApp => true | _ => false end)
          (RP.result_req_views (rres (prog [ Syntax.DeclarationStmt (Syntax.TypeDecl [ Syntax.AliasSpec (Syntax.BNamed (OID "T")) (Syntax.NamedType (Names.predeclared_ordinary Names.PInt)) ]) ; Syntax.ExprStmt (APP (OID "T") [ ILIT 1 ]) ]))) = true.
Proof. obs_direct (prog [ Syntax.DeclarationStmt (Syntax.TypeDecl [ Syntax.AliasSpec (Syntax.BNamed (OID "T")) (Syntax.NamedType (Names.predeclared_ordinary Names.PInt)) ]) ; Syntax.ExprStmt (APP (OID "T") [ ILIT 1 ]) ]). Qed.

(* §286 a var-origin call renders the source-value-application requirement view *)
Definition r_var_origin_view :
  existsb (fun v => match v with RP.RvSourceValueApp => true | _ => false end)
          (RP.result_req_views (rres (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "f"))) (Syntax.VarValues None (NE1 (VNAME "main"))) ]) ; Syntax.ExprStmt (APP (OID "f") []) ]))) = true.
Proof. obs_direct (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "f"))) (Syntax.VarValues None (NE1 (VNAME "main"))) ]) ; Syntax.ExprStmt (APP (OID "f") []) ]). Qed.

(* §286 a short-origin call renders the short-origin-application requirement view *)
Definition r_short_origin_view :
  existsb (fun v => match v with RP.RvShortOriginApp => true | _ => false end)
          (RP.result_req_views (rres (prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "f"))) (NE1 (VNAME "main")) ; Syntax.ExprStmt (APP (OID "f") []) ]))) = true.
Proof. obs_direct (prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "f"))) (NE1 (VNAME "main")) ; Syntax.ExprStmt (APP (OID "f") []) ]). Qed.

(* §286 an unmodelled-conversion call renders the application requirement view *)
Definition r_app_req_view :
  existsb (fun v => match v with RP.RvApplication => true | _ => false end)
          (RP.result_req_views (rres (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PAny) [ Syntax.Name (Names.predeclared_ordinary Names.PNil) ]) ]))) = true.
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PAny) [ Syntax.Name (Names.predeclared_ordinary Names.PNil) ]) ]). Qed.

(* §11 a negative-unary overflow under println defaults to an exact DefaultOverflow, never a defer *)
Definition r_neg_unary_overflow :
  existsb (fun f => match f with AN.OFValue _ (AN.VInvalid (AN.DefaultOverflow _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ Syntax.Unary Syntax.UnaryMinus (ILIT ((2 ^ 63 + 1)%N)) ]) ])) = true.
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ Syntax.Unary Syntax.UnaryMinus (ILIT ((2 ^ 63 + 1)%N)) ]) ]). Qed.

(* §250 a negative-unary overflow at a no-type const is a const-no-default requirement through the unary link *)
Definition r_neg_unary_const :
  existsb (fun f => match f with AN.OFValue _ (AN.VUnmet (AN.RConstNoDefault _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (Syntax.Unary Syntax.UnaryMinus (ILIT ((2 ^ 63 + 1)%N))))) ]) ])) = true.
Proof. obs_direct (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (Syntax.Unary Syntax.UnaryMinus (ILIT ((2 ^ 63 + 1)%N))))) ]) ]). Qed.

(* §287 a two-argument conversion is a conversion-arity invalidity on the app row *)
Definition r_conversion_arity :
  existsb (fun f => match f with AN.OFApp _ (AN.AInvalid (AN.ConversionArity _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PInt8) [ ILIT 1 ; ILIT 2 ]) ])) = true.
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PInt8) [ ILIT 1 ; ILIT 2 ]) ]). Qed.

(* §287 a one-argument call to the zero-parameter main is a main-arity invalidity, resolved at the head child *)
Definition r_main_arity :
  existsb (fun f => match f with AN.OFApp _ (AN.AInvalid (AN.MainArity _ _ _ _ _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (OID "main") [ ILIT 1 ]) ])) = true.
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (OID "main") [ ILIT 1 ]) ]). Qed.

(* §287 a const-binder call with an overflowing argument: NotCallable on the app, the argument defers to it *)
Definition r_const_call_arg_defers :
  existsb (fun f => match f with AN.OFApp _ (AN.AInvalid (AN.NotCallable _ _ _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "c"))) (Syntax.ExplicitConstInit None (NE1 (ILIT 1))) ]) ; Syntax.ExprStmt (APP (OID "c") [ ILIT ((2 ^ 63)%N) ]) ])) = true
  /\ existsb (fun f => match f with AN.OFValue _ (AN.VDependent (AN.DepArgInvalid _ _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "c"))) (Syntax.ExplicitConstInit None (NE1 (ILIT 1))) ]) ; Syntax.ExprStmt (APP (OID "c") [ ILIT ((2 ^ 63)%N) ]) ])) = true.
Proof. split; obs_direct (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "c"))) (Syntax.ExplicitConstInit None (NE1 (ILIT 1))) ]) ; Syntax.ExprStmt (APP (OID "c") [ ILIT ((2 ^ 63)%N) ]) ]). Qed.

(* §293 a consumed zero-result fixed-main application is a NoValueUsed value, here as println's argument *)
Definition r_novalue_println_main :
  existsb (fun f => match f with AN.OFValue _ (AN.VInvalid (AN.NoValueUsed _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ APP (OID "main") [] ]) ])) = true.
Proof. obs_direct (prog [ Syntax.ExprStmt (APP (Names.predeclared_ordinary Names.PPrintln) [ APP (OID "main") [] ]) ]). Qed.

(* §294 discriminator: a bare main() statement discards its result and stays Compiled *)
Definition r_bare_main_compiles :
  Compilable.disposition (prog [ Syntax.ExprStmt (APP (OID "main") []) ]) = Compilable.Compiled.
Proof. obs_disp. Qed.

(* §297 const x = main(): the main result is consumed by an initializer, so NoValueUsed *)
Definition r_novalue_const_main :
  existsb (fun f => match f with AN.OFValue _ (AN.VInvalid (AN.NoValueUsed _)) => true | _ => false end)
          (pfacts (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (APP (OID "main") []))) ]) ])) = true.
Proof. obs_direct (prog [ Syntax.DeclarationStmt (Syntax.ConstDecl [ Syntax.MakeConstSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.ExplicitConstInit None (NE1 (APP (OID "main") []))) ]) ]). Qed.

(* §298 var x = main(): consumed by a var initializer, so NoValueUsed *)
Definition r_novalue_var_main :
  existsb (fun f => match f with AN.OFValue _ (AN.VInvalid (AN.NoValueUsed _)) => true | _ => false end)
          (pfacts (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (APP (OID "main") []))) ]) ])) = true.
Proof. obs_direct (prog [ Syntax.DeclarationStmt (Syntax.VarDecl [ Syntax.MakeVarSpec (NE1 (Syntax.BNamed (OID "x"))) (Syntax.VarValues None (NE1 (APP (OID "main") []))) ]) ]). Qed.

(* §299 x := main(): consumed by a short RHS, so NoValueUsed *)
Definition r_novalue_short_main :
  existsb (fun f => match f with AN.OFValue _ (AN.VInvalid (AN.NoValueUsed _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "x"))) (NE1 (APP (OID "main") [])) ])) = true.
Proof. obs_direct (prog [ Syntax.ShortVarDecl (NE1 (Syntax.BNamed (OID "x"))) (NE1 (APP (OID "main") [])) ]). Qed.

(* §295 main()(): outer NotCallableExpr, inner main consumed as non-name head, so NoValueUsed *)
Definition r_main_call_call :
  existsb (fun f => match f with AN.OFApp _ (AN.AInvalid (AN.NotCallableExpr _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (Syntax.Application (APP (OID "main") []) []) ])) = true
  /\ existsb (fun f => match f with AN.OFValue _ (AN.VInvalid (AN.NoValueUsed _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (Syntax.Application (APP (OID "main") []) []) ])) = true.
Proof. split; obs_direct (prog [ Syntax.ExprStmt (Syntax.Application (APP (OID "main") []) []) ]). Qed.

(* §296 println()(): same shape, the zero-result println app is the consumed non-name head *)
Definition r_println_call_call :
  existsb (fun f => match f with AN.OFApp _ (AN.AInvalid (AN.NotCallableExpr _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (Syntax.Application (APP (Names.predeclared_ordinary Names.PPrintln) []) []) ])) = true
  /\ existsb (fun f => match f with AN.OFValue _ (AN.VInvalid (AN.NoValueUsed _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (Syntax.Application (APP (Names.predeclared_ordinary Names.PPrintln) []) []) ])) = true.
Proof. split; obs_direct (prog [ Syntax.ExprStmt (Syntax.Application (APP (Names.predeclared_ordinary Names.PPrintln) []) []) ]). Qed.

(* §317 an overflowing literal head defers to NotCallableExpr, not its own DefaultOverflow *)
Definition r_lithead_defers :
  existsb (fun f => match f with AN.OFValue _ (AN.VDependent (AN.DepHeadInvalid _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (Syntax.Application (ILIT ((2 ^ 63)%N)) []) ])) = true
  /\ existsb (fun f => match f with AN.OFValue _ (AN.VInvalid (AN.DefaultOverflow _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (Syntax.Application (ILIT ((2 ^ 63)%N)) []) ])) = false.
Proof. split; obs_direct (prog [ Syntax.ExprStmt (Syntax.Application (ILIT ((2 ^ 63)%N)) []) ]). Qed.

(* §369 an overflowing negative unary head likewise defers rather than emitting DefaultOverflow *)
Definition r_neghead_defers :
  existsb (fun f => match f with AN.OFValue _ (AN.VDependent (AN.DepHeadInvalid _ _ _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (Syntax.Application (NEG (ILIT ((2 ^ 63 + 1)%N))) []) ])) = true.
Proof. obs_direct (prog [ Syntax.ExprStmt (Syntax.Application (NEG (ILIT ((2 ^ 63 + 1)%N))) []) ]). Qed.

(* §12 a discarded overflowing literal does not default: only IllegalStatement, no DefaultOverflow *)
Definition r_discard_lit_no_default :
  existsb (fun f => match f with AN.OFStmt _ (AN.SInvalid (AN.IllegalStatement _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (ILIT ((2 ^ 63)%N)) ])) = true
  /\ existsb (fun f => match f with AN.OFValue _ (AN.VInvalid (AN.DefaultOverflow _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (ILIT ((2 ^ 63)%N)) ])) = false.
Proof. split; obs_direct (prog [ Syntax.ExprStmt (ILIT ((2 ^ 63)%N)) ]). Qed.

(* §64 the discarded negative unary overflow likewise stays IllegalStatement, never DefaultOverflow *)
Definition r_discard_unary_no_default :
  existsb (fun f => match f with AN.OFValue _ (AN.VInvalid (AN.DefaultOverflow _ _)) => true | _ => false end)
          (pfacts (prog [ Syntax.ExprStmt (NEG (ILIT ((2 ^ 63 + 1)%N))) ])) = false.
Proof. obs_direct (prog [ Syntax.ExprStmt (NEG (ILIT ((2 ^ 63 + 1)%N))) ]). Qed.

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
