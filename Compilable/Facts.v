(* Facts — resolution meanings, site roles, and the per-site diagnostics and boundaries the phase composes. *)
From Stdlib Require Import List Bool String Ascii ZArith NArith Lia.
From Fido Require Import Names Integer Float Complex FilePath Syntax Index Compilable.TypeResolution Compilable.Bindings Compilable.Report Compilable.Packages.
Import ListNotations.

(* The semantic type a predeclared type-name denotes, or None when the name is not one of the sixteen types. *)
Definition predeclared_type_of_name (n : Names.PredeclaredName) : option Compilable.TypeResolution.SemanticType :=
  match n with
  | Names.PInt    => Some (Compilable.TypeResolution.IntegerType Integer.Int)    | Names.PInt8  => Some (Compilable.TypeResolution.IntegerType Integer.Int8)
  | Names.PInt16  => Some (Compilable.TypeResolution.IntegerType Integer.Int16)  | Names.PInt32 => Some (Compilable.TypeResolution.IntegerType Integer.Int32)
  | Names.PInt64  => Some (Compilable.TypeResolution.IntegerType Integer.Int64)
  | Names.PUint   => Some (Compilable.TypeResolution.IntegerType Integer.Uint)   | Names.PUint8  => Some (Compilable.TypeResolution.IntegerType Integer.Uint8)
  | Names.PUint16 => Some (Compilable.TypeResolution.IntegerType Integer.Uint16) | Names.PUint32 => Some (Compilable.TypeResolution.IntegerType Integer.Uint32)
  | Names.PUint64 => Some (Compilable.TypeResolution.IntegerType Integer.Uint64)
  | Names.PFloat32 => Some (Compilable.TypeResolution.FloatType Float.F32) | Names.PFloat64 => Some (Compilable.TypeResolution.FloatType Float.F64)
  | Names.PComplex64 => Some (Compilable.TypeResolution.ComplexType Complex.C64) | Names.PComplex128 => Some (Compilable.TypeResolution.ComplexType Complex.C128)
  | Names.PByte => Some (Compilable.TypeResolution.IntegerType Integer.Uint8) | Names.PRune => Some (Compilable.TypeResolution.IntegerType Integer.Int32)
  | _ => None
  end.

(* The compiler owns the binding result of resolving a name: a semantic meaning, or unresolved/unmodelled. *)
Inductive Resolution : Type :=
| ResMeaning    : Compilable.TypeResolution.NameMeaning -> Resolution
| ResUnresolved : Resolution
| ResUnmodelled : Resolution.

(* The local typing spec needs a meaning or nothing; the compiler-owned failure kind stays behind. *)
Definition resolution_meaning (r : Resolution) : option Compilable.TypeResolution.NameMeaning :=
  match r with ResMeaning m => Some m | _ => None end.

Definition predeclared_meaning (n : Names.PredeclaredName) : Resolution :=
  match predeclared_type_of_name n with
  | Some t => ResMeaning (Compilable.TypeResolution.NMConversionType t)
  | None =>
      match n with
      | Names.PTrue    => ResMeaning (Compilable.TypeResolution.NMValueConstant (Compilable.TypeResolution.BoolConstant true))
      | Names.PFalse   => ResMeaning (Compilable.TypeResolution.NMValueConstant (Compilable.TypeResolution.BoolConstant false))
      | Names.PComplex => ResMeaning Compilable.TypeResolution.NMComplexBuiltin
      | Names.PPrintln => ResMeaning Compilable.TypeResolution.NMPrintlnBuiltin
      | _ => ResUnmodelled
      end
  end.

Definition object_meaning {p} {idx : Index.ProgramIndex p} (o : Compilable.Bindings.ObjectRef idx) : Resolution :=
  match o with
  | Compilable.Bindings.PredeclaredObject n => predeclared_meaning n
  | Compilable.Bindings.SourceObject _      => ResUnmodelled   (* type/value/callable meaning is a later root *)
  end.

Definition is_value_role (r : Index.Role) : bool :=
  match r with Index.ApplicationHead => false | _ => true end.
Definition is_stmt_expr_role (r : Index.Role) : bool :=
  match r with Index.ExprStatementExpr => true | _ => false end.

Section WithProgram.
Variable p : Syntax.Program.

(* the resolver at a use, over the retained index and the once-gathered establishers *)
Definition resolver_at (idx : Index.ProgramIndex p) (es : list (Compilable.Bindings.Establisher idx))
    (use_path : FilePath.T) (use_id : positive) (n : Names.OrdinaryIdentifier) : Resolution :=
  match Compilable.Bindings.resolve p idx es use_path use_id (Names.ordinary_spelling n) with
  | Some o => object_meaning o
  | None   => ResUnresolved
  end.

(* The local typing spec's view of the resolver: a meaning where one exists, None for unresolved/unmodelled. *)
Definition nm_at (idx : Index.ProgramIndex p) (es : list (Compilable.Bindings.Establisher idx))
    (use_path : FilePath.T) (use_id : positive) : Names.OrdinaryIdentifier -> option Compilable.TypeResolution.NameMeaning :=
  fun n => resolution_meaning (resolver_at idx es use_path use_id n).

(* whether an occurrence is a println argument whose default type cannot hold it — the exact overflow site *)
Definition arg_default_overflow (idx : Index.ProgramIndex p) (es : list (Compilable.Bindings.Establisher idx))
    (path : FilePath.T) (f : Syntax.File) (id : positive) (occ : Index.Occurrence)
  : option Compilable.TypeResolution.Constant :=
  match Index.occurrence_role occ with
  | Index.ApplicationArgument _ =>
      match Index.occurrence_parent occ with
      | Some pid =>
          match Index.source_occurrence_at f pid with
          | Some pocc =>
              match Index.view_expr pocc with
              | Some (Syntax.Application (Syntax.Name h) _) =>
                  match resolver_at idx es path pid h with
                  | ResMeaning Compilable.TypeResolution.NMPrintlnBuiltin =>
                      match Index.view_expr occ with
                      | Some e =>
                          match Compilable.TypeResolution.constant_info (nm_at idx es path id) e with
                          | Some ci =>
                              match Compilable.TypeResolution.resolve_constant_info ci with
                              | None    => Some (Compilable.TypeResolution.constant_info_exact ci)
                              | Some _  => None
                              end
                          | None => None
                          end
                      | None => None
                      end
                  | _ => None
                  end
              | _ => None
              end
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

Definition occ_diag (idx : Index.ProgramIndex p) (es : list (Compilable.Bindings.Establisher idx))
    (path : FilePath.T) (f : Syntax.File) (id : positive) (occ : Index.Occurrence)
  : list RootCause :=
  let k  := Index.MakeKey path id in
  (match Index.view_expr occ with
   | Some (Syntax.Name n) =>
       match Compilable.Bindings.resolve p idx es path id (Names.ordinary_spelling n) with None => [RCUnresolvedName k] | Some _ => [] end
   | _ => [] end)
  ++
  (match Index.view_expr occ with
   | Some (Syntax.Application (Syntax.Name h) (x :: nil)) =>
       match resolver_at idx es path id h with
       | ResMeaning (Compilable.TypeResolution.NMConversionType t) =>
           match Compilable.TypeResolution.constant_info (nm_at idx es path id) x with
           | Some ci => match Compilable.TypeResolution.convert_constant t ci with Some _ => [] | None => [RCInvalidConversion k t x] end
           | None => []
           end
       | _ => []
       end
   | _ => [] end)
  ++
  (match Index.view_expr occ with
   | Some (Syntax.Unary Syntax.UnaryMinus e') =>
       match Compilable.TypeResolution.constant_info (nm_at idx es path id) e' with
       | Some _ =>
           match Compilable.TypeResolution.constant_info (nm_at idx es path id) (Syntax.Unary Syntax.UnaryMinus e') with
           | Some _ => [] | None => [RCUnaryTypeMismatch k e']
           end
       | None => []
       end
   | _ => [] end)
  ++
  (match Index.view_expr occ with
   | Some (Syntax.Application (Syntax.Name h) args) =>
       match resolver_at idx es path id h with
       | ResMeaning (Compilable.TypeResolution.NMConversionType _) => match args with _ :: nil => [] | _ => [RCConversionArity k] end
       | ResMeaning Compilable.TypeResolution.NMComplexBuiltin     => match args with _ :: _ :: nil => [] | _ => [RCComplexArity k] end
       | ResMeaning Compilable.TypeResolution.NMPrintlnBuiltin     => if is_stmt_expr_role (Index.occurrence_role occ) then [] else [RCNoValueUsed k]
       | ResMeaning (Compilable.TypeResolution.NMValueConstant _)  => [RCNotCallable k]
       | ResUnresolved => []
       | ResUnmodelled => []
       end
   | Some (Syntax.Application (Syntax.LiteralExpr _) _) => [RCNotCallable k]
   | _ => [] end)
  ++
  (match Index.view_expr occ with
   | Some (Syntax.Application (Syntax.Name h) (re :: im :: nil)) =>
       match resolver_at idx es path id h with
       | ResMeaning Compilable.TypeResolution.NMComplexBuiltin =>
           match Compilable.TypeResolution.constant_info (nm_at idx es path id) re, Compilable.TypeResolution.constant_info (nm_at idx es path id) im with
           | Some cre, Some cim => match Compilable.TypeResolution.complex_class cre cim with Compilable.TypeResolution.CxError => [RCComplexTypeMismatch k] | _ => [] end
           | _, _ => []
           end
       | _ => []
       end
   | _ => [] end)
  ++
  (match Index.view_expr occ with
   | Some (Syntax.Name n) =>
       if is_value_role (Index.occurrence_role occ) then
         match resolver_at idx es path id n with
         | ResMeaning (Compilable.TypeResolution.NMConversionType _) | ResMeaning Compilable.TypeResolution.NMComplexBuiltin | ResMeaning Compilable.TypeResolution.NMPrintlnBuiltin => [RCTypeAsValue k]
         | _ => []
         end
       else []
   | _ => [] end)
  ++
  (match Index.view_stmt occ with
   | Some (Syntax.ExprStmt (Syntax.Application (Syntax.Name h) _)) =>
       match resolver_at idx es path id h with
       | ResMeaning Compilable.TypeResolution.NMPrintlnBuiltin => []
       | ResUnmodelled | ResUnresolved => []
       | _ => [RCIllegalStatement k]
       end
   | Some (Syntax.ExprStmt _) => [RCIllegalStatement k]
   | _ => [] end)
  ++
  (match arg_default_overflow idx es path f id occ with Some c => [RCDefaultNotRepresentable k c] | None => [] end).

Definition occ_boundary (idx : Index.ProgramIndex p) (es : list (Compilable.Bindings.Establisher idx))
    (path : FilePath.T) (id : positive) (occ : Index.Occurrence)
  : list Boundary :=
  let k  := Index.MakeKey path id in
  (match Index.view_expr occ with
   | Some (Syntax.Name n) =>
       if is_value_role (Index.occurrence_role occ) then
         match Compilable.Bindings.resolve p idx es path id (Names.ordinary_spelling n) with
         | Some o => match object_meaning o with ResMeaning (Compilable.TypeResolution.NMValueConstant _) => [] | _ => [MakeBoundary k (ReqValueMeaning (Compilable.Bindings.object_key o))] end
         | None   => []
         end
       else []
   | _ => [] end)
  ++
  (match Index.view_expr occ with
   | Some (Syntax.Application (Syntax.Name h) args) =>
       match resolver_at idx es path id h with
       | ResMeaning (Compilable.TypeResolution.NMConversionType _) => match args with _ :: nil => [] | _ => [MakeBoundary k ReqApplication] end
       | ResMeaning Compilable.TypeResolution.NMComplexBuiltin     => match args with _ :: _ :: nil => [] | _ => [MakeBoundary k ReqApplication] end
       | ResMeaning Compilable.TypeResolution.NMPrintlnBuiltin     => if is_stmt_expr_role (Index.occurrence_role occ) then [] else [MakeBoundary k ReqApplication]
       | ResUnresolved => []
       | _ => [MakeBoundary k ReqApplication]
       end
   | Some (Syntax.Application _ _) => [MakeBoundary k ReqApplication]
   | _ => [] end)
  ++
  (match Index.view_stmt occ with
   | Some (Syntax.ExprStmt (Syntax.Application (Syntax.Name h) _)) =>
       match resolver_at idx es path id h with ResMeaning Compilable.TypeResolution.NMPrintlnBuiltin => [] | _ => [MakeBoundary k ReqStatement] end
   | Some _ => [MakeBoundary k ReqStatement]
   | None => [] end)
  ++
  (match Index.view_toplevel occ with
   | Some (Syntax.TopDeclaration _) => [MakeBoundary k ReqDeclaration]
   | _ => [] end).

Definition file_diags (idx : Index.ProgramIndex p) (es : list (Compilable.Bindings.Establisher idx)) (b : FilePath.T * Syntax.File)
  : list RootCause :=
  flat_map (fun idocc => occ_diag idx es (fst b) (snd b) (fst idocc) (snd idocc)) (Index.occurrences_file (snd b)).
Definition expr_diags : list RootCause :=
  let idx := Index.index_program p in
  let es := Compilable.Bindings.establishers p idx in
  flat_map (file_diags idx es) (Syntax.file_bindings (Syntax.files p)).

Definition file_boundaries (idx : Index.ProgramIndex p) (es : list (Compilable.Bindings.Establisher idx)) (b : FilePath.T * Syntax.File)
  : list Boundary :=
  flat_map (fun idocc => occ_boundary idx es (fst b) (fst idocc) (snd idocc)) (Index.occurrences_file (snd b)).
Definition all_boundaries : list Boundary :=
  let idx := Index.index_program p in
  let es := Compilable.Bindings.establishers p idx in
  flat_map (file_boundaries idx es) (Syntax.file_bindings (Syntax.files p)).

(* Package-level diagnostics: the current grammar requires exactly one `main` per package. *)
Definition package_rule_diags : list RootCause :=
  flat_map (fun ds =>
     let dir := fst ds in let cnt := Compilable.Packages.summary_main_count (snd ds) in
     ((if Nat.ltb 1 cnt then [RCMainRedeclared dir] else [])
      ++ (if Nat.eqb cnt 0 then [RCMissingMain dir] else []))%list)
   (Compilable.Packages.PackageMap.elements (Compilable.Packages.package_summaries (Syntax.files p))).

Definition preflight_diags : list RootCause :=
  if Compilable.Packages.fresh_build_disposition_ok (Compilable.Packages.fresh_build_plan p) then []
  else match Compilable.Packages.selected_package_keys p with
       | dir :: nil => [RCBuildOutputDir dir (Compilable.Packages.default_exec_name (Syntax.module_spec p) dir)]
       | _ => []
       end.

(* preflight precedence: a fresh-build failure precedes package-semantic errors, which precede expression errors *)
Definition all_diags : list RootCause := (preflight_diags ++ package_rule_diags ++ expr_diags)%list.

End WithProgram.
