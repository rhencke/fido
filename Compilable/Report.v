(* Report — diagnostics (definite errors) and requirements (outside boundaries); each retains its exact site key. *)
From Stdlib Require Import List Bool String Ascii ZArith NArith Lia.
From Fido Require Import Names Integer Float Complex FilePath Syntax Index Compilable.TypeResolution Compilable.Bindings Compilable.Facts Compilable.Packages.
Import ListNotations.

Inductive RootCause : Type :=
| RCUnresolvedName        : Index.Key -> RootCause
| RCInvalidConversion     : Index.Key -> Compilable.TypeResolution.SemanticType -> Syntax.Expr -> RootCause
| RCDefaultNotRepresentable : Index.Key -> Compilable.TypeResolution.Constant -> RootCause
| RCUnaryTypeMismatch     : Index.Key -> Syntax.Expr -> RootCause
| RCComplexTypeMismatch   : Index.Key -> RootCause
| RCConversionArity       : Index.Key -> RootCause
| RCComplexArity          : Index.Key -> RootCause
| RCNotCallable           : Index.Key -> RootCause
| RCTypeAsValue           : Index.Key -> RootCause
| RCNoValueUsed           : Index.Key -> RootCause
| RCIllegalStatement      : Index.Key -> RootCause
| RCMainRedeclared        : string -> RootCause
| RCMissingMain           : string -> RootCause
| RCBuildOutputDir        : string -> string -> RootCause.

Inductive Requirement : Type :=
| ReqValueMeaning : option Index.Key -> Requirement
| ReqApplication  : Requirement
| ReqStatement    : Requirement
| ReqDeclaration  : Requirement
| ReqUnary        : Requirement.

Record Boundary : Type := MakeBoundary { boundary_site : Index.Key ; boundary_req : Requirement }.

Section WithProgram.
Variable p : Syntax.Program.

Definition occ_diag (idx : Index.ProgramIndex p) (es : list (Compilable.Bindings.Establisher idx))
    (path : FilePath.T) (f : Syntax.File) (id : positive) (c : Index.CFile f)
  : list RootCause :=
  let k  := Index.MakeKey path id in
  (match Index.cfile_view_expr c with
   | Some (Syntax.Name n) =>
       match Compilable.Bindings.resolve p idx es path id (Names.ordinary_spelling n) with None => [RCUnresolvedName k] | Some _ => [] end
   | _ => [] end)
  ++
  (match Index.cfile_view_expr c with
   | Some (Syntax.Application (Syntax.Name h) (x :: nil)) =>
       match Compilable.Facts.resolver_at p idx es path id h with
       | Compilable.Facts.ResMeaning (Compilable.TypeResolution.NMConversionType t) =>
           match Compilable.TypeResolution.constant_info (Compilable.Facts.nm_at p idx es path id) x with
           | Some ci => match Compilable.TypeResolution.convert_constant t ci with Some _ => [] | None => [RCInvalidConversion k t x] end
           | None => []
           end
       | _ => []
       end
   | _ => [] end)
  ++
  (match Index.cfile_view_expr c with
   | Some (Syntax.Unary Syntax.UnaryMinus e') =>
       match Compilable.TypeResolution.constant_info (Compilable.Facts.nm_at p idx es path id) e' with
       | Some _ =>
           match Compilable.TypeResolution.constant_info (Compilable.Facts.nm_at p idx es path id) (Syntax.Unary Syntax.UnaryMinus e') with
           | Some _ => [] | None => [RCUnaryTypeMismatch k e']
           end
       | None => []
       end
   | _ => [] end)
  ++
  (match Index.cfile_view_expr c with
   | Some (Syntax.Application (Syntax.Name h) args) =>
       match Compilable.Facts.resolver_at p idx es path id h with
       | Compilable.Facts.ResMeaning (Compilable.TypeResolution.NMConversionType _) => match args with _ :: nil => [] | _ => [RCConversionArity k] end
       | Compilable.Facts.ResMeaning Compilable.TypeResolution.NMComplexBuiltin     => match args with _ :: _ :: nil => [] | _ => [RCComplexArity k] end
       | Compilable.Facts.ResMeaning Compilable.TypeResolution.NMPrintlnBuiltin     => if Compilable.Facts.is_stmt_expr_role (Index.cfile_role c) then [] else [RCNoValueUsed k]
       | Compilable.Facts.ResMeaning (Compilable.TypeResolution.NMValueConstant _)  => [RCNotCallable k]
       | Compilable.Facts.ResUnresolved => []
       | Compilable.Facts.ResUnmodelled => []
       end
   | Some (Syntax.Application (Syntax.LiteralExpr _) _) => [RCNotCallable k]
   | _ => [] end)
  ++
  (match Index.cfile_view_expr c with
   | Some (Syntax.Application (Syntax.Name h) (re :: im :: nil)) =>
       match Compilable.Facts.resolver_at p idx es path id h with
       | Compilable.Facts.ResMeaning Compilable.TypeResolution.NMComplexBuiltin =>
           match Compilable.TypeResolution.constant_info (Compilable.Facts.nm_at p idx es path id) re, Compilable.TypeResolution.constant_info (Compilable.Facts.nm_at p idx es path id) im with
           | Some cre, Some cim => match Compilable.TypeResolution.complex_class cre cim with Compilable.TypeResolution.CxError => [RCComplexTypeMismatch k] | _ => [] end
           | _, _ => []
           end
       | _ => []
       end
   | _ => [] end)
  ++
  (match Index.cfile_view_expr c with
   | Some (Syntax.Name n) =>
       if Compilable.Facts.is_value_role (Index.cfile_role c) then
         match Compilable.Facts.resolver_at p idx es path id n with
         | Compilable.Facts.ResMeaning (Compilable.TypeResolution.NMConversionType _) | Compilable.Facts.ResMeaning Compilable.TypeResolution.NMComplexBuiltin | Compilable.Facts.ResMeaning Compilable.TypeResolution.NMPrintlnBuiltin => [RCTypeAsValue k]
         | _ => []
         end
       else []
   | _ => [] end)
  ++
  (match Index.cfile_view_stmt c with
   | Some (Syntax.ExprStmt (Syntax.Application (Syntax.Name h) _)) =>
       match Compilable.Facts.resolver_at p idx es path id h with
       | Compilable.Facts.ResMeaning Compilable.TypeResolution.NMPrintlnBuiltin => []
       | Compilable.Facts.ResUnmodelled | Compilable.Facts.ResUnresolved => []
       | _ => [RCIllegalStatement k]
       end
   | Some (Syntax.ExprStmt _) => [RCIllegalStatement k]
   | _ => [] end)
  ++
  (match Compilable.Facts.arg_default_overflow p idx es path f id c with Some cst => [RCDefaultNotRepresentable k cst] | None => [] end).

Definition occ_boundary (idx : Index.ProgramIndex p) (es : list (Compilable.Bindings.Establisher idx))
    (path : FilePath.T) (f : Syntax.File) (id : positive) (c : Index.CFile f)
  : list Boundary :=
  let k  := Index.MakeKey path id in
  (match Index.cfile_view_expr c with
   | Some (Syntax.Name n) =>
       if Compilable.Facts.is_value_role (Index.cfile_role c) then
         match Compilable.Bindings.resolve p idx es path id (Names.ordinary_spelling n) with
         | Some o => match Compilable.Facts.object_meaning o with Compilable.Facts.ResMeaning (Compilable.TypeResolution.NMValueConstant _) => [] | _ => [MakeBoundary k (ReqValueMeaning (Compilable.Bindings.object_key o))] end
         | None   => []
         end
       else []
   | _ => [] end)
  ++
  (match Index.cfile_view_expr c with
   | Some (Syntax.Application (Syntax.Name h) args) =>
       match Compilable.Facts.resolver_at p idx es path id h with
       | Compilable.Facts.ResMeaning (Compilable.TypeResolution.NMConversionType _) => match args with _ :: nil => [] | _ => [MakeBoundary k ReqApplication] end
       | Compilable.Facts.ResMeaning Compilable.TypeResolution.NMComplexBuiltin     => match args with _ :: _ :: nil => [] | _ => [MakeBoundary k ReqApplication] end
       | Compilable.Facts.ResMeaning Compilable.TypeResolution.NMPrintlnBuiltin     => if Compilable.Facts.is_stmt_expr_role (Index.cfile_role c) then [] else [MakeBoundary k ReqApplication]
       | Compilable.Facts.ResUnresolved => []
       | _ => [MakeBoundary k ReqApplication]
       end
   | Some (Syntax.Application _ _) => [MakeBoundary k ReqApplication]
   | _ => [] end)
  ++
  (match Index.cfile_view_stmt c with
   | Some (Syntax.ExprStmt (Syntax.Application (Syntax.Name h) _)) =>
       match Compilable.Facts.resolver_at p idx es path id h with Compilable.Facts.ResMeaning Compilable.TypeResolution.NMPrintlnBuiltin => [] | _ => [MakeBoundary k ReqStatement] end
   | Some _ => [MakeBoundary k ReqStatement]
   | None => [] end)
  ++
  (match Index.cfile_view_toplevel c with
   | Some (Syntax.TopDeclaration _) => [MakeBoundary k ReqDeclaration]
   | _ => [] end).

Definition file_diags (idx : Index.ProgramIndex p) (es : list (Compilable.Bindings.Establisher idx)) (fr : Index.Snapshot.FileRef p)
  : list RootCause :=
  flat_map (fun t => occ_diag idx es (Index.Snapshot.file_ref_path fr) (Index.Snapshot.local_source idx fr) (fst (fst t)) (snd t))
           (Index.Snapshot.local_index idx fr).

Definition file_boundaries (idx : Index.ProgramIndex p) (es : list (Compilable.Bindings.Establisher idx)) (fr : Index.Snapshot.FileRef p)
  : list Boundary :=
  flat_map (fun t => occ_boundary idx es (Index.Snapshot.file_ref_path fr) (Index.Snapshot.local_source idx fr) (fst (fst t)) (snd t))
           (Index.Snapshot.local_index idx fr).

(* Package-level diagnostics: attach the exact RootCause to Packages' one canonical per-package rule status. *)
Definition package_rule_diags : list RootCause :=
  flat_map (fun ds =>
     (match snd ds with
      | Compilable.Packages.PackageMainRedeclared => [RCMainRedeclared (fst ds)]
      | Compilable.Packages.PackageMissingMain => [RCMissingMain (fst ds)]
      | Compilable.Packages.PackageOneMain => []
      end)%list)
   (Compilable.Packages.package_rule_result p).

Definition preflight_diags : list RootCause :=
  if Compilable.Packages.fresh_build_disposition_ok (Compilable.Packages.fresh_build_plan p) then []
  else match Compilable.Packages.selected_package_keys p with
       | dir :: nil => [RCBuildOutputDir dir (Compilable.Packages.default_exec_name (Syntax.module_spec p) dir)]
       | _ => []
       end.

(* the one static phase: index/establishers built once; both ordered lists project from it (preflight<package<expr) *)
Definition elaborate_phase : list RootCause * list Boundary :=
  let idx := Index.index_program p in
  let es := Compilable.Bindings.establishers p idx in
  ((preflight_diags ++ package_rule_diags ++ flat_map (file_diags idx es) (Index.Snapshot.file_refs p))%list,
   flat_map (file_boundaries idx es) (Index.Snapshot.file_refs p)).
Definition all_diags : list RootCause := fst elaborate_phase.
Definition all_boundaries : list Boundary := snd elaborate_phase.

End WithProgram.
