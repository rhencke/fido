(* Compilable — the static semantic phase and the permanent three-way Compiled/Rejected/OutsideScope decision. *)

From Stdlib Require Import List Bool String Ascii ZArith NArith Lia.
From Fido Require Import Collections FilePath ModulePath Version Names Integer Float Complex Syntax Index Typing Bindings Packages.
Import ListNotations.

(* Predeclared object meaning: what a predeclared name denotes (type / value const / builtin) in the fragment. *)
Definition predeclared_type_of_name (n : Names.TypeName) : Typing.SemanticType :=
  match n with
  | Names.Int    => Typing.IntegerType Integer.Int    | Names.Int8  => Typing.IntegerType Integer.Int8
  | Names.Int16  => Typing.IntegerType Integer.Int16  | Names.Int32 => Typing.IntegerType Integer.Int32
  | Names.Int64  => Typing.IntegerType Integer.Int64
  | Names.Uint   => Typing.IntegerType Integer.Uint   | Names.Uint8  => Typing.IntegerType Integer.Uint8
  | Names.Uint16 => Typing.IntegerType Integer.Uint16 | Names.Uint32 => Typing.IntegerType Integer.Uint32
  | Names.Uint64 => Typing.IntegerType Integer.Uint64
  | Names.Float32 => Typing.FloatType Float.F32 | Names.Float64 => Typing.FloatType Float.F64
  | Names.Complex64 => Typing.ComplexType Complex.C64 | Names.Complex128 => Typing.ComplexType Complex.C128
  | Names.Byte => Typing.IntegerType Integer.Uint8 | Names.Rune => Typing.IntegerType Integer.Int32
  end.

Definition predeclared_meaning (n : Names.PredeclaredName) : Typing.NameMeaning :=
  match Names.predeclared_type_name n with
  | Some tn => Typing.NMConversionType (predeclared_type_of_name tn)
  | None =>
      match n with
      | Names.PTrue    => Typing.NMValueConstant (Typing.BoolConstant true)
      | Names.PFalse   => Typing.NMValueConstant (Typing.BoolConstant false)
      | Names.PComplex => Typing.NMComplexBuiltin
      | Names.PPrintln => Typing.NMPrintlnBuiltin
      | _ => Typing.NMUnmodelled
      end
  end.

Definition object_meaning (o : Bindings.ObjectRef) : Typing.NameMeaning :=
  match o with
  | Bindings.PredeclaredObject n => predeclared_meaning n
  | Bindings.SourceObject _      => Typing.NMUnmodelled   (* type/value/callable meaning is a later root *)
  end.

(* The predeclared spelling resolver — used only where no source binder shadows (a Compiled program). *)
Definition predeclared_resolver (n : Names.OrdinaryIdentifier) : Typing.NameMeaning :=
  match Names.classify_predeclared (Names.ordinary_spelling n) with
  | Some pn => predeclared_meaning pn
  | None    => Typing.NMUnresolved
  end.

(* Diagnostics (definite errors) and requirements (outside boundaries); each retains its exact site key. *)
Inductive RootCause : Type :=
| RCUnresolvedName        : Index.Key -> RootCause
| RCInvalidConversion     : Index.Key -> Typing.SemanticType -> Syntax.Expr -> RootCause
| RCDefaultNotRepresentable : Index.Key -> Typing.Constant -> RootCause
| RCMainRedeclared        : string -> RootCause
| RCMissingMain           : string -> RootCause
| RCBuildOutputDir        : string -> string -> RootCause.

Inductive Requirement : Type :=
| ReqValueMeaning : Bindings.ObjectRef -> Requirement
| ReqApplication  : Requirement
| ReqStatement    : Requirement
| ReqDeclaration  : Requirement
| ReqUnary        : Requirement.

Record Boundary : Type := MakeBoundary { boundary_site : Index.Key ; boundary_req : Requirement }.

Definition is_value_role (r : Index.Role) : bool :=
  match r with Index.ApplicationHead => false | _ => true end.
Definition is_stmt_expr_role (r : Index.Role) : bool :=
  match r with Index.ExprStatementExpr => true | _ => false end.

Section WithProgram.
Variable p : Syntax.Program.

(* The binding-derived resolver at a scope: shadowing through binding, occurrence-honest within one expression. *)
Definition resolver_at (sc : Bindings.ScopeId) (n : Names.OrdinaryIdentifier) : Typing.NameMeaning :=
  match Bindings.resolve p sc (Names.ordinary_spelling n) with
  | Some o => object_meaning o
  | None   => Typing.NMUnresolved
  end.

(* Whether an occurrence is a println argument whose default type cannot hold it — the exact overflow site. *)
Definition arg_default_overflow (path : FilePath.T) (f : Syntax.File) (id : positive) (occ : Index.Occurrence)
  : option Typing.Constant :=
  match Index.occurrence_role occ with
  | Index.ApplicationArgument _ =>
      match Index.occurrence_parent occ with
      | Some pid =>
          match Index.source_occurrence_at f pid with
          | Some pocc =>
              match Index.view_expr pocc with
              | Some (Syntax.Application (Syntax.Name h) _) =>
                  match resolver_at (Bindings.scope_of_id path f pid) h with
                  | Typing.NMPrintlnBuiltin =>
                      match Index.view_expr occ with
                      | Some e =>
                          match Typing.constant_info (resolver_at (Bindings.scope_of_id path f id)) e with
                          | Some ci =>
                              match Typing.resolve_constant_info ci with
                              | None    => Some (Typing.constant_info_exact ci)
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

Definition occ_diag (path : FilePath.T) (f : Syntax.File) (id : positive) (occ : Index.Occurrence)
  : list RootCause :=
  let sc := Bindings.scope_of_id path f id in
  let k  := Index.MakeKey path id in
  (match Index.view_expr occ with
   | Some (Syntax.Name n) =>
       match Bindings.resolve p sc (Names.ordinary_spelling n) with None => [RCUnresolvedName k] | Some _ => [] end
   | _ => [] end)
  ++
  (match Index.view_expr occ with
   | Some (Syntax.Application (Syntax.Name h) (x :: nil)) =>
       match resolver_at sc h with
       | Typing.NMConversionType t =>
           match Typing.constant_info (resolver_at sc) x with
           | Some ci => match Typing.convert_constant t ci with Some _ => [] | None => [RCInvalidConversion k t x] end
           | None => []
           end
       | _ => []
       end
   | _ => [] end)
  ++
  (match arg_default_overflow path f id occ with Some c => [RCDefaultNotRepresentable k c] | None => [] end).

Definition occ_boundary (path : FilePath.T) (f : Syntax.File) (id : positive) (occ : Index.Occurrence)
  : list Boundary :=
  let sc := Bindings.scope_of_id path f id in
  let k  := Index.MakeKey path id in
  (match Index.view_expr occ with
   | Some (Syntax.Name n) =>
       if is_value_role (Index.occurrence_role occ) then
         match Bindings.resolve p sc (Names.ordinary_spelling n) with
         | Some o => match object_meaning o with Typing.NMValueConstant _ => [] | _ => [MakeBoundary k (ReqValueMeaning o)] end
         | None   => []
         end
       else []
   | _ => [] end)
  ++
  (match Index.view_expr occ with
   | Some (Syntax.Application (Syntax.Name h) args) =>
       match resolver_at sc h with
       | Typing.NMConversionType _ => match args with _ :: nil => [] | _ => [MakeBoundary k ReqApplication] end
       | Typing.NMComplexBuiltin   => match args with _ :: _ :: nil => [] | _ => [MakeBoundary k ReqApplication] end
       | Typing.NMPrintlnBuiltin   => if is_stmt_expr_role (Index.occurrence_role occ) then [] else [MakeBoundary k ReqApplication]
       | Typing.NMUnresolved       => []
       | _ => [MakeBoundary k ReqApplication]
       end
   | Some (Syntax.Application _ _) => [MakeBoundary k ReqApplication]
   | _ => [] end)
  ++
  (match Index.view_stmt occ with
   | Some (Syntax.ExprStmt (Syntax.Application (Syntax.Name h) _)) =>
       match resolver_at sc h with Typing.NMPrintlnBuiltin => [] | _ => [MakeBoundary k ReqStatement] end
   | Some _ => [MakeBoundary k ReqStatement]
   | None => [] end)
  ++
  (match Index.view_toplevel occ with
   | Some (Syntax.TopDeclaration _) => [MakeBoundary k ReqDeclaration]
   | _ => [] end).

Definition file_diags (b : FilePath.T * Syntax.File) : list RootCause :=
  flat_map (fun idocc => occ_diag (fst b) (snd b) (fst idocc) (snd idocc)) (Index.occurrences_file (snd b)).
Definition expr_diags : list RootCause :=
  flat_map file_diags (Syntax.file_bindings (Syntax.files p)).

Definition file_boundaries (b : FilePath.T * Syntax.File) : list Boundary :=
  flat_map (fun idocc => occ_boundary (fst b) (snd b) (fst idocc) (snd idocc)) (Index.occurrences_file (snd b)).
Definition all_boundaries : list Boundary :=
  flat_map file_boundaries (Syntax.file_bindings (Syntax.files p)).

(* Package-level diagnostics: the current grammar requires exactly one `main` per package. *)
Definition package_rule_diags : list RootCause :=
  flat_map (fun ds =>
     let dir := fst ds in let cnt := Packages.summary_main_count (snd ds) in
     ((if Nat.ltb 1 cnt then [RCMainRedeclared dir] else [])
      ++ (if Nat.eqb cnt 0 then [RCMissingMain dir] else []))%list)
   (Packages.PackageMap.elements (Packages.package_summaries (Syntax.files p))).

Definition preflight_diags : list RootCause :=
  if Packages.fresh_build_disposition_ok (Packages.fresh_build_plan p) then []
  else match Packages.selected_package_keys p with
       | dir :: nil => [RCBuildOutputDir dir (Packages.default_exec_name (Syntax.module_spec p) dir)]
       | _ => []
       end.

Definition all_diags : list RootCause := (expr_diags ++ package_rule_diags ++ preflight_diags)%list.

End WithProgram.

(* The core and the three verdict payloads are sealed behind CAPABILITY; the only way to one is compile. *)
Definition Admissible (p : Syntax.Program) : Prop := all_diags p = [] /\ all_boundaries p = [].

Module Type CAPABILITY.
  Parameter Core : Syntax.Program -> Type.
  Parameter core_diagnostics : forall {p}, Core p -> list RootCause.
  Parameter core_boundaries  : forall {p}, Core p -> list Boundary.
  Parameter elaborate : forall p, Core p.
  Parameter elaborate_diagnostics : forall p, core_diagnostics (elaborate p) = all_diags p.
  Parameter elaborate_boundaries  : forall p, core_boundaries (elaborate p) = all_boundaries p.

  Parameter Program : Type.
  Parameter source   : Program -> Syntax.Program.
  Parameter core     : forall cp : Program, Core (source cp).
  Parameter accepted : forall cp : Program, core_diagnostics (core cp) = [].
  Parameter in_scope : forall cp : Program, core_boundaries (core cp) = [].

  Parameter Failure : Syntax.Program -> Type.
  Parameter failure_core : forall {p}, Failure p -> Core p.
  Parameter rejected : forall {p} (f : Failure p), core_diagnostics (failure_core f) <> [].

  Parameter Outside_ : Syntax.Program -> Type.
  Parameter outside_core    : forall {p}, Outside_ p -> Core p.
  Parameter outside_clean   : forall {p} (o : Outside_ p), core_diagnostics (outside_core o) = [].
  Parameter outside_blocked : forall {p} (o : Outside_ p), core_boundaries (outside_core o) <> [].

  Inductive Outcome (p : Syntax.Program) : Type :=
  | Compiled (cp : Program) (Hcp : source cp = p)
  | Rejected (f : Failure p)
  | OutsideScope (o : Outside_ p).

  Parameter compile : forall p : Syntax.Program, Outcome p.
  Parameter capability_of_admissible : forall p, Admissible p -> Program.
  Parameter capability_source : forall p (H : Admissible p), source (capability_of_admissible p H) = p.
End CAPABILITY.

Module Capability : CAPABILITY.
  Record CoreRep (p : Syntax.Program) : Type := MkCore {
    core_diagnostics : list RootCause;
    core_boundaries  : list Boundary;
    core_diags_pf    : core_diagnostics = all_diags p;
    core_bounds_pf   : core_boundaries = all_boundaries p
  }.
  Arguments core_diagnostics {p}. Arguments core_boundaries {p}.
  Definition Core := CoreRep.
  Definition elaborate (p : Syntax.Program) : Core p :=
    MkCore p (all_diags p) (all_boundaries p) eq_refl eq_refl.
  Lemma elaborate_diagnostics : forall p, core_diagnostics (elaborate p) = all_diags p. Proof. reflexivity. Qed.
  Lemma elaborate_boundaries  : forall p, core_boundaries (elaborate p) = all_boundaries p. Proof. reflexivity. Qed.

  Record ProgramRep : Type := MkProg {
    source   : Syntax.Program;
    core     : Core source;
    accepted : core_diagnostics core = [];
    in_scope : core_boundaries core = []
  }.
  Definition Program := ProgramRep.

  Record FailureRep (p : Syntax.Program) : Type := MkFail {
    failure_core : Core p;
    rejected     : core_diagnostics failure_core <> []
  }.
  Arguments failure_core {p}. Arguments rejected {p}.
  Definition Failure := FailureRep.

  Record OutsideRep (p : Syntax.Program) : Type := MkOut {
    outside_core    : Core p;
    outside_clean   : core_diagnostics outside_core = [];
    outside_blocked : core_boundaries outside_core <> []
  }.
  Arguments outside_core {p}. Arguments outside_clean {p}. Arguments outside_blocked {p}.
  Definition Outside_ := OutsideRep.

  Inductive Outcome (p : Syntax.Program) : Type :=
  | Compiled (cp : Program) (Hcp : source cp = p)
  | Rejected (f : Failure p)
  | OutsideScope (o : Outside_ p).

  Definition compile (p : Syntax.Program) : Outcome p.
    destruct (all_diags p) as [|d ds] eqn:Hd.
    - destruct (all_boundaries p) as [|b bs] eqn:Hb.
      + exact (Compiled p (MkProg p (elaborate p) Hd Hb) eq_refl).
      + refine (OutsideScope p (MkOut p (elaborate p) Hd _)).
        change (all_boundaries p <> []); rewrite Hb; discriminate.
    - refine (Rejected p (MkFail p (elaborate p) _)).
      change (all_diags p <> []); rewrite Hd; discriminate.
  Defined.

  Definition capability_of_admissible (p : Syntax.Program) (H : Admissible p) : Program :=
    MkProg p (elaborate p) (proj1 H) (proj2 H).
  Lemma capability_source : forall p (H : Admissible p), source (capability_of_admissible p H) = p.
  Proof. reflexivity. Qed.
End Capability.
Include Capability.
Arguments Compiled {p} _ _. Arguments Rejected {p} _. Arguments OutsideScope {p} _.
