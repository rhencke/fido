(* Compilable — the static semantic phase and the permanent three-way Compiled/Rejected/OutsideScope decision. *)

From Stdlib Require Import List Bool String Ascii ZArith NArith Lia.
From Fido Require Import Collections FilePath ModulePath Version Names Integer Float Complex Syntax Index Compilable.TypeResolution Compilable.Bindings Compilable.Report Compilable.Facts Packages.
Import ListNotations.

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

(* preflight precedence: a fresh-build failure precedes package-semantic errors, which precede expression errors *)
Definition all_diags : list RootCause := (preflight_diags ++ package_rule_diags ++ expr_diags)%list.

End WithProgram.

(* The core and the three verdict payloads are sealed behind CAPABILITY; the only way to one is compile. *)
Definition Admissible (p : Syntax.Program) : Prop := all_diags p = [] /\ all_boundaries p = [].

Definition nil_dec {A} (l : list A) : {l = []} + {l <> []}.
Proof. destruct l; [left; reflexivity | right; discriminate]. Defined.

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
  (* branch bridges: a client reads compile's verdict from the transparent reports, never the sealed capability *)
  Parameter compiled_diagnostics : forall p cp H, compile p = Compiled p cp H -> all_diags p = [].
  Parameter compiled_boundaries  : forall p cp H, compile p = Compiled p cp H -> all_boundaries p = [].
  Parameter rejected_diagnostics : forall p f, compile p = Rejected p f -> all_diags p <> [].
  Parameter outside_diagnostics  : forall p o, compile p = OutsideScope p o -> all_diags p = [].
  Parameter outside_boundaries   : forall p o, compile p = OutsideScope p o -> all_boundaries p <> [].
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

  Definition compile (p : Syntax.Program) : Outcome p :=
    match nil_dec (all_diags p) with
    | left Hd =>
        match nil_dec (all_boundaries p) with
        | left Hb  => Compiled p (MkProg p (elaborate p) Hd Hb) eq_refl
        | right Hb => OutsideScope p (MkOut p (elaborate p) Hd Hb)
        end
    | right Hd => Rejected p (MkFail p (elaborate p) Hd)
    end.

  Lemma compiled_diagnostics : forall p cp H, compile p = Compiled p cp H -> all_diags p = [].
  Proof.
    intros p cp H Hc. unfold compile in Hc. destruct (nil_dec (all_diags p)) as [Hd|Hd]; [exact Hd|discriminate Hc].
  Qed.
  Lemma compiled_boundaries : forall p cp H, compile p = Compiled p cp H -> all_boundaries p = [].
  Proof.
    intros p cp H Hc. unfold compile in Hc. destruct (nil_dec (all_diags p)) as [Hd|Hd]; [|discriminate Hc].
    destruct (nil_dec (all_boundaries p)) as [Hb|Hb]; [exact Hb | discriminate Hc].
  Qed.
  Lemma rejected_diagnostics : forall p f, compile p = Rejected p f -> all_diags p <> [].
  Proof.
    intros p f Hc. unfold compile in Hc. destruct (nil_dec (all_diags p)) as [Hd|Hd]; [|exact Hd].
    destruct (nil_dec (all_boundaries p)); discriminate Hc.
  Qed.
  Lemma outside_diagnostics : forall p o, compile p = OutsideScope p o -> all_diags p = [].
  Proof.
    intros p o Hc. unfold compile in Hc. destruct (nil_dec (all_diags p)) as [Hd|Hd]; [exact Hd|discriminate Hc].
  Qed.
  Lemma outside_boundaries : forall p o, compile p = OutsideScope p o -> all_boundaries p <> [].
  Proof.
    intros p o Hc. unfold compile in Hc. destruct (nil_dec (all_diags p)) as [Hd|Hd]; [|discriminate Hc].
    destruct (nil_dec (all_boundaries p)) as [Hb|Hb]; [discriminate Hc | exact Hb].
  Qed.
End Capability.
Include Capability.
Arguments Compiled {p} _ _. Arguments Rejected {p} _. Arguments OutsideScope {p} _.

(* extract the exact compiled program and its source identity from admissibility — through compile, no 2nd mint *)
Definition compiled_of (p : Syntax.Program) (H : Admissible p) : { cp : Program | source cp = p } :=
  match compile p as o return (compile p = o -> { cp : Program | source cp = p }) with
  | Compiled cp Hcp => fun _  => exist _ cp Hcp
  | Rejected f      => fun Hc => False_rect _ (rejected_diagnostics p f Hc (proj1 H))
  | OutsideScope o  => fun Hc => False_rect _ (outside_boundaries p o Hc (proj2 H))
  end eq_refl.
Definition program_of (p : Syntax.Program) (H : Admissible p) : Program := proj1_sig (compiled_of p H).
Definition program_of_source (p : Syntax.Program) (H : Admissible p) : source (program_of p H) = p :=
  proj2_sig (compiled_of p H).

(* the two exact verdict predicates a control asserts, decided through compile from the transparent reports *)
Definition compiles (p : Syntax.Program) : Prop := exists cp H, compile p = Compiled cp H.
Definition rejects  (p : Syntax.Program) : Prop := exists f, compile p = Rejected f.

Definition compiles_of_admissible (p : Syntax.Program) (H : Admissible p) : compiles p :=
  match compile p as o return (compile p = o -> compiles p) with
  | Compiled cp Hcp => fun Hc => ex_intro _ cp (ex_intro _ Hcp Hc)
  | Rejected f      => fun Hc => False_rect _ (rejected_diagnostics p f Hc (proj1 H))
  | OutsideScope o  => fun Hc => False_rect _ (outside_boundaries p o Hc (proj2 H))
  end eq_refl.
Definition rejects_of_diags (p : Syntax.Program) (Hd : all_diags p <> []) : rejects p :=
  match compile p as o return (compile p = o -> rejects p) with
  | Compiled cp Hcp => fun Hc => False_rect _ (Hd (compiled_diagnostics p cp Hcp Hc))
  | Rejected f      => fun Hc => ex_intro _ f Hc
  | OutsideScope o  => fun Hc => False_rect _ (Hd (outside_diagnostics p o Hc))
  end eq_refl.
