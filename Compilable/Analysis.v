(* Analysis — the sole fact and issue authority: per-occurrence outcomes, the issue table, and the preflight. *)

From Stdlib Require Import List Bool String Ascii ZArith NArith Lia Eqdep_dec.
From Fido Require Import Names Integer Float Complex Syntax Index Index.Model Index.Refs Index.Edges FilePath Compilable.TypeResolution Compilable.Bindings.
Import ListNotations.

Module TR := Compilable.TypeResolution.
Module BN := Compilable.Bindings.

(* Analysis fact algebra is indexed by exact Binding phase bp: payloads retain exact refs, cross-phase is rejected *)
Inductive Cause {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) : Type :=
| InvalidIdentity : forall (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
    (r : BN.ResolutionRef (BN.use_env bp u) n) (pn : Names.PredeclaredName),
    BN.resolution_object_view r = Some (BN.PredeclaredObject pn) -> Cause bp
| UnresolvedName : forall (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
    (r : BN.ResolutionRef (BN.use_env bp u) n),
    BN.resolution_object_view r = None -> BN.resolution_redecl_root r = None -> Cause bp
| TypeAsValue : forall (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
    (r : BN.ResolutionRef (BN.use_env bp u) n) (o : BN.ObjectRef idx),
    BN.resolution_object_view r = Some o -> Cause bp
| NotAType : forall (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
    (r : BN.ResolutionRef (BN.use_env bp u) n) (o : BN.ObjectRef idx),
    BN.resolution_object_view r = Some o -> Cause bp
| NotCallable : forall (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
    (r : BN.ResolutionRef (BN.use_env bp u) n) (o : BN.ObjectRef idx),
    BN.resolution_object_view r = Some o -> Cause bp
| NotCallableExpr : Index.NodeRef idx -> Cause bp
| ConversionArity : Names.PredeclaredName -> nat -> Cause bp
| ComplexArity : nat -> Cause bp
| ComplexMismatch : Index.NodeRef idx -> Index.NodeRef idx -> Cause bp
| UnaryMismatch : Index.NodeRef idx -> Cause bp
| ConversionOverflow : TR.TypeForm -> Index.NodeRef idx -> Cause bp
| ConversionNotRepresentable : TR.TypeForm -> Index.NodeRef idx -> Cause bp
| DefaultOverflow : TR.Constant -> Cause bp
| NoValueUsed : Cause bp
| IllegalStatement : Cause bp
| ConstMissingInit : forall (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF),
    BN.ConstSpecJudgmentRef bp cs -> Cause bp
| ResultCountMismatch : nat -> nat -> Cause bp
| ShortDuplicate : forall (st : Index.Refs.ShortStmtRef idx) (se : BN.ShortEventRef bp st)
    (dd : BN.ShortDuplicateDecision se) (n : Names.OrdinaryIdentifier),
    dd = BN.short_duplicate_decision se -> BN.short_dup_decision_name dd = Some n -> Cause bp
| MainArity : forall (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
    (r : BN.ResolutionRef (BN.use_env bp u) n) (f : BN.FunctionDeclRef idx),
    BN.resolution_object_view r = Some (BN.SourceObject (BN.DOFunc f)) ->
    list (Index.NodeRef idx) -> nat -> Cause bp.
Arguments InvalidIdentity {p idx s bd bp u n} _ _ _.
Arguments TypeAsValue {p idx s bd bp u n} _ _ _. Arguments NotAType {p idx s bd bp u n} _ _ _.
Arguments NotCallable {p idx s bd bp u n} _ _ _. Arguments NotCallableExpr {p idx s bd bp} _.
Arguments ConversionArity {p idx s bd bp} _ _. Arguments ComplexArity {p idx s bd bp} _.
Arguments ComplexMismatch {p idx s bd bp} _ _. Arguments UnaryMismatch {p idx s bd bp} _.
Arguments ConversionOverflow {p idx s bd bp} _ _. Arguments ConversionNotRepresentable {p idx s bd bp} _ _.
Arguments DefaultOverflow {p idx s bd bp} _. Arguments NoValueUsed {p idx s bd bp}. Arguments IllegalStatement {p idx s bd bp}.
Arguments ConstMissingInit {p idx s bd bp cs} _. Arguments ResultCountMismatch {p idx s bd bp} _ _.
Arguments ShortDuplicate {p idx s bd bp st se} _ _ _ _.
Arguments UnresolvedName {p idx s bd bp u n} _ _ _.
Arguments MainArity {p idx s bd bp u n} _ _ _ _ _.

Inductive Requirement {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) : Type :=
| ReqValueMeaning : forall (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
    (r : BN.ResolutionRef (BN.use_env bp u) n) (org : BN.DeclOrigin idx),
    BN.resolution_object_view r = Some (BN.SourceObject org) -> Requirement bp
| ReqTypeMeaning : forall (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
    (r : BN.ResolutionRef (BN.use_env bp u) n) (o : BN.ObjectRef idx),
    BN.resolution_object_view r = Some o -> Requirement bp
| ReqComplexType : Index.NodeRef idx -> Requirement bp
| ReqApplication : forall (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
    (r : BN.ResolutionRef (BN.use_env bp u) n) (pn : Names.PredeclaredName),
    BN.resolution_object_view r = Some (BN.PredeclaredObject pn) -> list (Index.NodeRef idx) -> Requirement bp
| ReqMainUse : forall (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
    (r : BN.ResolutionRef (BN.use_env bp u) n) (f : BN.FunctionDeclRef idx),
    BN.resolution_object_view r = Some (BN.SourceObject (BN.DOFunc f)) -> Requirement bp
| ReqConstDecl : forall (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF),
    BN.ConstSpecJudgmentRef bp cs -> Requirement bp
| ReqDeclMeaning : Index.NodeRef idx -> Requirement bp.
Arguments ReqDeclMeaning {p idx s bd bp} _.
Arguments ReqValueMeaning {p idx s bd bp u n} _ _ _. Arguments ReqTypeMeaning {p idx s bd bp u n} _ _ _.
Arguments ReqComplexType {p idx s bd bp} _. Arguments ReqApplication {p idx s bd bp u n} _ _ _ _.
Arguments ReqMainUse {p idx s bd bp u n} _ _ _. Arguments ReqConstDecl {p idx s bd bp cs} _.

(* the exact prerequisite of a dependent non-result: a redeclared/unbound name use, an invalid identity, or a child *)
Inductive Dependency {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) : Type :=
| DepRedeclaredName : forall (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
    (r : BN.ResolutionRef (BN.use_env bp u) n) (root : BN.RedeclRoot bp n),
    BN.resolution_redecl_root r = Some root -> Dependency bp
| DepUnboundName : forall (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
    (r : BN.ResolutionRef (BN.use_env bp u) n),
    BN.resolution_object_view r = None -> BN.resolution_redecl_root r = None -> Dependency bp
| DepInvalidId : forall (u : Index.NodeRef idx) (n : Names.OrdinaryIdentifier)
    (r : BN.ResolutionRef (BN.use_env bp u) n) (pn : Names.PredeclaredName),
    BN.resolution_object_view r = Some (BN.PredeclaredObject pn) -> Dependency bp
| DepChild : Index.NodeRef idx -> Dependency bp.
Arguments DepRedeclaredName {p idx s bd bp u n} _ _ _.
Arguments DepUnboundName {p idx s bd bp u n} _ _ _.
Arguments DepInvalidId {p idx s bd bp u n} _ _ _. Arguments DepChild {p idx s bd bp} _.

(* each family judgment is independent per node; a prerequisite failure is a dependent non-result, never a success *)
Inductive ValueOutcome {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) (site : Index.NodeRef idx) : Type :=
| VOK : TR.ResolvedConstant -> ValueOutcome bp site
| VNonconst : ValueOutcome bp site
| VInvalid : Cause bp -> ValueOutcome bp site
| VUnmet : Requirement bp -> ValueOutcome bp site
| VDependent : Dependency bp -> ValueOutcome bp site.
Arguments VOK {p idx s bd bp site} _. Arguments VNonconst {p idx s bd bp site}.
Arguments VInvalid {p idx s bd bp site} _. Arguments VUnmet {p idx s bd bp site} _. Arguments VDependent {p idx s bd bp site} _.

Inductive AppOutcome {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) (site : Index.NodeRef idx) : Type :=
| AOK : AppOutcome bp site
| AInvalid : Cause bp -> AppOutcome bp site
| AUnmet : Requirement bp -> AppOutcome bp site
| ADependent : Dependency bp -> AppOutcome bp site.
Arguments AOK {p idx s bd bp site}. Arguments AInvalid {p idx s bd bp site} _.
Arguments AUnmet {p idx s bd bp site} _. Arguments ADependent {p idx s bd bp site} _.

Inductive StmtOutcome {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) (site : Index.NodeRef idx) : Type :=
| SOK : StmtOutcome bp site
| SInvalid : Cause bp -> StmtOutcome bp site
| SUnmet : Requirement bp -> StmtOutcome bp site
| SDependent : Dependency bp -> StmtOutcome bp site.
Arguments SOK {p idx s bd bp site}. Arguments SInvalid {p idx s bd bp site} _.
Arguments SUnmet {p idx s bd bp site} _. Arguments SDependent {p idx s bd bp site} _.

Inductive TypeUseOutcome {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) (site : Index.NodeRef idx) : Type :=
| TOK : TR.TypeForm -> TypeUseOutcome bp site
| TInvalid : Cause bp -> TypeUseOutcome bp site
| TUnmet : Requirement bp -> TypeUseOutcome bp site
| TDependent : Dependency bp -> TypeUseOutcome bp site.
Arguments TOK {p idx s bd bp site} _. Arguments TInvalid {p idx s bd bp site} _.
Arguments TUnmet {p idx s bd bp site} _. Arguments TDependent {p idx s bd bp site} _.

Inductive PMeaning : Type :=
| PMConvForm : TR.TypeForm -> PMeaning
| PMValue : TR.Constant -> PMeaning
| PMComplex | PMPrintln
| PMInvalidId
| PMUnmodelled.

Definition pmeaning (n : Names.PredeclaredName) : PMeaning :=
  match TR.predeclared_meaning n with
  | TR.NMConversionForm t => PMConvForm t
  | TR.NMValueConstant c => PMValue c
  | TR.NMNoFormMeaning =>
      match n with
      | Names.PComplex => PMComplex | Names.PPrintln => PMPrintln
      | Names.PIota => PMInvalidId | Names.PNil => PMInvalidId
      | _ => PMUnmodelled
      end
  end.

Section OverPhase.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} (bp : BN.BindingPhase s bd).

(* the form/value meaning of a name at a use, for constant folding; None for anything without one *)
Definition nm_at (use : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) : option TR.NameMeaning :=
  match BN.resolution_object_view (BN.resolve bp use n) with
  | Some o =>
      match o with
      | BN.PredeclaredObject pn =>
          match pmeaning pn with
          | PMConvForm t => Some (TR.NMConversionForm t)
          | PMValue c => Some (TR.NMValueConstant c)
          | _ => None
          end
      | BN.SourceObject _ => None
      end
  | None => None
  end.

Definition resolve_constant_info (ci : TR.ConstantInfo) : option TR.ResolvedConstant :=
  match TR.ci_typed ci with
  | TR.ExplicitlyTyped tf =>
      match TR.convert_constant tf (TR.mk_cinfo (TR.ci_const ci) TR.Untyped) with
      | TR.Converted tc => Some (TR.mk_rc tf tc)
      | _ => None
      end
  | TR.Untyped => TR.default_constant (TR.ci_const ci)
  end.

(* a complex builtin component must be an untyped numeric or a typed float; the pair class decides the call *)
Inductive ComplexClass := CxOk | CxDefer | CxError.
Definition complex_comp (ci : TR.ConstantInfo) : option (option Float.Kind) :=
  match TR.ci_const ci, TR.ci_typed ci with
  | TR.CInt _, TR.Untyped => Some None
  | TR.CFloat _, TR.Untyped => Some None
  | TR.CFloat _, TR.ExplicitlyTyped (TR.FloatForm ft) => Some (Some ft)
  | _, _ => None
  end.
Definition complex_class (cre cim : TR.ConstantInfo) : ComplexClass :=
  match complex_comp cre, complex_comp cim with
  | None, _ | _, None => CxError
  | Some None, Some None => CxOk
  | Some (Some a), Some (Some b) => if Float.kind_equalb a b then CxDefer else CxError
  | _, _ => CxDefer
  end.

Definition mconst (m : Collections.NodeMap.t (option TR.ConstantInfo)) (rc : Index.NodeRef idx)
  : option TR.ConstantInfo :=
  match Collections.NodeMap.find (Index.nr_key rc) m with Some oc => oc | None => None end.
Definition node_const (m : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx)
  : option TR.ConstantInfo :=
  match Index.node_view r as v return Index.node_view r = v -> option TR.ConstantInfo with
  | Index.Model.VName n => fun _ =>
      match nm_at r n with Some (TR.NMValueConstant c) => Some (TR.mk_cinfo c TR.Untyped) | _ => None end
  | Index.Model.VLiteral (Syntax.IntegerLiteral k) => fun _ => Some (TR.mk_cinfo (TR.CInt (Z.of_N k)) TR.Untyped)
  | Index.Model.VLiteral (Syntax.FloatLiteral d) => fun _ => Some (TR.mk_cinfo (TR.CFloat (Float.nnd_value d)) TR.Untyped)
  | Index.Model.VLiteral (Syntax.StringLiteral str) => fun _ => Some (TR.mk_cinfo (TR.CString str) TR.Untyped)
  | Index.Model.VUnary Syntax.UnaryMinus => fun Hv =>
      match mconst m (Index.Edges.uo_child (Index.Edges.unary_operand (Index.Refs.mkUnaryRef r Syntax.UnaryMinus Hv))) with
      | Some ci =>
          match TR.constant_neg (TR.ci_const ci) with
          | Some c' =>
              match TR.ci_typed ci with
              | TR.ExplicitlyTyped tf =>
                  match TR.convert_constant tf (TR.mk_cinfo c' TR.Untyped) with
                  | TR.Converted _ => Some (TR.mk_cinfo c' (TR.ExplicitlyTyped tf))
                  | _ => None
                  end
              | TR.Untyped => Some (TR.mk_cinfo c' TR.Untyped)
              end
          | None => None
          end
      | None => None
      end
  | Index.Model.VApplication => fun Hv =>
      match Index.node_view (Index.Edges.ah_child (Index.Edges.app_head (Index.Refs.mkAppRef r Hv))) with
      | Index.Model.VName h =>
          match map (fun x => Index.Edges.aa_child (projT2 x)) (Index.Edges.application_args (Index.Refs.mkAppRef r Hv)) with
          | x :: nil =>
              match nm_at r h with
              | Some (TR.NMConversionForm t) =>
                  match mconst m x with
                  | Some ci => match TR.convert_constant t ci with
                               | TR.Converted tc => Some (TR.mk_cinfo (TR.typed_exact tc) (TR.ExplicitlyTyped t))
                               | _ => None
                               end
                  | None => None
                  end
              | _ => None
              end
          | re :: im :: nil =>
              match BN.resolution_object_view (BN.resolve bp r h) with
              | Some o =>
                  match o, mconst m re, mconst m im with
                  | BN.PredeclaredObject Names.PComplex, Some cre, Some cim =>
                      match TR.constant_to_float (TR.ci_const cre), TR.constant_to_float (TR.ci_const cim) with
                      | Some _, Some _ =>
                          option_map (fun c => TR.mk_cinfo c TR.Untyped)
                            (TR.complex_of_constants (TR.ci_const cre) (TR.ci_const cim))
                      | _, _ => None
                      end
                  | _, _, _ => None
                  end
              | None => None
              end
          | _ => None
          end
      | _ => None
      end
  | _ => fun _ => None
  end eq_refl.
(* the file's constants folded in descending position order — children before parents (file_nodes is trie order) *)
Definition const_table (fr : Index.FileRef idx) : Collections.NodeMap.t (option TR.ConstantInfo) :=
  fold_left (fun m pos =>
               match Index.mk_noderef fr (Pos.of_succ_nat pos) with
               | Some r => Collections.NodeMap.add (Index.nr_key r) (node_const m r) m
               | None => m
               end)
            (rev (seq 0 (Index.occ_count fr))) (Collections.NodeMap.empty _).
(* role decides value-use: an application head is a callee, not a value; expr-statement exprs go to own_stmt *)
Definition is_app_head (r : Index.NodeRef idx) : bool :=
  match Index.node_role r with Index.Model.RApplicationHead => true | _ => false end.
Definition value_ctx (r : Index.NodeRef idx) : bool :=
  match Index.node_role r with Index.Model.RApplicationHead => false | Index.Model.RExprStatementExpr => false | _ => true end.

(* a conversion/complex head folds its argument, so a folded value's default-int type is never forced *)
Definition head_folds (par : Index.NodeRef idx) : bool :=
  match Index.node_view par as v return Index.node_view par = v -> bool with
  | Index.Model.VApplication => fun Hv =>
      match Index.node_view (Index.Edges.ah_child (Index.Edges.app_head (Index.Refs.mkAppRef par Hv))) with
      | Index.Model.VName h =>
          match BN.resolution_object_view (BN.resolve bp par h) with
          | Some o =>
              match o with
              | BN.PredeclaredObject pn =>
                  match pmeaning pn with PMConvForm _ => true | PMComplex => true | _ => false end
              | BN.SourceObject _ => false
              end
          | None => false
          end
      | _ => false
      end
  | _ => fun _ => false
  end eq_refl.
Definition fold_consumed (r : Index.NodeRef idx) : bool :=
  match Index.node_role r with
  | Index.Model.RUnaryOperand => true
  | Index.Model.RApplicationArg _ => match Index.node_parent r with Some par => head_folds par | None => false end
  | _ => false
  end.


(* a const spec: a first spec omitting its initializer, or a known result-count mismatch, is an exact invalidity *)
Definition const_spec_disposition (cs : Index.Refs.SpecRef idx Index.Model.ConstSpecF) : ValueOutcome bp (Index.Refs.sp_node cs) :=
  let cjr := BN.const_spec_judgment bp cs in
  match Index.Refs.sp_shape cs with
  | Index.Model.CSExplicit _ nn nv =>
      if Nat.eqb nn nv then VUnmet (ReqConstDecl cjr) else VInvalid (ResultCountMismatch nn nv)
  | Index.Model.CSInherited _ =>
      match projT2 (BN.cjr_row cjr) with
      | BN.CJFirstInherited _ _ _ => VInvalid (ConstMissingInit cjr)
      | _ => VUnmet (ReqConstDecl cjr)
      end
  end.

Definition own_value (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx) : ValueOutcome bp r :=
  match Index.node_view r as v return Index.node_view r = v -> ValueOutcome bp r with
  | Index.Model.VName n => fun _ =>
      let r0 := BN.resolve bp r n in
      match BN.resolution_object_view r0 as ov return BN.resolution_object_view r0 = ov -> ValueOutcome bp r with
      | Some o => fun Hov =>
          match o as o' return o = o' -> ValueOutcome bp r with
          | BN.PredeclaredObject pn => fun Ho =>
              let Hpre := eq_trans Hov (f_equal (@Some _) Ho) in
              match pmeaning pn with
              | PMValue c => match TR.default_constant c with Some rc => VOK rc | None => VInvalid (InvalidIdentity r0 pn Hpre) end
              | PMInvalidId => VInvalid (InvalidIdentity r0 pn Hpre)
              | _ => if is_app_head r then VNonconst else VInvalid (TypeAsValue r0 o Hov)
              end
          | BN.SourceObject org => fun Ho =>
              let Hsrc := eq_trans Hov (f_equal (@Some _) Ho) in
              match org as org' return org = org' -> ValueOutcome bp r with
              | BN.DOBinder _ => fun _ => VUnmet (ReqValueMeaning r0 org Hsrc)
              | BN.DOShort _ => fun _ => VUnmet (ReqValueMeaning r0 org Hsrc)
              | BN.DOFunc f => fun Horg =>
                  if is_app_head r then VNonconst
                  else VUnmet (ReqMainUse r0 f (eq_trans Hsrc (f_equal (fun z => @Some _ (BN.SourceObject z)) Horg)))
              end eq_refl
          end eq_refl
      | None => fun Hov =>
          match BN.resolution_redecl_root r0 as rv return BN.resolution_redecl_root r0 = rv -> ValueOutcome bp r with
          | Some root => fun Hrr => VDependent (DepRedeclaredName r0 root Hrr)
          | None => fun Hrv => VInvalid (UnresolvedName r0 Hov Hrv)
          end eq_refl
      end eq_refl
  | Index.Model.VLiteral _ => fun _ =>
      match mconst ctab r with
      | Some ci => match resolve_constant_info ci with
                   | Some rc => VOK rc
                   | None => if fold_consumed r then VNonconst else VInvalid (DefaultOverflow (TR.ci_const ci))
                   end
      | None => VNonconst
      end
  | Index.Model.VUnary Syntax.UnaryMinus => fun Hv =>
      match mconst ctab (Index.Edges.uo_child (Index.Edges.unary_operand (Index.Refs.mkUnaryRef r Syntax.UnaryMinus Hv))) with
      | Some _ =>
          match mconst ctab r with
          | Some ci => match resolve_constant_info ci with
                       | Some rc => VOK rc
                       | None => if fold_consumed r then VNonconst else VInvalid (DefaultOverflow (TR.ci_const ci))
                       end
          | None => VInvalid (UnaryMismatch r)
          end
      | None => VNonconst
      end
  | Index.Model.VApplication => fun Hv =>
      match Index.node_view (Index.Edges.ah_child (Index.Edges.app_head (Index.Refs.mkAppRef r Hv))) with
      | Index.Model.VName h =>
          let r0 := BN.resolve bp r h in
          match BN.resolution_object_view r0 as ov return BN.resolution_object_view r0 = ov -> ValueOutcome bp r with
          | Some o => fun _ =>
              match o with
              | BN.PredeclaredObject pn =>
              match pmeaning pn, map (fun x => Index.Edges.aa_child (projT2 x)) (Index.Edges.application_args (Index.Refs.mkAppRef r Hv)) with
              | PMConvForm t, x :: nil =>
                  match mconst ctab x with
                  | Some ci => match TR.convert_constant t ci with
                               | TR.Converted tc => VOK (TR.mk_rc t tc)
                               | TR.Overflows _ => VInvalid (ConversionOverflow t x)
                               | TR.NotForm _ => VInvalid (ConversionNotRepresentable t x)
                               end
                  | None => VNonconst
                  end
              | PMComplex, re :: im :: nil =>
                  match mconst ctab re, mconst ctab im with
                  | Some cre, Some cim =>
                      match complex_class cre cim with
                      | CxOk => match mconst ctab r with
                                | Some ci => match resolve_constant_info ci with Some rc => VOK rc | None => VNonconst end
                                | None => VNonconst end
                      | CxDefer => VUnmet (ReqComplexType r)
                      | CxError => VInvalid (ComplexMismatch re im)
                      end
                  | _, _ => VNonconst
                  end
              | PMPrintln, _ => if value_ctx r then VInvalid NoValueUsed else VNonconst
              | _, _ => VNonconst
              end
              | BN.SourceObject _ => VNonconst
              end
          | None => fun Hov =>
              match BN.resolution_redecl_root r0 as rv return BN.resolution_redecl_root r0 = rv -> ValueOutcome bp r with
              | Some root => fun Hrr => VDependent (DepRedeclaredName r0 root Hrr)
              | None => fun Hrv => VDependent (DepUnboundName r0 Hov Hrv)
              end eq_refl
          end eq_refl
      | _ => VNonconst
      end
  (* declaration outcomes live on the declaration subject (spec / short statement), never on the binder *)
  | Index.Model.VConstSpec sh => fun Hv => const_spec_disposition (Index.Refs.mkSpecRef (fl := Index.Model.ConstSpecF) r sh Hv)
  | Index.Model.VVarSpec _ => fun _ => VUnmet (ReqDeclMeaning r)
  | Index.Model.VTypeSpec _ => fun _ => VUnmet (ReqDeclMeaning r)
  | _ => fun _ => VNonconst
  end eq_refl.

Definition own_app (r : Index.NodeRef idx) : AppOutcome bp r :=
  match Index.node_view r as v return Index.node_view r = v -> AppOutcome bp r with
  | Index.Model.VApplication => fun Hv =>
      let hd := Index.Edges.ah_child (Index.Edges.app_head (Index.Refs.mkAppRef r Hv)) in
      match Index.node_view hd with
      | Index.Model.VName h =>
          let r0 := BN.resolve bp r h in
          match BN.resolution_object_view r0 as ov return BN.resolution_object_view r0 = ov -> AppOutcome bp r with
          | Some o => fun Hov =>
              match o as o' return o = o' -> AppOutcome bp r with
              | BN.PredeclaredObject pn => fun Ho =>
              let Hpre := eq_trans Hov (f_equal (@Some _) Ho) in
              match pmeaning pn with
              | PMConvForm _ => match map (fun x => Index.Edges.aa_child (projT2 x)) (Index.Edges.application_args (Index.Refs.mkAppRef r Hv)) with _ :: nil => AOK | _ => AInvalid (ConversionArity pn (Datatypes.length (map (fun x => Index.Edges.aa_child (projT2 x)) (Index.Edges.application_args (Index.Refs.mkAppRef r Hv))))) end
              | PMComplex =>
                  (* application family = callability + arity only; the complex value is own_value's exact judgment *)
                  match map (fun x => Index.Edges.aa_child (projT2 x)) (Index.Edges.application_args (Index.Refs.mkAppRef r Hv)) with
                  | _ :: _ :: nil => AOK
                  | _ => AInvalid (ComplexArity (Datatypes.length (map (fun x => Index.Edges.aa_child (projT2 x)) (Index.Edges.application_args (Index.Refs.mkAppRef r Hv)))))
                  end
              | PMPrintln => AOK
              | PMValue _ => AInvalid (NotCallable r0 o Hov)
              | PMInvalidId => ADependent (DepInvalidId r0 pn Hpre)
              | PMUnmodelled => AUnmet (ReqApplication r0 pn Hpre (map (fun x => Index.Edges.aa_child (projT2 x)) (Index.Edges.application_args (Index.Refs.mkAppRef r Hv))))
              end
          | BN.SourceObject org => fun Ho =>
              let Hsrc := eq_trans Hov (f_equal (@Some _) Ho) in
              match org as org' return org = org' -> AppOutcome bp r with
              | BN.DOBinder _ => fun _ => AInvalid (NotCallable r0 o Hov)
              | BN.DOShort _ => fun _ => AInvalid (NotCallable r0 o Hov)
              | BN.DOFunc f => fun Horg =>
                  (* the fixed main is zero-parameter: a zero-argument call is a known zero-result call *)
                  let Hfunc := eq_trans Hsrc (f_equal (fun z => @Some _ (BN.SourceObject z)) Horg) in
                  match map (fun x => Index.Edges.aa_child (projT2 x)) (Index.Edges.application_args (Index.Refs.mkAppRef r Hv)) with
                  | nil => AOK
                  | args => AInvalid (MainArity r0 f Hfunc args (Datatypes.length args))
                  end
              end eq_refl
              end eq_refl
          | None => fun Hov =>
              match BN.resolution_redecl_root r0 as rv return BN.resolution_redecl_root r0 = rv -> AppOutcome bp r with
              | Some root => fun Hrr => ADependent (DepRedeclaredName r0 root Hrr)
              | None => fun Hrv => ADependent (DepUnboundName r0 Hov Hrv)
              end eq_refl
          end eq_refl
      | _ => AInvalid (NotCallableExpr hd)
      end
  | _ => fun _ => ADependent (DepChild r)
  end eq_refl.

(* the dependency when a statement's expr already owns an invalidity, unmet requirement, or a dependent non-result *)
Definition expr_dependency (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (e : Index.NodeRef idx) : option (Dependency bp) :=
  match own_value ctab e with
  | VInvalid _ | VUnmet _ | VDependent _ => Some (DepChild e)
  | _ => match Index.node_view e with
         | Index.Model.VApplication => match own_app e with AInvalid _ | AUnmet _ | ADependent _ => Some (DepChild e) | _ => None end
         | _ => None
         end
  end.

(* an expr-statement defers to an expr that owns an issue; otherwise it is a legal call statement or an illegal one *)
Definition own_stmt (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx) : StmtOutcome bp r :=
  match Index.node_view r as v return Index.node_view r = v -> StmtOutcome bp r with
  | Index.Model.VStmt Index.Model.SSExpr => fun Hv =>
      let e := Index.Edges.ee_child (Index.Edges.exprstmt_expr (Index.Refs.mkExprStmtRef r Hv)) in
      match expr_dependency ctab e with
      | Some d => SDependent d
      | None =>
          match Index.node_view e as ve return Index.node_view e = ve -> StmtOutcome bp r with
          | Index.Model.VApplication => fun He =>
              match Index.node_view (Index.Edges.ah_child (Index.Edges.app_head (Index.Refs.mkAppRef e He))) with
              | Index.Model.VName h =>
                  match BN.resolution_object_view (BN.resolve bp r h) with
                  | Some o =>
                      match o with
                      | BN.PredeclaredObject Names.PPrintln => SOK
                      | BN.SourceObject _ => SOK
                      | _ => SInvalid IllegalStatement
                      end
                  | None => SInvalid IllegalStatement
                  end
              | _ => SInvalid IllegalStatement
              end
          | _ => fun _ => SInvalid IllegalStatement
          end eq_refl
      end
  | Index.Model.VStmt (Index.Model.SSShort nn nv) => fun Hv =>
      (* short declaration: retain the exact short event and canonical duplicate decision naming the repeated left *)
      let se := BN.short_event bp (Index.Refs.mkShortStmtRef r nn nv Hv) in
      match BN.short_dup_decision_name (BN.short_duplicate_decision se)
        as nm return BN.short_dup_decision_name (BN.short_duplicate_decision se) = nm -> StmtOutcome bp r with
      | Some n => fun Hn => SInvalid (ShortDuplicate (BN.short_duplicate_decision se) n eq_refl Hn)
      | None => fun _ => SUnmet (ReqDeclMeaning r)
      end eq_refl
  | _ => fun _ => SDependent (DepChild r)
  end eq_refl.

(* the represented but unmodelled predeclared types: real Go types with no current C4 TypeForm *)
Definition is_unmodeled_type (pn : Names.PredeclaredName) : bool :=
  match pn with Names.PUintptr | Names.PAny | Names.PComparable | Names.PError => true | _ => false end.

(* a type use resolves its name: modelled type is its form, unmodelled real type a boundary, else invalid *)
Definition own_type (r : Index.NodeRef idx) : TypeUseOutcome bp r :=
  match Index.node_view r with
  | Index.Model.VTypeExpr (Syntax.NamedType n) =>
      let r0 := BN.resolve bp r n in
      match BN.resolution_object_view r0 as ov return BN.resolution_object_view r0 = ov -> TypeUseOutcome bp r with
      | Some o => fun Hov =>
          match o with
          | BN.PredeclaredObject pn =>
              match TR.predeclared_meaning pn with
              | TR.NMConversionForm t => TOK t
              | _ => if is_unmodeled_type pn
                     then TUnmet (ReqTypeMeaning r0 o Hov)
                     else TInvalid (NotAType r0 o Hov)
              end
          | BN.SourceObject (BN.DOBinder _) => TUnmet (ReqTypeMeaning r0 o Hov)
          | BN.SourceObject (BN.DOShort _) => TUnmet (ReqTypeMeaning r0 o Hov)
          | BN.SourceObject (BN.DOFunc _) => TInvalid (NotAType r0 o Hov)
          end
      | None => fun Hov =>
          match BN.resolution_redecl_root r0 as rv return BN.resolution_redecl_root r0 = rv -> TypeUseOutcome bp r with
          | Some root => fun Hrr => TDependent (DepRedeclaredName r0 root Hrr)
          | None => fun Hrv => TInvalid (UnresolvedName r0 Hov Hrv)
          end eq_refl
      end eq_refl
  | _ => TDependent (DepChild r)
  end.

End OverPhase.

(* one applicability-first fact per applicable family; an application carries disjoint callability and value facts *)
Inductive OccFact {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) : Type :=
| OFValue : forall r : Index.NodeRef idx, ValueOutcome bp r -> OccFact bp
| OFApp   : forall r : Index.NodeRef idx, AppOutcome bp r -> OccFact bp
| OFStmt  : forall r : Index.NodeRef idx, StmtOutcome bp r -> OccFact bp
| OFType  : forall r : Index.NodeRef idx, TypeUseOutcome bp r -> OccFact bp.
Arguments OccFact {p idx s bd} bp.
Arguments OFValue {p idx s bd bp} _ _. Arguments OFApp {p idx s bd bp} _ _.
Arguments OFStmt {p idx s bd bp} _ _. Arguments OFType {p idx s bd bp} _ _.

Section Retain.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} (bp : BN.BindingPhase s bd).

(* exactly the facts of the families that apply to a node, in family order; an inapplicable family yields none *)
Definition occ_facts (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx) : list (OccFact bp) :=
  match Index.node_view r with
  | Index.Model.VName _ | Index.Model.VLiteral _ | Index.Model.VUnary _ => [OFValue r (own_value bp ctab r)]
  | Index.Model.VApplication => [OFApp r (own_app bp r); OFValue r (own_value bp ctab r)]
  | Index.Model.VStmt Index.Model.SSExpr => [OFStmt r (own_stmt bp ctab r)]
  | Index.Model.VStmt (Index.Model.SSShort _ _) => [OFStmt r (own_stmt bp ctab r)]
  | Index.Model.VTypeExpr _ => [OFType r (own_type bp r)]
  | Index.Model.VConstSpec _ | Index.Model.VVarSpec _ | Index.Model.VTypeSpec _ => [OFValue r (own_value bp ctab r)]
  | _ => []
  end.

(* nonapplicability: occ_facts retains an application fact only at an application role, never elsewhere *)
Lemma no_app_fact_off_application (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r r' : Index.NodeRef idx) (o : AppOutcome bp r') :
  In (OFApp r' o) (occ_facts ctab r) -> Index.node_view r = Index.Model.VApplication.
Proof.
  intro Hin. unfold occ_facts in Hin. destruct (Index.node_view r); cbn in Hin;
    try (match type of Hin with context [match ?x with _ => _ end] => destruct x end; cbn in Hin);
    solve [ reflexivity | exfalso; intuition discriminate ].
Qed.
(* nonapplicability: occ_facts retains a statement fact only at a statement role *)
Lemma no_stmt_fact_off_statement (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r r' : Index.NodeRef idx) (o : StmtOutcome bp r') :
  In (OFStmt r' o) (occ_facts ctab r) -> exists st, Index.node_view r = Index.Model.VStmt st.
Proof.
  intro Hin. unfold occ_facts in Hin. destruct (Index.node_view r); cbn in Hin;
    try (match type of Hin with context [match ?x with _ => _ end] => destruct x end; cbn in Hin);
    solve [ eexists; reflexivity | exfalso; intuition discriminate ].
Qed.
(* nonapplicability: occ_facts retains a type-use fact only at a type-use role *)
Lemma no_type_fact_off_typeuse (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r r' : Index.NodeRef idx) (o : TypeUseOutcome bp r') :
  In (OFType r' o) (occ_facts ctab r) -> exists t, Index.node_view r = Index.Model.VTypeExpr t.
Proof.
  intro Hin. unfold occ_facts in Hin. destruct (Index.node_view r); cbn in Hin;
    try (match type of Hin with context [match ?x with _ => _ end] => destruct x end; cbn in Hin);
    solve [ eexists; reflexivity | exfalso; intuition discriminate ].
Qed.

(* one const table per file, built once and shared across that file's per-node facts (children stay in-file) *)
Definition raw_facts : list (OccFact bp) :=
  flat_map (fun fr => let ctab := const_table bp fr in flat_map (occ_facts ctab) (Index.file_nodes fr))
           (flat_map BN.PI.pkg_members (BN.PI.packages s)).

Definition FactPhase : Type := { m : list (OccFact bp) | m = raw_facts }.
Definition facts : FactPhase := exist _ raw_facts eq_refl.
Definition fact_list (fp : FactPhase) : list (OccFact bp) := proj1_sig fp.

End Retain.

Arguments FactPhase {p idx s bd} bp.
Arguments facts {p idx s bd} bp.
Arguments fact_list {p idx s bd bp} _.

Section Laws.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} (bp : BN.BindingPhase s bd).

(* the phase content is built once; every phase carries exactly the canonical classification, none caller-supplied *)
Lemma fact_once (fp : FactPhase bp) : fact_list fp = raw_facts bp.
Proof. exact (proj2_sig fp). Qed.

(* statement and type-use families have no Nonconst constructor: OK / invalid / unmet / dependent exhaust each *)
Lemma only_lawful_per_family (r : Index.NodeRef idx) :
  (forall o : StmtOutcome bp r, o = SOK \/ (exists c, o = SInvalid c) \/ (exists q, o = SUnmet q) \/ (exists d, o = SDependent d))
  /\ (forall o : TypeUseOutcome bp r, (exists f, o = TOK f) \/ (exists c, o = TInvalid c) \/ (exists q, o = TUnmet q) \/ (exists d, o = TDependent d)).
Proof.
  split; intro o; destruct o.
  - left; reflexivity.
  - right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; right; eexists; reflexivity.
  - left; eexists; reflexivity.
  - right; left; eexists; reflexivity.
  - right; right; left; eexists; reflexivity.
  - right; right; right; eexists; reflexivity.
Qed.

End Laws.

(* the fresh-build preflight: naming and root entries are PackageIdentity facts; Analysis owns only the collision *)

Inductive FreshBuildDisposition {p} {idx : Index.ProgramIndex p} (s : BN.PI.PackageSurface idx) : Type :=
| FreshOk : FreshBuildDisposition s
| FreshCollision : BN.PI.PackageRef s -> BN.PI.RootEntryRef idx -> FreshBuildDisposition s.
Arguments FreshOk {p idx s}.
Arguments FreshCollision {p idx s} _ _.

(* collision applicability is exactly OneSelected, independent of any package's main multiplicity *)
Definition raw_preflight {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}
  {bd : BN.PhaseData s} (bp : BN.BindingPhase s bd) : FreshBuildDisposition s :=
  let _ := bp in
  match BN.PI.package_selection s with
  | BN.PI.OneSelected pr =>
      match find (fun rr => andb (String.eqb (BN.PI.default_exec_name pr) (BN.PI.re_name rr))
                                 (match BN.PI.re_kind rr with BN.PI.RootDir => true | BN.PI.RootFile => false end))
                 (BN.PI.root_entries idx) with
      | Some rr => FreshCollision pr rr
      | None => FreshOk
      end
  | _ => FreshOk
  end.

Definition PackageFacts {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}
  {bd : BN.PhaseData s} (bp : BN.BindingPhase s bd) : Type := { d : FreshBuildDisposition s | d = raw_preflight bp }.
Definition package_facts {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}
  {bd : BN.PhaseData s} (bp : BN.BindingPhase s bd) : PackageFacts bp := exist _ (raw_preflight bp) eq_refl.
Definition preflight {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} {bp : BN.BindingPhase s bd}
  (pf : PackageFacts bp) : FreshBuildDisposition s := proj1_sig pf.
Definition package_rule {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} {bp : BN.BindingPhase s bd}
  (pf : PackageFacts bp) (pr : BN.PI.PackageRef s) : BN.MainStatus s pr := BN.package_main bp pr.

Lemma package_rule_is_projection {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}
  {bd : BN.PhaseData s} {bp : BN.BindingPhase s bd} (pf : PackageFacts bp) (pr : BN.PI.PackageRef s) :
  package_rule pf pr = BN.package_main bp pr.
Proof. reflexivity. Qed.

Lemma packages_consume_one_surface {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}
  {bd : BN.PhaseData s} {bp : BN.BindingPhase s bd} (pf : PackageFacts bp) : preflight pf = raw_preflight bp.
Proof. exact (proj2_sig pf). Qed.

(* the one canonical analysis result over p; analyze builds it once, holding FactPhase and PackageFacts as fields *)
Record Result (p : Syntax.Program) : Type := mk_result {
  res_index     : Index.ProgramIndex p ;
  res_surface   : BN.PI.PackageSurface res_index ;
  res_bind_data : BN.PhaseData res_surface ;
  res_binds     : BN.BindingPhase res_surface res_bind_data ;
  res_facts     : FactPhase res_binds ;
  res_pkg       : PackageFacts res_binds
}.
Arguments mk_result {p} _ _ _ _ _ _.
Arguments res_index {p} _. Arguments res_surface {p} _.
Arguments res_bind_data {p} _. Arguments res_binds {p} _.
Arguments res_facts {p} _. Arguments res_pkg {p} _.

Definition analyze (p : Syntax.Program) : Result p :=
  let i := Index.index_program p in
  let s := BN.PI.package_surface i in
  let b := BN.bindings s in
  mk_result i s (BN.phase_data s) b (facts b) (package_facts b).

(* the semantic family of an occurrence issue: declaration specs and short-decls are distinct from plain uses *)
Inductive Family : Type := FamValue | FamApplication | FamStatement | FamTypeUse | FamDeclaration.

(* an exact use context of a redeclared root: a name occurrence whose exact resolution yields that exact root *)
Record RedeclaredUseRef {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  {bp : BN.BindingPhase s bd} {n : Names.OrdinaryIdentifier} (root : BN.RedeclRoot bp n) : Type := mk_redeclared_use {
  ruc_node   : Index.NodeRef idx ;
  ruc_res    : BN.ResolutionRef (BN.use_env bp ruc_node) n ;
  ruc_yields : BN.resolution_redecl_root ruc_res = Some root
}.
Arguments mk_redeclared_use {p idx s bd bp n root} _ _ _.
Arguments ruc_node {p idx s bd bp n root} _.
Arguments ruc_res {p idx s bd bp n root} _.
Arguments ruc_yields {p idx s bd bp n root} _.

(* an issue roots at an exact node, an exact package, or an exact redeclaration root; never a self-fallback *)
Inductive IssueRoot {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) : Type :=
| RootNode : Index.NodeRef idx -> IssueRoot bp
| RootPackage : BN.PI.PackageRef s -> IssueRoot bp
| RootGroup : forall (n : Names.OrdinaryIdentifier), BN.RedeclRoot bp n -> IssueRoot bp.
Arguments RootNode {p idx s bd bp} _.
Arguments RootPackage {p idx s bd bp} _.
Arguments RootGroup {p idx s bd bp n} _.

(* the exact diagnostics: an occurrence invalidity, a missing fixed main, an output collision, a redeclared group *)
Inductive Diagnostic {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) : Type :=
| DOcc : Index.NodeRef idx -> Family -> Cause bp -> Diagnostic bp
| DMissingMain : BN.PI.PackageRef s -> Diagnostic bp
| DOutputCollision : BN.PI.PackageRef s -> BN.PI.RootEntryRef idx -> Diagnostic bp
| DRedeclaredGroup : forall (n : Names.OrdinaryIdentifier), BN.RedeclRoot bp n -> Diagnostic bp.
Arguments DOcc {p idx s bd bp} _ _ _.
Arguments DMissingMain {p idx s bd bp} _.
Arguments DOutputCollision {p idx s bd bp} _ _.
Arguments DRedeclaredGroup {p idx s bd bp n} _.

(* the exact boundaries: an occurrence-family unmet requirement, retaining its subject, family, and requirement *)
Inductive Boundary {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) : Type :=
| BOcc : Index.NodeRef idx -> Family -> Requirement bp -> Boundary bp.
Arguments BOcc {p idx s bd bp} _ _ _.

(* the issue cause a reader projects from a diagnostic row, exactly as retained, never re-derived from a weaker site *)
Inductive IssueCause {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) : Type :=
| OccCause : Cause bp -> IssueCause bp
| MissingMainCause : BN.PI.PackageRef s -> IssueCause bp
| OutputCollisionCause : BN.PI.PackageRef s -> BN.PI.RootEntryRef idx -> IssueCause bp
| RedeclaredGroupCause : forall (n : Names.OrdinaryIdentifier), BN.RedeclRoot bp n -> IssueCause bp.
Arguments OccCause {p idx s bd bp} _.
Arguments MissingMainCause {p idx s bd bp} _.
Arguments OutputCollisionCause {p idx s bd bp} _ _.
Arguments RedeclaredGroupCause {p idx s bd bp n} _.

Section IssueProjections.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} {bp : BN.BindingPhase s bd}.

(* the cause a row retains: a plain field read of the exact object stored at construction, not a reconstruction *)
Definition diag_cause (d : Diagnostic bp) : IssueCause bp :=
  match d with
  | DOcc _ _ c => OccCause c
  | DMissingMain pr => MissingMainCause pr
  | DOutputCollision pr rr => OutputCollisionCause pr rr
  | DRedeclaredGroup root => RedeclaredGroupCause root
  end.
Definition diag_family (d : Diagnostic bp) : option Family := match d with DOcc _ f _ => Some f | _ => None end.
(* related nodes a row projects: a complex mismatch's two sides, or a group's exact members (use contexts via Report) *)
Definition diag_related (d : Diagnostic bp) : list (Index.NodeRef idx) :=
  match d with
  | DOcc _ _ (ComplexMismatch a b) => [a; b]
  | DRedeclaredGroup root => map (fun m => BN.est_node (BN.es_est m)) (BN.bg_members (BN.rr_group (projT2 root)))
  | _ => []
  end.
Definition diag_root (d : Diagnostic bp) : IssueRoot bp :=
  match d with
  | DOcc r _ _ => RootNode r
  | DMissingMain pr => RootPackage pr
  | DOutputCollision pr _ => RootPackage pr
  | DRedeclaredGroup root => RootGroup root
  end.
Definition bound_req (b : Boundary bp) : Requirement bp := match b with BOcc _ _ q => q end.
Definition bound_family (b : Boundary bp) : Family := match b with BOcc _ f _ => f end.
Definition bound_root (b : Boundary bp) : IssueRoot bp := match b with BOcc r _ _ => RootNode r end.

End IssueProjections.

Section IssueTable.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} {bp : BN.BindingPhase s bd}
        (fp : FactPhase bp) (pf : PackageFacts bp).

(* the semantic family of an occurrence fact: a declaration spec or short-decl statement, else its plain family *)
Definition occ_family (o : OccFact bp) : Family :=
  match o with
  | OFApp _ _ => FamApplication
  | OFType _ _ => FamTypeUse
  | OFStmt r _ => match Index.node_view r with Index.Model.VStmt (Index.Model.SSShort _ _) => FamDeclaration | _ => FamStatement end
  | OFValue r _ => match Index.node_view r with Index.Model.VConstSpec _ | Index.Model.VVarSpec _ | Index.Model.VTypeSpec _ => FamDeclaration | _ => FamValue end
  end.

(* one occurrence fact yields one diagnostic exactly when its family outcome is invalid, retaining that exact cause *)
Definition occ_diag_rows (o : OccFact bp) : list (Diagnostic bp) :=
  let fam := occ_family o in
  match o with
  | OFValue r (VInvalid c) => [DOcc r fam c]
  | OFApp r (AInvalid c) => [DOcc r fam c]
  | OFStmt r (SInvalid c) => [DOcc r fam c]
  | OFType r (TInvalid c) => [DOcc r fam c]
  | _ => []
  end.
(* one occurrence fact yields one boundary exactly when its family outcome is unmet; invalid and unmet coexist (§6) *)
Definition occ_bound_rows (o : OccFact bp) : list (Boundary bp) :=
  let fam := occ_family o in
  match o with
  | OFValue r (VUnmet q) => [BOcc r fam q]
  | OFApp r (AUnmet q) => [BOcc r fam q]
  | OFStmt r (SUnmet q) => [BOcc r fam q]
  | OFType r (TUnmet q) => [BOcc r fam q]
  | _ => []
  end.

(* the sole selected package's default-output collision, retaining the exact colliding root entry *)
Definition collision_rows : list (Diagnostic bp) :=
  match preflight pf with FreshOk => [] | FreshCollision pr rr => [DOutputCollision pr rr] end.
(* a package with no fixed main is a missing-executable-entry diagnostic; multiple mains are a group redeclaration *)
Definition main_rows : list (Diagnostic bp) :=
  flat_map (fun pr => match BN.package_main bp pr with BN.MainMissing => [DMissingMain pr] | _ => [] end) (BN.PI.packages s).

(* every package-member name occurrence: the use sites a redeclared group can contextualize *)
Definition name_uses : list (Index.NodeRef idx) :=
  filter (fun r => match Index.node_view r with Index.Model.VName _ => true | _ => false end)
         (flat_map Index.file_nodes (flat_map BN.PI.pkg_members (BN.PI.packages s))).
(* one exact use context: a use of root's name resolving by exact-identity check to that exact root, with proof *)
Definition use_context_of {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot bp n0)
  (r : Index.NodeRef idx) : option (RedeclaredUseRef root) :=
  match Index.node_view r with
  | Index.Model.VName n =>
      match BN.ordinary_eq_dec n n0 with
      | left _ =>
          match BN.option_redeclroot_eq_dec (BN.resolution_redecl_root (BN.resolve bp r n0)) (Some root) with
          | left Hyields => Some (mk_redeclared_use r (BN.resolve bp r n0) Hyields)
          | right _ => None
          end
      | right _ => None
      end
  | _ => None
  end.
(* the exact use-site contexts of a redeclared root: uses of its name resolving, by exact identity, to it *)
Definition group_use_contexts {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot bp n0)
  : list (RedeclaredUseRef root) :=
  flat_map (fun r => match use_context_of root r with Some c => [c] | None => [] end) name_uses.

(* a returned use context's node is exactly the name occurrence it was built from *)
Lemma use_context_of_node {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot bp n0)
  (r : Index.NodeRef idx) (c : RedeclaredUseRef root) : use_context_of root r = Some c -> ruc_node c = r.
Proof.
  intro H. unfold use_context_of in H.
  destruct (Index.node_view r); try discriminate H.
  match type of H with context[BN.ordinary_eq_dec ?a ?b] => destruct (BN.ordinary_eq_dec a b) end; try discriminate H.
  match type of H with context[BN.option_redeclroot_eq_dec ?a ?b] => destruct (BN.option_redeclroot_eq_dec a b) end;
    try discriminate H.
  injection H as H. subst c. reflexivity.
Qed.

(* map proj over an option-collecting flat_map = filter, when proj recovers each collected element's source *)
Lemma flatmap_option_filter {A B} (f : A -> option B) (g : B -> A)
  (Hg : forall a b, f a = Some b -> g b = a) (L : list A) :
  map g (flat_map (fun a => match f a with Some b => [b] | None => nil end) L)
  = filter (fun a => match f a with Some _ => true | None => false end) L.
Proof.
  induction L as [|a rest IH]; [reflexivity|]. cbn. destruct (f a) as [b|] eqn:E.
  - cbn. rewrite (Hg a b E), IH. reflexivity.
  - exact IH.
Qed.

(* §24.4 ordering + completeness handle: the context nodes are exactly the qualifying name uses, in source order *)
Definition context_qualifies {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot bp n0) (r : Index.NodeRef idx) : bool :=
  match use_context_of root r with Some _ => true | None => false end.
Lemma group_use_contexts_nodes {n0 : Names.OrdinaryIdentifier} (root : BN.RedeclRoot bp n0) :
  map ruc_node (group_use_contexts root) = filter (context_qualifies root) name_uses.
Proof. exact (flatmap_option_filter (use_context_of root) ruc_node (use_context_of_node root) name_uses). Qed.
(* one redeclared-group diagnostic per exact enumerated root; use contexts stay off the disposition path (on demand) *)
Definition group_rows : list (Diagnostic bp) :=
  map (fun rr => DRedeclaredGroup (projT2 rr)) (BN.redeclaration_roots bp).

Definition occ_diags : list (Diagnostic bp) := flat_map occ_diag_rows (fact_list fp).

(* the canonical order: output collision, package main, ordinary redeclaration, then occurrence in fact-list order *)
Definition diagnostics : list (Diagnostic bp) := collision_rows ++ main_rows ++ group_rows ++ occ_diags.
Definition boundaries : list (Boundary bp) := flat_map occ_bound_rows (fact_list fp).

(* one fact yields a diagnostic XOR a boundary; distinct-family facts of one subject still coexist across facts (§6) *)
Lemma occ_row_exclusive (o : OccFact bp) : occ_diag_rows o <> [] -> occ_bound_rows o = [].
Proof.
  destruct o as [r ov | r oa | r os | r ot];
    [ destruct ov | destruct oa | destruct os | destruct ot ];
    cbn; intro H; solve [ reflexivity | exfalso; exact (H eq_refl) ].
Qed.

(* a dependent non-result is neither a diagnostic nor a boundary: it defers to its prerequisite, adding no issue *)
Lemma dependent_no_rows (r : Index.NodeRef idx) (d : Dependency bp) :
  occ_diag_rows (OFValue r (VDependent d)) = [] /\ occ_bound_rows (OFValue r (VDependent d)) = []
  /\ occ_diag_rows (OFApp r (ADependent d)) = [] /\ occ_bound_rows (OFApp r (ADependent d)) = []
  /\ occ_diag_rows (OFStmt r (SDependent d)) = [] /\ occ_bound_rows (OFStmt r (SDependent d)) = []
  /\ occ_diag_rows (OFType r (TDependent d)) = [] /\ occ_bound_rows (OFType r (TDependent d)) = [].
Proof. cbn; repeat split; reflexivity. Qed.

End IssueTable.

Arguments diagnostics {p idx s bd bp} fp pf.
Arguments boundaries {p idx s bd bp} fp.

Section IssueLaws.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} {bp : BN.BindingPhase s bd}.

(* the root algebra is total: every diagnostic roots at an exact node, package, or group, never a self-fallback *)
Lemma root_algebra_total (d : Diagnostic bp) :
  (exists r, diag_root d = RootNode r) \/ (exists pr, diag_root d = RootPackage pr)
  \/ (exists (n : Names.OrdinaryIdentifier) (root : BN.RedeclRoot bp n), diag_root d = RootGroup root).
Proof. destruct d; cbn; eauto 8. Qed.

(* §24.4 soundness: every exact use context's exact resolution yields exactly the root it is a context of *)
Lemma redeclared_use_sound {n0 : Names.OrdinaryIdentifier} {root : BN.RedeclRoot bp n0}
  (c : RedeclaredUseRef root) : BN.resolution_redecl_root (ruc_res c) = Some root.
Proof. exact (ruc_yields c). Qed.

(* §24.4 exact-root identity: a context belongs to no root other than the exact one its resolution yields *)
Lemma redeclared_use_root_unique {n0 : Names.OrdinaryIdentifier} {r1 r2 : BN.RedeclRoot bp n0}
  (c : RedeclaredUseRef r1) : BN.resolution_redecl_root (ruc_res c) = Some r2 -> r1 = r2.
Proof. intro H. pose proof (ruc_yields c) as Hy. rewrite Hy in H. injection H as H. exact H. Qed.

End IssueLaws.

(* §6 the complete disposition algebra + applicability before judgment *)
Inductive Disposition {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) : Type :=
| DSucceeded : Disposition bp
| DAbsent : Disposition bp
| DInvalid : IssueCause bp -> list (IssueCause bp) -> Disposition bp
| DUnsupported : Requirement bp -> list (Requirement bp) -> Disposition bp
| DInvalidAndUnsupported : IssueCause bp -> list (IssueCause bp) -> Requirement bp -> list (Requirement bp) -> Disposition bp.
Arguments DSucceeded {p idx s bd bp}. Arguments DAbsent {p idx s bd bp}.
Arguments DInvalid {p idx s bd bp} _ _. Arguments DUnsupported {p idx s bd bp} _ _.
Arguments DInvalidAndUnsupported {p idx s bd bp} _ _ _ _.

Section DispositionAlgebra.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} {bp : BN.BindingPhase s bd}
        (fp : FactPhase bp) (pf : PackageFacts bp).

(* the whole-program disposition aggregates the one canonical issue table into the complete 5-way algebra *)
Definition program_disposition : Disposition bp :=
  match diagnostics fp pf, boundaries fp with
  | nil, nil => DSucceeded
  | d :: ds, nil => DInvalid (diag_cause d) (map diag_cause ds)
  | nil, b :: bs => DUnsupported (bound_req b) (map bound_req bs)
  | d :: ds, b :: bs => DInvalidAndUnsupported (diag_cause d) (map diag_cause ds)
                                               (bound_req b) (map bound_req bs)
  end.

(* success is exactly empty reports; a rejected program with simultaneous boundaries is InvalidAndUnsupported *)
Lemma program_disposition_succeeded :
  program_disposition = DSucceeded <-> diagnostics fp pf = nil /\ boundaries fp = nil.
Proof.
  unfold program_disposition; destruct (diagnostics fp pf) as [|d ds], (boundaries fp) as [|b bs]; cbn.
  - split; intros _; [ split; reflexivity | reflexivity ].
  - split; [ discriminate | intros [_ H2]; discriminate H2 ].
  - split; [ discriminate | intros [H1 _]; discriminate H1 ].
  - split; [ discriminate | intros [H1 _]; discriminate H1 ].
Qed.

Lemma program_disposition_both :
  (exists d ds b bs c1 c2 q1 q2, diagnostics fp pf = d :: ds /\ boundaries fp = b :: bs
     /\ program_disposition = DInvalidAndUnsupported c1 c2 q1 q2) \/
  program_disposition = DSucceeded \/
  (exists c cs, program_disposition = DInvalid c cs) \/
  (exists q qs, program_disposition = DUnsupported q qs).
Proof.
  unfold program_disposition; destruct (diagnostics fp pf) as [|d ds] eqn:Ed, (boundaries fp) as [|b bs] eqn:Eb.
  - right; left; reflexivity.
  - right; right; right; eexists; eexists; reflexivity.
  - right; right; left; eexists; eexists; reflexivity.
  - left; do 8 eexists; repeat split; reflexivity.
Qed.

End DispositionAlgebra.

(* §11 structural progress + cost: every construction is structural recursion over finite maps, no fuel or budget *)
Section Cost.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s} (bp : BN.BindingPhase s bd).

(* one structural pass: each node contributes the facts of its applicable families via a single flat_map, no fuel *)
Lemma fact_phase_one_pass : fact_list (facts bp) = raw_facts bp.
Proof. unfold fact_list, facts; cbn [proj1_sig]. reflexivity. Qed.

End Cost.

(* the canonical issue lists and 5-way summary as projections of the one retained result, for downstream readers *)
Definition result_diagnostics {p} (r : Result p) : list (Diagnostic (res_binds r)) :=
  diagnostics (res_facts r) (res_pkg r).
Definition result_boundaries {p} (r : Result p) : list (Boundary (res_binds r)) :=
  boundaries (res_facts r).
Definition result_disposition {p} (r : Result p) : Disposition (res_binds r) :=
  program_disposition (res_facts r) (res_pkg r).

(* an issue is a diagnostic or a boundary; the two classes partition the one canonical sequence *)
Inductive IssueClass : Type := ClassDiagnostic | ClassBoundary.

Inductive Issue {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) : Type :=
| IDiag  : Diagnostic bp -> Issue bp
| IBound : Boundary bp -> Issue bp.
Arguments IDiag {p idx s bd bp} _.
Arguments IBound {p idx s bd bp} _.

(* the one canonical issue sequence: every diagnostic then every boundary, each kept in its own source order *)
Definition result_issues {p} (r : Result p) : list (Issue (res_binds r)) :=
  map IDiag (result_diagnostics r) ++ map IBound (result_boundaries r).

Section IssueIdentity.
Context {p : Syntax.Program}.

(* an issue's class, root, family, subject, and cause-or-requirement, projected from whichever row it is *)
Definition issue_class {r : Result p} (i : Issue (res_binds r)) : IssueClass :=
  match i with IDiag _ => ClassDiagnostic | IBound _ => ClassBoundary end.
Definition issue_root {r : Result p} (i : Issue (res_binds r)) : IssueRoot (res_binds r) :=
  match i with IDiag d => diag_root d | IBound b => bound_root b end.
Definition issue_family {r : Result p} (i : Issue (res_binds r)) : option Family :=
  match i with IDiag d => diag_family d | IBound b => Some (bound_family b) end.
Definition issue_cause_or_req {r : Result p} (i : Issue (res_binds r))
  : IssueCause (res_binds r) + Requirement (res_binds r) :=
  match i with IDiag d => inl (diag_cause d) | IBound b => inr (bound_req b) end.
Definition issue_related {r : Result p} (i : Issue (res_binds r)) : list (Index.NodeRef (res_index r)) :=
  match i with IDiag d => diag_related d | IBound _ => [] end.

(* an issue identity: an exact ordinal into result_issues, retaining the exact row it indexes there *)
Record IssueRef (r : Result p) : Type := mkIssueRef {
  ir_ord : nat ;
  ir_row : Issue (res_binds r) ;
  ir_at  : nth_error (result_issues r) ir_ord = Some ir_row
}.
Arguments mkIssueRef {r} _ _ _.
Arguments ir_ord {r} _.
Arguments ir_row {r} _.
Arguments ir_at {r} _.

(* Diagnostic and Boundary are projections of an issue ref: exactly the row it references, never a synthesis *)
Definition iref_diagnostic {r : Result p} (ref : IssueRef r) : option (Diagnostic (res_binds r)) :=
  match ir_row ref with IDiag d => Some d | IBound _ => None end.
Definition iref_boundary {r : Result p} (ref : IssueRef r) : option (Boundary (res_binds r)) :=
  match ir_row ref with IBound b => Some b | IDiag _ => None end.

(* bidirectional membership: a ref is exactly a position that indexes an issue in the one sequence *)
Lemma issue_ref_sound (r : Result p) (ref : IssueRef r) :
  nth_error (result_issues r) (ir_ord ref) = Some (ir_row ref).
Proof. exact (ir_at ref). Qed.
Lemma issue_ref_complete (r : Result p) (n : nat) (i : Issue (res_binds r)) :
  nth_error (result_issues r) n = Some i -> exists ref : IssueRef r, ir_ord ref = n /\ ir_row ref = i.
Proof. intro H. exists (mkIssueRef n i H). split; reflexivity. Qed.

(* exact identity: the ordinal alone determines the issue a ref names *)
Lemma issue_ref_ord_identity (r : Result p) (a b : IssueRef r) : ir_ord a = ir_ord b -> ir_row a = ir_row b.
Proof. intro H. pose proof (ir_at a); pose proof (ir_at b); congruence. Qed.

(* class partition: the sequence is exactly the diagnostics block followed by the boundaries block *)
Lemma result_issues_class_split (r : Result p) :
  result_issues r = map IDiag (result_diagnostics r) ++ map IBound (result_boundaries r).
Proof. reflexivity. Qed.

(* the row any position names is exactly a canonical diagnostic or boundary, never a fabricated one *)
Lemma idiag_in (r : Result p) (n : nat) (d : Diagnostic (res_binds r)) :
  nth_error (result_issues r) n = Some (IDiag d) -> In d (result_diagnostics r).
Proof.
  intro H. apply nth_error_In in H. unfold result_issues in H. apply in_app_or in H.
  destruct H as [Hd|Hb].
  - apply in_map_iff in Hd. destruct Hd as [d' [Heq Hin]]. injection Heq as Heq. subst d'. exact Hin.
  - apply in_map_iff in Hb. destruct Hb as [b' [Heq _]]. discriminate Heq.
Qed.
Lemma ibound_in (r : Result p) (n : nat) (b : Boundary (res_binds r)) :
  nth_error (result_issues r) n = Some (IBound b) -> In b (result_boundaries r).
Proof.
  intro H. apply nth_error_In in H. unfold result_issues in H. apply in_app_or in H.
  destruct H as [Hd|Hb].
  - apply in_map_iff in Hd. destruct Hd as [d' [Heq _]]. discriminate Heq.
  - apply in_map_iff in Hb. destruct Hb as [b' [Heq Hin]]. injection Heq as Heq. subst b'. exact Hin.
Qed.

(* payload: the exact row a ref names is a canonical row of its class *)
Lemma iref_payload (r : Result p) (ref : IssueRef r) :
  match ir_row ref with
  | IDiag d => In d (result_diagnostics r)
  | IBound b => In b (result_boundaries r)
  end.
Proof.
  pose proof (ir_at ref) as H. set (row := ir_row ref) in *. clearbody row.
  destruct row as [d|b].
  - exact (idiag_in r (ir_ord ref) d H).
  - exact (ibound_in r (ir_ord ref) b H).
Qed.

(* stable order: the k-th diagnostic sits at ordinal k; the j-th boundary at ordinal (#diagnostics + j) *)
Lemma issue_diag_at (r : Result p) (n : nat) (d : Diagnostic (res_binds r)) :
  nth_error (result_diagnostics r) n = Some d -> nth_error (result_issues r) n = Some (IDiag d).
Proof.
  intro H. unfold result_issues.
  rewrite nth_error_app1 by (rewrite <- nth_error_Some; rewrite (map_nth_error _ _ _ H); discriminate).
  exact (map_nth_error _ _ _ H).
Qed.
Lemma issue_bound_at (r : Result p) (n : nat) (b : Boundary (res_binds r)) :
  nth_error (result_boundaries r) n = Some b ->
  nth_error (result_issues r) ((Datatypes.length (result_diagnostics r) + n)%nat) = Some (IBound b).
Proof.
  intro H. unfold result_issues.
  rewrite nth_error_app2 by (first [rewrite length_map | rewrite map_length]; apply Nat.le_add_r).
  first [rewrite length_map | rewrite map_length]. rewrite Nat.add_comm, Nat.add_sub.
  exact (map_nth_error _ _ _ H).
Qed.

(* no collapse: N diagnostics and M boundaries give exactly N+M distinct ordinal slots, none merged or dropped *)
Lemma result_issues_length (r : Result p) :
  Datatypes.length (result_issues r)
  = (Datatypes.length (result_diagnostics r) + Datatypes.length (result_boundaries r))%nat.
Proof.
  unfold result_issues.
  first [rewrite app_length | rewrite length_app];
  first [rewrite !length_map | rewrite !map_length]; reflexivity.
Qed.
Lemma iref_ord_bound (r : Result p) (ref : IssueRef r) :
  (ir_ord ref < Datatypes.length (result_issues r))%nat.
Proof. rewrite <- nth_error_Some. rewrite (ir_at ref). discriminate. Qed.

End IssueIdentity.

(* the record parameters generalize over p and r on section close; keep both implicit for external readers *)
Arguments mkIssueRef {p r} _ _ _.
Arguments ir_ord {p r} _.
Arguments ir_row {p r} _.
Arguments ir_at {p r} _.
