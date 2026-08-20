(* Analysis — the sole fact and issue authority: per-occurrence outcomes, the issue table, and the preflight. *)

From Stdlib Require Import List Bool String Ascii ZArith NArith Lia Eqdep_dec.
From Fido Require Import Names Integer Float Complex Syntax Index FilePath Compilable.TypeResolution Compilable.Bindings.
Import ListNotations.

Module TR := Compilable.TypeResolution.
Module BN := Compilable.Bindings.

Inductive Cause {p} (idx : Index.ProgramIndex p) : Type :=
| InvalidIdentity : Names.PredeclaredName -> Cause idx
| UnresolvedName : Names.OrdinaryIdentifier -> Index.NodeRef idx -> Cause idx
| TypeAsValue : BN.ObjectRef idx -> Cause idx
| NotAType : BN.ObjectRef idx -> Cause idx
| NotCallable : BN.ObjectRef idx -> Cause idx
| NotCallableExpr : Index.NodeRef idx -> Cause idx
| ConversionArity : Names.PredeclaredName -> nat -> Cause idx
| ComplexArity : nat -> Cause idx
| ComplexMismatch : Index.NodeRef idx -> Index.NodeRef idx -> Cause idx
| UnaryMismatch : Index.NodeRef idx -> Cause idx
| ConversionOverflow : TR.TypeForm -> Index.NodeRef idx -> Cause idx
| ConversionNotRepresentable : TR.TypeForm -> Index.NodeRef idx -> Cause idx
| DefaultOverflow : TR.Constant -> Cause idx
| NoValueUsed : Cause idx
| IllegalStatement : Cause idx
| ConstMissingInit : BN.ConstSpecStatus idx -> Cause idx
| ResultCountMismatch : nat -> nat -> Cause idx
| ShortDuplicate : Names.OrdinaryIdentifier -> Cause idx
| MainArity : BN.FunctionDeclRef idx -> list (Index.NodeRef idx) -> nat -> Cause idx.
Arguments InvalidIdentity {p idx} _. Arguments UnresolvedName {p idx} _ _.
Arguments TypeAsValue {p idx} _. Arguments NotAType {p idx} _.
Arguments NotCallable {p idx} _. Arguments NotCallableExpr {p idx} _.
Arguments ConversionArity {p idx} _ _. Arguments ComplexArity {p idx} _.
Arguments ComplexMismatch {p idx} _ _. Arguments UnaryMismatch {p idx} _.
Arguments ConversionOverflow {p idx} _ _. Arguments ConversionNotRepresentable {p idx} _ _.
Arguments DefaultOverflow {p idx} _. Arguments NoValueUsed {p idx}. Arguments IllegalStatement {p idx}.
Arguments ConstMissingInit {p idx} _. Arguments ResultCountMismatch {p idx} _ _. Arguments ShortDuplicate {p idx} _.
Arguments MainArity {p idx} _ _ _.

Inductive Requirement {p} (idx : Index.ProgramIndex p) : Type :=
| ReqValueMeaning : BN.BinderRef idx -> Requirement idx
| ReqTypeMeaning : BN.ObjectRef idx -> Requirement idx
| ReqComplexType : Index.NodeRef idx -> Requirement idx
| ReqApplication : Names.PredeclaredName -> list (Index.NodeRef idx) -> Requirement idx
| ReqMainUse : Index.MainOccurrenceRef idx -> Requirement idx
| ReqConstDecl : BN.ConstSpecStatus idx -> Requirement idx
| ReqDeclMeaning : Index.NodeRef idx -> Requirement idx.
Arguments ReqDeclMeaning {p idx} _.
Arguments ReqValueMeaning {p idx} _. Arguments ReqTypeMeaning {p idx} _.
Arguments ReqComplexType {p idx} _. Arguments ReqApplication {p idx} _ _.
Arguments ReqMainUse {p idx} _. Arguments ReqConstDecl {p idx} _.

Inductive AppResult : Type :=
| AppValue : TR.ResolvedConstant -> AppResult
| AppBuiltinStmt : AppResult.

(* each occurrence family is an independent per-node judgment: no cross-node blocking, so parent and child coexist *)
Inductive ValueOutcome {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) : Type :=
| VOK : TR.ResolvedConstant -> ValueOutcome site
| VNonconst : ValueOutcome site
| VInvalid : Cause idx -> ValueOutcome site
| VUnmet : Requirement idx -> ValueOutcome site.
Arguments VOK {p idx site} _. Arguments VNonconst {p idx site}.
Arguments VInvalid {p idx site} _. Arguments VUnmet {p idx site} _.

Inductive AppOutcome {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) : Type :=
| AOK : AppResult -> AppOutcome site
| AInvalid : Cause idx -> AppOutcome site
| AUnmet : Requirement idx -> AppOutcome site.
Arguments AOK {p idx site} _. Arguments AInvalid {p idx site} _.
Arguments AUnmet {p idx site} _.

Inductive StmtOutcome {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) : Type :=
| SOK : StmtOutcome site
| SInvalid : Cause idx -> StmtOutcome site
| SUnmet : Requirement idx -> StmtOutcome site.
Arguments SOK {p idx site}. Arguments SInvalid {p idx site} _.
Arguments SUnmet {p idx site} _.

Inductive TypeUseOutcome {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) : Type :=
| TOK : TR.TypeForm -> TypeUseOutcome site
| TInvalid : Cause idx -> TypeUseOutcome site
| TUnmet : Requirement idx -> TypeUseOutcome site.
Arguments TOK {p idx site} _. Arguments TInvalid {p idx site} _.
Arguments TUnmet {p idx site} _.

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
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} (bp : BN.BindingPhase s).

(* the form/value meaning of a name at a use, for constant folding; None for anything without one *)
Definition nm_at (use : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) : option TR.NameMeaning :=
  match BN.resolve bp use n with
  | BN.RBound (BN.PredeclaredObject pn) =>
      match pmeaning pn with
      | PMConvForm t => Some (TR.NMConversionForm t)
      | PMValue c => Some (TR.NMValueConstant c)
      | _ => None
      end
  | _ => None
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

(* the numbered argument edges: the direct children after the exact application head, no role filter *)
Definition app_args (r : Index.NodeRef idx) (H : Index.node_view r = Index.VApplication)
  : list (Index.NodeRef idx) := tl (Index.node_children r).
Definition mconst (m : Collections.NodeMap.t (option TR.ConstantInfo)) (rc : Index.NodeRef idx)
  : option TR.ConstantInfo :=
  match Collections.NodeMap.find (Index.nr_key rc) m with Some oc => oc | None => None end.
Definition node_const (m : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx)
  : option TR.ConstantInfo :=
  match Index.node_view r as v return Index.node_view r = v -> option TR.ConstantInfo with
  | Index.VName n => fun _ =>
      match nm_at r n with Some (TR.NMValueConstant c) => Some (TR.mk_cinfo c TR.Untyped) | _ => None end
  | Index.VLiteral (Syntax.IntegerLiteral k) => fun _ => Some (TR.mk_cinfo (TR.CInt (Z.of_N k)) TR.Untyped)
  | Index.VLiteral (Syntax.FloatLiteral d) => fun _ => Some (TR.mk_cinfo (TR.CFloat (Float.nnd_value d)) TR.Untyped)
  | Index.VLiteral (Syntax.StringLiteral str) => fun _ => Some (TR.mk_cinfo (TR.CString str) TR.Untyped)
  | Index.VUnary Syntax.UnaryMinus => fun Hv =>
      match mconst m (Index.first_edge r (f_equal Index.requires_first_edge Hv)) with
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
  | Index.VApplication => fun Hv =>
      match Index.node_view (Index.first_edge r (f_equal Index.requires_first_edge Hv)) with
      | Index.VName h =>
          match app_args r Hv with
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
              match BN.resolve bp r h with
              | BN.RBound (BN.PredeclaredObject Names.PComplex) =>
                  match mconst m re, mconst m im with
                  | Some cre, Some cim =>
                      match TR.constant_to_float (TR.ci_const cre), TR.constant_to_float (TR.ci_const cim) with
                      | Some _, Some _ =>
                          option_map (fun c => TR.mk_cinfo c TR.Untyped)
                            (TR.complex_of_constants (TR.ci_const cre) (TR.ci_const cim))
                      | _, _ => None
                      end
                  | _, _ => None
                  end
              | _ => None
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
  match Index.node_role r with Index.RApplicationHead => true | _ => false end.
Definition value_ctx (r : Index.NodeRef idx) : bool :=
  match Index.node_role r with Index.RApplicationHead => false | Index.RExprStatementExpr => false | _ => true end.

(* a conversion/complex head folds its argument, so a folded value's default-int type is never forced *)
Definition head_folds (par : Index.NodeRef idx) : bool :=
  match Index.node_view par as v return Index.node_view par = v -> bool with
  | Index.VApplication => fun Hv =>
      match Index.node_view (Index.first_edge par (f_equal Index.requires_first_edge Hv)) with
      | Index.VName h =>
          match BN.resolve bp par h with
          | BN.RBound (BN.PredeclaredObject pn) =>
              match pmeaning pn with PMConvForm _ => true | PMComplex => true | _ => false end
          | _ => false
          end
      | _ => false
      end
  | _ => fun _ => false
  end eq_refl.
Definition fold_consumed (r : Index.NodeRef idx) : bool :=
  match Index.node_role r with
  | Index.RUnaryOperand => true
  | Index.RApplicationArg _ => match Index.node_parent r with Some par => head_folds par | None => false end
  | _ => false
  end.


(* a const spec: a first spec omitting its initializer, or a known result-count mismatch, is an exact invalidity *)
Definition const_spec_disposition (r : Index.NodeRef idx) : ValueOutcome r :=
  let st := BN.const_spec_status r in
  match Index.node_view r with
  | Index.VConstSpec (Index.CSExplicit _ nn nv) =>
      if Nat.eqb nn nv then VUnmet (ReqConstDecl st) else VInvalid (ResultCountMismatch nn nv)
  | Index.VConstSpec Index.CSInherited =>
      if BN.cs_first st then VInvalid (ConstMissingInit st) else VUnmet (ReqConstDecl st)
  | _ => VNonconst
  end.

Definition own_value (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx) : ValueOutcome r :=
  match Index.node_view r as v return Index.node_view r = v -> ValueOutcome r with
  | Index.VName n => fun _ =>
      match BN.resolve bp r n with
      | BN.RUnbound => VInvalid (UnresolvedName n r)
      | BN.RBound (BN.PredeclaredObject pn) =>
          match pmeaning pn with
          | PMValue c => match TR.default_constant c with Some rc => VOK rc | None => VInvalid (InvalidIdentity pn) end
          | PMInvalidId => VInvalid (InvalidIdentity pn)
          | _ => if is_app_head r then VNonconst else VInvalid (TypeAsValue (BN.PredeclaredObject pn))
          end
      | BN.RBound (BN.SourceObject (BN.DOBinder b)) => VUnmet (ReqValueMeaning b)
      | BN.RBound (BN.SourceObject (BN.DOFunc f)) => if is_app_head r then VNonconst else VUnmet (ReqMainUse (BN.function_occ f))
      | BN.RRedeclared _ => VNonconst
      end
  | Index.VLiteral _ => fun _ =>
      match mconst ctab r with
      | Some ci => match resolve_constant_info ci with
                   | Some rc => VOK rc
                   | None => if fold_consumed r then VNonconst else VInvalid (DefaultOverflow (TR.ci_const ci))
                   end
      | None => VNonconst
      end
  | Index.VUnary Syntax.UnaryMinus => fun Hv =>
      match mconst ctab (Index.first_edge r (f_equal Index.requires_first_edge Hv)) with
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
  | Index.VApplication => fun Hv =>
      match Index.node_view (Index.first_edge r (f_equal Index.requires_first_edge Hv)) with
      | Index.VName h =>
          match BN.resolve bp r h with
          | BN.RBound (BN.PredeclaredObject pn) =>
              match pmeaning pn, app_args r Hv with
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
          | _ => VNonconst
          end
      | _ => VNonconst
      end
  (* declaration outcomes live on the declaration subject (spec / short statement), never on the binder *)
  | Index.VConstSpec _ => fun _ => const_spec_disposition r
  | Index.VVarSpec _ => fun _ => VUnmet (ReqDeclMeaning r)
  | Index.VTypeSpec _ => fun _ => VUnmet (ReqDeclMeaning r)
  | _ => fun _ => VNonconst
  end eq_refl.

Definition own_app (r : Index.NodeRef idx) : AppOutcome r :=
  match Index.node_view r as v return Index.node_view r = v -> AppOutcome r with
  | Index.VApplication => fun Hv =>
      let hd := Index.first_edge r (f_equal Index.requires_first_edge Hv) in
      match Index.node_view hd with
      | Index.VName h =>
          match BN.resolve bp r h with
          | BN.RBound (BN.PredeclaredObject pn) =>
              match pmeaning pn with
              | PMConvForm _ => match app_args r Hv with _ :: nil => AOK (AppBuiltinStmt) | _ => AInvalid (ConversionArity pn (Datatypes.length (app_args r Hv))) end
              | PMComplex =>
                  (* application family = callability + arity only; the complex value is own_value's exact judgment *)
                  match app_args r Hv with
                  | _ :: _ :: nil => AOK AppBuiltinStmt
                  | _ => AInvalid (ComplexArity (Datatypes.length (app_args r Hv)))
                  end
              | PMPrintln => AOK AppBuiltinStmt
              | PMValue _ => AInvalid (NotCallable (BN.PredeclaredObject pn))
              | PMInvalidId => AOK AppBuiltinStmt
              | PMUnmodelled => AUnmet (ReqApplication pn (app_args r Hv))
              end
          | BN.RBound (BN.SourceObject (BN.DOBinder b)) => AInvalid (NotCallable (BN.SourceObject (BN.DOBinder b)))
          | BN.RBound (BN.SourceObject (BN.DOFunc f)) =>
              (* the fixed main is a zero-parameter function: a zero-argument call succeeds as a known zero-result call *)
              match app_args r Hv with
              | nil => AOK AppBuiltinStmt
              | args => AInvalid (MainArity f args (Datatypes.length args))
              end
          | BN.RRedeclared _ => AOK AppBuiltinStmt
          | BN.RUnbound => AOK AppBuiltinStmt
          end
      | _ => AInvalid (NotCallableExpr hd)
      end
  | _ => fun _ => AOK AppBuiltinStmt
  end eq_refl.

(* the statement expr already owns a diagnostic or boundary: the illegal-statement judgment is dependent, not a root *)
Definition child_owns_issue (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (e : Index.NodeRef idx) : bool :=
  match own_value ctab e with
  | VInvalid _ | VUnmet _ => true
  | _ => match own_app e with AInvalid _ | AUnmet _ => true | _ => false end
  end.

(* an expr-statement is illegal only when its expr is otherwise valid but not a legal statement head *)
Definition own_stmt (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx) : StmtOutcome r :=
  match Index.node_view r as v return Index.node_view r = v -> StmtOutcome r with
  | Index.VStmt Index.SSExpr => fun Hv =>
      let e := Index.first_edge r (f_equal Index.requires_first_edge Hv) in
      if child_owns_issue ctab e then SOK
      else match Index.node_view e as ve return Index.node_view e = ve -> StmtOutcome r with
           | Index.VApplication => fun He =>
               match Index.node_view (Index.first_edge e (f_equal Index.requires_first_edge He)) with
               | Index.VName h =>
                   match BN.resolve bp r h with
                   | BN.RBound (BN.PredeclaredObject Names.PPrintln) => SOK
                   | BN.RUnbound => SOK
                   | BN.RBound (BN.SourceObject _) => SOK
                   | _ => SInvalid IllegalStatement
                   end
               | _ => SInvalid IllegalStatement
               end
           | _ => fun _ => SInvalid IllegalStatement
           end eq_refl
  | Index.VStmt (Index.SSShort _) => fun _ =>
      (* a short declaration: a repeated left name is invalid; otherwise its later meaning is a boundary *)
      match BN.short_stmt_dup_name bp r with
      | Some n => SInvalid (ShortDuplicate n)
      | None => SUnmet (ReqDeclMeaning r)
      end
  | _ => fun _ => SOK
  end eq_refl.

(* the represented but unmodelled predeclared types: real Go types with no current C4 TypeForm *)
Definition is_unmodeled_type (pn : Names.PredeclaredName) : bool :=
  match pn with Names.PUintptr | Names.PAny | Names.PComparable | Names.PError => true | _ => false end.

(* a type use resolves its name: modelled type is its form, unmodelled real type a boundary, else invalid *)
Definition own_type (r : Index.NodeRef idx) : TypeUseOutcome r :=
  match Index.node_view r with
  | Index.VTypeExpr (Syntax.NamedType n) =>
      match BN.resolve bp r n with
      | BN.RBound (BN.PredeclaredObject pn) =>
          match TR.predeclared_meaning pn with
          | TR.NMConversionForm t => TOK t
          | _ => if is_unmodeled_type pn
                 then TUnmet (ReqTypeMeaning (BN.PredeclaredObject pn))
                 else TInvalid (NotAType (BN.PredeclaredObject pn))
          end
      | BN.RBound (BN.SourceObject (BN.DOBinder b)) => TUnmet (ReqTypeMeaning (BN.SourceObject (BN.DOBinder b)))
      | BN.RBound (BN.SourceObject (BN.DOFunc m)) => TInvalid (NotAType (BN.SourceObject (BN.DOFunc m)))
      | BN.RRedeclared _ => TOK TR.BoolForm
      | BN.RUnbound => TInvalid (UnresolvedName n r)
      end
  | _ => TOK TR.BoolForm
  end.

End OverPhase.

(* one applicability-first fact per applicable family; an application carries disjoint callability and value facts *)
Inductive OccFact {p} {idx : Index.ProgramIndex p} : Type :=
| OFValue : forall r : Index.NodeRef idx, ValueOutcome r -> OccFact
| OFApp   : forall r : Index.NodeRef idx, AppOutcome r -> OccFact
| OFStmt  : forall r : Index.NodeRef idx, StmtOutcome r -> OccFact
| OFType  : forall r : Index.NodeRef idx, TypeUseOutcome r -> OccFact.
Arguments OccFact {p} idx.
Arguments OFValue {p idx} _ _. Arguments OFApp {p idx} _ _.
Arguments OFStmt {p idx} _ _. Arguments OFType {p idx} _ _.

Section Retain.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} (bp : BN.BindingPhase s).

(* exactly the facts of the families that apply to a node, in family order; an inapplicable family yields none *)
Definition occ_facts (ctab : Collections.NodeMap.t (option TR.ConstantInfo)) (r : Index.NodeRef idx) : list (OccFact idx) :=
  match Index.node_view r with
  | Index.VName _ | Index.VLiteral _ | Index.VUnary _ => [OFValue r (own_value bp ctab r)]
  | Index.VApplication => [OFApp r (own_app bp r); OFValue r (own_value bp ctab r)]
  | Index.VStmt Index.SSExpr => [OFStmt r (own_stmt bp ctab r)]
  | Index.VStmt (Index.SSShort _) => [OFStmt r (own_stmt bp ctab r)]
  | Index.VTypeExpr _ => [OFType r (own_type bp r)]
  | Index.VConstSpec _ | Index.VVarSpec _ | Index.VTypeSpec _ => [OFValue r (own_value bp ctab r)]
  | _ => []
  end.

(* one const table per file, built once and shared across that file's per-node facts (children stay in-file) *)
Definition raw_facts : list (OccFact idx) :=
  flat_map (fun fr => let ctab := const_table bp fr in flat_map (occ_facts ctab) (Index.file_nodes fr))
           (flat_map BN.PI.pkg_members (BN.PI.packages s)).

Definition FactPhase : Type := { m : list (OccFact idx) | m = raw_facts }.
Definition facts : FactPhase := exist _ raw_facts eq_refl.
Definition fact_list (fp : FactPhase) : list (OccFact idx) := proj1_sig fp.

End Retain.

Arguments FactPhase {p idx s} bp.
Arguments facts {p idx s} bp.
Arguments fact_list {p idx s bp} _.

Section Laws.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} (bp : BN.BindingPhase s).

(* the phase content is built once; every phase carries exactly the canonical classification, none caller-supplied *)
Lemma fact_once (fp : FactPhase bp) : fact_list fp = raw_facts bp.
Proof. exact (proj2_sig fp). Qed.

(* statement and type-use families have no Nonconst constructor: OK / invalid / unmet exhaust each *)
Lemma only_lawful_per_family (r : Index.NodeRef idx) :
  (forall o : StmtOutcome r, o = SOK \/ (exists c, o = SInvalid c) \/ (exists q, o = SUnmet q))
  /\ (forall o : TypeUseOutcome r, (exists f, o = TOK f) \/ (exists c, o = TInvalid c) \/ (exists q, o = TUnmet q)).
Proof. split; intro o; destruct o; eauto 7. Qed.

End Laws.

(* the fresh-build preflight: naming and root entries are PackageIdentity facts; Analysis owns only the collision *)

Inductive FreshBuildDisposition {p} {idx : Index.ProgramIndex p} (s : BN.PI.PackageSurface idx) : Type :=
| FreshOk : FreshBuildDisposition s
| FreshCollision : BN.PI.PackageRef s -> BN.PI.RootEntryRef idx -> FreshBuildDisposition s.
Arguments FreshOk {p idx s}.
Arguments FreshCollision {p idx s} _ _.

(* collision applicability is exactly OneSelected, independent of any package's main multiplicity *)
Definition raw_preflight {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}
  (bp : BN.BindingPhase s) : FreshBuildDisposition s :=
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
  (bp : BN.BindingPhase s) : Type := { d : FreshBuildDisposition s | d = raw_preflight bp }.
Definition package_facts {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}
  (bp : BN.BindingPhase s) : PackageFacts bp := exist _ (raw_preflight bp) eq_refl.
Definition preflight {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bp : BN.BindingPhase s}
  (pf : PackageFacts bp) : FreshBuildDisposition s := proj1_sig pf.
Definition package_rule {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bp : BN.BindingPhase s}
  (pf : PackageFacts bp) (pr : BN.PI.PackageRef s) : BN.MainStatus s pr := BN.package_main bp pr.

Lemma package_rule_is_projection {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}
  {bp : BN.BindingPhase s} (pf : PackageFacts bp) (pr : BN.PI.PackageRef s) :
  package_rule pf pr = BN.package_main bp pr.
Proof. reflexivity. Qed.

Lemma packages_consume_one_surface {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}
  {bp : BN.BindingPhase s} (pf : PackageFacts bp) : preflight pf = raw_preflight bp.
Proof. exact (proj2_sig pf). Qed.

(* the one canonical analysis result over p; analyze builds it once, holding FactPhase and PackageFacts as fields *)
Record Result (p : Syntax.Program) : Type := mk_result {
  res_index   : Index.ProgramIndex p ;
  res_surface : BN.PI.PackageSurface res_index ;
  res_binds   : BN.BindingPhase res_surface ;
  res_facts   : FactPhase res_binds ;
  res_pkg     : PackageFacts res_binds
}.
Arguments mk_result {p} _ _ _ _ _.
Arguments res_index {p} _. Arguments res_surface {p} _. Arguments res_binds {p} _.
Arguments res_facts {p} _. Arguments res_pkg {p} _.

Definition analyze (p : Syntax.Program) : Result p :=
  let i := Index.index_program p in
  let s := BN.PI.package_surface i in
  let b := BN.bindings s in
  mk_result i s b (facts b) (package_facts b).

(* the semantic family of an occurrence issue: declaration specs and short-decls are distinct from plain uses *)
Inductive Family : Type := FamValue | FamApplication | FamStatement | FamTypeUse | FamDeclaration.

(* an issue roots at an exact node, an exact package, or an exact declaration group; never a self-fallback *)
Inductive IssueRoot {p} {idx : Index.ProgramIndex p} (s : BN.PI.PackageSurface idx) : Type :=
| RootNode : Index.NodeRef idx -> IssueRoot s
| RootPackage : BN.PI.PackageRef s -> IssueRoot s
| RootGroup : BN.DeclarationGroupRef s -> IssueRoot s.
Arguments RootNode {p idx s} _.
Arguments RootPackage {p idx s} _.
Arguments RootGroup {p idx s} _.

(* the exact diagnostics: an occurrence invalidity, a missing fixed main, an output collision, a redeclared group *)
Inductive Diagnostic {p} {idx : Index.ProgramIndex p} (s : BN.PI.PackageSurface idx) : Type :=
| DOcc : Index.NodeRef idx -> Family -> Cause idx -> Diagnostic s
| DMissingMain : BN.PI.PackageRef s -> Diagnostic s
| DOutputCollision : BN.PI.PackageRef s -> BN.PI.RootEntryRef idx -> Diagnostic s
| DRedeclaredGroup : BN.DeclarationGroupRef s -> list (Index.NodeRef idx) -> Diagnostic s.
Arguments DOcc {p idx s} _ _ _.
Arguments DMissingMain {p idx s} _.
Arguments DOutputCollision {p idx s} _ _.
Arguments DRedeclaredGroup {p idx s} _ _.

(* the exact boundaries: an occurrence-family unmet requirement, retaining its subject, family, and requirement *)
Inductive Boundary {p} {idx : Index.ProgramIndex p} (s : BN.PI.PackageSurface idx) : Type :=
| BOcc : Index.NodeRef idx -> Family -> Requirement idx -> Boundary s.
Arguments BOcc {p idx s} _ _ _.

(* the issue cause a reader projects from a diagnostic row, exactly as retained, never re-derived from a weaker site *)
Inductive IssueCause {p} {idx : Index.ProgramIndex p} (s : BN.PI.PackageSurface idx) : Type :=
| OccCause : Cause idx -> IssueCause s
| MissingMainCause : BN.PI.PackageRef s -> IssueCause s
| OutputCollisionCause : BN.PI.PackageRef s -> BN.PI.RootEntryRef idx -> IssueCause s
| RedeclaredGroupCause : BN.DeclarationGroupRef s -> IssueCause s.
Arguments OccCause {p idx s} _.
Arguments MissingMainCause {p idx s} _.
Arguments OutputCollisionCause {p idx s} _ _.
Arguments RedeclaredGroupCause {p idx s} _.

Section IssueProjections.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}.

(* the cause a row retains: a plain field read of the exact object stored at construction, not a reconstruction *)
Definition diag_cause (d : Diagnostic s) : IssueCause s :=
  match d with
  | DOcc _ _ c => OccCause c
  | DMissingMain pr => MissingMainCause pr
  | DOutputCollision pr rr => OutputCollisionCause pr rr
  | DRedeclaredGroup g _ => RedeclaredGroupCause g
  end.
Definition diag_family (d : Diagnostic s) : option Family := match d with DOcc _ f _ => Some f | _ => None end.
(* the exact related nodes a row retains: a complex mismatch's two sides, or a group's members and use contexts *)
Definition diag_related (d : Diagnostic s) : list (Index.NodeRef idx) :=
  match d with
  | DOcc _ _ (ComplexMismatch a b) => [a; b]
  | DRedeclaredGroup g ctxs => map BN.est_node (BN.dg_members g) ++ ctxs
  | _ => []
  end.
Definition diag_root (d : Diagnostic s) : IssueRoot s :=
  match d with
  | DOcc r _ _ => RootNode r
  | DMissingMain pr => RootPackage pr
  | DOutputCollision pr _ => RootPackage pr
  | DRedeclaredGroup g _ => RootGroup g
  end.
Definition bound_req (b : Boundary s) : Requirement idx := match b with BOcc _ _ q => q end.
Definition bound_family (b : Boundary s) : Family := match b with BOcc _ f _ => f end.
Definition bound_root (b : Boundary s) : IssueRoot s := match b with BOcc r _ _ => RootNode r end.

End IssueProjections.

Section IssueTable.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bp : BN.BindingPhase s}
        (fp : FactPhase bp) (pf : PackageFacts bp).

(* the semantic family of an occurrence fact: a declaration spec or short-decl statement, else its plain family *)
Definition occ_family (o : OccFact idx) : Family :=
  match o with
  | OFApp _ _ => FamApplication
  | OFType _ _ => FamTypeUse
  | OFStmt r _ => match Index.node_view r with Index.VStmt (Index.SSShort _) => FamDeclaration | _ => FamStatement end
  | OFValue r _ => match Index.node_view r with Index.VConstSpec _ | Index.VVarSpec _ | Index.VTypeSpec _ => FamDeclaration | _ => FamValue end
  end.

(* one occurrence fact yields one diagnostic exactly when its family outcome is invalid, retaining that exact cause *)
Definition occ_diag_rows (o : OccFact idx) : list (Diagnostic s) :=
  let fam := occ_family o in
  match o with
  | OFValue r (VInvalid c) => [DOcc r fam c]
  | OFApp r (AInvalid c) => [DOcc r fam c]
  | OFStmt r (SInvalid c) => [DOcc r fam c]
  | OFType r (TInvalid c) => [DOcc r fam c]
  | _ => []
  end.
(* one occurrence fact yields one boundary exactly when its family outcome is unmet; invalid and unmet coexist (§6) *)
Definition occ_bound_rows (o : OccFact idx) : list (Boundary s) :=
  let fam := occ_family o in
  match o with
  | OFValue r (VUnmet q) => [BOcc r fam q]
  | OFApp r (AUnmet q) => [BOcc r fam q]
  | OFStmt r (SUnmet q) => [BOcc r fam q]
  | OFType r (TUnmet q) => [BOcc r fam q]
  | _ => []
  end.

(* the sole selected package's default-output collision, retaining the exact colliding root entry *)
Definition collision_rows : list (Diagnostic s) :=
  match preflight pf with FreshOk => [] | FreshCollision pr rr => [DOutputCollision pr rr] end.
(* a package with no fixed main is a missing-executable-entry diagnostic; multiple mains are a group redeclaration *)
Definition main_rows : list (Diagnostic s) :=
  flat_map (fun pr => match BN.package_main bp pr with BN.MainMissing => [DMissingMain pr] | _ => [] end) (BN.PI.packages s).

(* redeclaration: 2+ decl ests (spec or func) share one scope+spelling; short-lhs excluded, main included *)
Definition group_redeclared (e : BN.Est s) : bool :=
  andb (BN.is_decl_est e)
    (andb (match BN.group_status (BN.decl_group bp e) with Some (BN.GRedeclared _ _ _) => true | _ => false end)
          (match BN.decl_group bp e with m :: _ => BN.est_eqb m e | [] => false end)).

(* two group refs are the same group iff they share the exact scope and spelling that key the declaration group *)
Definition same_groupref (a b : BN.DeclarationGroupRef s) : bool :=
  andb (BN.scope_eqb (BN.dg_scope a) (BN.dg_scope b)) (Names.ordinary_equalb (BN.dg_name a) (BN.dg_name b)).
(* every package-member name occurrence: the use sites a redeclared group can contextualize *)
Definition name_uses : list (Index.NodeRef idx) :=
  filter (fun r => match Index.node_view r with Index.VName _ => true | _ => false end)
         (flat_map Index.file_nodes (flat_map BN.PI.pkg_members (BN.PI.packages s))).
(* the exact use-site contexts of a redeclared group: name occurrences resolving to it as an ambiguous group *)
Definition group_use_contexts (g : BN.DeclarationGroupRef s) : list (Index.NodeRef idx) :=
  filter (fun r => match Index.node_view r with
                   | Index.VName n => match BN.resolve bp r n with BN.RRedeclared g' => same_groupref g' g | _ => false end
                   | _ => false end) name_uses.
(* one redeclared-group diagnostic per group, keyed at its first declaration member, with its exact use contexts *)
Definition group_rows : list (Diagnostic s) :=
  flat_map (fun e => if group_redeclared e
                     then [DRedeclaredGroup (BN.decl_group_ref bp e) (group_use_contexts (BN.decl_group_ref bp e))]
                     else []) (BN.bp_ests bp).

Definition occ_diags : list (Diagnostic s) := flat_map occ_diag_rows (fact_list fp).

(* the canonical order: output collision, package main, ordinary redeclaration, then occurrence in fact-list order *)
Definition diagnostics : list (Diagnostic s) := collision_rows ++ main_rows ++ group_rows ++ occ_diags.
Definition boundaries : list (Boundary s) := flat_map occ_bound_rows (fact_list fp).

(* one fact yields a diagnostic XOR a boundary; distinct-family facts of one subject still coexist across facts (§6) *)
Lemma occ_row_exclusive (o : OccFact idx) : occ_diag_rows o <> [] -> occ_bound_rows o = [].
Proof.
  destruct o as [r ov | r oa | r os | r ot];
    [ destruct ov | destruct oa | destruct os | destruct ot ];
    cbn; intro H; solve [ reflexivity | exfalso; exact (H eq_refl) ].
Qed.

End IssueTable.

Arguments diagnostics {p idx s bp} fp pf.
Arguments boundaries {p idx s bp} fp.

Section IssueLaws.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}.

(* the root algebra is total: every diagnostic roots at an exact node, package, or group, never a self-fallback *)
Lemma root_algebra_total (d : Diagnostic s) :
  (exists r, diag_root d = RootNode r) \/ (exists pr, diag_root d = RootPackage pr) \/ (exists g, diag_root d = RootGroup g).
Proof. destruct d; cbn; eauto 6. Qed.

End IssueLaws.

(* §6 the complete disposition algebra + applicability before judgment *)
Inductive Disposition {p} {idx : Index.ProgramIndex p} (s : BN.PI.PackageSurface idx) : Type :=
| DSucceeded : Disposition s
| DAbsent : Disposition s
| DInvalid : IssueCause s -> list (IssueCause s) -> Disposition s
| DUnsupported : Requirement idx -> list (Requirement idx) -> Disposition s
| DInvalidAndUnsupported : IssueCause s -> list (IssueCause s) -> Requirement idx -> list (Requirement idx) -> Disposition s.
Arguments DSucceeded {p idx s}. Arguments DAbsent {p idx s}.
Arguments DInvalid {p idx s} _ _. Arguments DUnsupported {p idx s} _ _.
Arguments DInvalidAndUnsupported {p idx s} _ _ _ _.

(* NotApplicable is not a disposition: a generic lookup returns it or an exact applicability witness plus fact *)
Inductive FamilyResult {p} {idx : Index.ProgramIndex p} (s : BN.PI.PackageSurface idx) : Type :=
| NotApplicable : FamilyResult s
| Applicable : Disposition s -> FamilyResult s.
Arguments NotApplicable {p idx s}. Arguments Applicable {p idx s} _.

Section DispositionAlgebra.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bp : BN.BindingPhase s}
        (fp : FactPhase bp) (pf : PackageFacts bp).

Definition occ_disp_v {r : Index.NodeRef idx} (o : ValueOutcome r) : Disposition s :=
  match o with VOK _ => DSucceeded | VNonconst => DAbsent | VInvalid c => DInvalid (OccCause c) nil | VUnmet q => DUnsupported q nil end.
Definition occ_disp_a {r : Index.NodeRef idx} (o : AppOutcome r) : Disposition s :=
  match o with AOK _ => DSucceeded | AInvalid c => DInvalid (OccCause c) nil | AUnmet q => DUnsupported q nil end.
Definition occ_disp_s {r : Index.NodeRef idx} (o : StmtOutcome r) : Disposition s :=
  match o with SOK => DSucceeded | SInvalid c => DInvalid (OccCause c) nil | SUnmet q => DUnsupported q nil end.
Definition occ_disp_t {r : Index.NodeRef idx} (o : TypeUseOutcome r) : Disposition s :=
  match o with TOK _ => DSucceeded | TInvalid c => DInvalid (OccCause c) nil | TUnmet q => DUnsupported q nil end.

(* applicability-first: a family applies by role/view, then computes its outcome; else NotApplicable, no fact *)
Definition family_lookup (r : Index.NodeRef idx) (f : Family) : FamilyResult s :=
  let ctab := const_table bp (Index.nr_file r) in
  match f with
  | FamValue => match Index.node_view r with Index.VName _ | Index.VLiteral _ | Index.VUnary _ | Index.VApplication => Applicable (occ_disp_v (own_value bp ctab r)) | _ => NotApplicable end
  | FamApplication => match Index.node_view r with Index.VApplication => Applicable (occ_disp_a (own_app bp r)) | _ => NotApplicable end
  | FamStatement => match Index.node_view r with Index.VStmt Index.SSExpr => Applicable (occ_disp_s (own_stmt bp ctab r)) | _ => NotApplicable end
  | FamTypeUse => match Index.node_view r with Index.VTypeExpr _ => Applicable (occ_disp_t (own_type bp r)) | _ => NotApplicable end
  | FamDeclaration => match Index.node_view r with
                      | Index.VConstSpec _ | Index.VVarSpec _ | Index.VTypeSpec _ => Applicable (occ_disp_v (own_value bp ctab r))
                      | Index.VStmt (Index.SSShort _) => Applicable (occ_disp_s (own_stmt bp ctab r))
                      | _ => NotApplicable
                      end
  end.

(* the whole-program disposition aggregates the one canonical issue table into the complete 5-way algebra *)
Definition program_disposition : Disposition s :=
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

(* applicability: the value family does not apply to a statement occurrence — NotApplicable, never a fact *)
Lemma value_not_applicable_to_statement (r : Index.NodeRef idx) (st : Index.StmtShape) :
  Index.node_view r = Index.VStmt st -> family_lookup r FamValue = NotApplicable.
Proof. intro H; unfold family_lookup; rewrite H; reflexivity. Qed.

End DispositionAlgebra.

(* §11 structural progress + cost: every construction is structural recursion over finite maps, no fuel or budget *)
Section Cost.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} (bp : BN.BindingPhase s).

(* one structural pass: each node contributes the facts of its applicable families via a single flat_map, no fuel *)
Lemma fact_phase_one_pass : fact_list (facts bp) = raw_facts bp.
Proof. unfold fact_list, facts; cbn [proj1_sig]. reflexivity. Qed.

End Cost.

(* the canonical issue lists and 5-way summary as projections of the one retained result, for downstream readers *)
Definition result_diagnostics {p} (r : Result p) : list (Diagnostic (res_surface r)) :=
  diagnostics (res_facts r) (res_pkg r).
Definition result_boundaries {p} (r : Result p) : list (Boundary (res_surface r)) :=
  boundaries (res_facts r).
Definition result_disposition {p} (r : Result p) : Disposition (res_surface r) :=
  program_disposition (res_facts r) (res_pkg r).

