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
| ConstMissingInit : Cause idx
| ResultCountMismatch : nat -> nat -> Cause idx
| ShortDuplicate : Names.OrdinaryIdentifier -> Cause idx.
Arguments InvalidIdentity {p idx} _. Arguments UnresolvedName {p idx} _ _.
Arguments TypeAsValue {p idx} _. Arguments NotAType {p idx} _.
Arguments NotCallable {p idx} _. Arguments NotCallableExpr {p idx} _.
Arguments ConversionArity {p idx} _ _. Arguments ComplexArity {p idx} _.
Arguments ComplexMismatch {p idx} _ _. Arguments UnaryMismatch {p idx} _.
Arguments ConversionOverflow {p idx} _ _. Arguments ConversionNotRepresentable {p idx} _ _.
Arguments DefaultOverflow {p idx} _. Arguments NoValueUsed {p idx}. Arguments IllegalStatement {p idx}.
Arguments ConstMissingInit {p idx}. Arguments ResultCountMismatch {p idx} _ _. Arguments ShortDuplicate {p idx} _.

Inductive Requirement {p} (idx : Index.ProgramIndex p) : Type :=
| ReqValueMeaning : BN.BinderRef idx -> Requirement idx
| ReqTypeMeaning : BN.ObjectRef idx -> Requirement idx
| ReqComplexType : Index.NodeRef idx -> Requirement idx
| ReqApplication : Names.PredeclaredName -> list (Index.NodeRef idx) -> Requirement idx
| ReqMainUse : Index.MainOccurrenceRef idx -> Requirement idx
| ReqDeclMeaning : Index.NodeRef idx -> Requirement idx.
Arguments ReqDeclMeaning {p idx} _.
Arguments ReqValueMeaning {p idx} _. Arguments ReqTypeMeaning {p idx} _.
Arguments ReqComplexType {p idx} _. Arguments ReqApplication {p idx} _ _.
Arguments ReqMainUse {p idx} _.

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
Definition const_at (r : Index.NodeRef idx) : option TR.ConstantInfo :=
  mconst (const_table (Index.nr_file r)) r.

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

(* the first repeated short left-hand name of a short statement, over its ordered left-hand binders *)
Fixpoint first_short_dup (bs : list (Index.NodeRef idx)) : option Names.OrdinaryIdentifier :=
  match bs with
  | [] => None
  | b :: rest => match BN.binder_ident b with
                 | Some n => if BN.short_lhs_duplicate b n then Some n else first_short_dup rest
                 | None => first_short_dup rest
                 end
  end.

(* a const spec: a first spec omitting its initializer, or a known result-count mismatch, is an exact invalidity *)
Definition const_spec_disposition (r : Index.NodeRef idx) : ValueOutcome r :=
  match Index.node_view r with
  | Index.VConstSpec (Index.CSExplicit _) =>
      let nn := List.length (filter (fun c => match Index.node_role c with Index.RSpecName Index.ConstSpecF => true | _ => false end)
                                    (Index.node_children r)) in
      let nv := List.length (filter (fun c => match Index.node_role c with Index.RPlain => true | _ => false end)
                                    (Index.node_children r)) in
      if Nat.eqb nn nv then VUnmet (ReqDeclMeaning r) else VInvalid (ResultCountMismatch nn nv)
  | Index.VConstSpec Index.CSInherited => if BN.spec_is_first r then VInvalid ConstMissingInit else VUnmet (ReqDeclMeaning r)
  | _ => VNonconst
  end.

Definition own_value (r : Index.NodeRef idx) : ValueOutcome r :=
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
      | BN.RBound (BN.SourceObject b) => VUnmet (ReqValueMeaning b)
      | BN.RBound (BN.MainObject m) => if is_app_head r then VNonconst else VUnmet (ReqMainUse m)
      end
  | Index.VLiteral _ => fun _ =>
      match const_at r with
      | Some ci => match resolve_constant_info ci with
                   | Some rc => VOK rc
                   | None => if fold_consumed r then VNonconst else VInvalid (DefaultOverflow (TR.ci_const ci))
                   end
      | None => VNonconst
      end
  | Index.VUnary Syntax.UnaryMinus => fun Hv =>
      match const_at (Index.first_edge r (f_equal Index.requires_first_edge Hv)) with
      | Some _ =>
          match const_at r with
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
                  match const_at x with
                  | Some ci => match TR.convert_constant t ci with
                               | TR.Converted tc => VOK (TR.mk_rc t tc)
                               | TR.Overflows _ => VInvalid (ConversionOverflow t x)
                               | TR.NotForm _ => VInvalid (ConversionNotRepresentable t x)
                               end
                  | None => VNonconst
                  end
              | PMComplex, re :: im :: nil =>
                  match const_at re, const_at im with
                  | Some cre, Some cim =>
                      match complex_class cre cim with
                      | CxOk => match const_at r with
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
          | BN.RBound (BN.SourceObject b) => AInvalid (NotCallable (BN.SourceObject b))
          | BN.RBound (BN.MainObject m) => AUnmet (ReqMainUse m)
          | BN.RUnbound => AOK AppBuiltinStmt
          end
      | _ => AInvalid (NotCallableExpr hd)
      end
  | _ => fun _ => AOK AppBuiltinStmt
  end eq_refl.

(* the statement expr already owns a diagnostic or boundary: the illegal-statement judgment is dependent, not a root *)
Definition child_owns_issue (e : Index.NodeRef idx) : bool :=
  match own_value e with
  | VInvalid _ | VUnmet _ => true
  | _ => match own_app e with AInvalid _ | AUnmet _ => true | _ => false end
  end.

(* an expr-statement is illegal only when its expr is otherwise valid but not a legal statement head *)
Definition own_stmt (r : Index.NodeRef idx) : StmtOutcome r :=
  match Index.node_view r as v return Index.node_view r = v -> StmtOutcome r with
  | Index.VStmt Index.SSExpr => fun Hv =>
      let e := Index.first_edge r (f_equal Index.requires_first_edge Hv) in
      if child_owns_issue e then SOK
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
  | Index.VStmt Index.SSShort => fun _ =>
      (* a short declaration: a repeated left name is invalid; otherwise its later meaning is a boundary *)
      match first_short_dup (filter (fun c => match Index.node_role c with Index.RShortLhs => true | _ => false end)
                                    (Index.node_children r)) with
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
      | BN.RBound (BN.SourceObject b) => TUnmet (ReqTypeMeaning (BN.SourceObject b))
      | BN.RBound (BN.MainObject m) => TInvalid (NotAType (BN.MainObject m))
      | BN.RUnbound => TInvalid (UnresolvedName n r)
      end
  | _ => TOK TR.BoolForm
  end.

(* every occurrence, enumerated once through the retained surface; the let _ := bp keeps this generalized over bp *)
Definition all_index_nodes : list (Index.NodeRef idx) :=
  let _ := bp in flat_map Index.file_nodes (flat_map BN.PI.pkg_members (BN.PI.packages s)).

Lemma node_in_file_nodes (r : Index.NodeRef idx) : In r (Index.file_nodes (Index.nr_file r)).
Proof.
  pose proof (Index.nr_in r) as Hmem.
  apply Index.NodeFacts.mem_in_iff in Hmem. destruct Hmem as [c Hmt].
  apply Index.NodeFacts.elements_mapsto_iff in Hmt.
  apply SetoidList.InA_alt in Hmt. destruct Hmt as [[k v] [Heq Hk]].
  destruct Heq as [Hkey _]; cbn in Hkey.
  unfold Index.file_nodes. apply in_flat_map. exists (k, v). split; [exact Hk|].
  cbn [fst]. rewrite <- Hkey, Index.mk_noderef_self. apply in_eq.
Qed.

Lemma node_in_all (r : Index.NodeRef idx) : In r all_index_nodes.
Proof.
  unfold all_index_nodes; cbv zeta. apply in_flat_map. exists (Index.nr_file r). split.
  - apply in_flat_map. exists (BN.PI.package_of_file s (Index.nr_file r)). split.
    + apply BN.PI.packages_complete.
    + apply BN.PI.pkg_members_of_file.
  - apply node_in_file_nodes.
Qed.

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

Definition of_node {p} {idx : Index.ProgramIndex p} (o : OccFact idx) : Index.NodeRef idx :=
  match o with OFValue r _ | OFApp r _ | OFStmt r _ | OFType r _ => r end.

Section Retain.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} (bp : BN.BindingPhase s).

(* exactly the facts of the families that apply to a node, in family order; an inapplicable family yields none *)
Definition occ_facts (r : Index.NodeRef idx) : list (OccFact idx) :=
  match Index.node_view r with
  | Index.VName _ | Index.VLiteral _ | Index.VUnary _ => [OFValue r (own_value bp r)]
  | Index.VApplication => [OFApp r (own_app bp r); OFValue r (own_value bp r)]
  | Index.VStmt Index.SSExpr => [OFStmt r (own_stmt bp r)]
  | Index.VStmt Index.SSShort => [OFStmt r (own_stmt bp r)]
  | Index.VTypeExpr _ => [OFType r (own_type bp r)]
  | Index.VConstSpec _ | Index.VVarSpec _ | Index.VTypeSpec _ => [OFValue r (own_value bp r)]
  | _ => []
  end.

Definition raw_facts : list (OccFact idx) := flat_map occ_facts (all_index_nodes bp).

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
| FreshCollision : BN.PI.PackageRef s -> string -> FreshBuildDisposition s.
Arguments FreshOk {p idx s}.
Arguments FreshCollision {p idx s} _ _.

(* collision applicability is exactly OneSelected, independent of any package's main multiplicity *)
Definition raw_preflight {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}
  (bp : BN.BindingPhase s) : FreshBuildDisposition s :=
  let _ := bp in
  match BN.PI.package_selection s with
  | BN.PI.OneSelected pr =>
      match find (String.eqb (BN.PI.default_exec_name pr)) (BN.PI.root_entry_names s) with
      | Some root => FreshCollision pr root
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

(* the one canonical issue table: Analysis owns cause, class, subject, root, and source order *)

Inductive DiagSite {p} {idx : Index.ProgramIndex p} (s : BN.PI.PackageSurface idx) : Type :=
| AtOcc : OccFact idx -> DiagSite s
| AtPackage : BN.PI.PackageRef s -> DiagSite s
| AtGroup : BN.Est s -> DiagSite s.
Arguments AtOcc {p idx s} _.
Arguments AtPackage {p idx s} _.
Arguments AtGroup {p idx s} _.

Inductive IssueRoot {p} {idx : Index.ProgramIndex p} (s : BN.PI.PackageSurface idx) : Type :=
| RootNode : Index.NodeRef idx -> IssueRoot s
| RootPackage : BN.PI.PackageRef s -> IssueRoot s.
Arguments RootNode {p idx s} _.
Arguments RootPackage {p idx s} _.

Inductive IssueCause {p} {idx : Index.ProgramIndex p} (s : BN.PI.PackageSurface idx) : Type :=
| OccCause : Cause idx -> IssueCause s
| PkgMissingMain : BN.PI.PackageRef s -> IssueCause s
| PkgMainRedeclared : forall pr : BN.PI.PackageRef s,
    BN.MainDeclRef s pr -> BN.MainDeclRef s pr -> list (BN.MainDeclRef s pr) -> IssueCause s
| PkgOutputCollision : BN.PI.PackageRef s -> IssueCause s
| OrdinaryRedeclared : BN.Est s -> BN.Est s -> list (BN.Est s) -> IssueCause s.
Arguments OccCause {p idx s} _.
Arguments PkgMissingMain {p idx s} _.
Arguments PkgMainRedeclared {p idx s} _ _ _ _.
Arguments PkgOutputCollision {p idx s} _.
Arguments OrdinaryRedeclared {p idx s} _ _ _.

Section IssueTable.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bp : BN.BindingPhase s}
        (fp : FactPhase bp) (pf : PackageFacts bp).

Definition v_invalid {r : Index.NodeRef idx} (o : ValueOutcome r) : bool := match o with VInvalid _ => true | _ => false end.
Definition a_invalid {r : Index.NodeRef idx} (o : AppOutcome r) : bool := match o with AInvalid _ => true | _ => false end.
Definition s_invalid {r : Index.NodeRef idx} (o : StmtOutcome r) : bool := match o with SInvalid _ => true | _ => false end.
Definition t_invalid {r : Index.NodeRef idx} (o : TypeUseOutcome r) : bool := match o with TInvalid _ => true | _ => false end.
Definition v_unmet {r : Index.NodeRef idx} (o : ValueOutcome r) : bool := match o with VUnmet _ => true | _ => false end.
Definition a_unmet {r : Index.NodeRef idx} (o : AppOutcome r) : bool := match o with AUnmet _ => true | _ => false end.
Definition s_unmet {r : Index.NodeRef idx} (o : StmtOutcome r) : bool := match o with SUnmet _ => true | _ => false end.
Definition t_unmet {r : Index.NodeRef idx} (o : TypeUseOutcome r) : bool := match o with TUnmet _ => true | _ => false end.

Definition occ_diag (o : OccFact idx) : bool :=
  match o with OFValue _ ov => v_invalid ov | OFApp _ oa => a_invalid oa | OFStmt _ os => s_invalid os | OFType _ ot => t_invalid ot end.
(* a boundary is an unmet family outcome; no diagnostic-suppresses-boundary rule, so invalid and unmet coexist (§6) *)
Definition occ_bound (o : OccFact idx) : bool :=
  match o with OFValue _ ov => v_unmet ov | OFApp _ oa => a_unmet oa | OFStmt _ os => s_unmet os | OFType _ ot => t_unmet ot end.

Definition pkg_main_issue (pr : BN.PI.PackageRef s) : bool :=
  match BN.package_main bp pr with BN.MainMissing => true | BN.MainMultiple _ _ _ => true | _ => false end.
Definition collision_list : list (BN.PI.PackageRef s) :=
  match preflight pf with FreshOk => [] | FreshCollision pr _ => [pr] end.
Definition pkg_collides (pr : BN.PI.PackageRef s) : bool := existsb (BN.PI.packageref_eqb pr) collision_list.

(* ordinary redeclaration: 2+ const/var/type spec ests share one scope and spelling (short repeats and main excluded) *)
Definition is_spec_est (e : BN.Est s) : bool :=
  match Index.node_role (BN.binder_node (BN.est_binder e)) with Index.RSpecName _ => true | _ => false end.
Definition spec_group (e : BN.Est s) : list (BN.Est s) := filter is_spec_est (BN.group_members bp e).
Definition group_redeclared (e : BN.Est s) : bool :=
  andb (is_spec_est e)
    (andb (match BN.group_status (spec_group e) with Some (BN.GRedeclared _ _ _) => true | _ => false end)
          (match spec_group e with m :: _ => BN.est_eqb m e | [] => false end)).

Definition produces_diag (site : DiagSite s) : bool :=
  let _ := fp in
  match site with
  | AtOcc o => occ_diag o
  | AtPackage pr => pkg_main_issue pr || pkg_collides pr
  | AtGroup e => group_redeclared e
  end.
Definition produces_bound (o : OccFact idx) : bool := let _ := fp in let _ := pf in occ_bound o.

Record Diagnostic := diag_at { diag_site : DiagSite s ; diag_ok : produces_diag diag_site = true }.
Record Boundary := bound_at { bound_fact : OccFact idx ; bound_ok : produces_bound bound_fact = true }.

(* the exact cause of a producing occurrence fact, no invented fallback: the produces proof discharges non-invalid *)
Definition occ_cause (o : OccFact idx) (H : occ_diag o = true) : Cause idx.
Proof.
  destruct o as [r ov | r oa | r os | r ot]; cbn in H.
  - destruct ov; cbn in H; solve [ discriminate H | assumption ].
  - destruct oa; cbn in H; solve [ discriminate H | assumption ].
  - destruct os; cbn in H; solve [ discriminate H | assumption ].
  - destruct ot; cbn in H; solve [ discriminate H | assumption ].
Defined.
Definition occ_req (o : OccFact idx) (H : produces_bound o = true) : Requirement idx.
Proof.
  assert (Hb : occ_bound o = true) by exact H.
  destruct o as [r ov | r oa | r os | r ot]; cbn in Hb.
  - destruct ov; cbn in Hb; solve [ discriminate Hb | assumption ].
  - destruct oa; cbn in Hb; solve [ discriminate Hb | assumption ].
  - destruct os; cbn in Hb; solve [ discriminate Hb | assumption ].
  - destruct ot; cbn in Hb; solve [ discriminate Hb | assumption ].
Defined.

Definition pkg_cause (pr : BN.PI.PackageRef s) : IssueCause s :=
  match BN.package_main bp pr with
  | BN.MainMissing => PkgMissingMain pr
  | BN.MainMultiple m1 m2 rest => PkgMainRedeclared pr m1 m2 rest
  | BN.MainOne _ => PkgOutputCollision pr
  end.

(* the exact redeclared spec establishments of a group; the produces proof discharges the unique/none cases *)
Definition group_cause (e : BN.Est s) (H : group_redeclared e = true) : IssueCause s.
Proof.
  unfold group_redeclared in H.
  apply andb_prop in H as [_ H]; apply andb_prop in H as [Hstat _].
  destruct (BN.group_status (spec_group e)) as [gs|] eqn:E; [| discriminate Hstat].
  destruct gs as [m | a b rest]; [ discriminate Hstat | exact (OrdinaryRedeclared a b rest) ].
Defined.

Definition diag_cause (d : Diagnostic) : IssueCause s :=
  (match diag_site d as st return produces_diag st = true -> IssueCause s with
   | AtOcc o => fun H => OccCause (occ_cause o H)
   | AtPackage pr => fun _ => pkg_cause pr
   | AtGroup e => fun H => group_cause e H
   end) (diag_ok d).

Definition occ_related (o : OccFact idx) : list (Index.NodeRef idx) :=
  match o with OFValue _ (VInvalid (ComplexMismatch a b)) => [a; b] | _ => [] end.
Definition diag_related (d : Diagnostic) : list (Index.NodeRef idx) :=
  match diag_site d with
  | AtOcc o => occ_related o
  | AtPackage pr =>
      match BN.package_main bp pr with
      | BN.MainMultiple m1 m2 rest => map BN.main_node (m1 :: m2 :: rest)
      | _ => []
      end
  | AtGroup e => map (fun m => BN.binder_node (BN.est_binder m)) (spec_group e)
  end.
Definition diag_root (d : Diagnostic) : IssueRoot s :=
  match diag_site d with
  | AtOcc o => RootNode (of_node o)
  | AtPackage pr => RootPackage pr
  | AtGroup e => RootNode (BN.binder_node (BN.est_binder e))
  end.

Definition bound_req (b : Boundary) : Requirement idx := occ_req (bound_fact b) (bound_ok b).
Definition bound_root (b : Boundary) : IssueRoot s := RootNode (of_node (bound_fact b)).

Fixpoint build_diags (sites : list (DiagSite s))
  : (forall d, In d sites -> produces_diag d = true) -> list Diagnostic :=
  match sites with
  | [] => fun _ => []
  | site :: rest => fun H =>
      diag_at site (H site (or_introl eq_refl)) :: build_diags rest (fun d Hd => H d (or_intror Hd))
  end.
Fixpoint build_bounds (os : list (OccFact idx))
  : (forall o, In o os -> produces_bound o = true) -> list Boundary :=
  match os with
  | [] => fun _ => []
  | o :: rest => fun H =>
      bound_at o (H o (or_introl eq_refl)) :: build_bounds rest (fun o' Ho' => H o' (or_intror Ho'))
  end.

Lemma filter_diag_ok : forall (sites : list (DiagSite s)) d,
  In d (filter produces_diag sites) -> produces_diag d = true.
Proof. intros sites d Hin; apply filter_In in Hin; exact (proj2 Hin). Qed.
Lemma filter_bound_ok : forall (os : list (OccFact idx)) o,
  In o (filter produces_bound os) -> produces_bound o = true.
Proof. intros os o Hin; apply filter_In in Hin; exact (proj2 Hin). Qed.

(* the canonical order: fresh-output collision, then package main, then occurrence in fact-list order *)
Definition collision_diags : list Diagnostic :=
  build_diags (filter produces_diag (map AtPackage collision_list)) (filter_diag_ok _).
Definition main_diags : list Diagnostic :=
  build_diags (filter produces_diag (map AtPackage (filter pkg_main_issue (BN.PI.packages s)))) (filter_diag_ok _).
Definition redecl_diags : list Diagnostic :=
  build_diags (filter produces_diag (map AtGroup (BN.bp_ests bp))) (filter_diag_ok _).
Definition occ_diags : list Diagnostic :=
  build_diags (filter produces_diag (map AtOcc (fact_list fp))) (filter_diag_ok _).

Definition diagnostics : list Diagnostic := collision_diags ++ main_diags ++ redecl_diags ++ occ_diags.
Definition boundaries : list Boundary :=
  build_bounds (filter produces_bound (fact_list fp)) (filter_bound_ok _).

End IssueTable.

Arguments Diagnostic {p idx s bp} fp pf.
Arguments Boundary {p idx s bp} fp pf.

Section IssueLaws.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bp : BN.BindingPhase s}
        (fp : FactPhase bp) (pf : PackageFacts bp).

(* a diagnostic stores only its site plus a producing proof; the proof is irrelevant *)
Lemma report_projection_only (d1 d2 : Diagnostic fp pf) :
  diag_site fp pf d1 = diag_site fp pf d2 -> d1 = d2.
Proof. destruct d1 as [a Ha], d2 as [b Hb]; cbn; intro E; subst b; f_equal; apply (UIP_dec Bool.bool_dec). Qed.

(* the root algebra is total: every diagnostic roots at a node or a package, never a self-fallback *)
Lemma root_algebra_total (d : Diagnostic fp pf) :
  (exists r, diag_root fp pf d = RootNode r) \/ (exists pr, diag_root fp pf d = RootPackage pr).
Proof. unfold diag_root; destruct (diag_site fp pf d); eauto. Qed.

(* the diagnostic order: preflight collision, package main, ordinary redeclaration, then occurrence *)
Lemma precedence_total :
  diagnostics fp pf = collision_diags fp pf ++ main_diags fp pf ++ redecl_diags fp pf ++ occ_diags fp pf.
Proof. reflexivity. Qed.

(* one fact carries one outcome: a diagnostic XOR a boundary; distinct family facts of a subject still coexist *)
Lemma occ_diag_bound_exclusive (o : OccFact idx) :
  occ_diag o = true -> occ_bound o = false.
Proof.
  destruct o as [r ov | r oa | r os | r ot]; cbn;
    [ destruct ov | destruct oa | destruct os | destruct ot ];
    intro H; solve [ reflexivity | discriminate H ].
Qed.

End IssueLaws.

(* §6 the complete disposition algebra + applicability before judgment *)
Inductive Family : Type := FamValue | FamApplication | FamStatement | FamTypeUse | FamDeclaration.

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
  match f with
  | FamValue => match Index.node_view r with Index.VName _ | Index.VLiteral _ | Index.VUnary _ | Index.VApplication => Applicable (occ_disp_v (own_value bp r)) | _ => NotApplicable end
  | FamApplication => match Index.node_view r with Index.VApplication => Applicable (occ_disp_a (own_app bp r)) | _ => NotApplicable end
  | FamStatement => match Index.node_view r with Index.VStmt Index.SSExpr => Applicable (occ_disp_s (own_stmt bp r)) | _ => NotApplicable end
  | FamTypeUse => match Index.node_view r with Index.VTypeExpr _ => Applicable (occ_disp_t (own_type bp r)) | _ => NotApplicable end
  | FamDeclaration => match Index.node_view r with
                      | Index.VConstSpec _ | Index.VVarSpec _ | Index.VTypeSpec _ => Applicable (occ_disp_v (own_value bp r))
                      | Index.VStmt Index.SSShort => Applicable (occ_disp_s (own_stmt bp r))
                      | _ => NotApplicable
                      end
  end.

(* the whole-program disposition aggregates the one canonical issue table into the complete 5-way algebra *)
Definition program_disposition : Disposition s :=
  match diagnostics fp pf, boundaries fp pf with
  | nil, nil => DSucceeded
  | d :: ds, nil => DInvalid (diag_cause fp pf d) (map (diag_cause fp pf) ds)
  | nil, b :: bs => DUnsupported (bound_req fp pf b) (map (bound_req fp pf) bs)
  | d :: ds, b :: bs => DInvalidAndUnsupported (diag_cause fp pf d) (map (diag_cause fp pf) ds)
                                               (bound_req fp pf b) (map (bound_req fp pf) bs)
  end.

(* success is exactly empty reports; a rejected program with simultaneous boundaries is InvalidAndUnsupported *)
Lemma program_disposition_succeeded :
  program_disposition = DSucceeded <-> diagnostics fp pf = nil /\ boundaries fp pf = nil.
Proof.
  unfold program_disposition; destruct (diagnostics fp pf) as [|d ds], (boundaries fp pf) as [|b bs]; cbn.
  - split; intros _; [ split; reflexivity | reflexivity ].
  - split; [ discriminate | intros [_ H2]; discriminate H2 ].
  - split; [ discriminate | intros [H1 _]; discriminate H1 ].
  - split; [ discriminate | intros [H1 _]; discriminate H1 ].
Qed.

Lemma program_disposition_both :
  (exists d ds b bs c1 c2 q1 q2, diagnostics fp pf = d :: ds /\ boundaries fp pf = b :: bs
     /\ program_disposition = DInvalidAndUnsupported c1 c2 q1 q2) \/
  program_disposition = DSucceeded \/
  (exists c cs, program_disposition = DInvalid c cs) \/
  (exists q qs, program_disposition = DUnsupported q qs).
Proof.
  unfold program_disposition; destruct (diagnostics fp pf) as [|d ds] eqn:Ed, (boundaries fp pf) as [|b bs] eqn:Eb.
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
Definition result_diagnostics {p} (r : Result p) : list (Diagnostic (res_facts r) (res_pkg r)) :=
  diagnostics (res_facts r) (res_pkg r).
Definition result_boundaries {p} (r : Result p) : list (Boundary (res_facts r) (res_pkg r)) :=
  boundaries (res_facts r) (res_pkg r).
Definition result_disposition {p} (r : Result p) : Disposition (res_surface r) :=
  program_disposition (res_facts r) (res_pkg r).

