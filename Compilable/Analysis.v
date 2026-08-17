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
| ReqDeclMeaning : Index.NodeRef idx -> Requirement idx.
Arguments ReqDeclMeaning {p idx} _.
Arguments ReqValueMeaning {p idx} _. Arguments ReqTypeMeaning {p idx} _.
Arguments ReqComplexType {p idx} _. Arguments ReqApplication {p idx} _ _.

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

(* fold an expression to a constant info, resolving each name at the enclosing use position *)
Fixpoint constant_info (use : Index.NodeRef idx) (e : Syntax.Expr) : option TR.ConstantInfo :=
  match e with
  | Syntax.Name n =>
      match nm_at use n with Some (TR.NMValueConstant c) => Some (TR.mk_cinfo c TR.Untyped) | _ => None end
  | Syntax.LiteralExpr (Syntax.IntegerLiteral k) => Some (TR.mk_cinfo (TR.CInt (Z.of_N k)) TR.Untyped)
  | Syntax.LiteralExpr (Syntax.FloatLiteral d) => Some (TR.mk_cinfo (TR.CFloat (Float.nnd_value d)) TR.Untyped)
  | Syntax.LiteralExpr (Syntax.StringLiteral str) => Some (TR.mk_cinfo (TR.CString str) TR.Untyped)
  | Syntax.Unary Syntax.UnaryMinus e' =>
      match constant_info use e' with
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
  | Syntax.Application (Syntax.Name h) (x :: nil) =>
      match nm_at use h with
      | Some (TR.NMConversionForm t) =>
          match constant_info use x with
          | Some ci => match TR.convert_constant t ci with
                       | TR.Converted tc => Some (TR.mk_cinfo (TR.typed_exact tc) (TR.ExplicitlyTyped t))
                       | _ => None
                       end
          | None => None
          end
      | _ => None
      end
  | Syntax.Application (Syntax.Name h) (re :: im :: nil) =>
      match BN.resolve bp use h with
      | BN.RBound (BN.PredeclaredObject Names.PComplex) =>
          match constant_info use re, constant_info use im with
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

Definition is_arg_role (r : Index.Role) : bool := match r with Index.RApplicationArg _ => true | _ => false end.
Definition app_arg_nodes (r : Index.NodeRef idx) : list (Index.NodeRef idx) :=
  filter (fun c => is_arg_role (Index.node_role c)) (Index.node_children r).
Definition is_head_role (r : Index.Role) : bool := match r with Index.RApplicationHead => true | _ => false end.
Definition app_head_node (r : Index.NodeRef idx) : Index.NodeRef idx :=
  match filter (fun c => is_head_role (Index.node_role c)) (Index.node_children r) with h :: _ => h | [] => r end.
Definition arg0 (r : Index.NodeRef idx) : Index.NodeRef idx :=
  match app_arg_nodes r with a :: _ => a | [] => r end.
Definition arg1 (r : Index.NodeRef idx) : Index.NodeRef idx :=
  match app_arg_nodes r with _ :: b :: _ => b | _ => r end.

(* role decides value-use: an application head is a callee, not a value; expr-statement exprs go to own_stmt *)
Definition is_app_head (r : Index.NodeRef idx) : bool :=
  match Index.node_role r with Index.RApplicationHead => true | _ => false end.
Definition value_ctx (r : Index.NodeRef idx) : bool :=
  match Index.node_role r with Index.RApplicationHead => false | Index.RExprStatementExpr => false | _ => true end.

(* a conversion/complex head folds its argument, so a folded value's default-int type is never forced *)
Definition head_folds (par : Index.NodeRef idx) : bool :=
  match Index.node_view par with
  | Index.VExpr (Syntax.Application (Syntax.Name h) _) =>
      match BN.resolve bp par h with
      | BN.RBound (BN.PredeclaredObject pn) =>
          match pmeaning pn with PMConvForm _ => true | PMComplex => true | _ => false end
      | _ => false
      end
  | _ => false
  end.
Definition fold_consumed (r : Index.NodeRef idx) : bool :=
  match Index.node_role r with
  | Index.RUnaryOperand => true
  | Index.RApplicationArg _ => match Index.node_parent r with Some par => head_folds par | None => false end
  | _ => false
  end.

(* a declaration occurrence is the first spec of its enclosing declaration when it heads its parent's children *)
Definition is_first_of_parent (r : Index.NodeRef idx) : bool :=
  match Index.node_parent r with
  | Some par => match Index.node_children par with c :: _ => Nat.eqb (Index.nr_pos c) (Index.nr_pos r) | [] => true end
  | None => true
  end.

(* a short left-hand name repeated earlier in the same short statement is an exact duplicate invalidity *)
Definition is_short_duplicate (r : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) : bool :=
  match Index.node_parent r with
  | Some stmt =>
      existsb (fun c => andb (Nat.ltb (Index.nr_pos c) (Index.nr_pos r))
                             (match BN.binder_ident c with Some m => Names.ordinary_equalb m n | None => false end))
              (filter (fun c => match Index.node_role c with Index.RShortLhs => true | _ => false end)
                      (Index.node_children stmt))
  | None => false
  end.

(* the first repeated short left-hand name of a short statement, over its ordered left-hand binders *)
Fixpoint first_short_dup (bs : list (Index.NodeRef idx)) : option Names.OrdinaryIdentifier :=
  match bs with
  | [] => None
  | b :: rest => match BN.binder_ident b with
                 | Some n => if is_short_duplicate b n then Some n else first_short_dup rest
                 | None => first_short_dup rest
                 end
  end.

(* a const spec: a first spec omitting its initializer, or a known result-count mismatch, is an exact invalidity *)
Definition const_spec_disposition (r : Index.NodeRef idx) (cs : Syntax.ConstSpec) : ValueOutcome r :=
  match Syntax.const_init cs with
  | Syntax.ExplicitConstInit _ vals =>
      let nn := List.length (Collections.ne_to_list (Syntax.const_names cs)) in
      let nv := List.length (Collections.ne_to_list vals) in
      if Nat.eqb nn nv then VUnmet (ReqDeclMeaning r) else VInvalid (ResultCountMismatch nn nv)
  | Syntax.InheritedConstInit => if is_first_of_parent r then VInvalid ConstMissingInit else VUnmet (ReqDeclMeaning r)
  end.

Definition own_value (r : Index.NodeRef idx) : ValueOutcome r :=
  match Index.node_view r with
  | Index.VExpr (Syntax.Name n) =>
      match BN.resolve bp r n with
      | BN.RUnbound => VInvalid (UnresolvedName n r)
      | BN.RBound (BN.PredeclaredObject pn) =>
          match pmeaning pn with
          | PMValue c => match TR.default_constant c with Some rc => VOK rc | None => VInvalid (InvalidIdentity pn) end
          | PMInvalidId => VInvalid (InvalidIdentity pn)
          | _ => if is_app_head r then VNonconst else VInvalid (TypeAsValue (BN.PredeclaredObject pn))
          end
      | BN.RBound (BN.SourceObject b) => VUnmet (ReqValueMeaning b)
      end
  | Index.VExpr (Syntax.LiteralExpr l) =>
      match constant_info r (Syntax.LiteralExpr l) with
      | Some ci => match resolve_constant_info ci with
                   | Some rc => VOK rc
                   | None => if fold_consumed r then VNonconst else VInvalid (DefaultOverflow (TR.ci_const ci))
                   end
      | None => VNonconst
      end
  | Index.VExpr (Syntax.Unary Syntax.UnaryMinus e') =>
      match constant_info r e' with
      | Some _ =>
          match constant_info r (Syntax.Unary Syntax.UnaryMinus e') with
          | Some ci => match resolve_constant_info ci with
                       | Some rc => VOK rc
                       | None => if fold_consumed r then VNonconst else VInvalid (DefaultOverflow (TR.ci_const ci))
                       end
          | None => VInvalid (UnaryMismatch (arg0 r))
          end
      | None => VNonconst
      end
  | Index.VExpr (Syntax.Application (Syntax.Name h) args) =>
      match BN.resolve bp r h with
      | BN.RBound (BN.PredeclaredObject pn) =>
          match pmeaning pn, args with
          | PMConvForm t, x :: nil =>
              match constant_info r x with
              | Some ci => match TR.convert_constant t ci with
                           | TR.Converted tc => VOK (TR.mk_rc t tc)
                           | TR.Overflows _ => VInvalid (ConversionOverflow t (arg0 r))
                           | TR.NotForm _ => VInvalid (ConversionNotRepresentable t (arg0 r))
                           end
              | None => VNonconst
              end
          | PMComplex, re :: im :: nil =>
              match constant_info r re, constant_info r im with
              | Some cre, Some cim =>
                  match complex_class cre cim with
                  | CxOk => match constant_info r (Syntax.Application (Syntax.Name h) (re :: im :: nil)) with
                            | Some ci => match resolve_constant_info ci with Some rc => VOK rc | None => VNonconst end
                            | None => VNonconst end
                  | CxDefer => VUnmet (ReqComplexType r)
                  | CxError => VInvalid (ComplexMismatch (arg0 r) (arg1 r))
                  end
              | _, _ => VNonconst
              end
          | PMPrintln, _ => if value_ctx r then VInvalid NoValueUsed else VNonconst
          | _, _ => VNonconst
          end
      | _ => VNonconst
      end
  (* declaration outcomes live on the declaration subject (spec / short statement), never on the binder *)
  | Index.VConstSpec cs => const_spec_disposition r cs
  | Index.VVarSpec _ => VUnmet (ReqDeclMeaning r)
  | Index.VTypeSpec _ => VUnmet (ReqDeclMeaning r)
  | _ => VNonconst
  end.

Definition own_app (r : Index.NodeRef idx) : AppOutcome r :=
  match Index.node_view r with
  | Index.VExpr (Syntax.Application head args) =>
      match head with
      | Syntax.Name h =>
          match BN.resolve bp r h with
          | BN.RBound (BN.PredeclaredObject pn) =>
              match pmeaning pn with
              | PMConvForm _ => match args with _ :: nil => AOK (AppBuiltinStmt) | _ => AInvalid (ConversionArity pn (Datatypes.length args)) end
              | PMComplex =>
                  match args with
                  | re :: im :: nil =>
                      match constant_info r re, constant_info r im with
                      | Some cre, Some cim =>
                          match complex_class cre cim with
                          | CxOk => AOK AppBuiltinStmt
                          | CxDefer => AUnmet (ReqComplexType r)
                          | CxError => AInvalid (ComplexMismatch (arg0 r) (arg1 r))
                          end
                      | _, _ => AOK AppBuiltinStmt
                      end
                  | _ => AInvalid (ComplexArity (Datatypes.length args))
                  end
              | PMPrintln => AOK AppBuiltinStmt
              | PMValue _ => AInvalid (NotCallable (BN.PredeclaredObject pn))
              | PMInvalidId => AOK AppBuiltinStmt
              | PMUnmodelled => AUnmet (ReqApplication pn (app_arg_nodes r))
              end
          | BN.RBound (BN.SourceObject b) => AInvalid (NotCallable (BN.SourceObject b))
          | BN.RUnbound => AOK AppBuiltinStmt
          end
      | _ => AInvalid (NotCallableExpr (app_head_node r))
      end
  | _ => AOK AppBuiltinStmt
  end.

Definition is_exprstmt_role (r : Index.Role) : bool :=
  match r with Index.RExprStatementExpr => true | _ => false end.
Definition stmt_expr_node (r : Index.NodeRef idx) : Index.NodeRef idx :=
  match filter (fun c => is_exprstmt_role (Index.node_role c)) (Index.node_children r) with e :: _ => e | [] => r end.

(* the statement expr already owns a diagnostic or boundary: the illegal-statement judgment is dependent, not a root *)
Definition child_owns_issue (e : Index.NodeRef idx) : bool :=
  match own_value e with
  | VInvalid _ | VUnmet _ => true
  | _ => match own_app e with AInvalid _ | AUnmet _ => true | _ => false end
  end.

(* an expr-statement is illegal only when its expr is otherwise valid but not a legal statement head *)
Definition own_stmt (r : Index.NodeRef idx) : StmtOutcome r :=
  match Index.node_view r with
  | Index.VStmt (Syntax.ExprStmt e) =>
      if child_owns_issue (stmt_expr_node r) then SOK
      else match e with
           | Syntax.Application (Syntax.Name h) _ =>
               match BN.resolve bp r h with
               | BN.RBound (BN.PredeclaredObject Names.PPrintln) => SOK
               | BN.RUnbound => SOK
               | BN.RBound (BN.SourceObject _) => SOK
               | _ => SInvalid IllegalStatement
               end
           | _ => SInvalid IllegalStatement
           end
  | Index.VStmt (Syntax.ShortVarDecl _ _) =>
      (* a short declaration: a repeated left name is invalid; otherwise its later meaning is a boundary *)
      match first_short_dup (filter (fun c => match Index.node_role c with Index.RShortLhs => true | _ => false end)
                                    (Index.node_children r)) with
      | Some n => SInvalid (ShortDuplicate n)
      | None => SUnmet (ReqDeclMeaning r)
      end
  | _ => SOK
  end.

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

(* the retained fact phase: each occurrence classified once, then projected as a read, never reclassified *)

Record NodeFacts {p} {idx : Index.ProgramIndex p} : Type := mkNF {
  nf_node : Index.NodeRef idx ;
  nf_v : ValueOutcome nf_node ;
  nf_a : AppOutcome nf_node ;
  nf_s : StmtOutcome nf_node ;
  nf_t : TypeUseOutcome nf_node
}.
Arguments NodeFacts {p} idx.
Arguments mkNF {p idx} _ _ _ _ _.
Arguments nf_node {p idx} _.
Arguments nf_v {p idx} _. Arguments nf_a {p idx} _. Arguments nf_s {p idx} _. Arguments nf_t {p idx} _.

Section Retain.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} (bp : BN.BindingPhase s).

(* one classification per node: each family is its own independent per-node judgment, no cross-node blocking *)
Definition build_nf (r : Index.NodeRef idx) : NodeFacts idx :=
  mkNF r (own_value bp r) (own_app bp r) (own_stmt bp r) (own_type bp r).

Definition raw_facts : list (NodeFacts idx) := map build_nf (all_index_nodes bp).

(* every retained fact is its node's canonical build_nf, so Report reads it in place, never reclassifying *)
Lemma fact_list_build (m : NodeFacts idx) :
  In m (map build_nf (all_index_nodes bp)) -> m = build_nf (nf_node m).
Proof.
  intro Hin. apply in_map_iff in Hin. destruct Hin as [x [Heq _]].
  assert (Hn : nf_node m = x) by (rewrite <- Heq; reflexivity).
  rewrite Hn, Heq. reflexivity.
Qed.

Definition FactPhase : Type := { m : list (NodeFacts idx) | m = raw_facts }.
Definition facts : FactPhase := exist _ raw_facts eq_refl.
Definition fact_list (fp : FactPhase) : list (NodeFacts idx) := proj1_sig fp.

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

(* iota and nil in a governed value context are invalid identities *)
Lemma iota_nil_contextual (r : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) (pn : Names.PredeclaredName) :
  Index.node_view r = Index.VExpr (Syntax.Name n) ->
  BN.resolve bp r n = BN.RBound (BN.PredeclaredObject pn) ->
  pmeaning pn = PMInvalidId ->
  own_value bp r = VInvalid (InvalidIdentity pn).
Proof.
  intros Hv Hres Hpm; unfold own_value; rewrite Hv; cbv beta iota; rewrite Hres; cbv beta iota; rewrite Hpm; reflexivity.
Qed.

(* a source-object value use is an unmet later-root requirement *)
Lemma source_value_outside (r : Index.NodeRef idx) (n : Names.OrdinaryIdentifier) (b : BN.BinderRef idx) :
  Index.node_view r = Index.VExpr (Syntax.Name n) ->
  BN.resolve bp r n = BN.RBound (BN.SourceObject b) ->
  own_value bp r = VUnmet (ReqValueMeaning b).
Proof.
  intros Hv Hres; unfold own_value; rewrite Hv; cbv beta iota; rewrite Hres; reflexivity.
Qed.

(* an untyped nested complex with a non-real component is a complex mismatch naming both argument sites *)
Lemma nested_complex_zero_imag (r : Index.NodeRef idx) (h : Names.OrdinaryIdentifier) (re im : Syntax.Expr)
      (cre cim : TR.ConstantInfo) :
  Index.node_view r = Index.VExpr (Syntax.Application (Syntax.Name h) (re :: im :: nil)) ->
  BN.resolve bp r h = BN.RBound (BN.PredeclaredObject Names.PComplex) ->
  constant_info bp r re = Some cre -> constant_info bp r im = Some cim ->
  complex_class cre cim = CxError ->
  own_value bp r = VInvalid (ComplexMismatch (arg0 r) (arg1 r)).
Proof.
  intros Hv Hres Hre Him Hcx; unfold own_value; rewrite Hv; cbv beta iota; rewrite Hres; cbv beta iota;
    change (pmeaning Names.PComplex) with PMComplex; cbv beta iota;
    rewrite Hre, Him; cbv beta iota; rewrite Hcx; reflexivity.
Qed.

(* a typed complex requiring later identity meaning is unmet, with no diagnostic *)
Lemma typed_complex_outside (r : Index.NodeRef idx) (h : Names.OrdinaryIdentifier) (re im : Syntax.Expr)
      (cre cim : TR.ConstantInfo) :
  Index.node_view r = Index.VExpr (Syntax.Application (Syntax.Name h) (re :: im :: nil)) ->
  BN.resolve bp r h = BN.RBound (BN.PredeclaredObject Names.PComplex) ->
  constant_info bp r re = Some cre -> constant_info bp r im = Some cim ->
  complex_class cre cim = CxDefer ->
  own_value bp r = VUnmet (ReqComplexType r).
Proof.
  intros Hv Hres Hre Him Hcx; unfold own_value; rewrite Hv; cbv beta iota; rewrite Hres; cbv beta iota;
    change (pmeaning Names.PComplex) with PMComplex; cbv beta iota;
    rewrite Hre, Him; cbv beta iota; rewrite Hcx; reflexivity.
Qed.

(* a valid but unmodelled callable is an unmet application requirement *)
Lemma unmodelled_callable (r : Index.NodeRef idx) (h : Names.OrdinaryIdentifier) (args : list Syntax.Expr)
      (pn : Names.PredeclaredName) :
  Index.node_view r = Index.VExpr (Syntax.Application (Syntax.Name h) args) ->
  BN.resolve bp r h = BN.RBound (BN.PredeclaredObject pn) ->
  pmeaning pn = PMUnmodelled ->
  own_app bp r = AUnmet (ReqApplication pn (app_arg_nodes r)).
Proof.
  intros Hv Hres Hpm; unfold own_app; rewrite Hv; cbv beta iota; rewrite Hres; cbv beta iota; rewrite Hpm; reflexivity.
Qed.

End Laws.

(* the fresh-build preflight: default output name from the import path; collision only for the one selected package *)
Local Open Scope string_scope.

Definition ascii_is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in andb (Nat.leb 48 n) (Nat.leb n 57).
Fixpoint str_all_digits (s : string) : bool :=
  match s with EmptyString => true | String c s' => andb (ascii_is_digit c) (str_all_digits s') end.
Definition is_version_element (s : string) : bool :=
  match s with
  | String c0 (String c1 rest) =>
      andb (Ascii.eqb c0 "v"%char)
        (andb (negb (Ascii.eqb c1 "0"%char))
          (andb (negb (andb (Ascii.eqb c1 "1"%char)
                            (match rest with EmptyString => true | _ => false end)))
                (str_all_digits (String c1 rest))))
  | _ => false
  end.
Definition default_exec_name_c (comps : list string) : string :=
  match comps with
  | _ :: _ :: _ =>
      let final := List.last comps ""%string in
      if is_version_element final then List.last (List.removelast comps) ""%string else final
  | _ => List.last comps ""%string
  end.

Inductive FreshBuildDisposition {p} {idx : Index.ProgramIndex p} (s : BN.PI.PackageSurface idx) : Type :=
| FreshOk : FreshBuildDisposition s
| FreshCollision : BN.PI.PackageRef s -> string -> FreshBuildDisposition s.
Arguments FreshOk {p idx s}.
Arguments FreshCollision {p idx s} _ _.

Definition exec_name_of {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}
  (pr : BN.PI.PackageRef s) : string := default_exec_name_c (FilePath.pkg_components (BN.PI.pkg_dir pr)).

Definition first_dir_component {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}
  (pr : BN.PI.PackageRef s) : option string :=
  match FilePath.pkg_components (BN.PI.pkg_dir pr) with c :: _ => Some c | [] => None end.
Definition root_dir_names {p} {idx : Index.ProgramIndex p} (s : BN.PI.PackageSurface idx) : list string :=
  fold_right (fun pr acc => match first_dir_component pr with Some c => c :: acc | None => acc end) [] (BN.PI.packages s).

(* collision applicability is exactly OneSelected, independent of any package's main multiplicity *)
Definition raw_preflight {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx}
  (bp : BN.BindingPhase s) : FreshBuildDisposition s :=
  let _ := bp in
  match BN.PI.package_selection s with
  | BN.PI.OneSelected pr =>
      match find (String.eqb (exec_name_of pr)) (root_dir_names s) with
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

Local Close Scope string_scope.

(* the one canonical issue table: Analysis owns cause, class, subject, root, and source order *)

Inductive DiagSite {p} {idx : Index.ProgramIndex p} (s : BN.PI.PackageSurface idx) : Type :=
| AtOcc : NodeFacts idx -> DiagSite s
| AtPackage : BN.PI.PackageRef s -> DiagSite s.
Arguments AtOcc {p idx s} _.
Arguments AtPackage {p idx s} _.

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
| PkgOutputCollision : BN.PI.PackageRef s -> IssueCause s.
Arguments OccCause {p idx s} _.
Arguments PkgMissingMain {p idx s} _.
Arguments PkgMainRedeclared {p idx s} _ _ _ _.
Arguments PkgOutputCollision {p idx s} _.

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

Definition facts_diag (nf : NodeFacts idx) : bool :=
  v_invalid (nf_v nf) || a_invalid (nf_a nf) || s_invalid (nf_s nf) || t_invalid (nf_t nf).
Definition facts_bound (nf : NodeFacts idx) : bool :=
  negb (facts_diag nf) && (v_unmet (nf_v nf) || a_unmet (nf_a nf) || s_unmet (nf_s nf) || t_unmet (nf_t nf)).

Definition pkg_main_issue (pr : BN.PI.PackageRef s) : bool :=
  match BN.package_main bp pr with BN.MainMissing => true | BN.MainMultiple _ _ _ => true | _ => false end.
Definition collision_list : list (BN.PI.PackageRef s) :=
  match preflight pf with FreshOk => [] | FreshCollision pr _ => [pr] end.
Definition pkg_collides (pr : BN.PI.PackageRef s) : bool := existsb (BN.PI.packageref_eqb pr) collision_list.

Definition produces_diag (site : DiagSite s) : bool :=
  let _ := fp in
  match site with
  | AtOcc nf => facts_diag nf
  | AtPackage pr => pkg_main_issue pr || pkg_collides pr
  end.
Definition produces_bound (nf : NodeFacts idx) : bool := let _ := fp in let _ := pf in facts_bound nf.

Record Diagnostic := diag_at { diag_site : DiagSite s ; diag_ok : produces_diag diag_site = true }.
Record Boundary := bound_at { bound_facts : NodeFacts idx ; bound_ok : produces_bound bound_facts = true }.

(* the exact cause of a producing occurrence, no invented fallback: the produces proof discharges all-valid *)
Definition occ_cause (nf : NodeFacts idx) (H : facts_diag nf = true) : Cause idx.
Proof.
  unfold facts_diag in H.
  destruct (nf_v nf); try assumption; cbn in H; try discriminate H;
  destruct (nf_a nf); try assumption; cbn in H; try discriminate H;
  destruct (nf_s nf); try assumption; cbn in H; try discriminate H;
  destruct (nf_t nf); try assumption; cbn in H; discriminate H.
Defined.
Definition occ_req (nf : NodeFacts idx) (H : produces_bound nf = true) : Requirement idx.
Proof.
  assert (Hu : (v_unmet (nf_v nf) || a_unmet (nf_a nf) || s_unmet (nf_s nf) || t_unmet (nf_t nf)) = true).
  { assert (Hb : facts_bound nf = true) by exact H. unfold facts_bound in Hb.
    apply andb_prop in Hb; exact (proj2 Hb). }
  destruct (nf_v nf); try assumption; cbn in Hu;
  destruct (nf_a nf); try assumption; cbn in Hu;
  destruct (nf_s nf); try assumption; cbn in Hu;
  destruct (nf_t nf); try assumption; cbn in Hu; discriminate Hu.
Defined.

Definition pkg_cause (pr : BN.PI.PackageRef s) : IssueCause s :=
  match BN.package_main bp pr with
  | BN.MainMissing => PkgMissingMain pr
  | BN.MainMultiple m1 m2 rest => PkgMainRedeclared pr m1 m2 rest
  | BN.MainOne _ => PkgOutputCollision pr
  end.

Definition diag_cause (d : Diagnostic) : IssueCause s :=
  (match diag_site d as st return produces_diag st = true -> IssueCause s with
   | AtOcc nf => fun H => OccCause (occ_cause nf H)
   | AtPackage pr => fun _ => pkg_cause pr
   end) (diag_ok d).

Definition facts_related (nf : NodeFacts idx) : list (Index.NodeRef idx) :=
  match nf_v nf with VInvalid (ComplexMismatch a b) => [a; b] | _ => [] end.
Definition diag_related (d : Diagnostic) : list (Index.NodeRef idx) :=
  match diag_site d with
  | AtOcc nf => facts_related nf
  | AtPackage pr =>
      match BN.package_main bp pr with
      | BN.MainMultiple m1 m2 rest => map BN.main_node (m1 :: m2 :: rest)
      | _ => []
      end
  end.
Definition diag_root (d : Diagnostic) : IssueRoot s :=
  match diag_site d with AtOcc nf => RootNode (nf_node nf) | AtPackage pr => RootPackage pr end.

Definition bound_req (b : Boundary) : Requirement idx := occ_req (bound_facts b) (bound_ok b).
Definition bound_root (b : Boundary) : IssueRoot s := RootNode (nf_node (bound_facts b)).

Fixpoint build_diags (sites : list (DiagSite s))
  : (forall d, In d sites -> produces_diag d = true) -> list Diagnostic :=
  match sites with
  | [] => fun _ => []
  | site :: rest => fun H =>
      diag_at site (H site (or_introl eq_refl)) :: build_diags rest (fun d Hd => H d (or_intror Hd))
  end.
Fixpoint build_bounds (nfs : list (NodeFacts idx))
  : (forall nf, In nf nfs -> produces_bound nf = true) -> list Boundary :=
  match nfs with
  | [] => fun _ => []
  | nf :: rest => fun H =>
      bound_at nf (H nf (or_introl eq_refl)) :: build_bounds rest (fun nf' Hnf' => H nf' (or_intror Hnf'))
  end.

Lemma filter_diag_ok : forall (sites : list (DiagSite s)) d,
  In d (filter produces_diag sites) -> produces_diag d = true.
Proof. intros sites d Hin; apply filter_In in Hin; exact (proj2 Hin). Qed.
Lemma filter_bound_ok : forall (nfs : list (NodeFacts idx)) nf,
  In nf (filter produces_bound nfs) -> produces_bound nf = true.
Proof. intros nfs nf Hin; apply filter_In in Hin; exact (proj2 Hin). Qed.

(* the canonical order: fresh-output collision, then package main, then occurrence in fact-list order *)
Definition collision_diags : list Diagnostic :=
  build_diags (filter produces_diag (map AtPackage collision_list)) (filter_diag_ok _).
Definition main_diags : list Diagnostic :=
  build_diags (filter produces_diag (map AtPackage (filter pkg_main_issue (BN.PI.packages s)))) (filter_diag_ok _).
Definition occ_diags : list Diagnostic :=
  build_diags (filter produces_diag (map AtOcc (fact_list fp))) (filter_diag_ok _).

Definition diagnostics : list Diagnostic := collision_diags ++ main_diags ++ occ_diags.
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

(* the diagnostic order is preflight collision, then package main, then occurrence *)
Lemma precedence_total :
  diagnostics fp pf = collision_diags fp pf ++ main_diags fp pf ++ occ_diags fp pf.
Proof. reflexivity. Qed.

(* a node that produces a diagnostic produces no boundary (the boundary gate negates the diagnostic bit) *)
Lemma decided_invalid_no_boundary (nf : NodeFacts idx) :
  facts_diag nf = true -> produces_bound fp pf nf = false.
Proof. unfold produces_bound, facts_bound; intro H; rewrite H; reflexivity. Qed.

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

(* an occurrence family applies by role/view, then reads its exact retained outcome as a disposition *)
Definition family_lookup (nf : NodeFacts idx) (f : Family) : FamilyResult s :=
  let r := nf_node nf in
  match f with
  | FamValue => match Index.node_view r with Index.VExpr _ => Applicable (occ_disp_v (nf_v nf)) | _ => NotApplicable end
  | FamApplication => match Index.node_view r with Index.VExpr (Syntax.Application _ _) => Applicable (occ_disp_a (nf_a nf)) | _ => NotApplicable end
  | FamStatement => match Index.node_view r with Index.VStmt (Syntax.ExprStmt _) => Applicable (occ_disp_s (nf_s nf)) | _ => NotApplicable end
  | FamTypeUse => match Index.node_view r with Index.VTypeExpr _ => Applicable (occ_disp_t (nf_t nf)) | _ => NotApplicable end
  | FamDeclaration => match Index.node_view r with
                      | Index.VConstSpec _ | Index.VVarSpec _ | Index.VTypeSpec _ => Applicable (occ_disp_v (nf_v nf))
                      | Index.VStmt (Syntax.ShortVarDecl _ _) => Applicable (occ_disp_s (nf_s nf))
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
Lemma value_not_applicable_to_statement (nf : NodeFacts idx) (st : Syntax.Stmt) :
  Index.node_view (nf_node nf) = Index.VStmt st -> family_lookup nf FamValue = NotApplicable.
Proof. intro H; unfold family_lookup; rewrite H; reflexivity. Qed.

End DispositionAlgebra.

(* §11 structural progress + cost: every construction is structural recursion over finite maps, no fuel or budget *)
Section Cost.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} (bp : BN.BindingPhase s).

(* the fact phase is exactly one row per indexed occurrence: a single pass over N, never a re-scan *)
Lemma fact_phase_one_pass : List.length (fact_list (facts bp)) = List.length (all_index_nodes bp).
Proof. unfold fact_list, facts, raw_facts; cbn [proj1_sig]. apply List.length_map. Qed.

End Cost.

