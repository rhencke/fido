(* Facts — one site-indexed classification phase: value, application, statement, and type-use outcomes over
   the retained binding phase, with contextual builtin policy, exact conversion mapping, and strict-descendant
   blocking.  Report only projects from this. *)

From Stdlib Require Import List Bool String ZArith NArith Lia.
From Fido Require Import Names Integer Float Complex Syntax Index Compilable.TypeResolution Compilable.Bindings.
Import ListNotations.

Module TR := Compilable.TypeResolution.
Module BN := Compilable.Bindings.

(* ---- payload algebras ---- *)

Inductive Cause {p} (idx : Index.ProgramIndex p) : Type :=
| InvalidIdentity : Names.PredeclaredName -> Cause idx
| UnresolvedName : Names.OrdinaryIdentifier -> Index.NodeRef idx -> Cause idx
| TypeAsValue : BN.ObjectRef idx -> Cause idx
| NotCallable : BN.ObjectRef idx -> Cause idx
| ConversionArity : Names.PredeclaredName -> nat -> Cause idx
| ComplexArity : nat -> Cause idx
| ComplexMismatch : Index.NodeRef idx -> Index.NodeRef idx -> Cause idx
| UnaryMismatch : Index.NodeRef idx -> Cause idx
| ConversionOverflow : TR.TypeForm -> Index.NodeRef idx -> Cause idx
| ConversionNotRepresentable : TR.TypeForm -> Index.NodeRef idx -> Cause idx
| DefaultOverflow : TR.Constant -> Cause idx
| NoValueUsed : Cause idx
| IllegalStatement : Cause idx.
Arguments InvalidIdentity {p idx} _. Arguments UnresolvedName {p idx} _ _.
Arguments TypeAsValue {p idx} _. Arguments NotCallable {p idx} _.
Arguments ConversionArity {p idx} _ _. Arguments ComplexArity {p idx} _.
Arguments ComplexMismatch {p idx} _ _. Arguments UnaryMismatch {p idx} _.
Arguments ConversionOverflow {p idx} _ _. Arguments ConversionNotRepresentable {p idx} _ _.
Arguments DefaultOverflow {p idx} _. Arguments NoValueUsed {p idx}. Arguments IllegalStatement {p idx}.

Inductive Requirement {p} (idx : Index.ProgramIndex p) : Type :=
| ReqValueMeaning : BN.BinderRef idx -> Requirement idx
| ReqTypeMeaning : BN.ObjectRef idx -> Requirement idx
| ReqComplexType : Index.NodeRef idx -> Requirement idx
| ReqApplication : Names.PredeclaredName -> list (Index.NodeRef idx) -> Requirement idx.
Arguments ReqValueMeaning {p idx} _. Arguments ReqTypeMeaning {p idx} _.
Arguments ReqComplexType {p idx} _. Arguments ReqApplication {p idx} _ _.

Record BlockWitness {p} {idx : Index.ProgramIndex p} (blocked : Index.NodeRef idx) : Type := block_witness {
  bw_root : Index.NodeRef idx ;
  bw_desc : Index.strict_descendant blocked bw_root
}.
Arguments block_witness {p idx blocked} _ _.
Arguments bw_root {p idx blocked} _.
Arguments bw_desc {p idx blocked} _.

Inductive AppResult : Type :=
| AppValue : TR.ResolvedConstant -> AppResult
| AppBuiltinStmt : AppResult.

Inductive ValueOutcome {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) : Type :=
| VOK : TR.ResolvedConstant -> ValueOutcome site
| VNonconst : ValueOutcome site
| VInvalid : Cause idx -> ValueOutcome site
| VUnmet : Requirement idx -> ValueOutcome site
| VBlocked : BlockWitness site -> ValueOutcome site.
Arguments VOK {p idx site} _. Arguments VNonconst {p idx site}.
Arguments VInvalid {p idx site} _. Arguments VUnmet {p idx site} _. Arguments VBlocked {p idx site} _.

Inductive AppOutcome {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) : Type :=
| AOK : AppResult -> AppOutcome site
| AInvalid : Cause idx -> AppOutcome site
| AUnmet : Requirement idx -> AppOutcome site
| ABlocked : BlockWitness site -> AppOutcome site.
Arguments AOK {p idx site} _. Arguments AInvalid {p idx site} _.
Arguments AUnmet {p idx site} _. Arguments ABlocked {p idx site} _.

Inductive StmtOutcome {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) : Type :=
| SOK : StmtOutcome site
| SInvalid : Cause idx -> StmtOutcome site
| SUnmet : Requirement idx -> StmtOutcome site
| SBlocked : BlockWitness site -> StmtOutcome site.
Arguments SOK {p idx site}. Arguments SInvalid {p idx site} _.
Arguments SUnmet {p idx site} _. Arguments SBlocked {p idx site} _.

Inductive TypeUseOutcome {p} {idx : Index.ProgramIndex p} (site : Index.NodeRef idx) : Type :=
| TOK : TR.TypeForm -> TypeUseOutcome site
| TInvalid : Cause idx -> TypeUseOutcome site
| TUnmet : Requirement idx -> TypeUseOutcome site
| TBlocked : BlockWitness site -> TypeUseOutcome site.
Arguments TOK {p idx site} _. Arguments TInvalid {p idx site} _.
Arguments TUnmet {p idx site} _. Arguments TBlocked {p idx site} _.

(* ---- contextual predeclared meaning and the constant-folding resolver ---- *)

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

(* ---- argument-occurrence navigation ---- *)

Definition is_arg_role (r : Index.Role) : bool := match r with Index.RApplicationArg _ => true | _ => false end.
Definition app_arg_nodes (r : Index.NodeRef idx) : list (Index.NodeRef idx) :=
  filter (fun c => is_arg_role (Index.node_role c)) (Index.node_children r).
Definition arg0 (r : Index.NodeRef idx) : Index.NodeRef idx :=
  match app_arg_nodes r with a :: _ => a | [] => r end.
Definition arg1 (r : Index.NodeRef idx) : Index.NodeRef idx :=
  match app_arg_nodes r with _ :: b :: _ => b | _ => r end.

(* ---- per-site classification, before blocking ---- *)

(* an occurrence's role decides whether it is a value use at all: an application HEAD is a callee, never a
   value, and the discarded expression of an expression statement is governed by own_stmt, not by a value
   diagnostic.  A predeclared conversion/complex/println/unmodelled name is [TypeAsValue] only in a real value
   use, and a void builtin call ([println]) has no value only where one is consumed. *)
Definition is_app_head (r : Index.NodeRef idx) : bool :=
  match Index.node_role r with Index.RApplicationHead => true | _ => false end.
Definition value_ctx (r : Index.NodeRef idx) : bool :=
  match Index.node_role r with Index.RApplicationHead => false | Index.RExprStatementExpr => false | _ => true end.

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
      | Some ci => match resolve_constant_info ci with Some rc => VOK rc | None => VNonconst end
      | None => VNonconst
      end
  | Index.VExpr (Syntax.Unary Syntax.UnaryMinus e') =>
      match constant_info r e' with
      | Some _ =>
          match constant_info r (Syntax.Unary Syntax.UnaryMinus e') with
          | Some ci => match resolve_constant_info ci with Some rc => VOK rc | None => VNonconst end
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
  | _ => VNonconst
  end.

Definition own_app (r : Index.NodeRef idx) : AppOutcome r :=
  match Index.node_view r with
  | Index.VExpr (Syntax.Application (Syntax.Name h) args) =>
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
  | Index.VExpr (Syntax.Application (Syntax.LiteralExpr _) _) => AInvalid (NotCallable (BN.PredeclaredObject Names.PNil))
  | _ => AOK AppBuiltinStmt
  end.

Definition own_stmt (r : Index.NodeRef idx) : StmtOutcome r :=
  match Index.node_view r with
  | Index.VStmt (Syntax.ExprStmt (Syntax.Application (Syntax.Name h) _)) =>
      match BN.resolve bp r h with
      | BN.RBound (BN.PredeclaredObject Names.PPrintln) => SOK
      | BN.RUnbound => SOK
      | BN.RBound (BN.SourceObject _) => SOK
      | _ => SInvalid IllegalStatement
      end
  | Index.VStmt (Syntax.ExprStmt _) => SInvalid IllegalStatement
  | _ => SOK
  end.

Definition own_type (r : Index.NodeRef idx) : TypeUseOutcome r := TOK TR.BoolForm.

(* ---- strict-descendant blocking ---- *)

Definition value_fails (r : Index.NodeRef idx) : bool :=
  match own_value r with VInvalid _ => true | VUnmet _ => true | _ => false end.

Definition strict_descendant_b (a b : Index.NodeRef idx) : bool :=
  andb (Index.fileref_eqb (Index.nr_file a) (Index.nr_file b))
  (andb (Nat.ltb (Index.nr_pos a) (Index.nr_pos b)) (Nat.leb (Index.nr_pos b) (Index.node_extent a))).

Lemma strict_descendant_b_spec : forall a b, strict_descendant_b a b = true -> Index.strict_descendant a b.
Proof.
  intros a b H. unfold strict_descendant_b in H.
  apply andb_prop in H as [Hf H]. apply andb_prop in H as [Hlt Hle].
  split; [ apply Index.fileref_eqb_spec; exact Hf
         | split; [ apply Nat.ltb_lt; exact Hlt | apply Nat.leb_le; exact Hle ] ].
Qed.

(* every occurrence, enumerated once through the retained surface (the [let _ := bp] keeps this generalized
   over [bp] like the rest of the phase, so the whole phase shares one argument shape) *)
Definition all_index_nodes : list (Index.NodeRef idx) :=
  let _ := bp in flat_map Index.file_nodes (flat_map BN.PI.pkg_members (BN.PI.packages s)).

Lemma node_in_file_nodes (r : Index.NodeRef idx) : In r (Index.file_nodes (Index.nr_file r)).
Proof.
  unfold Index.file_nodes. apply in_flat_map. exists (Index.nr_pos r). split.
  - apply in_seq; split; [ lia | exact (Index.nr_lt r) ].
  - unfold Index.mk_noderef.
    destruct (Bool.bool_dec (Nat.ltb (Index.nr_pos r) (Index.occ_count (Index.nr_file r))) true) as [E|E].
    + left; apply Index.noderef_positional; reflexivity.
    + exfalso; apply E; apply Nat.ltb_lt; exact (Index.nr_lt r).
Qed.

Lemma node_in_all (r : Index.NodeRef idx) : In r all_index_nodes.
Proof.
  unfold all_index_nodes. apply in_flat_map. exists (Index.nr_file r). split.
  - apply in_flat_map. exists (BN.PI.package_of_file s (Index.nr_file r)). split.
    + apply BN.PI.packages_complete.
    + apply BN.PI.pkg_members_exact; symmetry; apply BN.PI.package_of_file_total.
  - apply node_in_file_nodes.
Qed.

(* the own-value validity of every occurrence, computed ONCE (the expensive classification is not repeated per
   candidate the way a per-node file rescan would); blocking then only folds these cached bits *)
Definition dfails : list (Index.NodeRef idx * bool) :=
  map (fun d => (d, value_fails d)) all_index_nodes.

Definition find_failing_in (df : list (Index.NodeRef idx * bool)) (r : Index.NodeRef idx) : option (BlockWitness r) :=
  fold_right (fun (p : Index.NodeRef idx * bool) (acc : option (BlockWitness r)) =>
    if snd p then
      match Bool.bool_dec (strict_descendant_b r (fst p)) true with
      | left H => Some (block_witness (fst p) (strict_descendant_b_spec r (fst p) H))
      | right _ => acc
      end
    else acc) None df.

Definition find_failing (r : Index.NodeRef idx) : option (BlockWitness r) := find_failing_in dfails r.

Lemma find_failing_witness : forall r w,
  find_failing r = Some w -> Index.strict_descendant r (bw_root w) /\ value_fails (bw_root w) = true.
Proof.
  intros r w. unfold find_failing, find_failing_in, dfails.
  induction all_index_nodes as [|d rest IH]; cbn [map fold_right fst snd].
  - discriminate.
  - destruct (value_fails d) eqn:Hvf.
    + destruct (Bool.bool_dec (strict_descendant_b r d) true) as [H|H].
      * intro E; injection E as <-; cbn. split; [ apply strict_descendant_b_spec; exact H | exact Hvf ].
      * exact IH.
    + exact IH.
Qed.

Definition value_fact_c (r : Index.NodeRef idx) : ValueOutcome r :=
  match find_failing r with Some w => VBlocked w | None => own_value r end.
Definition app_fact_c (r : Index.NodeRef idx) : AppOutcome r :=
  match find_failing r with Some w => ABlocked w | None => own_app r end.
Definition stmt_fact_c (r : Index.NodeRef idx) : StmtOutcome r :=
  match find_failing r with Some w => SBlocked w | None => own_stmt r end.
Definition type_fact_c (r : Index.NodeRef idx) : TypeUseOutcome r :=
  match find_failing r with Some w => TBlocked w | None => own_type r end.

End OverPhase.

(* ---- the retained fact phase: each occurrence classified ONCE over one enumeration, then projected ----
   [value_fact_c] above is the classifying SPEC; [FactPhase] retains the result so every projection is a read,
   never a reclassification (blocking's [find_failing] is evaluated once per node, not once per family). *)

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

(* one classification per node: blocking folds the SHARED validity cache [df], and all four families are read
   from the single [find_failing_in] result — the expensive own-value classification is never recomputed per
   candidate.  [raw_facts] binds the cache once with [let], so [vm_compute] shares it across every node. *)
Definition build_nf (df : list (Index.NodeRef idx * bool)) (r : Index.NodeRef idx) : NodeFacts idx :=
  match find_failing_in df r with
  | Some w => mkNF r (VBlocked w) (ABlocked w) (SBlocked w) (TBlocked w)
  | None   => mkNF r (own_value bp r) (own_app bp r) (own_stmt bp r) (own_type r)
  end.

Lemma build_nf_eq (r : Index.NodeRef idx) :
  build_nf (dfails bp) r = mkNF r (value_fact_c bp r) (app_fact_c bp r) (stmt_fact_c bp r) (type_fact_c bp r).
Proof.
  unfold build_nf, value_fact_c, app_fact_c, stmt_fact_c, type_fact_c, find_failing.
  destruct (find_failing_in (dfails bp) r); reflexivity.
Qed.

Definition raw_facts : list (NodeFacts idx) :=
  let df := dfails bp in map (build_nf df) (all_index_nodes bp).

(* a blocked node's retained facts are all Blocked in every family, so Report (folding [fact_list] directly)
   emits neither a diagnostic nor a boundary for it — no [lookup4]/[eq_rect] transport is ever needed. *)
Lemma build_nf_blocked (r : Index.NodeRef idx) (w : BlockWitness r) :
  find_failing bp r = Some w ->
  build_nf (dfails bp) r = mkNF r (VBlocked w) (ABlocked w) (SBlocked w) (TBlocked w).
Proof. intro H. unfold build_nf, find_failing in *. rewrite H. reflexivity. Qed.

(* every retained fact is exactly its node's canonical classification: [nf] in the stream is the [build_nf] of
   its own node, so Report reads [nf_v]/[nf_a]/[nf_s]/[nf_t] in place — a projection, never a reclassification. *)
Lemma fact_list_build (m : NodeFacts idx) :
  In m (map (build_nf (dfails bp)) (all_index_nodes bp)) ->
  m = build_nf (dfails bp) (nf_node m).
Proof.
  intro Hin. apply in_map_iff in Hin. destruct Hin as [x [Heq _]].
  assert (Hn : nf_node m = x).
  { rewrite <- Heq. unfold build_nf. destruct (find_failing_in (dfails bp) x); reflexivity. }
  rewrite Hn, Heq. reflexivity.
Qed.

Definition FactPhase : Type := { m : list (NodeFacts idx) | m = raw_facts }.
Definition facts : FactPhase := exist _ raw_facts eq_refl.
Definition fact_list (fp : FactPhase) : list (NodeFacts idx) := proj1_sig fp.

End Retain.

Arguments FactPhase {p idx s} bp.
Arguments facts {p idx s} bp.
Arguments fact_list {p idx s bp} _.

(* ---- laws ---- *)

Section Laws.
Context {p : Syntax.Program} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} (bp : BN.BindingPhase s).

(* the phase content is built once; every phase carries exactly the canonical classification, none caller-supplied *)
Lemma fact_once (fp : FactPhase bp) : fact_list fp = raw_facts bp.
Proof. exact (proj2_sig fp). Qed.

(* statement and type-use families have no Nonconst constructor *)
Lemma only_lawful_per_family (r : Index.NodeRef idx) :
  (forall o : StmtOutcome r, o = SOK \/ (exists c, o = SInvalid c) \/ (exists q, o = SUnmet q) \/ (exists w, o = SBlocked w))
  /\ (forall o : TypeUseOutcome r, (exists f, o = TOK f) \/ (exists c, o = TInvalid c) \/ (exists q, o = TUnmet q) \/ (exists w, o = TBlocked w)).
Proof. split; intro o; destruct o; eauto 7. Qed.

(* a blocked site points down to a strict descendant, so blocking follows the well-founded strict descent *)
Lemma block_terminating (r : Index.NodeRef idx) (w : BlockWitness r) :
  find_failing bp r = Some w -> Index.strict_descendant r (bw_root w).
Proof. intro H; exact (proj1 (find_failing_witness bp r w H)). Qed.

(* the descendant a block points to really is invalid or unmet *)
Lemma block_root_real (r : Index.NodeRef idx) (w : BlockWitness r) :
  find_failing bp r = Some w -> value_fails bp (bw_root w) = true.
Proof. intro H; exact (proj2 (find_failing_witness bp r w H)). Qed.

(* no blocked self-edge: the block root is strictly deeper than the blocked site *)
Lemma block_no_overlap (r : Index.NodeRef idx) (w : BlockWitness r) :
  find_failing bp r = Some w -> r <> bw_root w.
Proof.
  intro H. destruct (proj1 (find_failing_witness bp r w H)) as [_ [Hlt _]].
  intro Heq; pose proof (f_equal Index.nr_pos Heq) as Hp; lia.
Qed.

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

