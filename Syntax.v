From Stdlib Require Import NArith List String.
From Stdlib Require Import Permutation SetoidList.
From Fido Require Import FilePath Collections ModulePath Version Float Names.
Import ListNotations.

(* A binding position names an ordinary identifier or is blank; blank establishes no object. *)
Inductive BindingName : Type :=
| BNamed : Names.OrdinaryIdentifier -> BindingName
| BBlank : BindingName.

Inductive UnaryOp : Type := UnaryMinus.

(* Numeric source literals are magnitudes; a negative value is exactly one [Unary UnaryMinus]. *)
Inductive Literal : Type :=
| IntegerLiteral : N -> Literal
| FloatLiteral   : Float.NonNegativeDecimal -> Literal
| StringLiteral  : string -> Literal.

(* A type use names an ordinary source identifier; predeclared meaning is a later binding fact. *)
Inductive TypeExpr : Type := NamedType : Names.OrdinaryIdentifier -> TypeExpr.
Definition type_expr_ident (t : TypeExpr) : Names.OrdinaryIdentifier := match t with NamedType n => n end.

Inductive Expr : Type :=
| Name        : Names.OrdinaryIdentifier -> Expr
| LiteralExpr : Literal -> Expr
| Unary       : UnaryOp -> Expr -> Expr
| Application : Expr -> list Expr -> Expr.

(* The default [Expr] recursor is too weak under the nested [list]; this carries a [Forall] over arguments. *)
Fixpoint Expr_ind' (P : Expr -> Prop)
  (HName  : forall n, P (Name n))
  (HLit   : forall l, P (LiteralExpr l))
  (HUnary : forall op e, P e -> P (Unary op e))
  (HApp   : forall head args, P head -> List.Forall P args -> P (Application head args))
  (e : Expr) : P e :=
  match e with
  | Name n        => HName n
  | LiteralExpr l => HLit l
  | Unary op e'   => HUnary op e' (Expr_ind' P HName HLit HUnary HApp e')
  | Application head args =>
      HApp head args (Expr_ind' P HName HLit HUnary HApp head)
        ((fix args_ind (es : list Expr) : List.Forall P es :=
            match es with
            | nil => List.Forall_nil P
            | cons x xs =>
                List.Forall_cons x (Expr_ind' P HName HLit HUnary HApp x) (args_ind xs)
            end) args)
  end.

(* A const spec binds one or more names to an explicit initializer or inherits the preceding one. *)
Inductive ConstInitializer : Type :=
| ExplicitConstInit  : option TypeExpr -> Collections.NonEmpty Expr -> ConstInitializer
| InheritedConstInit : ConstInitializer.

Record ConstSpec : Type := MakeConstSpec {
  const_names : Collections.NonEmpty BindingName ;
  const_init  : ConstInitializer
}.

(* A var spec is a type-only declaration or one or more names bound to initializer values. *)
Inductive VarInitializer : Type :=
| VarTypeOnly : TypeExpr -> VarInitializer
| VarValues   : option TypeExpr -> Collections.NonEmpty Expr -> VarInitializer.

Record VarSpec : Type := MakeVarSpec {
  var_names : Collections.NonEmpty BindingName ;
  var_init  : VarInitializer
}.

(* A type spec is an alias or a defined type over one target type use. *)
Inductive TypeSpec : Type :=
| AliasSpec : BindingName -> TypeExpr -> TypeSpec
| DefSpec   : BindingName -> TypeExpr -> TypeSpec.

(* A declaration groups specs; the group is a list because an empty group is valid Go. *)
Inductive Declaration : Type :=
| ConstDecl : list ConstSpec -> Declaration
| VarDecl   : list VarSpec -> Declaration
| TypeDecl  : list TypeSpec -> Declaration.

(* A statement is an expression, a local declaration, or a short variable declaration. *)
Inductive Stmt : Type :=
| ExprStmt        : Expr -> Stmt
| DeclarationStmt : Declaration -> Stmt
| ShortVarDecl    : Collections.NonEmpty BindingName -> Collections.NonEmpty Expr -> Stmt.

Inductive Block : Type := MakeBlock : list Stmt -> Block.

(* The package clause as source syntax; only the canonical package main is representable. *)
Inductive PackageClause : Type := MainPackage.

(* An import spec: the type is empty, so [list ImportSpec] can only be [nil]. *)
Inductive ImportSpec : Type := .

(* A top-level declaration is a package-level declaration or the main function body. *)
Inductive TopLevelDecl : Type :=
| TopDeclaration : Declaration -> TopLevelDecl
| Main           : Block -> TopLevelDecl.

Record File : Type := MakeFile {
  package : PackageClause;
  imports : list ImportSpec;
  declarations   : list TopLevelDecl
}.

(* A construction and view value pairing a path with its source; the map key below is the path authority. *)
Record FileNode : Type := MakeFileNode {
  path   : FilePath.T;
  source : File
}.

Module FileMap := Collections.FileMap.
Module FileFacts := Collections.FileFacts.

Definition Files : Type := FileMap.t File.

Definition empty_files : Files := FileMap.empty File.
Definition find_file (p : FilePath.T) (fm : Files) : option File := FileMap.find p fm.
Definition maps_to_file (p : FilePath.T) (sf : File) (fm : Files) : Prop := FileMap.MapsTo p sf fm.
Definition file_mem (p : FilePath.T) (fm : Files) : bool := FileMap.mem p fm.
Definition file_count (fm : Files) : nat := FileMap.cardinal fm.
Definition file_bindings (fm : Files) : list (FilePath.T * File) := FileMap.elements fm.
Definition file_paths (fm : Files) : list FilePath.T := List.map fst (file_bindings fm).
Lemma file_bindings_find : forall (fm : Files) (b : FilePath.T * File),
  List.In b (file_bindings fm) -> find_file (fst b) fm = Some (snd b).
Proof.
  intros fm [k e] Hin. unfold file_bindings, find_file in *. simpl in *.
  apply FileFacts.find_mapsto_iff, FileFacts.elements_mapsto_iff, SetoidList.InA_alt.
  exists (k, e). split; [ split; reflexivity | exact Hin ].
Qed.

Lemma find_file_bindings : forall (fm : Files) k e,
  find_file k fm = Some e -> List.In (k, e) (file_bindings fm).
Proof.
  intros fm k e H. unfold file_bindings, find_file in *.
  apply FileFacts.find_mapsto_iff, FileFacts.elements_mapsto_iff, SetoidList.InA_alt in H.
  destruct H as [[k' e'] [[Hk He] Hin]]. cbn in Hk, He.
  unfold Collections.FilePathOrder.eq in Hk. subst. exact Hin.
Qed.

Lemma file_bindings_nodup_keys : forall fm, List.NoDup (List.map fst (file_bindings fm)).
Proof.
  intro fm. unfold file_bindings. pose proof (FileMap.elements_3w fm) as H.
  generalize dependent (FileMap.elements fm). clear fm. intro l.
  induction l as [|[k e] l IH]; simpl; intro H; [constructor|].
  inversion H as [|x xs Hni Hnd Heq]; subst. constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [[k' e'] [Hk Hin']]. cbn in Hk; subst k'.
    apply Hni, SetoidList.InA_alt. exists (k, e'). split; [ reflexivity | exact Hin' ].
  - apply IH; exact Hnd.
Qed.
Definition file_nodes (fm : Files) : list FileNode :=
  List.map (fun b => MakeFileNode (fst b) (snd b)) (file_bindings fm).
Definition map_file_values {B} (f : File -> B) (fm : Files) : FileMap.t B := FileMap.map f fm.
Definition FilesEqual (fm1 fm2 : Files) : Prop := FileMap.Equal fm1 fm2.

Lemma files_equal_refl : forall fm, FilesEqual fm fm.
Proof. intros fm p. reflexivity. Qed.
Lemma files_equal_sym : forall fm1 fm2, FilesEqual fm1 fm2 -> FilesEqual fm2 fm1.
Proof. intros fm1 fm2 H p. symmetry. apply H. Qed.
Lemma files_equal_trans : forall fm1 fm2 fm3, FilesEqual fm1 fm2 -> FilesEqual fm2 fm3 -> FilesEqual fm1 fm3.
Proof. intros fm1 fm2 fm3 H12 H23 p. rewrite H12. apply H23. Qed.

(* The duplicate-rejecting builder: standard [mem] then [add], rejecting a repeated path before adding. *)

Fixpoint files_of_nodes (nodes : list FileNode) : option Files :=
  match nodes with
  | [] => Some empty_files
  | n :: rest =>
      match files_of_nodes rest with
      | None => None
      | Some fm => if file_mem (path n) fm then None
                   else Some (FileMap.add (path n) (source n) fm)
      end
  end.

Lemma files_of_nodes_in : forall nodes fm,
  files_of_nodes nodes = Some fm ->
  forall p, FileMap.In p fm <-> In p (List.map path nodes).
Proof.
  induction nodes as [ | n rest IH ]; simpl; intros fm Hbuild p.
  - injection Hbuild as <-. split.
    + intros [sf Hsf]. exfalso. apply (FileMap.empty_1 (elt:=File) Hsf).
    + intros [].
  - destruct (files_of_nodes rest) as [fm'|] eqn:Erest; [ | discriminate ].
    destruct (file_mem (path n) fm') eqn:Emem; [ discriminate | ].
    injection Hbuild as <-. specialize (IH fm' eq_refl).
    rewrite FileFacts.add_in_iff, IH. split.
    + intros [Heq | Hin]; [ left; exact Heq | right; exact Hin ].
    + intros [Heq | Hin]; [ left; exact Heq | right; exact Hin ].
Qed.

Theorem files_of_nodes_success_iff_unique : forall nodes,
  (exists fm, files_of_nodes nodes = Some fm) <-> NoDup (List.map path nodes).
Proof.
  induction nodes as [ | n rest IH ]; simpl.
  - split; [ intros _; constructor | intros _; eexists; reflexivity ].
  - split.
    + intros [fm Hbuild]. destruct (files_of_nodes rest) as [fm'|] eqn:Erest; [ | discriminate ].
      destruct (file_mem (path n) fm') eqn:Emem; [ discriminate | ].
      constructor.
      * intro Hin. assert (Hbad : FileMap.In (path n) fm').
        { apply (files_of_nodes_in rest fm' Erest). exact Hin. }
        apply FileMap.mem_1 in Hbad. unfold file_mem in Emem. rewrite Hbad in Emem. discriminate.
      * apply IH. exists fm'; reflexivity.
    + intro Hnd. inversion Hnd as [ | h t Hni Hnd' ]; subst.
      destruct (proj2 IH Hnd') as [fm' Hrest]. rewrite Hrest.
      destruct (file_mem (path n) fm') eqn:Emem.
      * exfalso. unfold file_mem in Emem. apply FileMap.mem_2 in Emem.
        apply (files_of_nodes_in rest fm' Hrest) in Emem. contradiction.
      * eexists; reflexivity.
Qed.

Theorem files_of_nodes_none_iff_duplicate : forall nodes,
  files_of_nodes nodes = None <-> ~ NoDup (List.map path nodes).
Proof.
  intro nodes. split.
  - intros Hnone Hnd. destruct (proj2 (files_of_nodes_success_iff_unique nodes) Hnd) as [fm Hfm].
    rewrite Hfm in Hnone. discriminate.
  - intro Hnd. destruct (files_of_nodes nodes) as [fm|] eqn:E; [ | reflexivity ].
    exfalso. apply Hnd. apply (files_of_nodes_success_iff_unique nodes). eexists; exact E.
Qed.

Lemma files_of_nodes_maps_to : forall nodes fm,
  files_of_nodes nodes = Some fm ->
  forall n, In n nodes -> maps_to_file (path n) (source n) fm.
Proof.
  induction nodes as [ | h rest IH ]; simpl; intros fm Hbuild n Hin; [ contradiction | ].
  destruct (files_of_nodes rest) as [fm'|] eqn:Erest; [ | discriminate ].
  destruct (file_mem (path h) fm') eqn:Emem; [ discriminate | ].
  injection Hbuild as <-. unfold maps_to_file. destruct Hin as [ -> | Hin ].
  - apply FileMap.add_1. reflexivity.
  - assert (Hin' : FileMap.In (path n) fm')
      by (apply (files_of_nodes_in rest fm' Erest); apply in_map; exact Hin).
    assert (Hne : path h <> path n).
    { intro Heq. rewrite Heq in Emem. apply FileMap.mem_1 in Hin'. unfold file_mem in Emem.
      rewrite Hin' in Emem. discriminate. }
    apply FileMap.add_2; [ exact Hne | apply (IH fm' eq_refl n Hin) ].
Qed.

Lemma files_of_nodes_mapsto_source : forall nodes fm,
  files_of_nodes nodes = Some fm ->
  forall p sf, maps_to_file p sf fm -> exists n, In n nodes /\ path n = p /\ source n = sf.
Proof.
  induction nodes as [ | h rest IH ]; simpl; intros fm Hbuild p sf Hmt.
  - injection Hbuild as <-. unfold maps_to_file in Hmt. exfalso. apply (FileMap.empty_1 Hmt).
  - destruct (files_of_nodes rest) as [fm'|] eqn:Erest; [ | discriminate ].
    destruct (file_mem (path h) fm') eqn:Emem; [ discriminate | ].
    injection Hbuild as <-. unfold maps_to_file in Hmt.
    apply FileFacts.add_mapsto_iff in Hmt. destruct Hmt as [ [Heq Hsf] | [Hne Hmt'] ].
    + exists h. split; [ left; reflexivity | split; [ exact Heq | exact Hsf ] ].
    + destruct (IH fm' eq_refl p sf Hmt') as [ n [Hin [Hp Hsf]] ].
      exists n. split; [ right; exact Hin | split; [ exact Hp | exact Hsf ] ].
Qed.

Lemma files_of_nodes_find : forall nodes fm p sf,
  files_of_nodes nodes = Some fm ->
  (find_file p fm = Some sf <-> exists n, In n nodes /\ path n = p /\ source n = sf).
Proof.
  intros nodes fm p sf Hbuild. unfold find_file. split.
  - intro Hf. apply FileFacts.find_mapsto_iff in Hf. exact (files_of_nodes_mapsto_source nodes fm Hbuild p sf Hf).
  - intros [n [Hin [Hp Hsf]]]. apply FileFacts.find_mapsto_iff.
    pose proof (files_of_nodes_maps_to nodes fm Hbuild n Hin) as Hmt.
    unfold maps_to_file in Hmt. rewrite Hp, Hsf in Hmt. exact Hmt.
Qed.

Lemma files_of_nodes_duplicate_rejects : forall p sf,
  files_of_nodes (MakeFileNode p sf :: MakeFileNode p sf :: nil) = None.
Proof.
  intros p sf. apply files_of_nodes_none_iff_duplicate. simpl.
  intro Hnd. inversion Hnd as [ | x l Hni _ ]; subst. apply Hni. left. reflexivity.
Qed.

Lemma files_of_nodes_duplicate_different_source_rejects : forall p sf1 sf2,
  files_of_nodes (MakeFileNode p sf1 :: MakeFileNode p sf2 :: nil) = None.
Proof.
  intros p sf1 sf2. apply files_of_nodes_none_iff_duplicate. simpl.
  intro Hnd. inversion Hnd as [ | x l Hni _ ]; subst. apply Hni. left. reflexivity.
Qed.

(* Permuting the input nodes yields a semantically equal map, so construction order never leaks. *)
Lemma files_of_nodes_permutation : forall nodes1 nodes2 fm1 fm2,
  Permutation nodes1 nodes2 ->
  files_of_nodes nodes1 = Some fm1 -> files_of_nodes nodes2 = Some fm2 ->
  FilesEqual fm1 fm2.
Proof.
  intros nodes1 nodes2 fm1 fm2 Hperm H1 H2 p.
  destruct (FileMap.find p fm1) as [sf|] eqn:E1.
  - apply (files_of_nodes_find nodes1 fm1 p sf H1) in E1. destruct E1 as [n [Hin [Hp Hs]]].
    symmetry. apply (files_of_nodes_find nodes2 fm2 p sf H2).
    exists n. split; [ apply (Permutation_in _ Hperm); exact Hin | split; [ exact Hp | exact Hs ] ].
  - destruct (FileMap.find p fm2) as [sf|] eqn:E2; [ | reflexivity ].
    exfalso. apply (files_of_nodes_find nodes2 fm2 p sf H2) in E2. destruct E2 as [n [Hin [Hp Hs]]].
    assert (Hbad : find_file p fm1 = Some sf).
    { apply (files_of_nodes_find nodes1 fm1 p sf H1).
      exists n. split; [ apply (Permutation_in _ (Permutation_sym Hperm)); exact Hin
                       | split; [ exact Hp | exact Hs ] ]. }
    unfold find_file in Hbad. rewrite E1 in Hbad. discriminate.
Qed.

(* The module spec: intrinsic facts about the generated module, not about its environment. *)
Record ModuleSpec : Type := MakeModuleSpec {
  module_path       : ModulePath.T;
  module_version : Version
}.


Record Program : Type := MakeProgram {
  module_spec : ModuleSpec;
  files  : Files
}.

Definition program_bindings (p : Program) : list (FilePath.T * File) := file_bindings (files p).
Definition program_keys (p : Program) : list FilePath.T := file_paths (files p).
Definition program_find (path : FilePath.T) (p : Program) : option File := find_file path (files p).

Definition main_source (decls : list TopLevelDecl) : File := MakeFile MainPackage [] decls.

Definition main_file_node (path : FilePath.T) (decls : list TopLevelDecl) : FileNode :=
  MakeFileNode path (main_source decls).

Definition singleton_program (ms : ModuleSpec) (path : FilePath.T) (decls : list TopLevelDecl) : Program :=
  MakeProgram ms (FileMap.add path (main_source decls) empty_files).

(* A module-only program: a valid [ModuleSpec] with NO source files. *)
Definition empty_program (ms : ModuleSpec) : Program :=
  MakeProgram ms empty_files.

Definition build_program (ms : ModuleSpec) (nodes : list FileNode) : option Program :=
  match files_of_nodes nodes with
  | None => None
  | Some fm => Some (MakeProgram ms fm)
  end.

Theorem build_program_some_iff_unique : forall ms nodes,
  (exists p, build_program ms nodes = Some p) <-> NoDup (List.map path nodes).
Proof.
  intros ms nodes. unfold build_program. rewrite <- files_of_nodes_success_iff_unique. split.
  - intros [p Hp]. destruct (files_of_nodes nodes) as [fm|] eqn:E; [ eexists; reflexivity | discriminate ].
  - intros [fm Hfm]. rewrite Hfm. eexists; reflexivity.
Qed.
