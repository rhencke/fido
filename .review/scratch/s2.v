
(* ── Index: exact source occurrences ───────────────────────────────────────── *)
Inductive Role : Type :=
| RFilePackage | RDeclarationSpec | RVarSpecType
| RConstInitializerExpression | RVarInitializerExpression | RShortRightExpression
| RStatementExpression | RUnaryOperand | RApplicationHead | RApplicationArgument.

Inductive ExprChildRole : Role -> Type :=
| ECConstInitializer : ExprChildRole RConstInitializerExpression
| ECVarInitializer   : ExprChildRole RVarInitializerExpression
| ECShortRight       : ExprChildRole RShortRightExpression
| ECStatement        : ExprChildRole RStatementExpression
| ECUnaryOperand     : ExprChildRole RUnaryOperand
| ECApplicationHead  : ExprChildRole RApplicationHead
| ECApplicationArg   : ExprChildRole RApplicationArgument.

Inductive UseRole : Type := TypeNameRole | ValueNameRole | HeadNameRole.

Parameter NodeRef : SyntaxProgram -> Type.
Parameter node_key : forall {p}, NodeRef p -> IndexKey.
Parameter ExprRef ConstDeclRef ConstSpecRef BindingNameRef BlankRef : SyntaxProgram -> Type.
Parameter TypeUseRef NameUseRef UnaryRef ApplicationRef : SyntaxProgram -> Type.
Parameter ExpressionStatementRef VariableSiteRef : SyntaxProgram -> Type.
Parameter StatementRef FileRef : SyntaxProgram -> Type.
Parameter AliasSpecRef BoundDefinedTypeRef : SyntaxProgram -> Type.
Parameter VarSpecRef ShortDeclRef : SyntaxProgram -> Type.

(* ── §2 Dependent source-shape refinements ─────────────────────────────────── *)
(* Each payload projects its exact parent occurrence, so the constructor index is definitionally that
   projected occurrence and no payload can be borrowed from another. *)
Parameter LiteralRef : SyntaxProgram -> Type.
Parameter literal_expr : forall {p}, LiteralRef p -> ExprRef p.
Parameter name_use_expr : forall {p}, NameUseRef p -> ExprRef p.
Parameter unary_expr : forall {p}, UnaryRef p -> ExprRef p.
Parameter application_expr_of : forall {p}, ApplicationRef p -> ExprRef p.

Inductive ExprView {p} : ExprRef p -> Type :=
| EVLiteral     : forall (l : LiteralRef p), ExprView (literal_expr l)
| EVName        : forall (u : NameUseRef p), ExprView (name_use_expr u)
| EVUnary       : forall (n : UnaryRef p), ExprView (unary_expr n)
| EVApplication : forall (a : ApplicationRef p), ExprView (application_expr_of a).

Parameter expr_view : forall {p} (r : ExprRef p), @ExprView p r.

(* §3 Object-establishing binders are a strict subset of named occurrences. *)
Parameter ObjectEstablisher : SyntaxProgram -> Type.
Parameter establisher_spelling : forall {p}, ObjectEstablisher p -> string.

(* Each binder payload projects its exact parent BindingNameRef. *)
Parameter blank_binding_name : forall {p}, BlankRef p -> BindingNameRef p.
Parameter establisher_binding_name : forall {p}, ObjectEstablisher p -> BindingNameRef p.
Parameter short_lhs_binding_name : forall {p}, ShortDeclRef p -> BindingNameRef p -> BindingNameRef p.
Parameter short_lhs_decl : forall {p}, BindingNameRef p -> option (ShortDeclRef p).
Parameter short_lhs_spelling : forall {p}, BindingNameRef p -> string.
Parameter short_lhs_scope : forall {p}, BindingNameRef p -> ScopeId p.
Parameter short_lhs_position : forall {p}, BindingNameRef p -> nat.

Inductive BindingNameView {p} : BindingNameRef p -> Type :=
| BNBlank   : forall (k : BlankRef p), BindingNameView (blank_binding_name k)
| BNRegular : forall (est : ObjectEstablisher p) (c : DeclContext),
    BindingNameView (establisher_binding_name est)
| BNShort   : forall (d : ShortDeclRef p) (n : BindingNameRef p) (sp : string),
    short_lhs_decl n = Some d -> short_lhs_spelling n = sp ->
    BindingNameView n.

Parameter binding_name_view : forall {p} (n : BindingNameRef p), @BindingNameView p n.

(* §2 Object-site refinements — each payload projects its exact parent site. *)
Parameter ObjectSiteRef : SyntaxProgram -> Type.
Parameter object_site_key : forall {p}, ObjectSiteRef p -> IndexKey.
Parameter const_object_site : forall {p}, ConstSpecRef p -> ObjectSiteRef p.
Parameter var_object_site : forall {p}, VariableSiteRef p -> ObjectSiteRef p.
Parameter alias_object_site : forall {p}, AliasSpecRef p -> ObjectSiteRef p.
Parameter defined_object_site : forall {p}, BoundDefinedTypeRef p -> ObjectSiteRef p.
Parameter main_object_site : forall {p}, FileRef p -> ObjectSiteRef p.

Inductive ObjectSiteView {p} : ObjectSiteRef p -> Type :=
| OSConst   : forall (c : ConstSpecRef p), ObjectSiteView (const_object_site c)
| OSVar     : forall (v : VariableSiteRef p), ObjectSiteView (var_object_site v)
| OSAlias   : forall (a : AliasSpecRef p), ObjectSiteView (alias_object_site a)
| OSDefined : forall (d : BoundDefinedTypeRef p), ObjectSiteView (defined_object_site d)
| OSMain    : forall (f : FileRef p), ObjectSiteView (main_object_site f).

Parameter object_site_view : forall {p} (s : ObjectSiteRef p), @ObjectSiteView p s.
Parameter object_site_spelling : forall {p}, ObjectSiteRef p -> string.
Parameter object_site_scope : forall {p}, ObjectSiteRef p -> ScopeId p.

Parameter establisher_site : forall {p}, ObjectEstablisher p -> ObjectSiteRef p.
Parameter variable_site_establisher : forall {p}, VariableSiteRef p -> ObjectEstablisher p.

Inductive ConsumptionSiteRef (p : SyntaxProgram) : Type :=
| ConstSite : ConstSpecRef p -> ConsumptionSiteRef p
| VarSite   : VarSpecRef p -> ConsumptionSiteRef p
| ShortSite : ShortDeclRef p -> ConsumptionSiteRef p.

(* Structural source laws. *)
Parameter expr_node : forall {p}, ExprRef p -> NodeRef p.
Parameter application_expr application_head : forall {p}, ApplicationRef p -> ExprRef p.
Parameter application_key : forall {p}, ApplicationRef p -> IndexKey.
Parameter statement_expression : forall {p}, ExpressionStatementRef p -> ExprRef p.
Parameter statement_application : forall {p}, ExpressionStatementRef p -> option (ApplicationRef p).
Parameter statement_application_is_its_expression : forall {p}
  (s : ExpressionStatementRef p) (a : ApplicationRef p),
  statement_application s = Some a -> statement_expression s = application_expr a.
Parameter unary_operand : forall {p}, UnaryRef p -> ExprRef p.
Parameter OccupiesRole : forall {p}, NodeRef p -> NodeRef p -> Role -> Prop.

Parameter DirectExprUseRef : SyntaxProgram -> Type.
Parameter direct_parent : forall {p}, DirectExprUseRef p -> NodeRef p.
Parameter direct_child  : forall {p}, DirectExprUseRef p -> ExprRef p.
Parameter direct_role   : forall {p}, DirectExprUseRef p -> Role.
Parameter direct_is_expr_child : forall {p} (u : DirectExprUseRef p), ExprChildRole (direct_role u).
Parameter direct_occupies : forall {p} (u : DirectExprUseRef p),
  OccupiesRole (direct_parent u) (expr_node (direct_child u)) (direct_role u).
Parameter application_head_use : forall {p}, ApplicationRef p -> DirectExprUseRef p.
Parameter application_argument_uses : forall {p}, ApplicationRef p -> list (DirectExprUseRef p).
Parameter unary_operand_use : forall {p}, UnaryRef p -> DirectExprUseRef p.
Parameter NameAtPosition : forall {p}, ConstSpecRef p -> BindingNameRef p -> nat -> Prop.

Parameter SpecInDecl : forall {p}, ConstDeclRef p -> ConstSpecRef p -> Prop.
Parameter NearestPrecedingExplicit :
  forall {p}, ConstDeclRef p -> ConstSpecRef p -> ConstSpecRef p -> Prop.
Parameter ExprAtPosition : forall {p}, ConstSpecRef p -> ExprRef p -> nat -> Prop.
Parameter SpecTypeUse : forall {p}, ConstSpecRef p -> option (TypeUseRef p) -> Prop.
Parameter StructuralIota : forall {p}, ConstSpecRef p -> nat -> Prop.

Record InheritedConstUseRef (p : SyntaxProgram) : Type := MakeInheritedConstUse {
  ic_decl        : ConstDeclRef p;
  ic_current     : ConstSpecRef p;
  ic_predecessor : ConstSpecRef p;
  ic_name        : BindingNameRef p;
  ic_expr        : ExprRef p;
  ic_type        : option (TypeUseRef p);
  ic_position    : nat;
  ic_iota        : nat;
  ic_current_in_decl    : SpecInDecl ic_decl ic_current;
  ic_pred_in_decl       : SpecInDecl ic_decl ic_predecessor;
  ic_pred_is_nearest    : NearestPrecedingExplicit ic_decl ic_current ic_predecessor;
  ic_name_at_position   : NameAtPosition ic_current ic_name ic_position;
  ic_expr_at_position   : ExprAtPosition ic_predecessor ic_expr ic_position;
  ic_type_is_predecessors : SpecTypeUse ic_predecessor ic_type;
  ic_iota_is_structural : StructuralIota ic_current ic_iota
}.

Inductive ExprUseRef (p : SyntaxProgram) : Type :=
| DirectUse    : DirectExprUseRef p -> ExprUseRef p
| InheritedUse : InheritedConstUseRef p -> ExprUseRef p.

Definition expression_of_use {p} (u : ExprUseRef p) : ExprRef p :=
  match u with DirectUse _ d => direct_child d | InheritedUse _ i => ic_expr p i end.

Inductive UseRefinement : Type := HeadRefinement | StatementRefinement | ResultRefinement.

Definition refinement_of_child_role {r : Role} (h : ExprChildRole r) : UseRefinement :=
  match h with
  | ECApplicationHead  => HeadRefinement
  | ECStatement        => StatementRefinement
  | ECConstInitializer | ECVarInitializer | ECShortRight | ECUnaryOperand | ECApplicationArg =>
      ResultRefinement
  end.

Definition use_refinement {p} (u : ExprUseRef p) : UseRefinement :=
  match u with
  | DirectUse _ d    => refinement_of_child_role (direct_is_expr_child d)
  | InheritedUse _ _ => ResultRefinement
  end.
