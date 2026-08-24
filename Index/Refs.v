(* Index.Refs — exact refined source-occurrence refs: main/block/app/unary/exprstmt/short/spec + positional laws. *)
From Stdlib Require Import List Bool Arith PeanoNat Lia Eqdep_dec PArith FSets.FMapFacts.
From Fido Require Import Syntax Index.Model Index.
Import ListNotations.

Record MainOccurrenceRef {p} (idx : ProgramIndex p) : Type := mkMainOccurrenceRef {
  mo_node : NodeRef idx ;
  mo_ok   : is_main_view (node_view mo_node) = true
}.
Arguments mkMainOccurrenceRef {p idx} _ _.
Arguments mo_node {p idx} _.
Arguments mo_ok {p idx} _.

Record BlockRef {p} (idx : ProgramIndex p) : Type := mkBlockRef {
  bl_node : NodeRef idx ;
  bl_ok   : is_block_view (node_view bl_node) = true
}.
Arguments mkBlockRef {p idx} _ _.
Arguments bl_node {p idx} _.
Arguments bl_ok {p idx} _.

Lemma mainocc_positional {p} {idx : ProgramIndex p} (a b : MainOccurrenceRef idx) :
  mo_node a = mo_node b -> a = b.
Proof. destruct a as [na Ha], b as [nb Hb]; cbn; intro E; subst nb; f_equal; apply (UIP_dec Bool.bool_dec). Qed.

Lemma blockref_positional {p} {idx : ProgramIndex p} (a b : BlockRef idx) :
  bl_node a = bl_node b -> a = b.
Proof. destruct a as [na Ha], b as [nb Hb]; cbn; intro E; subst nb; f_equal; apply (UIP_dec Bool.bool_dec). Qed.

(* exact refined parents: each edge family is requested only from a parent proven to be its exact kind *)
Record AppRef {p} (idx : ProgramIndex p) : Type := mkAppRef {
  app_node : NodeRef idx ;
  app_ok   : node_view app_node = VApplication
}.
Arguments mkAppRef {p idx} _ _.
Arguments app_node {p idx} _.
Arguments app_ok {p idx} _.

Record UnaryRef {p} (idx : ProgramIndex p) : Type := mkUnaryRef {
  un_node : NodeRef idx ;
  un_op   : Syntax.UnaryOp ;
  un_ok   : node_view un_node = VUnary un_op
}.
Arguments mkUnaryRef {p idx} _ _ _.
Arguments un_node {p idx} _.
Arguments un_op {p idx} _.
Arguments un_ok {p idx} _.

Record ExprStmtRef {p} (idx : ProgramIndex p) : Type := mkExprStmtRef {
  exs_node : NodeRef idx ;
  exs_ok   : node_view exs_node = VStmt SSExpr
}.
Arguments mkExprStmtRef {p idx} _ _.
Arguments exs_node {p idx} _.
Arguments exs_ok {p idx} _.

Record ShortStmtRef {p} (idx : ProgramIndex p) : Type := mkShortStmtRef {
  sh_node   : NodeRef idx ;
  sh_names  : nat ;
  sh_values : nat ;
  sh_ok     : node_view sh_node = VStmt (SSShort sh_names sh_values)
}.
Arguments mkShortStmtRef {p idx} _ _ _ _.
Arguments sh_node {p idx} _.
Arguments sh_names {p idx} _.
Arguments sh_values {p idx} _.
Arguments sh_ok {p idx} _.

(* one flavor-indexed spec parent: the exact shape is retained, so every field formula reads it *)
Definition SpecShape (fl : SpecFlavor) : Type :=
  match fl with ConstSpecF => ConstShape | VarSpecF => VarShape | TypeSpecF => TypeSpecShape end.
Definition spec_view_of (fl : SpecFlavor) : SpecShape fl -> NodeView :=
  match fl with ConstSpecF => VConstSpec | VarSpecF => VVarSpec | TypeSpecF => VTypeSpec end.
Record SpecRef {p} (idx : ProgramIndex p) (fl : SpecFlavor) : Type := mkSpecRef {
  sp_node  : NodeRef idx ;
  sp_shape : SpecShape fl ;
  sp_ok    : node_view sp_node = spec_view_of fl sp_shape
}.
Arguments mkSpecRef {p idx fl} _ _ _.
Arguments sp_node {p idx fl} _.
Arguments sp_shape {p idx fl} _.
Arguments sp_ok {p idx fl} _.

(* the scalar layout each spec shape fixes: name count, declared-type presence, value count *)
Definition shape_names (fl : SpecFlavor) : SpecShape fl -> nat :=
  match fl with
  | ConstSpecF => fun sh => match sh with CSExplicit _ nn _ => nn | CSInherited nn => nn end
  | VarSpecF   => fun sh => match sh with VSTypeOnly nn => nn | VSValues _ nn _ => nn end
  | TypeSpecF  => fun _ => 1
  end.
Definition shape_has_type (fl : SpecFlavor) : SpecShape fl -> bool :=
  match fl with
  | ConstSpecF => fun sh => match sh with CSExplicit ht _ _ => ht | CSInherited _ => false end
  | VarSpecF   => fun sh => match sh with VSTypeOnly _ => true | VSValues ht _ _ => ht end
  | TypeSpecF  => fun _ => true
  end.
Definition shape_values (fl : SpecFlavor) : SpecShape fl -> nat :=
  match fl with
  | ConstSpecF => fun sh => match sh with CSExplicit _ _ nv => nv | CSInherited _ => 0 end
  | VarSpecF   => fun sh => match sh with VSValues _ _ nv => nv | VSTypeOnly _ => 0 end
  | TypeSpecF  => fun _ => 0
  end.
Definition type_ordinal (fl : SpecFlavor) (sh : SpecShape fl) : nat := shape_names fl sh.
Definition value_ordinal (fl : SpecFlavor) (sh : SpecShape fl) (j : nat) : nat :=
  shape_names fl sh + (if shape_has_type fl sh then 1 else 0) + j.

(* the shape-fixed count IS the layout count of the spec's view: the two authorities agree by computation *)
Lemma spec_layout_count : forall fl (sh : SpecShape fl),
  layout_count (spec_view_of fl sh)
  = Some (shape_names fl sh + (if shape_has_type fl sh then 1 else 0) + shape_values fl sh).
Proof. destruct fl; destruct sh; cbn; try reflexivity; f_equal; lia. Qed.

