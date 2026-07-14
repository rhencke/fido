(** ============================================================================
    GoTypes — the ONE Go type-system authority for the current bool/int fragment.  It is EVIDENCE over the
    ONE raw [GoAST], never a second (typed) AST: raw [GoExpr] stays untyped syntax, and typing is a judgment
    over that same syntax.

    The permanent type universe here is EXACTLY [TBool] and [TInt] — the two types the admitted fragment
    already needs.  A future type constructor is a reviewed semantic milestone (static typing +
    representability + compiler facts + safety + rendering + tests + docs together); there are no placeholder
    constructors.

    The foundational distinction (Go's own): a raw literal denotes an EXACT UNTYPED CONSTANT value
    ([GoConst], arbitrary-precision), independent of any width.  Only in a USE CONTEXT that requires a typed
    value is a DEFAULT TYPE chosen and REPRESENTABILITY checked (int constants have a contextual range
    obligation; the untyped constant itself is exact).  This is the single authority every later feature
    (assignments, variables, arguments, conversions, typed constants, more numeric types) will build on.
    ============================================================================ *)
From Stdlib Require Import NArith ZArith List Bool.
From Fido Require Import Ints GoAST.
Import ListNotations.
Open Scope Z_scope.

(** ---- the one type universe (exactly the two types the current fragment needs) ---- *)
Inductive GoType : Type :=
| TBool
| TInt.

Definition gotype_eqb (a b : GoType) : bool :=
  match a, b with TBool, TBool => true | TInt, TInt => true | _, _ => false end.

Lemma gotype_eqb_eq : forall a b, gotype_eqb a b = true <-> a = b.
Proof. intros [] []; simpl; split; congruence. Qed.

(** ---- exact untyped constant values of the current raw literals ---- *)
Inductive GoConst : Type :=
| CBool : bool -> GoConst
| CInt  : Z -> GoConst.

(** the ONE constant interpretation of the raw expressions.  Total by construction; a raw int literal is an
    EXACT value (no range check here — representability is a separate contextual obligation). *)
Definition const_value (e : GoExpr) : GoConst :=
  match e with
  | EBool b => CBool b
  | EInt n  => CInt (Z.of_N n)
  | ENeg n  => CInt (- Z.of_N n)
  end.

(** determinism + totality are structural (a function of the syntax). *)
Lemma const_value_deterministic : forall e c1 c2,
  const_value e = c1 -> const_value e = c2 -> c1 = c2.
Proof. intros e c1 c2 <- <-; reflexivity. Qed.

(** [EInt 0] and [ENeg 0] denote the SAME untyped constant (signed zero is one value). *)
Lemma const_value_zero_sign : const_value (EInt 0) = const_value (ENeg 0).
Proof. reflexivity. Qed.

(** the DEFAULT type — the type chosen for a constant in a context that requires a typed value.  It is NOT a
    property of the raw literal (the literal stays untyped); [TInt] is not baked into [EInt]/[ENeg]. *)
Definition const_default_type (c : GoConst) : GoType :=
  match c with CBool _ => TBool | CInt _ => TInt end.

Lemma const_default_type_bool : forall b, const_default_type (CBool b) = TBool.
Proof. reflexivity. Qed.
Lemma const_default_type_int : forall z, const_default_type (CInt z) = TInt.
Proof. reflexivity. Qed.

(** ---- representability: one type-directed authority (the SINGLE integer-range decision) ---- *)
Inductive ConstRepresentable : GoType -> GoConst -> Prop :=
| RBool : forall b, ConstRepresentable TBool (CBool b)
| RInt  : forall z, int_min <= z <= int_max -> ConstRepresentable TInt (CInt z).

Definition const_representableb (t : GoType) (c : GoConst) : bool :=
  match t, c with
  | TBool, CBool _ => true
  | TInt,  CInt z  => (int_min <=? z) && (z <=? int_max)
  | _, _ => false
  end.

Lemma const_representableb_iff : forall t c, const_representableb t c = true <-> ConstRepresentable t c.
Proof.
  intros t c; split.
  - destruct t; destruct c as [ b | z ]; simpl; intro H; try discriminate.
    + constructor.
    + apply Bool.andb_true_iff in H as [Hl Hr]; apply Z.leb_le in Hl; apply Z.leb_le in Hr;
        constructor; split; assumption.
  - intro H; destruct H as [ b | z [Hl Hr] ]; simpl.
    + reflexivity.
    + apply Bool.andb_true_iff; split; apply Z.leb_le; assumption.
Qed.

(** ---- use-context resolution: one expression-use context and its per-type policy ---- *)
Inductive ExprUse : Type :=
| UsePrintlnArg.

(** the exhaustive per-type use policy.  A `println` argument accepts BOTH current types. *)
Inductive UseAllows : ExprUse -> GoType -> Prop :=
| UAPrintlnBool : UseAllows UsePrintlnArg TBool
| UAPrintlnInt  : UseAllows UsePrintlnArg TInt.

Definition use_allowsb (u : ExprUse) (t : GoType) : bool :=
  match u, t with UsePrintlnArg, TBool => true | UsePrintlnArg, TInt => true end.

Lemma use_allowsb_iff : forall u t, use_allowsb u t = true <-> UseAllows u t.
Proof.
  intros [] []; simpl; split; try (intros _; constructor); try reflexivity; intro H; inversion H.
Qed.

(** the declarative resolved typing of ONE expression in a use context: the expression denotes one exact
    untyped constant, whose DEFAULT type is [t], the context ALLOWS [t], and the constant is REPRESENTABLE as
    [t].  (No typed-expression AST, no copied "resolved expression" — this is a relation over the raw syntax.) *)
Inductive ResolveExpr : ExprUse -> GoExpr -> GoType -> Prop :=
| Resolve : forall u e t,
    const_default_type (const_value e) = t ->
    UseAllows u t ->
    ConstRepresentable t (const_value e) ->
    ResolveExpr u e t.

Definition resolve_expr (u : ExprUse) (e : GoExpr) : option GoType :=
  let c := const_value e in
  let t := const_default_type c in
  if use_allowsb u t && const_representableb t c then Some t else None.

Lemma resolve_expr_sound : forall u e t, resolve_expr u e = Some t -> ResolveExpr u e t.
Proof.
  intros u e t; unfold resolve_expr.
  destruct (use_allowsb u (const_default_type (const_value e))) eqn:Hu;
    destruct (const_representableb (const_default_type (const_value e)) (const_value e)) eqn:Hr;
    simpl; intro H; try discriminate.
  injection H as <-. apply use_allowsb_iff in Hu; apply const_representableb_iff in Hr.
  constructor; [ reflexivity | exact Hu | exact Hr ].
Qed.

Lemma resolve_expr_complete : forall u e t, ResolveExpr u e t -> resolve_expr u e = Some t.
Proof.
  intros u e t H; destruct H as [ u0 e0 t0 Hdt Hu Hr ].
  apply use_allowsb_iff in Hu; apply const_representableb_iff in Hr.
  unfold resolve_expr; rewrite Hdt, Hu, Hr; reflexivity.
Qed.

(** the resolved type, when it exists, is EXACTLY the constant's default type — never the wrong type. *)
Lemma resolve_expr_default : forall u e t, ResolveExpr u e t -> t = const_default_type (const_value e).
Proof. intros u e t H; destruct H as [ u0 e0 t0 Hdt Hu Hr ]; symmetry; exact Hdt. Qed.

Lemma resolve_expr_deterministic : forall u e t1 t2, ResolveExpr u e t1 -> ResolveExpr u e t2 -> t1 = t2.
Proof.
  intros u e t1 t2 H1 H2.
  rewrite (resolve_expr_default _ _ _ H1), (resolve_expr_default _ _ _ H2); reflexivity.
Qed.

(** an expression is typed in a use context iff it resolves to SOME type there. *)
Definition expr_typedb (u : ExprUse) (e : GoExpr) : bool :=
  match resolve_expr u e with Some _ => true | None => false end.

Lemma expr_typedb_iff : forall u e, expr_typedb u e = true <-> exists t, ResolveExpr u e t.
Proof.
  intros u e; unfold expr_typedb; destruct (resolve_expr u e) as [ t | ] eqn:Hr; split.
  - intros _; exists t; apply resolve_expr_sound; exact Hr.
  - intros _; reflexivity.
  - intro H; discriminate H.
  - intros [t' Ht]; apply resolve_expr_complete in Ht; rewrite Ht in Hr; discriminate.
Qed.

(** ---- whole-current-fragment typing judgments (replacing the old ExprOk/StmtOk/DeclOk/FileOk family) ---- *)

Inductive StmtTyped : GoStmt -> Prop :=
| STPrintln : forall args,
    Forall (fun e => exists t, ResolveExpr UsePrintlnArg e t) args -> StmtTyped (SPrintln args).

Inductive DeclTyped : GoDecl -> Prop :=
| DTMain : forall body, Forall StmtTyped body -> DeclTyped (DMain body).

Definition FileTyped (f : GoFileAST) : Prop := Forall DeclTyped f.

Definition ProgramTyped (p : GoProgram) : Prop := Forall (fun e => FileTyped (snd e)) (prog_entries p).

Definition stmt_typedb (s : GoStmt) : bool :=
  match s with SPrintln args => forallb (expr_typedb UsePrintlnArg) args end.
Definition decl_typedb (d : GoDecl) : bool :=
  match d with DMain body => forallb stmt_typedb body end.
Definition file_typedb (f : GoFileAST) : bool := forallb decl_typedb f.
Definition program_typedb (p : GoProgram) : bool :=
  forallb (fun e => file_typedb (snd e)) (prog_entries p).

Lemma forallb_Forall {X} : forall (f : X -> bool) (P : X -> Prop) (l : list X),
  (forall x, f x = true <-> P x) -> (forallb f l = true <-> Forall P l).
Proof.
  intros f P l Hpt; induction l as [ | x l' IH ]; simpl.
  - split; [ constructor | reflexivity ].
  - rewrite Bool.andb_true_iff, Hpt, IH.
    split; [ intros [Hx Hl]; constructor; assumption
           | intro H; inversion H; subst; split; assumption ].
Qed.

Lemma stmt_typedb_iff : forall s, stmt_typedb s = true <-> StmtTyped s.
Proof.
  intros [args]; simpl.
  rewrite (forallb_Forall (expr_typedb UsePrintlnArg) (fun e => exists t, ResolveExpr UsePrintlnArg e t)
             args (fun e => expr_typedb_iff UsePrintlnArg e)).
  split; [ intro H; constructor; exact H | intro H; inversion H; subst; assumption ].
Qed.

Lemma decl_typedb_iff : forall d, decl_typedb d = true <-> DeclTyped d.
Proof.
  intros [body]; simpl. rewrite (forallb_Forall stmt_typedb StmtTyped body stmt_typedb_iff).
  split; [ intro H; constructor; exact H | intro H; inversion H; subst; assumption ].
Qed.

Lemma file_typedb_iff : forall f, file_typedb f = true <-> FileTyped f.
Proof. intro f; unfold file_typedb, FileTyped; apply forallb_Forall; exact decl_typedb_iff. Qed.

Lemma program_typedb_iff : forall p, program_typedb p = true <-> ProgramTyped p.
Proof.
  intro p; unfold program_typedb, ProgramTyped.
  apply forallb_Forall; intro e; apply file_typedb_iff.
Qed.

(** the empty file is typed vacuously; so is the empty program. *)
Lemma empty_file_typed : FileTyped [].
Proof. constructor. Qed.

(** ---- boundary / range fixtures (the grammar of typing, kernel-checked) ---- *)
Example res_bool_true  : resolve_expr UsePrintlnArg (EBool true)  = Some TBool. Proof. reflexivity. Qed.
Example res_bool_false : resolve_expr UsePrintlnArg (EBool false) = Some TBool. Proof. reflexivity. Qed.
Example res_int_zero   : resolve_expr UsePrintlnArg (EInt 0)      = Some TInt.  Proof. reflexivity. Qed.
Example res_neg_zero   : resolve_expr UsePrintlnArg (ENeg 0)      = Some TInt.  Proof. reflexivity. Qed.
Example const_zero_eq  : const_value (EInt 0) = const_value (ENeg 0). Proof. reflexivity. Qed.
(* max int = 2^63-1 = 9223372036854775807 as EInt magnitude; min int = -(2^63) as ENeg magnitude. *)
Example res_int_max    : resolve_expr UsePrintlnArg (EInt 9223372036854775807) = Some TInt. Proof. reflexivity. Qed.
Example res_int_min    : resolve_expr UsePrintlnArg (ENeg 9223372036854775808) = Some TInt. Proof. reflexivity. Qed.
(* a mixed statement, empty println, empty file, empty program are all typed. *)
Example stmt_mixed_typed : stmt_typedb (SPrintln [EBool true; EInt 42; ENeg 1]) = true. Proof. reflexivity. Qed.
Example stmt_empty_typed : stmt_typedb (SPrintln []) = true. Proof. reflexivity. Qed.
Example file_empty_typed : file_typedb [] = true. Proof. reflexivity. Qed.

(* negatives: overflow / underflow / cross-type do NOT resolve. *)
Example res_over  : resolve_expr UsePrintlnArg (EInt 9223372036854775808) = None. Proof. reflexivity. Qed.
Example res_under : resolve_expr UsePrintlnArg (ENeg 9223372036854775809) = None. Proof. reflexivity. Qed.
Example bool_not_int  : const_representableb TInt  (CBool true) = false. Proof. reflexivity. Qed.
Example int_not_bool  : const_representableb TBool (CInt 3)     = false. Proof. reflexivity. Qed.
Example over_stmt_untyped : stmt_typedb (SPrintln [EInt 9223372036854775808]) = false. Proof. reflexivity. Qed.
