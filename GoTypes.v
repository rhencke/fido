(** ============================================================================
    GoTypes — the ONE Go type-system authority for the current bool/integer/string fragment.  It is EVIDENCE
    over the ONE raw [GoAST], never a second (typed) AST: raw [GoExpr] stays untyped syntax, and typing is a
    judgment over that same syntax.

    The permanent type universe here is [TBool], the INTEGER FAMILY [TInteger it] over the one [IntegerType]
    descriptor (ten live Go integer types), and [TString].  Each landed TOGETHER with its syntax and complete
    semantics (static typing + representability + compiler facts + safety + rendering + tests + docs); there
    are no placeholder constructors ahead of the syntax that needs them.

    The foundational distinction (Go's own): a raw literal denotes an EXACT UNTYPED CONSTANT value
    ([GoConst] — ints arbitrary-precision [Z], strings exact byte sequences), independent of any width.  An
    explicit integer conversion [EIntConvert it e] does NOT change that mathematical value; it produces a
    TYPED constant of type [TInteger it] and imposes a representability obligation at [it].  In a USE CONTEXT
    that requires a typed value, an UNTYPED constant is given a DEFAULT TYPE (int constants default to
    [TInteger IInt]) and REPRESENTABILITY is checked, while a TYPED constant RETAINS its type and value (it is
    NOT defaulted again, and its carried value must remain representable).  This is the single authority every
    later feature (assignments, variables, arguments, arithmetic, more numeric types) builds on.
    ============================================================================ *)
From Stdlib Require Import NArith ZArith List Bool String Ascii Lia.
From Fido Require Import Ints GoAST.
Import ListNotations.
Open Scope Z_scope.

(** The semantic value of a Go string is an EXACT BYTE SEQUENCE.  We use Rocq [string] directly (a sequence
    of [ascii] bytes) as that value, with exactly that meaning — it is NOT Unicode scalar values / code
    points / UTF-8-decoded characters / source-literal spelling (the canonical source spelling is a separate
    proved encoding in [GoRender]).  No wrapper and no invariant are needed: every finite byte sequence is a
    valid Go string value in represented scope (no length limit, no well-formedness side condition). *)

(** ---- the one type universe: bool, the integer FAMILY, and string ---- *)
Inductive GoType : Type :=
| TBool
| TInteger : IntegerType -> GoType
| TString.

Definition gotype_eqb (a b : GoType) : bool :=
  match a, b with
  | TBool, TBool => true
  | TInteger it1, TInteger it2 => integer_type_eqb it1 it2
  | TString, TString => true
  | _, _ => false
  end.

Lemma gotype_eqb_eq : forall a b, gotype_eqb a b = true <-> a = b.
Proof.
  intros [| it1 |] [| it2 |]; simpl; split; intro H; try reflexivity; try discriminate.
  - apply integer_type_eqb_eq in H; subst; reflexivity.
  - injection H as Heq; subst; apply integer_type_eqb_eq; reflexivity.
Qed.

(** ---- exact untyped constant values of the current raw literals ---- *)
Inductive GoConst : Type :=
| CBool   : bool -> GoConst
| CInt    : Z -> GoConst
| CString : string -> GoConst.

(** the ONE constant interpretation of the raw expressions.  Total by construction; a raw int literal is an
    EXACT value (no range check here — representability is a separate contextual obligation); a raw string
    literal denotes its EXACT byte sequence; an explicit integer conversion PRESERVES the exact mathematical
    value (no range check, no wrap here — the representability obligation is [const_info]/[ResolveExpr]). *)
Fixpoint const_value (e : GoExpr) : GoConst :=
  match e with
  | EBool b          => CBool b
  | EInt n           => CInt (Z.of_N n)
  | ENeg n           => CInt (- Z.of_N n)
  | EString s        => CString s
  | EIntConvert _ e' => const_value e'
  end.

(** a conversion never changes the exact mathematical constant value. *)
Lemma const_value_convert : forall it e, const_value (EIntConvert it e) = const_value e.
Proof. reflexivity. Qed.

(** determinism + totality are structural (a function of the syntax). *)
Lemma const_value_deterministic : forall e c1 c2,
  const_value e = c1 -> const_value e = c2 -> c1 = c2.
Proof. intros e c1 c2 <- <-; reflexivity. Qed.

(** [EInt 0] and [ENeg 0] denote the SAME untyped constant (signed zero is one value). *)
Lemma const_value_zero_sign : const_value (EInt 0) = const_value (ENeg 0).
Proof. reflexivity. Qed.

(** the DEFAULT type — the type chosen for an UNTYPED constant in a context that requires a typed value.  It
    is NOT a property of the raw literal (the literal stays untyped); an int constant defaults to the
    platform [int] = [TInteger IInt]. *)
Definition const_default_type (c : GoConst) : GoType :=
  match c with CBool _ => TBool | CInt _ => TInteger IInt | CString _ => TString end.

Lemma const_default_type_bool : forall b, const_default_type (CBool b) = TBool.
Proof. reflexivity. Qed.
Lemma const_default_type_int : forall z, const_default_type (CInt z) = TInteger IInt.
Proof. reflexivity. Qed.
Lemma const_default_type_string : forall s, const_default_type (CString s) = TString.
Proof. reflexivity. Qed.

(** ---- representability: one type-directed authority (the SINGLE integer-range decision, per member) ---- *)
Inductive ConstRepresentable : GoType -> GoConst -> Prop :=
| RBool   : forall b, ConstRepresentable TBool (CBool b)
| RInt    : forall it z, IntRepresentable it z -> ConstRepresentable (TInteger it) (CInt z)
| RString : forall s, ConstRepresentable TString (CString s).

(** every string constant is representable as [TString] (no length limit); a [CInt z] is representable as
    [TInteger it] iff [z] fits [it]; all cross-kind cases fall to [false]. *)
Definition const_representableb (t : GoType) (c : GoConst) : bool :=
  match t, c with
  | TBool,       CBool _   => true
  | TInteger it, CInt z    => integer_representableb it z
  | TString,     CString _ => true
  | _, _ => false
  end.

Lemma const_representableb_iff : forall t c, const_representableb t c = true <-> ConstRepresentable t c.
Proof.
  intros t c; split.
  - destruct t as [| it |]; destruct c as [ b | z | s ]; simpl; intro H; try discriminate.
    + constructor.
    + apply integer_representableb_spec in H; constructor; exact H.
    + constructor.
  - intro H; destruct H as [ b | it z Hr | s ]; simpl.
    + reflexivity.
    + apply integer_representableb_spec; exact Hr.
    + reflexivity.
Qed.

(** ---- one constant-status analysis: untyped vs typed constants over the same raw AST (Go's own lattice) ----
    A raw literal is an UNTYPED constant; an explicit integer conversion of a constant is a TYPED constant of
    the destination type, carrying the exact pre-conversion value RANGE-CHECKED against the destination.  A
    conversion of a bool/string constant is rejected; an invalid inner conversion returns [None] and cannot be
    revived by an outer conversion (the value is checked at EVERY layer). *)
Inductive ConstInfo : Type :=
| UntypedConst : GoConst -> ConstInfo
| TypedConst   : GoType -> GoConst -> ConstInfo.

Definition ci_const (ci : ConstInfo) : GoConst :=
  match ci with UntypedConst c => c | TypedConst _ c => c end.

Definition info_type (ci : ConstInfo) : GoType :=
  match ci with UntypedConst c => const_default_type c | TypedConst t _ => t end.

Fixpoint const_info (e : GoExpr) : option ConstInfo :=
  match e with
  | EBool b   => Some (UntypedConst (CBool b))
  | EInt n    => Some (UntypedConst (CInt (Z.of_N n)))
  | ENeg n    => Some (UntypedConst (CInt (- Z.of_N n)))
  | EString s => Some (UntypedConst (CString s))
  | EIntConvert target e' =>
      match const_info e' with
      | Some (UntypedConst (CInt z)) =>
          if integer_representableb target z
          then Some (TypedConst (TInteger target) (CInt z)) else None
      | Some (TypedConst (TInteger _) (CInt z)) =>
          if integer_representableb target z
          then Some (TypedConst (TInteger target) (CInt z)) else None
      | _ => None
      end
  end.

(** [const_info] carries EXACTLY the [const_value] of the expression (a conversion preserves the value). *)
Lemma const_info_value : forall e ci, const_info e = Some ci -> ci_const ci = const_value e.
Proof.
  induction e as [ b | n | n | s | it e IHe ]; intros ci H; simpl in H.
  - injection H as <-; reflexivity.
  - injection H as <-; reflexivity.
  - injection H as <-; reflexivity.
  - injection H as <-; reflexivity.
  - destruct (const_info e) as [ci'|] eqn:Hce; [| discriminate].
    destruct ci' as [ c' | t' c' ].
    + destruct c' as [ b | z | s ]; try discriminate.
      destruct (integer_representableb it z) eqn:Hrep; [| discriminate].
      injection H as <-; simpl.
      specialize (IHe (UntypedConst (CInt z)) eq_refl); simpl in IHe; exact IHe.
    + destruct t' as [| it' |]; try discriminate;
        destruct c' as [ b | z | s ]; try discriminate;
        destruct (integer_representableb it z) eqn:Hrep; try discriminate;
        injection H as <-; simpl;
        specialize (IHe (TypedConst (TInteger it') (CInt z)) eq_refl); simpl in IHe; exact IHe.
Qed.

(** successful analysis is deterministic (a function of the syntax). *)
Lemma const_info_deterministic : forall e ci1 ci2,
  const_info e = Some ci1 -> const_info e = Some ci2 -> ci1 = ci2.
Proof. intros e ci1 ci2 H1 H2; rewrite H1 in H2; injection H2 as <-; reflexivity. Qed.

(** a typed constant produced by the analyzer carries a REPRESENTABLE value at its type. *)
Lemma const_info_typed_representable : forall e t c,
  const_info e = Some (TypedConst t c) -> ConstRepresentable t c.
Proof.
  induction e as [ b | n | n | s | it e IHe ]; intros t c H; simpl in H; try discriminate.
  destruct (const_info e) as [ci'|] eqn:Hce; [| discriminate].
  destruct ci' as [ c' | t' c' ].
  - destruct c' as [ b | z | s ]; try discriminate.
    destruct (integer_representableb it z) eqn:Hrep; [| discriminate].
    injection H as <- <-. apply const_representableb_iff; simpl; exact Hrep.
  - destruct t' as [| it' |]; try discriminate;
      destruct c' as [ b | z | s ]; try discriminate;
      destruct (integer_representableb it z) eqn:Hrep; try discriminate;
      injection H as <- <-; apply const_representableb_iff; simpl; exact Hrep.
Qed.

(** an invalid inner conversion propagates: it cannot be revived by an outer conversion. *)
Lemma const_info_none_propagates : forall target e,
  const_info e = None -> const_info (EIntConvert target e) = None.
Proof. intros target e H; simpl; rewrite H; reflexivity. Qed.

(** ---- use-context resolution: one expression-use context and its per-type policy ---- *)
Inductive ExprUse : Type :=
| UsePrintlnArg.

(** the exhaustive per-type use policy.  A `println` argument accepts ALL current types — bool, every integer
    member, and string. *)
Inductive UseAllows : ExprUse -> GoType -> Prop :=
| UAPrintlnBool   : UseAllows UsePrintlnArg TBool
| UAPrintlnInt    : forall it, UseAllows UsePrintlnArg (TInteger it)
| UAPrintlnString : UseAllows UsePrintlnArg TString.

Definition use_allowsb (u : ExprUse) (t : GoType) : bool :=
  match u, t with
  | UsePrintlnArg, TBool       => true
  | UsePrintlnArg, TInteger _  => true
  | UsePrintlnArg, TString     => true
  end.

Lemma use_allowsb_iff : forall u t, use_allowsb u t = true <-> UseAllows u t.
Proof.
  intros [] [| it |]; simpl; split; intro H; try constructor; try reflexivity; inversion H.
Qed.

(** the declarative resolved typing of ONE expression in a use context: the expression analyzes to one
    constant-status [ci] (untyped or typed), whose RESOLVED type [t] is [info_type ci] (an untyped constant's
    default type, or a typed constant's OWN type — a typed constant is NOT defaulted), the context ALLOWS [t],
    and the carried constant is REPRESENTABLE as [t].  (No typed-expression AST, no copied "resolved
    expression" — this is a relation over the raw syntax, driven by [const_info].) *)
Inductive ResolveExpr : ExprUse -> GoExpr -> GoType -> Prop :=
| Resolve : forall u e ci t,
    const_info e = Some ci ->
    info_type ci = t ->
    UseAllows u t ->
    ConstRepresentable t (ci_const ci) ->
    ResolveExpr u e t.

Definition resolve_expr (u : ExprUse) (e : GoExpr) : option GoType :=
  match const_info e with
  | None => None
  | Some ci =>
      let t := info_type ci in
      if use_allowsb u t && const_representableb t (ci_const ci) then Some t else None
  end.

Lemma resolve_expr_sound : forall u e t, resolve_expr u e = Some t -> ResolveExpr u e t.
Proof.
  intros u e t; unfold resolve_expr.
  destruct (const_info e) as [ci|] eqn:Hci; [| intro H; discriminate].
  destruct (use_allowsb u (info_type ci) && const_representableb (info_type ci) (ci_const ci)) eqn:Hcond;
    [| intro H; discriminate].
  intro H; injection H as <-.
  apply Bool.andb_true_iff in Hcond as [Hu Hr].
  apply use_allowsb_iff in Hu; apply const_representableb_iff in Hr.
  econstructor; [ exact Hci | reflexivity | exact Hu | exact Hr ].
Qed.

Lemma resolve_expr_complete : forall u e t, ResolveExpr u e t -> resolve_expr u e = Some t.
Proof.
  intros u e t H; induction H as [ u0 e0 ci t0 Hci Htype Hu Hr ].
  apply use_allowsb_iff in Hu; apply const_representableb_iff in Hr.
  unfold resolve_expr; rewrite Hci, Htype, Hu, Hr; reflexivity.
Qed.

(** the resolved type, when it exists, is EXACTLY [info_type] of the analyzed constant — never the wrong type. *)
Lemma resolve_expr_info_type : forall u e t ci,
  const_info e = Some ci -> ResolveExpr u e t -> t = info_type ci.
Proof.
  intros u e t ci Hci H; apply resolve_expr_complete in H.
  unfold resolve_expr in H; rewrite Hci in H.
  destruct (use_allowsb u (info_type ci) && const_representableb (info_type ci) (ci_const ci));
    [ injection H as H'; symmetry; exact H' | discriminate ].
Qed.

Lemma resolve_expr_deterministic : forall u e t1 t2, ResolveExpr u e t1 -> ResolveExpr u e t2 -> t1 = t2.
Proof.
  intros u e t1 t2 H1 H2.
  apply resolve_expr_complete in H1; apply resolve_expr_complete in H2.
  rewrite H1 in H2; injection H2 as <-; reflexivity.
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

(** ---- whole-current-fragment typing judgments ---- *)

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

(** ---- a canonical integer literal for a (possibly negative) [Z], used by the generic boundary theorems ---- *)
Definition int_lit (z : Z) : GoExpr :=
  if Z.leb 0 z then EInt (Z.to_N z) else ENeg (Z.to_N (- z)).

Lemma const_value_int_lit : forall z, const_value (int_lit z) = CInt z.
Proof.
  intro z; unfold int_lit; destruct (Z.leb 0 z) eqn:E; simpl.
  - apply Z.leb_le in E; rewrite Z2N.id by exact E; reflexivity.
  - apply Z.leb_gt in E; rewrite Z2N.id by lia; f_equal; lia.
Qed.

Lemma const_info_int_lit : forall z, const_info (int_lit z) = Some (UntypedConst (CInt z)).
Proof.
  intro z; unfold int_lit; destruct (Z.leb 0 z) eqn:E; simpl.
  - apply Z.leb_le in E; rewrite Z2N.id by exact E; reflexivity.
  - apply Z.leb_gt in E; rewrite Z2N.id by lia; do 3 f_equal; lia.
Qed.

(** ---- generic boundary theorems: for EVERY integer type, its min/max convert-resolve and one past either
    endpoint does not (the exact-boundary coverage of §17, over all ten members at once) ---- *)
Lemma resolve_convert_representable : forall it z,
  IntRepresentable it z ->
  resolve_expr UsePrintlnArg (EIntConvert it (int_lit z)) = Some (TInteger it).
Proof.
  intros it z Hz. apply integer_representableb_spec in Hz.
  unfold resolve_expr; simpl; rewrite const_info_int_lit, Hz; simpl; rewrite Hz; reflexivity.
Qed.

Lemma resolve_convert_unrepresentable : forall it z,
  integer_representableb it z = false ->
  resolve_expr UsePrintlnArg (EIntConvert it (int_lit z)) = None.
Proof.
  intros it z Hz. unfold resolve_expr; simpl; rewrite const_info_int_lit, Hz; reflexivity.
Qed.

Theorem resolve_convert_min : forall it,
  resolve_expr UsePrintlnArg (EIntConvert it (int_lit (integer_min it))) = Some (TInteger it).
Proof. intro it; apply resolve_convert_representable, integer_min_representable. Qed.

Theorem resolve_convert_max : forall it,
  resolve_expr UsePrintlnArg (EIntConvert it (int_lit (integer_max it))) = Some (TInteger it).
Proof. intro it; apply resolve_convert_representable, integer_max_representable. Qed.

Theorem resolve_convert_below : forall it,
  resolve_expr UsePrintlnArg (EIntConvert it (int_lit (integer_min it - 1))) = None.
Proof. intro it; apply resolve_convert_unrepresentable, integer_min_pred_not_representable. Qed.

Theorem resolve_convert_above : forall it,
  resolve_expr UsePrintlnArg (EIntConvert it (int_lit (integer_max it + 1))) = None.
Proof. intro it; apply resolve_convert_unrepresentable, integer_max_succ_not_representable. Qed.

(** ---- concrete boundary / conversion / type-at-use fixtures (the grammar of typing, kernel-checked) ---- *)
Example res_bool_true  : resolve_expr UsePrintlnArg (EBool true)  = Some TBool. Proof. reflexivity. Qed.
Example res_bool_false : resolve_expr UsePrintlnArg (EBool false) = Some TBool. Proof. reflexivity. Qed.
Example res_int_zero   : resolve_expr UsePrintlnArg (EInt 0) = Some (TInteger IInt). Proof. reflexivity. Qed.
Example res_neg_zero   : resolve_expr UsePrintlnArg (ENeg 0) = Some (TInteger IInt). Proof. reflexivity. Qed.
Example const_zero_eq  : const_value (EInt 0) = const_value (ENeg 0). Proof. reflexivity. Qed.

(* a BARE integer literal defaults to [int]; the [int] boundaries resolve, one past does not. *)
Example res_int_default : resolve_expr UsePrintlnArg (EInt 42) = Some (TInteger IInt). Proof. reflexivity. Qed.
Example res_int_max : resolve_expr UsePrintlnArg (EInt (Z.to_N int_max))     = Some (TInteger IInt). Proof. reflexivity. Qed.
Example res_int_min : resolve_expr UsePrintlnArg (ENeg (Z.to_N (- int_min))) = Some (TInteger IInt). Proof. reflexivity. Qed.
Example res_over  : resolve_expr UsePrintlnArg (EInt (Z.to_N (int_max + 1)))   = None. Proof. reflexivity. Qed.
Example res_under : resolve_expr UsePrintlnArg (ENeg (Z.to_N (- int_min + 1))) = None. Proof. reflexivity. Qed.
(* bare 2^63 does NOT resolve (it does not fit the default [int]); as an arbitrary-precision constant it is
   still exact, and even above 2^64 the constant value is retained though it fits no integer type. *)
Example res_2p63_no_resolve : resolve_expr UsePrintlnArg (EInt 9223372036854775808) = None. Proof. reflexivity. Qed.
Example const_huge_exact : const_value (EInt 18446744073709551617) = CInt 18446744073709551617. Proof. reflexivity. Qed.
Example res_huge_no_resolve : resolve_expr UsePrintlnArg (EInt 18446744073709551617) = None. Proof. reflexivity. Qed.

(* explicit conversions — type at use, with a representability recheck at the destination. *)
Example res_uint64_2p63 : resolve_expr UsePrintlnArg (EIntConvert IUint64 (EInt 9223372036854775808)) = Some (TInteger IUint64).
Proof. reflexivity. Qed.
Example res_int64_2p63_reject : resolve_expr UsePrintlnArg (EIntConvert IInt64 (EInt 9223372036854775808)) = None.
Proof. reflexivity. Qed.
Example res_uint8_0   : resolve_expr UsePrintlnArg (EIntConvert IUint8 (EInt 0))   = Some (TInteger IUint8). Proof. reflexivity. Qed.
Example res_uint8_255 : resolve_expr UsePrintlnArg (EIntConvert IUint8 (EInt 255)) = Some (TInteger IUint8). Proof. reflexivity. Qed.
Example res_uint8_m1  : resolve_expr UsePrintlnArg (EIntConvert IUint8 (ENeg 1))   = None. Proof. reflexivity. Qed.
Example res_uint8_256 : resolve_expr UsePrintlnArg (EIntConvert IUint8 (EInt 256)) = None. Proof. reflexivity. Qed.
Example res_int8_min  : resolve_expr UsePrintlnArg (EIntConvert IInt8 (ENeg 128)) = Some (TInteger IInt8). Proof. reflexivity. Qed.
Example res_int8_max  : resolve_expr UsePrintlnArg (EIntConvert IInt8 (EInt 127)) = Some (TInteger IInt8). Proof. reflexivity. Qed.
Example res_int8_under : resolve_expr UsePrintlnArg (EIntConvert IInt8 (ENeg 129)) = None. Proof. reflexivity. Qed.
Example res_int8_over  : resolve_expr UsePrintlnArg (EIntConvert IInt8 (EInt 128)) = None. Proof. reflexivity. Qed.
Example res_uint64_max  : resolve_expr UsePrintlnArg (EIntConvert IUint64 (EInt 18446744073709551615)) = Some (TInteger IUint64). Proof. reflexivity. Qed.
Example res_uint64_over : resolve_expr UsePrintlnArg (EIntConvert IUint64 (EInt 18446744073709551616)) = None. Proof. reflexivity. Qed.

(* nested (transitive) conversions recheck the carried value at EACH layer. *)
Example const_int8_int16_127 :
  const_info (EIntConvert IInt8 (EIntConvert IInt16 (EInt 127))) = Some (TypedConst (TInteger IInt8) (CInt 127)).
Proof. reflexivity. Qed.
Example const_int8_int16_128_reject :
  const_info (EIntConvert IInt8 (EIntConvert IInt16 (EInt 128))) = None. Proof. reflexivity. Qed.
Example const_uint8_int_300_reject :
  const_info (EIntConvert IUint8 (EIntConvert IInt (EInt 300))) = None. Proof. reflexivity. Qed.
Example const_uint8_int_255_accept :
  const_info (EIntConvert IUint8 (EIntConvert IInt (EInt 255))) = Some (TypedConst (TInteger IUint8) (CInt 255)).
Proof. reflexivity. Qed.

(* a conversion of a bool/string constant is rejected. *)
Example conv_bool_reject : const_info (EIntConvert IInt8 (EBool true)) = None. Proof. reflexivity. Qed.
Example conv_str_reject  : const_info (EIntConvert IUint64 (EString "x")) = None. Proof. reflexivity. Qed.
Example res_conv_bool_reject : resolve_expr UsePrintlnArg (EIntConvert IInt8 (EBool true)) = None. Proof. reflexivity. Qed.
Example res_conv_str_reject  : resolve_expr UsePrintlnArg (EIntConvert IUint64 (EString "x")) = None. Proof. reflexivity. Qed.

(* type identity: [int]/[int64] and [uint]/[uint64] are DISTINCT static types. *)
Example tint_neq_tint64  : TInteger IInt  <> TInteger IInt64.
Proof. intro H; injection H as H; exact (IInt_neq_IInt64 H). Qed.
Example tuint_neq_tuint64 : TInteger IUint <> TInteger IUint64.
Proof. intro H; injection H as H; exact (IUint_neq_IUint64 H). Qed.

(* a mixed statement, empty println, empty file, and the empty PROGRAM are all typed. *)
Example stmt_mixed_typed : stmt_typedb (SPrintln [EBool true; EInt 42; ENeg 1]) = true. Proof. reflexivity. Qed.
Example stmt_conv_typed  : stmt_typedb (SPrintln [EIntConvert IInt8 (EInt 127); EIntConvert IUint64 (EInt 18446744073709551615)]) = true. Proof. reflexivity. Qed.
Example stmt_empty_typed : stmt_typedb (SPrintln []) = true. Proof. reflexivity. Qed.
Example file_empty_typed : file_typedb [] = true. Proof. reflexivity. Qed.
Example empty_program_typed : forall ms, program_typedb (empty_program ms) = true. Proof. intro ms; reflexivity. Qed.

(* an out-of-range argument (bare or via conversion) fails typing at statement AND file level. *)
Example over_stmt_untyped : stmt_typedb (SPrintln [EInt (Z.to_N (int_max + 1))]) = false. Proof. reflexivity. Qed.
Example conv_over_file_untyped : file_typedb [ DMain [ SPrintln [EIntConvert IInt8 (EInt 128)] ] ] = false. Proof. reflexivity. Qed.

(* wrong-type representability is false ... *)
Example bool_not_int : const_representableb (TInteger IInt) (CBool true) = false. Proof. reflexivity. Qed.
Example int_not_bool : const_representableb TBool (CInt 3) = false. Proof. reflexivity. Qed.
(* ... and at the RESOLUTION level a boolean does NOT resolve as an integer, nor an integer as bool. *)
Example bool_not_resolve_int : ~ ResolveExpr UsePrintlnArg (EBool true) (TInteger IInt).
Proof. intro H; apply resolve_expr_complete in H; cbn in H; discriminate H. Qed.
Example int_not_resolve_bool : ~ ResolveExpr UsePrintlnArg (EInt 3) TBool.
Proof. intro H; apply resolve_expr_complete in H; cbn in H; discriminate H. Qed.

(* ---- strings: every string literal resolves to [TString], for ARBITRARY finite byte sequences. *)
Example res_str_empty : resolve_expr UsePrintlnArg (EString "") = Some TString. Proof. reflexivity. Qed.
Example res_str_ascii : resolve_expr UsePrintlnArg (EString "hello") = Some TString. Proof. reflexivity. Qed.
Example res_str_bytes :
  resolve_expr UsePrintlnArg
    (EString (String (ascii_of_nat 0) (String (ascii_of_nat 127)
             (String (ascii_of_nat 128) (String (ascii_of_nat 255) EmptyString)))))
  = Some TString. Proof. reflexivity. Qed.
Example str_default_type : const_default_type (CString "abc") = TString. Proof. reflexivity. Qed.
Lemma str_representable : forall s, ConstRepresentable TString (CString s).
Proof. intro s; constructor. Qed.
Lemma str_representableb : forall s, const_representableb TString (CString s) = true.
Proof. reflexivity. Qed.
Example stmt_mixed_str_typed : stmt_typedb (SPrintln [EBool true; EInt 42; EString "hello"]) = true. Proof. reflexivity. Qed.
Example cstr_not_int  : const_representableb (TInteger IInt) (CString "x") = false. Proof. reflexivity. Qed.
Example bool_not_str  : const_representableb TString (CBool true)  = false. Proof. reflexivity. Qed.
Example int_not_str   : const_representableb TString (CInt 3)      = false. Proof. reflexivity. Qed.
Example str_not_resolve_int : ~ ResolveExpr UsePrintlnArg (EString "x") (TInteger IInt).
Proof. intro H; apply resolve_expr_complete in H; cbn in H; discriminate H. Qed.
