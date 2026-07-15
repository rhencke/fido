(** ============================================================================
    GoTypes — the ONE Go type-system authority for the current bool/integer/string fragment.  It is EVIDENCE
    over the ONE raw [GoAST], never a second (typed) AST: raw [GoExpr] stays untyped syntax, and typing is a
    judgment over that same syntax.

    The permanent type universe here is [TBool], the INTEGER FAMILY [TInteger it] over the one [IntegerType]
    descriptor (ten live Go integer types), the FLOAT FAMILY [TFloat ft] over the one [FloatType] descriptor
    (float32/float64), and [TString].  Each landed TOGETHER with its syntax and complete semantics (static
    typing + representability + compiler facts + safety + rendering + tests + docs); there are no placeholder
    constructors ahead of the syntax that needs them.

    The foundational distinction (Go's own): a raw literal denotes an EXACT UNTYPED CONSTANT value
    ([GoConst] — ints arbitrary-precision [Z], floats an exact rational [FloatConst], strings exact byte
    sequences), independent of any width.  An explicit conversion routes through the ONE [convert_const]
    authority: an integer conversion [EIntConvert it e] does NOT change the value (range-checked at [it]); a
    float conversion [EFloatConvert ft e] ROUNDS the value ONCE at the destination format [ft].  In a USE
    CONTEXT that requires a typed value, an UNTYPED constant is given a DEFAULT TYPE (int constants default to
    [TInteger IInt], floats to [TFloat F64]) and REPRESENTABILITY is checked, while a TYPED constant RETAINS
    its type and value (it is NOT defaulted again, and — already validated by [convert_const] — is TRUSTED,
    not re-checked).  This is the single authority every later feature (assignments, variables, arguments,
    arithmetic, more numeric types) builds on.
    ============================================================================ *)
From Stdlib Require Import NArith ZArith List Bool String Ascii Lia.
From Fido Require Import Ints Floats GoAST.
Import ListNotations.
Open Scope Z_scope.

(** The semantic value of a Go string is an EXACT BYTE SEQUENCE.  We use Rocq [string] directly (a sequence
    of [ascii] bytes) as that value, with exactly that meaning — it is NOT Unicode scalar values / code
    points / UTF-8-decoded characters / source-literal spelling (the canonical source spelling is a separate
    proved encoding in [GoRender]).  No wrapper and no invariant are needed: every finite byte sequence is a
    valid Go string value in represented scope (no length limit, no well-formedness side condition). *)

(** ---- the one type universe: bool, the integer FAMILY, the float FAMILY, and string ---- *)
Inductive GoType : Type :=
| TBool
| TInteger : IntegerType -> GoType
| TFloat   : FloatType -> GoType
| TString.

Definition gotype_eqb (a b : GoType) : bool :=
  match a, b with
  | TBool, TBool => true
  | TInteger it1, TInteger it2 => integer_type_eqb it1 it2
  | TFloat ft1, TFloat ft2 => float_type_eqb ft1 ft2
  | TString, TString => true
  | _, _ => false
  end.

Lemma gotype_eqb_eq : forall a b, gotype_eqb a b = true <-> a = b.
Proof.
  intros [| it1 | ft1 |] [| it2 | ft2 |]; simpl; split; intro H; try reflexivity; try discriminate.
  - apply integer_type_eqb_eq in H; subst; reflexivity.
  - injection H as Heq; subst; apply integer_type_eqb_eq; reflexivity.
  - apply float_type_eqb_eq in H; subst; reflexivity.
  - injection H as Heq; subst; apply float_type_eqb_eq; reflexivity.
Qed.

(** ---- exact untyped constant values of the current raw literals ---- *)
Inductive GoConst : Type :=
| CBool   : bool -> GoConst
| CInt    : Z -> GoConst
| CFloat  : FloatConst -> GoConst
| CString : string -> GoConst.

(** the exact integer VALUE of a floating constant, if it denotes one exactly (a fractional constant has
    none) — the sole float->integer bridge, used by [convert_const]. *)
Definition fc_to_int (q : FloatConst) : option Z :=
  if Z.eqb (Z.rem (fc_num q) (Zpos (fc_den q))) 0
  then Some (fc_num q / Zpos (fc_den q)) else None.

(** decidable equality of float formats — reduces to [left eq_refl] on equal concrete formats, so a same-format
    conversion computes to the identity (see [same_ft_identity]). *)
Definition float_type_eq_dec (a b : FloatType) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

(** ============================================================================
    §2-3 INTRINSIC TYPED CONSTANTS — a genuinely [GoType]-indexed family.  A typed constant cannot exist
    without the structural evidence its type requires: an integer carries a proof it is representable at its
    type, a float carries a [TypedFloatConst] (exact rounded rational + canonical runtime value + coherence).
    The loose [(GoType, GoConst)] pair is GONE — a mismatched or out-of-range typed constant is
    UNREPRESENTABLE, not merely rejected, and no [ci_ok := True] convention is needed.
    ============================================================================ *)
Inductive TypedConst : GoType -> Type :=
| TCBool    : bool -> TypedConst TBool
| TCInteger : forall (it : IntegerType) (z : Z), integer_representableb it z = true -> TypedConst (TInteger it)
| TCFloat   : forall (ft : FloatType), TypedFloatConst ft -> TypedConst (TFloat ft)
| TCString  : string -> TypedConst TString.

(** §3 exact-value erasure: forget the type, keep the exact mathematical constant.  It reads the stored data —
    it NEVER inspects source syntax and NEVER re-rounds a float (a float's exact value is the already-rounded
    [tfc_exact]). *)
Definition typed_const_exact {t : GoType} (tc : TypedConst t) : GoConst :=
  match tc with
  | TCBool b        => CBool b
  | TCInteger _ z _ => CInt z
  | TCFloat _ tfc   => CFloat (tfc_exact tfc)
  | TCString s      => CString s
  end.

(** a decidable bool guard carrying its own proof — avoids a dependent [if]-convoy in [typed_integer_of_Z]. *)
Definition bool_true_dec (b : bool) : {b = true} + {b = false} :=
  match b with true => left eq_refl | false => right eq_refl end.

(** construct a typed integer constant at [it] iff [z] is representable there (§13.A) — carries the range proof. *)
Definition typed_integer_of_Z (it : IntegerType) (z : Z) : option (TypedConst (TInteger it)) :=
  match bool_true_dec (integer_representableb it z) with
  | left H  => Some (TCInteger it z H)
  | right _ => None
  end.

(** construct a typed float constant at [ft] by the ONE [round_typed_float] authority (§13.C/D). *)
Definition typed_float_of_const (ft : FloatType) (q : FloatConst) : option (TypedConst (TFloat ft)) :=
  option_map (TCFloat ft) (round_typed_float ft q).

(** the ONE constant interpretation of the raw expressions — PARTIAL, because an explicit conversion may be
    compiler-invalid (out-of-range / fractional-to-integer / float overflow) and thus denote NO value.  A raw
    literal is an EXACT value (a bare float is its EXACT rational, unrounded — no range check here); an
    explicit conversion routes through the ONE [convert_const] authority (integer conversions preserve the
    value when it fits; float conversions round ONCE at the destination). *)
Fixpoint const_value (e : GoExpr) : option GoConst :=
  match e with
  | EBool b            => Some (CBool b)
  | EInt n             => Some (CInt (Z.of_N n))
  | ENeg n             => Some (CInt (- Z.of_N n))
  | EString s          => Some (CString s)
  | EFloat d           => Some (CFloat (decimal_value d))
  | EIntConvert it e'  =>
      match const_value e' with
      | Some (CInt z)   => if integer_representableb it z then Some (CInt z) else None
      | Some (CFloat q) => match fc_to_int q with
                           | Some z => if integer_representableb it z then Some (CInt z) else None
                           | None => None end
      | _ => None
      end
  | EFloatConvert ft e' =>
      match const_value e' with
      | Some (CInt z)   => option_map CFloat (round_float_const ft (fc_of_Z z))
      | Some (CFloat q) => option_map CFloat (round_float_const ft q)
      | _ => None
      end
  end.

(** determinism is structural (a function of the syntax). *)
Lemma const_value_deterministic : forall e c1 c2,
  const_value e = c1 -> const_value e = c2 -> c1 = c2.
Proof. intros e c1 c2 <- <-; reflexivity. Qed.

(** [EInt 0] and [ENeg 0] denote the SAME untyped constant (signed zero is one value). *)
Lemma const_value_zero_sign : const_value (EInt 0) = const_value (ENeg 0).
Proof. reflexivity. Qed.

(** the DEFAULT type — the type chosen for an UNTYPED constant in a context that requires a typed value.  It
    is NOT a property of the raw literal (the literal stays untyped); an int constant defaults to the
    platform [int] = [TInteger IInt], a floating constant to [float64] = [TFloat F64]. *)
Definition const_default_type (c : GoConst) : GoType :=
  match c with
  | CBool _   => TBool
  | CInt _    => TInteger IInt
  | CFloat _  => TFloat F64
  | CString _ => TString
  end.

Lemma const_default_type_bool : forall b, const_default_type (CBool b) = TBool.
Proof. reflexivity. Qed.
Lemma const_default_type_int : forall z, const_default_type (CInt z) = TInteger IInt.
Proof. reflexivity. Qed.
Lemma const_default_type_float : forall q, const_default_type (CFloat q) = TFloat F64.
Proof. reflexivity. Qed.
Lemma const_default_type_string : forall s, const_default_type (CString s) = TString.
Proof. reflexivity. Qed.

(** ---- representability: one type-directed authority (the SINGLE integer-range decision, per member) ---- *)
Inductive ConstRepresentable : GoType -> GoConst -> Prop :=
| RBool   : forall b, ConstRepresentable TBool (CBool b)
| RInt    : forall it z, IntRepresentable it z -> ConstRepresentable (TInteger it) (CInt z)
| RFloat  : forall ft q, FloatConstRepresentable ft q -> ConstRepresentable (TFloat ft) (CFloat q)
| RString : forall s, ConstRepresentable TString (CString s).

(** every string constant is representable as [TString] (no length limit); a [CInt z] is representable as
    [TInteger it] iff [z] fits [it]; a [CFloat q] is representable as [TFloat ft] iff it rounds at [ft]
    without overflow (the ONE [Floats] authority — no second float-overflow checker); cross-kind [false]. *)
Definition const_representableb (t : GoType) (c : GoConst) : bool :=
  match t, c with
  | TBool,       CBool _   => true
  | TInteger it, CInt z    => integer_representableb it z
  | TFloat ft,   CFloat q  => float_representableb ft q
  | TString,     CString _ => true
  | _, _ => false
  end.

Lemma const_representableb_iff : forall t c, const_representableb t c = true <-> ConstRepresentable t c.
Proof.
  intros t c; split.
  - destruct t as [| it | ft |]; destruct c as [ b | z | q | s ]; simpl; intro H; try discriminate.
    + constructor.
    + apply integer_representableb_spec in H; constructor; exact H.
    + apply float_representableb_spec in H; constructor; exact H.
    + constructor.
  - intro H; destruct H as [ b | it z Hr | ft q Hr | s ]; simpl.
    + reflexivity.
    + apply integer_representableb_spec; exact Hr.
    + apply float_representableb_spec; exact Hr.
    + reflexivity.
Qed.

(** ============================================================================
    §9-11 one constant-status analysis over the same raw AST (Go's own lattice): a raw literal is an UNTYPED
    constant ([CIUntyped]); an explicit conversion is a TYPED constant ([CITyped] carrying the INTRINSIC
    [TypedConst] — its validity is in its type, so no [ci_ok] convention).  A conversion of a bool/string
    constant is unrepresentable; an invalid inner conversion returns [None] and cannot be revived (the value
    is checked at EVERY layer).
    ============================================================================ *)
Inductive ConstInfo : Type :=
| CIUntyped : GoConst -> ConstInfo
| CITyped   : forall (t : GoType), TypedConst t -> ConstInfo.

(** §10 exact-value projection: an untyped constant is its own exact value; a typed constant's is its
    intrinsic [typed_const_exact].  There is no "type of an untyped constant" here — an untyped status has no
    assigned type yet (a DEFAULT is a separate query, [default_const]). *)
Definition const_info_exact (ci : ConstInfo) : GoConst :=
  match ci with CIUntyped c => c | CITyped _ tc => typed_const_exact tc end.

(** §11 the packed typed result of resolving ONE expression: existential semantic evidence, NOT a typed AST
    and NOT a copy of the raw expression. *)
Inductive ResolvedConst : Type :=
| pack_resolved : forall (t : GoType), TypedConst t -> ResolvedConst.

Definition resolved_const_type (rc : ResolvedConst) : GoType :=
  match rc with pack_resolved t _ => t end.
Definition resolved_const_exact (rc : ResolvedConst) : GoConst :=
  match rc with pack_resolved _ tc => typed_const_exact tc end.

(** §13.E same-format float identity: converting a typed float constant to its OWN format returns the existing
    [TypedFloatConst] unchanged (no reround) — the transport is trivial because [float_type_eq_dec ft ft]
    reduces to [left eq_refl]. *)
Definition same_ft_identity (ft : FloatType) (ci : ConstInfo) : option (TypedConst (TFloat ft)) :=
  match ci with
  | CITyped (TFloat ft') tc =>
      match float_type_eq_dec ft' ft with
      | left Heq => Some (eq_rect (TFloat ft') (fun T => TypedConst T) tc (TFloat ft) (f_equal TFloat Heq))
      | right _  => None
      end
  | _ => None
  end.

(** §13.C/D/E/F float-target conversion: same-format returns the identity; otherwise round the exact source
    value ONCE at the destination (a different-format typed source rounds its [tfc_exact], preserving the
    explicit conversion boundary — this is exactly the double-rounding scar). *)
Definition convert_to_float (ft : FloatType) (ci : ConstInfo) : option (TypedConst (TFloat ft)) :=
  match same_ft_identity ft ci with
  | Some tc => Some tc
  | None =>
      match const_info_exact ci with
      | CInt z   => typed_float_of_const ft (fc_of_Z z)
      | CFloat q => typed_float_of_const ft q
      | _        => None
      end
  end.

(** §12-13 the ONE target-directed constant-conversion authority: it CONSUMES the source constant status and
    produces an INTRINSIC typed constant at the destination.  Integer target: the exact source (integer, or a
    float's integral exact value) must be representable.  Float target: [convert_to_float].  bool/string
    target: unrepresentable. *)
Definition convert_const (target : GoType) (ci : ConstInfo) : option (TypedConst target) :=
  match target with
  | TBool    => None
  | TString  => None
  | TInteger it =>
      match const_info_exact ci with
      | CInt z   => typed_integer_of_Z it z
      | CFloat q => match fc_to_int q with
                    | Some z => typed_integer_of_Z it z
                    | None => None end
      | _ => None
      end
  | TFloat ft => convert_to_float ft ci
  end.

Fixpoint const_info (e : GoExpr) : option ConstInfo :=
  match e with
  | EBool b   => Some (CIUntyped (CBool b))
  | EInt n    => Some (CIUntyped (CInt (Z.of_N n)))
  | ENeg n    => Some (CIUntyped (CInt (- Z.of_N n)))
  | EString s => Some (CIUntyped (CString s))
  | EFloat d  => Some (CIUntyped (CFloat (decimal_value d)))
  | EIntConvert target e' =>
      match const_info e' with
      | Some ci => option_map (CITyped (TInteger target)) (convert_const (TInteger target) ci)
      | None => None
      end
  | EFloatConvert target e' =>
      match const_info e' with
      | Some ci => option_map (CITyped (TFloat target)) (convert_const (TFloat target) ci)
      | None => None
      end
  end.

(** §16 defaulting: an UNTYPED constant becomes a validated typed constant in a use context — bool/string
    always; an int defaults to platform [int] iff representable; a bare float performs its ONE F64 rounding
    (via [round_typed_float]).  A bare overflowing float has no default typed constant. *)
Definition default_const (c : GoConst) : option ResolvedConst :=
  match c with
  | CBool b   => Some (pack_resolved TBool (TCBool b))
  | CInt z    => option_map (pack_resolved (TInteger IInt)) (typed_integer_of_Z IInt z)
  | CFloat q  => option_map (pack_resolved (TFloat F64)) (typed_float_of_const F64 q)
  | CString s => Some (pack_resolved TString (TCString s))
  end.

(** §17 resolve a constant status to a validated typed constant: an untyped status defaults; a typed status is
    packed unchanged (its validity is intrinsic — no [ci_ok], no "typed constants are trusted" branch). *)
Definition resolve_const_info (ci : ConstInfo) : option ResolvedConst :=
  match ci with
  | CIUntyped c  => default_const c
  | CITyped t tc => Some (pack_resolved t tc)
  end.

(** successful analysis is deterministic (a function of the syntax). *)
Lemma const_info_deterministic : forall e ci1 ci2,
  const_info e = Some ci1 -> const_info e = Some ci2 -> ci1 = ci2.
Proof. intros e ci1 ci2 H1 H2; rewrite H1 in H2; injection H2 as <-; reflexivity. Qed.

(** an invalid inner conversion propagates: it cannot be revived by an outer conversion (either kind). *)
Lemma const_info_int_none : forall target e,
  const_info e = None -> const_info (EIntConvert target e) = None.
Proof. intros target e H; simpl; rewrite H; reflexivity. Qed.
Lemma const_info_float_none : forall target e,
  const_info e = None -> const_info (EFloatConvert target e) = None.
Proof. intros target e H; simpl; rewrite H; reflexivity. Qed.

(** ---- use-context resolution: one expression-use context and its per-type policy ---- *)
Inductive ExprUse : Type :=
| UsePrintlnArg.

(** the exhaustive per-type use policy.  A `println` argument accepts ALL current types — bool, every integer
    member, and string. *)
Inductive UseAllows : ExprUse -> GoType -> Prop :=
| UAPrintlnBool   : UseAllows UsePrintlnArg TBool
| UAPrintlnInt    : forall it, UseAllows UsePrintlnArg (TInteger it)
| UAPrintlnFloat  : forall ft, UseAllows UsePrintlnArg (TFloat ft)
| UAPrintlnString : UseAllows UsePrintlnArg TString.

Definition use_allowsb (u : ExprUse) (t : GoType) : bool :=
  match u, t with
  | UsePrintlnArg, TBool       => true
  | UsePrintlnArg, TInteger _  => true
  | UsePrintlnArg, TFloat _    => true
  | UsePrintlnArg, TString     => true
  end.

Lemma use_allowsb_iff : forall u t, use_allowsb u t = true <-> UseAllows u t.
Proof.
  intros [] [| it | ft |]; simpl; split; intro H; try constructor; try reflexivity; inversion H.
Qed.

(** §18 the declarative resolved typing of ONE expression in a use context: the expression analyzes to a
    constant-status [ci], which RESOLVES ([resolve_const_info]) to a validated typed constant [rc] — a bare
    literal defaults, a typed constant packs unchanged — whose INTRINSIC type [resolved_const_type rc] the
    context ALLOWS.  There is NO [ci_ok]: validity is carried by the typed constant itself.  No
    typed-expression AST, no copied "resolved expression" — a relation over the raw syntax driven by
    [const_info]/[resolve_const_info]. *)
Inductive ResolveExpr : ExprUse -> GoExpr -> GoType -> Prop :=
| Resolve : forall u e ci rc,
    const_info e = Some ci ->
    resolve_const_info ci = Some rc ->
    UseAllows u (resolved_const_type rc) ->
    ResolveExpr u e (resolved_const_type rc).

(** the resolution that EXPOSES the [ResolvedConst] witness (evaluation and the root theorem consume this). *)
Definition resolve_expr_const (u : ExprUse) (e : GoExpr) : option ResolvedConst :=
  match const_info e with
  | None => None
  | Some ci =>
      match resolve_const_info ci with
      | None => None
      | Some rc => if use_allowsb u (resolved_const_type rc) then Some rc else None
      end
  end.

Definition resolve_expr (u : ExprUse) (e : GoExpr) : option GoType :=
  option_map resolved_const_type (resolve_expr_const u e).

Lemma resolve_expr_const_sound : forall u e rc,
  resolve_expr_const u e = Some rc ->
  exists ci, const_info e = Some ci /\ resolve_const_info ci = Some rc
             /\ UseAllows u (resolved_const_type rc).
Proof.
  intros u e rc H; unfold resolve_expr_const in H.
  destruct (const_info e) as [ci|] eqn:Hci; [| discriminate].
  destruct (resolve_const_info ci) as [rc'|] eqn:Hrc; [| discriminate].
  destruct (use_allowsb u (resolved_const_type rc')) eqn:Hua; [| discriminate].
  injection H as ->. exists ci; split; [ reflexivity | split; [ exact Hrc | apply use_allowsb_iff; exact Hua ] ].
Qed.

Lemma resolve_expr_sound : forall u e t, resolve_expr u e = Some t -> ResolveExpr u e t.
Proof.
  intros u e t H. unfold resolve_expr in H.
  destruct (resolve_expr_const u e) as [rc|] eqn:Hrc; cbn [option_map] in H; [| discriminate].
  injection H as <-. destruct (resolve_expr_const_sound u e rc Hrc) as [ci [Hci [Hri Hua]]].
  eapply Resolve; [ exact Hci | exact Hri | exact Hua ].
Qed.

Lemma resolve_expr_complete : forall u e t, ResolveExpr u e t -> resolve_expr u e = Some t.
Proof.
  intros u e t H; destruct H as [ u0 e0 ci rc Hci Hrc Hua ].
  apply use_allowsb_iff in Hua.
  unfold resolve_expr, resolve_expr_const; rewrite Hci, Hrc, Hua; reflexivity.
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

Lemma const_value_int_lit : forall z, const_value (int_lit z) = Some (CInt z).
Proof.
  intro z; unfold int_lit; destruct (Z.leb 0 z) eqn:E; cbn [const_value].
  - apply Z.leb_le in E; rewrite Z2N.id by exact E; reflexivity.
  - apply Z.leb_gt in E; rewrite Z2N.id by lia; do 2 f_equal; lia.
Qed.

Lemma const_info_int_lit : forall z, const_info (int_lit z) = Some (CIUntyped (CInt z)).
Proof.
  intro z; unfold int_lit; destruct (Z.leb 0 z) eqn:E; cbn [const_info].
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
  unfold resolve_expr, resolve_expr_const.
  cbn [const_info]. rewrite const_info_int_lit.
  cbn [option_map convert_const const_info_exact].
  unfold typed_integer_of_Z.
  destruct (bool_true_dec (integer_representableb it z)) as [H'|H'].
  - reflexivity.
  - congruence.
Qed.

Lemma resolve_convert_unrepresentable : forall it z,
  integer_representableb it z = false ->
  resolve_expr UsePrintlnArg (EIntConvert it (int_lit z)) = None.
Proof.
  intros it z Hz.
  unfold resolve_expr, resolve_expr_const.
  cbn [const_info]. rewrite const_info_int_lit.
  cbn [option_map convert_const const_info_exact].
  unfold typed_integer_of_Z.
  destruct (bool_true_dec (integer_representableb it z)) as [H'|H'].
  - congruence.
  - reflexivity.
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
Example const_huge_exact : const_value (EInt 18446744073709551617) = Some (CInt 18446744073709551617). Proof. reflexivity. Qed.
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
  const_info (EIntConvert IInt8 (EIntConvert IInt16 (EInt 127)))
    = Some (CITyped (TInteger IInt8) (TCInteger IInt8 127 eq_refl)).
Proof. reflexivity. Qed.
Example const_int8_int16_128_reject :
  const_info (EIntConvert IInt8 (EIntConvert IInt16 (EInt 128))) = None. Proof. reflexivity. Qed.
Example const_uint8_int_300_reject :
  const_info (EIntConvert IUint8 (EIntConvert IInt (EInt 300))) = None. Proof. reflexivity. Qed.
Example const_uint8_int_255_accept :
  const_info (EIntConvert IUint8 (EIntConvert IInt (EInt 255)))
    = Some (CITyped (TInteger IUint8) (TCInteger IUint8 255 eq_refl)).
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

(* ---- floats: bare literal defaults to float64; explicit conversions type at use; cross-family and
   float->integer constant conversions match Go's constant rules (§22/§34/§35). ---- *)
Definition d_15em1 : DecimalFloat := mkDecimal 15 (-1) eq_refl.   (* 1.5 *)
Definition d_3    : DecimalFloat := mkDecimal 3 0 eq_refl.        (* 3.0 *)
Definition d_35em1 : DecimalFloat := mkDecimal 35 (-1) eq_refl.   (* 3.5 *)
Definition d_128  : DecimalFloat := mkDecimal 128 0 eq_refl.      (* 128.0 *)
Definition d_m1   : DecimalFloat := mkDecimal (-1) 0 eq_refl.     (* -1.0 *)
Definition d_scar : DecimalFloat := mkDecimal 2305843146652647425 0 eq_refl.

Example res_float_default : resolve_expr UsePrintlnArg (EFloat d_15em1) = Some (TFloat F64). Proof. reflexivity. Qed.
Example res_float32_conv  : resolve_expr UsePrintlnArg (EFloatConvert F32 (EFloat d_15em1)) = Some (TFloat F32). Proof. reflexivity. Qed.
Example res_float64_conv  : resolve_expr UsePrintlnArg (EFloatConvert F64 (EFloat d_15em1)) = Some (TFloat F64). Proof. reflexivity. Qed.
Example float_default_type : const_default_type (CFloat fc_zero) = TFloat F64. Proof. reflexivity. Qed.

(* §34 float->integer CONSTANT conversions: integral value + range required; a fraction / overflow rejects. *)
Example res_int_of_3_0     : resolve_expr UsePrintlnArg (EIntConvert IInt  (EFloat d_3))    = Some (TInteger IInt).  Proof. reflexivity. Qed.
Example res_int_of_3_5_rej : resolve_expr UsePrintlnArg (EIntConvert IInt  (EFloat d_35em1)) = None.                Proof. reflexivity. Qed.
Example res_int8_127_0     : resolve_expr UsePrintlnArg (EIntConvert IInt8 (EFloat (mkDecimal 127 0 eq_refl))) = Some (TInteger IInt8). Proof. reflexivity. Qed.
Example res_int8_128_0_rej : resolve_expr UsePrintlnArg (EIntConvert IInt8 (EFloat d_128))  = None.                Proof. reflexivity. Qed.
Example res_uint8_m1_0_rej : resolve_expr UsePrintlnArg (EIntConvert IUint8 (EFloat d_m1))  = None.                Proof. reflexivity. Qed.

(* §35 wrong-type conversions reject; a float typed constant and float64 are DISTINCT static types. *)
Example res_float32_true_rej : resolve_expr UsePrintlnArg (EFloatConvert F32 (EBool true))   = None. Proof. reflexivity. Qed.
Example res_float64_str_rej  : resolve_expr UsePrintlnArg (EFloatConvert F64 (EString "x"))  = None. Proof. reflexivity. Qed.
Example res_int_of_true_rej  : resolve_expr UsePrintlnArg (EIntConvert IInt (EBool true))    = None. Proof. reflexivity. Qed.
Example tfloat32_neq_tfloat64 : TFloat F32 <> TFloat F64.
Proof. intro H; injection H as H; discriminate. Qed.

(* ★§30 the DOUBLE-ROUNDING SCAR at the conversion-syntax level: direct float32(big) and nested
   float32(float64(big)) analyze to typed float32 constants with DIFFERENT exact rounded values. *)
Example const_scar_direct :
  option_map const_info_exact (const_info (EFloatConvert F32 (EFloat d_scar)))
    = Some (CFloat (fc_of_Z 2305843284091600896)).
Proof. vm_compute. reflexivity. Qed.
Example const_scar_nested :
  option_map const_info_exact (const_info (EFloatConvert F32 (EFloatConvert F64 (EFloat d_scar))))
    = Some (CFloat (fc_of_Z 2305843009213693952)).
Proof. vm_compute. reflexivity. Qed.
Example const_scar_direct_differs_nested :
  option_map const_info_exact (const_info (EFloatConvert F32 (EFloat d_scar)))
    <> option_map const_info_exact (const_info (EFloatConvert F32 (EFloatConvert F64 (EFloat d_scar)))).
Proof. rewrite const_scar_direct, const_scar_nested; discriminate. Qed.

(* a mixed float statement types; a default-overflowing bare float does NOT type. *)
Example stmt_float_mixed : stmt_typedb (SPrintln [EBool true; EFloat d_15em1; EFloatConvert F32 (EFloat d_3)]) = true. Proof. reflexivity. Qed.
Example stmt_float_overflow_untyped :
  stmt_typedb (SPrintln [EFloat (mkDecimal 1 4096 eq_refl)]) = false.   (* 1e4096 overflows default float64 *)
Proof. vm_compute. reflexivity. Qed.
