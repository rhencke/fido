(** Typing — the ONE Go type-system authority for the current bool/integer/float/complex/string fragment.  It
    is EVIDENCE over the ONE raw [Syntax], never a second (typed) AST: raw [Syntax.Expr] stays untyped syntax, and
    typing is a judgment over that same syntax.

    The permanent type universe here is [BoolType], the INTEGER FAMILY [IntegerType it] over the one [Integer.Kind]
    descriptor (ten live Go integer types), the FLOAT FAMILY [FloatType ft] over the one [Float.Kind] descriptor
    (float32/float64), the COMPLEX FAMILY [ComplexType ct] over the one [Complex.Kind] descriptor (complex64/
    complex128, whose real/imaginary components are float32/float64 via [Complex.component_kind]), and
    [StringType].  Each landed TOGETHER with its syntax and complete semantics (static typing + representability +
    compiler facts + safety + rendering + tests + docs); there are no placeholder constructors ahead of the
    syntax that needs them.

    The foundational distinction (Go's own): a raw literal denotes an EXACT UNTYPED CONSTANT value
    ([Constant] — ints arbitrary-precision [Z], floats an exact rational [Float.Constant], a complex an exact PAIR
    of rational components [Complex.Constant], strings exact byte sequences), independent of any width.  An
    explicit conversion [Syntax.Convert ts e] names a SOURCE type ([ts]); the semantic target [SemanticType] is the
    compiler-owned resolution [rt ts] (§7 — the resolver lives in [Admissible], never here), and the value
    routes through the ONE [convert_constant] authority at that target: an integer target does NOT change the
    value (range-checked at the integer type); a float target ROUNDS the value ONCE at the destination format;
    a complex target rounds EACH component ONCE at the format's component precision.  In a USE CONTEXT that
    requires a typed value, an UNTYPED
    constant is given a DEFAULT TYPE (int constants default to [IntegerType Integer.Int], floats to [FloatType F64], complex
    to [ComplexType C128]) and REPRESENTABILITY is checked (for a numeric target BY the SAME [convert_constant], so
    representability and conversion never disagree), while a TYPED constant RETAINS its type and value (it is
    NOT defaulted again; its validity is INTRINSIC — carried by the dependently-typed [TypedConstant]
    constructor's own proof — so there is nothing to re-check).  This is the single authority every later
    feature (assignments, variables, arguments, arithmetic, more numeric types) builds on. *)
From Stdlib Require Import NArith ZArith List Bool String Ascii Lia.
From Stdlib Require Import SetoidList Permutation.
From Fido Require Import Integer Float Complex Syntax.
Import ListNotations.
Open Scope Z_scope.

(** The semantic value of a Go string is an EXACT BYTE SEQUENCE.  We use Rocq [string] directly (a sequence
    of [ascii] bytes) as that value, with exactly that meaning — it is NOT Unicode scalar values / code
    points / UTF-8-decoded characters / source-literal spelling (the canonical source spelling is a separate
    proved encoding in [Render]).  No wrapper and no invariant are needed: every finite byte sequence is a
    valid Go string value in represented scope (no length limit, no well-formedness side condition). *)

(** ---- the one type universe: bool, the integer FAMILY, the float FAMILY, the complex FAMILY, and string ---- *)
Inductive SemanticType : Type :=
| BoolType
| IntegerType : Integer.Kind -> SemanticType
| FloatType   : Float.Kind -> SemanticType
| ComplexType : Complex.Kind -> SemanticType
| StringType.

Definition type_equalb (a b : SemanticType) : bool :=
  match a, b with
  | BoolType, BoolType => true
  | IntegerType it1, IntegerType it2 => Integer.equalb it1 it2
  | FloatType ft1, FloatType ft2 => Float.kind_equalb ft1 ft2
  | ComplexType ct1, ComplexType ct2 => Complex.kind_equalb ct1 ct2
  | StringType, StringType => true
  | _, _ => false
  end.

Lemma type_equalb_spec : forall a b, type_equalb a b = true <-> a = b.
Proof.
  intros [| it1 | ft1 | ct1 |] [| it2 | ft2 | ct2 |]; simpl; split; intro H;
    try reflexivity; try discriminate.
  - apply Integer.equalb_spec in H; subst; reflexivity.
  - injection H as Heq; subst; apply Integer.equalb_spec; reflexivity.
  - apply Float.kind_equalb_spec in H; subst; reflexivity.
  - injection H as Heq; subst; apply Float.kind_equalb_spec; reflexivity.
  - apply Complex.kind_equalb_spec in H; subst; reflexivity.
  - injection H as Heq; subst; apply Complex.kind_equalb_spec; reflexivity.
Qed.

(** ---- exact untyped constant values of the current raw literals ---- *)
Inductive Constant : Type :=
| BoolConstant    : bool -> Constant
| IntegerConstant     : Z -> Constant
| FloatConstant   : Float.Constant -> Constant
| ComplexConstant : Complex.Constant -> Constant
| StringConstant  : string -> Constant.

(** the exact integer VALUE of a floating constant, if it denotes one exactly (a fractional constant has
    none) — the sole float->integer bridge, used by [convert_constant]. *)
Definition constant_to_int (q : Float.Constant) : option Z :=
  if Z.eqb (Z.rem (Float.numerator q) (Zpos (Float.denominator q))) 0
  then Some (Float.numerator q / Zpos (Float.denominator q)) else None.

(** decidable equality of float formats — reduces to [left eq_refl] on equal concrete formats, so a same-format
    conversion computes to the identity (see [same_float_kind_identity]). *)
Definition float_kind_eq_dec (a b : Float.Kind) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

(** decidable equality of complex formats — the [same_complex_kind_identity] analogue of [float_kind_eq_dec]. *)
Definition complex_kind_eq_dec (a b : Complex.Kind) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

(** INTRINSIC TYPED CONSTANTS — a genuinely [SemanticType]-indexed family.  A typed constant cannot exist
    without the structural evidence its type requires: an integer carries a proof it is representable at its
    type, a float carries a [Float.TypedConstant] (exact rounded rational + canonical runtime value + coherence).
    The loose [(SemanticType, Constant)] pair is GONE — a mismatched or out-of-range typed constant is
    UNREPRESENTABLE, not merely rejected, and no [ci_ok := True] convention is needed. *)
Inductive TypedConstant : SemanticType -> Type :=
| TypedBool    : bool -> TypedConstant BoolType
| TypedInteger : forall (it : Integer.Kind) (z : Z), Integer.representableb it z = true -> TypedConstant (IntegerType it)
| TypedFloat   : forall (ft : Float.Kind), Float.TypedConstant ft -> TypedConstant (FloatType ft)
| TypedComplex : forall (ct : Complex.Kind), Complex.TypedConstant ct -> TypedConstant (ComplexType ct)
| TypedString  : string -> TypedConstant StringType.

(** exact-value erasure: forget the type, keep the exact mathematical constant.  It reads the stored data —
    it NEVER inspects source syntax and NEVER re-rounds a float (a float's exact value is the already-rounded
    [Float.exact]; a complex's is the pair of already-rounded component exacts, [Complex.typed_exact]). *)
Definition typed_exact {t : SemanticType} (tc : TypedConstant t) : Constant :=
  match tc with
  | TypedBool b        => BoolConstant b
  | TypedInteger _ z _ => IntegerConstant z
  | TypedFloat _ tfc   => FloatConstant (Float.exact tfc)
  | TypedComplex _ tcc => ComplexConstant (Complex.typed_exact tcc)
  | TypedString s      => StringConstant s
  end.

(** extract the intrinsic [Float.TypedConstant] / [Complex.TypedConstant] from a typed constant KNOWN (by its index)
    to be at a float / complex type — an index-annotated match (axiom-free; no dependent destruction / UIP).
    Used ONLY by the same-component reuse paths ([reuse_float_as_complex] / [reuse_complex_as_float]). *)
Definition typed_float {ft : Float.Kind} (tc : TypedConstant (FloatType ft)) : Float.TypedConstant ft :=
  match tc in TypedConstant t return match t with FloatType f => Float.TypedConstant f | _ => unit end with
  | TypedFloat _ tfc => tfc
  | TypedBool _ => tt | TypedInteger _ _ _ => tt | TypedComplex _ _ => tt | TypedString _ => tt
  end.

Definition typed_complex {ct : Complex.Kind} (tc : TypedConstant (ComplexType ct)) : Complex.TypedConstant ct :=
  match tc in TypedConstant t return match t with ComplexType c => Complex.TypedConstant c | _ => unit end with
  | TypedComplex _ tcc => tcc
  | TypedBool _ => tt | TypedInteger _ _ _ => tt | TypedFloat _ _ => tt | TypedString _ => tt
  end.

(** a decidable bool guard carrying its own proof — avoids a dependent [if]-convoy in [typed_integer_of_Z]. *)
Definition bool_true_dec (b : bool) : {b = true} + {b = false} :=
  match b with true => left eq_refl | false => right eq_refl end.

(** construct a typed integer constant at [it] iff [z] is representable there — carries the range proof. *)
Definition typed_integer_of_Z (it : Integer.Kind) (z : Z) : option (TypedConstant (IntegerType it)) :=
  match bool_true_dec (Integer.representableb it z) with
  | left H  => Some (TypedInteger it z H)
  | right _ => None
  end.

(** construct a typed float constant at [ft] by the ONE [round_typed_float] authority. *)
Definition typed_float_of_constant (ft : Float.Kind) (q : Float.Constant) : option (TypedConstant (FloatType ft)) :=
  option_map (TypedFloat ft) (round_typed_float ft q).

(** construct a typed complex constant at [ct] by the ONE [Complex.round_typed] authority (each component
    rounds ONCE at [Complex.component_kind ct]; either component's overflow rejects the whole). *)
Definition typed_complex_of_constant (ct : Complex.Kind) (c : Complex.Constant) : option (TypedConstant (ComplexType ct)) :=
  option_map (TypedComplex ct) (Complex.round_typed ct c).

(** the exact NUMERIC embedding of a constant into the exact complex plane (a pure exact helper — NO rounding):
    an integer / float embeds as a real component with exact zero imaginary; a complex is itself; bool/string
    have none.  [convert_to_complex] rounds the result at the destination component format. *)
Definition numeric_constant_to_complex (c : Constant) : option Complex.Constant :=
  match c with
  | IntegerConstant z     => Some (Complex.of_real (Float.constant_of_Z z))
  | FloatConstant q   => Some (Complex.of_real q)
  | ComplexConstant c => Some c
  | _          => None
  end.

(** the ONE constant interpretation of the raw expressions — PARTIAL, because an explicit conversion may be
    compiler-invalid (out-of-range / fractional-to-integer / float overflow) and thus denote NO value.  A raw
    literal is an EXACT value (a bare float is its EXACT rational, unrounded — no range check here); an
    explicit conversion routes through the ONE [convert_constant] authority (integer conversions preserve the
    value when it fits; float conversions round ONCE at the destination). *)
(** The exact value of an expression is [constant_info_exact] applied to [constant_info] — there is NO separate
    [const_value] construction path (which would re-do conversion/rounding and be a second authority). *)

(** one constant-status analysis over the same raw AST (Go's own lattice): a raw literal is an UNTYPED
    constant ([UntypedInfo]); an explicit conversion is a TYPED constant ([TypedInfo] carrying the INTRINSIC
    [TypedConstant] — its validity is in its type, so no [ci_ok] convention).  A conversion of a bool/string
    constant is unrepresentable; an invalid inner conversion returns [None] and cannot be revived (the value
    is checked at EVERY layer). *)
Inductive ConstantInfo : Type :=
| UntypedInfo : Constant -> ConstantInfo
| TypedInfo   : forall (t : SemanticType), TypedConstant t -> ConstantInfo.

(** exact-value projection: an untyped constant is its own exact value; a typed constant's is its
    intrinsic [typed_exact].  There is no "type of an untyped constant" here — an untyped status has no
    assigned type yet (a DEFAULT is a separate query, [default_constant]). *)
Definition constant_info_exact (ci : ConstantInfo) : Constant :=
  match ci with UntypedInfo c => c | TypedInfo _ tc => typed_exact tc end.

(** the packed typed result of resolving ONE expression: existential semantic evidence, NOT a typed AST
    and NOT a copy of the raw expression. *)
Inductive ResolvedConstant : Type :=
| pack_resolved : forall (t : SemanticType), TypedConstant t -> ResolvedConstant.

Definition resolved_constant_type (rc : ResolvedConstant) : SemanticType :=
  match rc with pack_resolved t _ => t end.
Definition resolved_constant_exact (rc : ResolvedConstant) : Constant :=
  match rc with pack_resolved _ tc => typed_exact tc end.

(** same-format float identity: converting a typed float constant to its OWN format returns the existing
    [Float.TypedConstant] unchanged (no reround) — the transport is trivial because [float_kind_eq_dec ft ft]
    reduces to [left eq_refl]. *)
Definition same_float_kind_identity (ft : Float.Kind) (ci : ConstantInfo) : option (TypedConstant (FloatType ft)) :=
  match ci with
  | TypedInfo (FloatType ft') tc =>
      match float_kind_eq_dec ft' ft with
      | left Heq => Some (eq_rect (FloatType ft') (fun T => TypedConstant T) tc (FloatType ft) (f_equal FloatType Heq))
      | right _  => None
      end
  | _ => None
  end.

(** same-format complex identity: converting a typed complex constant to its OWN format returns the
    existing [Complex.TypedConstant] unchanged (no reround) — the [same_float_kind_identity] analogue. *)
Definition same_complex_kind_identity (ct : Complex.Kind) (ci : ConstantInfo) : option (TypedConstant (ComplexType ct)) :=
  match ci with
  | TypedInfo (ComplexType ct') tc =>
      match complex_kind_eq_dec ct' ct with
      | left Heq => Some (eq_rect (ComplexType ct') (fun T => TypedConstant T) tc (ComplexType ct) (f_equal ComplexType Heq))
      | right _  => None
      end
  | _ => None
  end.

(** component reuse (typed float -> matching complex): a typed float constant whose format equals the
    complex component format becomes the REAL component DIRECTLY (no reround); the imaginary component is the
    constructed positive zero. *)
Definition reuse_float_as_complex (ct : Complex.Kind) (ci : ConstantInfo) : option (TypedConstant (ComplexType ct)) :=
  match ci with
  | TypedInfo (FloatType ft') tc =>
      match float_kind_eq_dec ft' (Complex.component_kind ct) with
      | left Heq =>
          option_map
            (fun imz => TypedComplex ct
               (Complex.make_typed_constant (eq_rect ft' (fun f => Float.TypedConstant f) (typed_float tc)
                              (Complex.component_kind ct) Heq) imz))
            (round_typed_float (Complex.component_kind ct) Float.constant_zero)
      | right _ => None
      end
  | _ => None
  end.

(** component projection (typed complex -> matching float): a typed complex constant whose component
    format equals the float destination AND whose EXACT imaginary component is zero projects its EXISTING real
    [Float.TypedConstant] DIRECTLY (no reround). *)
Definition reuse_complex_as_float (ft : Float.Kind) (ci : ConstantInfo) : option (TypedConstant (FloatType ft)) :=
  match ci with
  | TypedInfo (ComplexType ct') tc =>
      match float_kind_eq_dec (Complex.component_kind ct') ft with
      | left Heq =>
          if Complex.constant_imaginary_is_zero (Complex.typed_exact (typed_complex tc))
          then Some (eq_rect (Complex.component_kind ct') (fun f => TypedConstant (FloatType f))
                             (TypedFloat (Complex.component_kind ct') (Complex.typed_real (typed_complex tc)))
                             ft Heq)
          else None
      | right _ => None
      end
  | _ => None
  end.

(** + float-target conversion: same-format float returns the identity; a matching-component
    zero-imaginary typed complex projects its real component; otherwise round the exact source value ONCE at
    the destination (a different-format typed source rounds its [Float.exact], preserving the explicit
    conversion boundary — the double-rounding scar).  A complex source needs exact-zero imaginary. *)
Definition convert_to_float (ft : Float.Kind) (ci : ConstantInfo) : option (TypedConstant (FloatType ft)) :=
  match same_float_kind_identity ft ci with
  | Some tc => Some tc
  | None =>
  match reuse_complex_as_float ft ci with
  | Some tc => Some tc
  | None =>
      match constant_info_exact ci with
      | IntegerConstant z    => typed_float_of_constant ft (Float.constant_of_Z z)
      | FloatConstant q  => typed_float_of_constant ft q
      | ComplexConstant c => match Complex.real_if_imaginary_zero c with
                      | Some q => typed_float_of_constant ft q
                      | None   => None end
      | _         => None
      end
  end end.

(** complex-target conversion: same-format complex returns the identity; a matching-component typed
    float reuses that float as the real component (positive-zero imaginary); otherwise embed the exact source
    numerically ([numeric_constant_to_complex]) and round each component ONCE at the destination component format
    (a different-format complex source rounds its two [Complex.typed_exact] components — the component-level
    double-rounding boundary). *)
Definition convert_to_complex (ct : Complex.Kind) (ci : ConstantInfo) : option (TypedConstant (ComplexType ct)) :=
  match same_complex_kind_identity ct ci with
  | Some tc => Some tc
  | None =>
  match reuse_float_as_complex ct ci with
  | Some tc => Some tc
  | None =>
      match numeric_constant_to_complex (constant_info_exact ci) with
      | Some c => typed_complex_of_constant ct c
      | None   => None
      end
  end end.

(** the ONE target-directed constant-conversion authority: it CONSUMES the source constant
    status and produces an INTRINSIC typed constant at the destination.  Integer target: the exact source (an
    integer, a float's integral exact value, or a zero-imaginary complex's integral real) must be
    representable.  Float target: [convert_to_float].  Complex target: [convert_to_complex].  bool/string
    target: unrepresentable. *)
Definition convert_constant (target : SemanticType) (ci : ConstantInfo) : option (TypedConstant target) :=
  match target with
  | BoolType    => None
  | StringType  => None
  | IntegerType it =>
      match constant_info_exact ci with
      | IntegerConstant z   => typed_integer_of_Z it z
      | FloatConstant q => match constant_to_int q with
                    | Some z => typed_integer_of_Z it z
                    | None => None end
      | ComplexConstant c => match Complex.real_if_imaginary_zero c with
                      | Some q => match constant_to_int q with
                                  | Some z => typed_integer_of_Z it z
                                  | None => None end
                      | None => None end
      | _ => None
      end
  | FloatType ft => convert_to_float ft ci
  | ComplexType ct => convert_to_complex ct ci
  end.

(** the SINGLE typing/defaulting construction for an UNTYPED constant at a REQUESTED type: bool/string
    at their own type; every NUMERIC target ROUTES THROUGH the ONE [convert_constant] authority applied to the
    untyped status — so untyped representability AGREES with explicit conversion BY CONSTRUCTION (no second
    range/rounding/dispatch Index.table).  A numeric constant at a bool/string target, or bool/string at a numeric
    target, is [None]. *)
Definition type_untyped_constant_at (t : SemanticType) (c : Constant) : option (TypedConstant t) :=
  match t with
  | BoolType       => match c with BoolConstant b   => Some (TypedBool b)  | _ => None end
  | StringType     => match c with StringConstant s => Some (TypedString s) | _ => None end
  | IntegerType it => convert_constant (IntegerType it) (UntypedInfo c)
  | FloatType ft   => convert_constant (FloatType ft) (UntypedInfo c)
  | ComplexType ct => convert_constant (ComplexType ct) (UntypedInfo c)
  end.

(** representability is DERIVED from successful typing at the requested type — and for numeric targets that
    typing IS [convert_constant], so representability and explicit conversion cannot disagree. *)
Definition ConstantRepresentable (t : SemanticType) (c : Constant) : Prop :=
  exists tc : TypedConstant t, type_untyped_constant_at t c = Some tc.

Definition constant_representableb (t : SemanticType) (c : Constant) : bool :=
  match type_untyped_constant_at t c with Some _ => true | None => false end.

Lemma constant_representableb_iff : forall t c, constant_representableb t c = true <-> ConstantRepresentable t c.
Proof.
  intros t c; unfold constant_representableb, ConstantRepresentable.
  destruct (type_untyped_constant_at t c) as [tc|] eqn:E; split.
  - intros _; exists tc; reflexivity.
  - intros _; reflexivity.
  - discriminate.
  - intros [tc' H]; discriminate.
Qed.

(** untyped representability of a NUMERIC target is DEFINITIONALLY [convert_constant] of the untyped status — the
    representability relation and the explicit-conversion authority never disagree. *)
Lemma type_untyped_int_convert : forall it c,
  type_untyped_constant_at (IntegerType it) c = convert_constant (IntegerType it) (UntypedInfo c).
Proof. reflexivity. Qed.
Lemma type_untyped_float_convert : forall ft c,
  type_untyped_constant_at (FloatType ft) c = convert_constant (FloatType ft) (UntypedInfo c).
Proof. reflexivity. Qed.
Lemma type_untyped_complex_convert : forall ct c,
  type_untyped_constant_at (ComplexType ct) c = convert_constant (ComplexType ct) (UntypedInfo c).
Proof. reflexivity. Qed.

(** ---- the index-free typing specification, parameterized by ONE source-name resolver ----

    A conversion node carries a SOURCE type name ([Syntax.TypeExpr]); the semantic target [SemanticType] is obtained
    by resolving that name in the current predeclared context.  That resolution is compiler-owned (§7): its ONE
    authority — the source-name-to-[SemanticType] Index.table — lives in [Admissible], NEVER here.  So the whole index-free
    typing spec ([constant_info] … [Program]) is parameterized by a total resolver [rt : Syntax.TypeExpr -> SemanticType]
    that [Admissible] supplies and against which the production occurrence pass is proved exact.  The single
    target-directed conversion authority [convert_constant] is unchanged: it still receives a semantic [SemanticType]
    ([rt ts]) and never inspects a source name or a rendered string. *)
Section TypingResolver.
Variable rt : Syntax.TypeExpr -> SemanticType.

Fixpoint constant_info (e : Syntax.Expr) : option ConstantInfo :=
  match e with
  | Syntax.BoolLiteral b   => Some (UntypedInfo (BoolConstant b))
  | Syntax.IntegerLiteral n    => Some (UntypedInfo (IntegerConstant (Z.of_N n)))
  | Syntax.NegatedIntegerLiteral n    => Some (UntypedInfo (IntegerConstant (- Z.of_N n)))
  | Syntax.StringLiteral s => Some (UntypedInfo (StringConstant s))
  | Syntax.FloatLiteral d  => Some (UntypedInfo (FloatConstant (Float.decimal_value d)))
  | Syntax.ComplexLiteral dc => Some (UntypedInfo (ComplexConstant (Complex.decimal_value dc)))
  | Syntax.Convert ts x =>
      match constant_info x with
      | Some ci => option_map (TypedInfo (rt ts)) (convert_constant (rt ts) ci)
      | None => None
      end
  end.

(** the ONE-NODE semantic layer: the constant status of a SINGLE expression node, given the ALREADY
    COMPUTED status of its one current expression child (None for a leaf, or a conversion whose child failed).
    A leaf constructs its exact untyped value (the child input is irrelevant); a conversion consumes the child
    status and calls the SAME [convert_constant] — no duplicated conversion/range/rounding logic, no second
    classifier.  A bottom-up analysis applies this once per occurrence, reading the child status from a map
    instead of recomputing [constant_info] over the whole subtree. *)
Definition constant_info_step (e : Syntax.Expr) (child : option ConstantInfo) : option ConstantInfo :=
  match e with
  | Syntax.BoolLiteral b     => Some (UntypedInfo (BoolConstant b))
  | Syntax.IntegerLiteral n      => Some (UntypedInfo (IntegerConstant (Z.of_N n)))
  | Syntax.NegatedIntegerLiteral n      => Some (UntypedInfo (IntegerConstant (- Z.of_N n)))
  | Syntax.StringLiteral s   => Some (UntypedInfo (StringConstant s))
  | Syntax.FloatLiteral d    => Some (UntypedInfo (FloatConstant (Float.decimal_value d)))
  | Syntax.ComplexLiteral dc => Some (UntypedInfo (ComplexConstant (Complex.decimal_value dc)))
  | Syntax.Convert ts _ =>
      match child with Some ci => option_map (TypedInfo (rt ts)) (convert_constant (rt ts) ci) | None => None end
  end.

(** the one current expression child of a node (the conversion operand); [None] for leaves. *)
Definition expression_child (e : Syntax.Expr) : option Syntax.Expr :=
  match e with
  | Syntax.Convert _ e' => Some e'
  | _ => None
  end.

(** the ONE recursive authority reflects the one-node step: [constant_info] of a node is [constant_info_step] applied
    to the status of its current child.  So [constant_info] and the bottom-up analysis use the SAME step. *)
Lemma constant_info_step_reflect : forall e,
  constant_info e = constant_info_step e (match expression_child e with Some c => constant_info c | None => None end).
Proof. intro e; destruct e; reflexivity. Qed.

(** defaulting: an UNTYPED constant becomes a validated typed constant in a use context — bool/string
    always; an int defaults to platform [int] iff representable; a bare float performs its ONE F64 rounding
    (via [round_typed_float]).  A bare overflowing float has no default typed constant. *)
Definition default_constant (c : Constant) : option ResolvedConstant :=
  match c with
  | BoolConstant b    => Some (pack_resolved BoolType (TypedBool b))
  | IntegerConstant z     => option_map (pack_resolved (IntegerType Integer.Int)) (typed_integer_of_Z Integer.Int z)
  | FloatConstant q   => option_map (pack_resolved (FloatType F64)) (typed_float_of_constant F64 q)
  | ComplexConstant c => option_map (pack_resolved (ComplexType C128)) (typed_complex_of_constant C128 c)
  | StringConstant s  => Some (pack_resolved StringType (TypedString s))
  end.

(** resolve a constant status to a validated typed constant: an untyped status defaults; a typed status is
    packed unchanged (its validity is intrinsic — no [ci_ok], no "typed constants are trusted" branch). *)
Definition resolve_constant_info (ci : ConstantInfo) : option ResolvedConstant :=
  match ci with
  | UntypedInfo c  => default_constant c
  | TypedInfo t tc => Some (pack_resolved t tc)
  end.

(** a successful constant-status resolution is deterministic (a function of the syntax). *)
Lemma constant_info_deterministic : forall e ci1 ci2,
  constant_info e = Some ci1 -> constant_info e = Some ci2 -> ci1 = ci2.
Proof. intros e ci1 ci2 H1 H2; rewrite H1 in H2; injection H2 as <-; reflexivity. Qed.

(** [Syntax.IntegerLiteral 0] and [Syntax.NegatedIntegerLiteral 0] denote the SAME untyped constant (signed zero is one value). *)
Lemma constant_info_zero_sign : constant_info (Syntax.IntegerLiteral 0) = constant_info (Syntax.NegatedIntegerLiteral 0).
Proof. reflexivity. Qed.

(** SAME-FORMAT FLOAT IDENTITY (LOAD-BEARING): converting a typed float constant to its OWN format
    returns the EXISTING [Float.TypedConstant] unchanged — no reround, no reconstruction.  This is exactly what
    makes nested same-type conversions [float32(float32 q)] / [float64(float64 q)] identities at the typed-
    constant level, so evaluation never rounds a typed float constant a second time. *)
Lemma convert_constant_same_float : forall ft (tc : TypedConstant (FloatType ft)),
  convert_constant (FloatType ft) (TypedInfo (FloatType ft) tc) = Some tc.
Proof. intros ft tc; destruct ft; reflexivity. Qed.

(** SAME-FORMAT COMPLEX IDENTITY (LOAD-BEARING, UNIVERSAL): converting a typed complex constant to its
    OWN format returns the EXISTING [Complex.TypedConstant] unchanged — no reround, no component reconstruction,
    the same stored runtime component objects.  This is what makes [complex64(complex64 ...)] /
    [complex128(complex128 ...)] identities at the typed-constant level. *)
Lemma convert_constant_same_complex : forall ct (tc : TypedConstant (ComplexType ct)),
  convert_constant (ComplexType ct) (TypedInfo (ComplexType ct) tc) = Some tc.
Proof. intros ct tc; destruct ct; reflexivity. Qed.

(** COMPONENT REUSE (LOAD-BEARING, UNIVERSAL): converting a typed FLOAT constant whose format is the
    complex component format to that complex type REUSES the existing [Float.TypedConstant] as the REAL component
    (the SAME object [typed_float tc], no reround); the imaginary component is the constructed +0. *)
Lemma convert_complex_reuses_float_component : forall ct (tc : TypedConstant (FloatType (Complex.component_kind ct))),
  exists tcc, convert_constant (ComplexType ct) (TypedInfo (FloatType (Complex.component_kind ct)) tc)
                = Some (TypedComplex ct tcc)
           /\ Complex.typed_real tcc = typed_float tc.
Proof.
  intros ct tc; destruct ct.
  - destruct (round_typed_float F32 Float.constant_zero) as [imz|] eqn:Hz; [ | vm_compute in Hz; discriminate ].
    exists (Complex.make_typed_constant (typed_float tc) imz); split; [ | reflexivity ].
    unfold convert_constant, convert_to_complex, same_complex_kind_identity, reuse_float_as_complex;
      cbn [Complex.component_kind float_kind_eq_dec eq_rect option_map]; rewrite Hz; reflexivity.
  - destruct (round_typed_float F64 Float.constant_zero) as [imz|] eqn:Hz; [ | vm_compute in Hz; discriminate ].
    exists (Complex.make_typed_constant (typed_float tc) imz); split; [ | reflexivity ].
    unfold convert_constant, convert_to_complex, same_complex_kind_identity, reuse_float_as_complex;
      cbn [Complex.component_kind float_kind_eq_dec eq_rect option_map]; rewrite Hz; reflexivity.
Qed.

(** COMPONENT PROJECTION (LOAD-BEARING, UNIVERSAL): converting a typed COMPLEX constant whose EXACT
    imaginary component is zero to its matching component float PROJECTS the existing real [Float.TypedConstant]
    DIRECTLY (the SAME object [Complex.typed_real (typed_complex tc)], no reround). *)
Lemma convert_float_reuses_complex_component : forall ct (tc : TypedConstant (ComplexType ct)),
  Complex.constant_imaginary_is_zero (Complex.typed_exact (typed_complex tc)) = true ->
  convert_constant (FloatType (Complex.component_kind ct)) (TypedInfo (ComplexType ct) tc)
    = Some (TypedFloat (Complex.component_kind ct) (Complex.typed_real (typed_complex tc))).
Proof.
  intros ct tc Hz; destruct ct;
    unfold convert_constant, convert_to_float, same_float_kind_identity, reuse_complex_as_float;
    cbn [Complex.component_kind float_kind_eq_dec eq_rect]; rewrite Hz; reflexivity.
Qed.

(** the exact value of an INTEGER-typed constant is an in-range [IntegerConstant] — extracted via an index-annotated
    match (axiom-free; no dependent destruction / UIP). *)
Lemma typed_int_value : forall it (tc : TypedConstant (IntegerType it)),
  exists z, typed_exact tc = IntegerConstant z /\ Integer.representableb it z = true.
Proof.
  intros it tc.
  refine (match tc as tc0 in TypedConstant t
          return (match t with
                  | IntegerType it' => exists z, typed_exact tc0 = IntegerConstant z /\ Integer.representableb it' z = true
                  | _ => True end)
          with
          | TypedInteger it0 z0 Hpf => _
          | _ => I
          end).
  exists z0; split; [ reflexivity | exact Hpf ].
Qed.

(** the UNIVERSAL integer same-type identity: converting a typed integer constant to its OWN type
    PRESERVES the exact value and type (an identity up to the proof-irrelevant range proof). *)
Lemma convert_constant_same_int : forall it (tc : TypedConstant (IntegerType it)),
  exists tc', convert_constant (IntegerType it) (TypedInfo (IntegerType it) tc) = Some tc'
           /\ typed_exact tc' = typed_exact tc.
Proof.
  intros it tc.
  destruct (typed_int_value it tc) as [ z [ Hexact Hz ] ].
  cbn [convert_constant constant_info_exact]; rewrite Hexact.
  unfold typed_integer_of_Z; destruct (bool_true_dec (Integer.representableb it z)) as [H'|H'].
  - exists (TypedInteger it z H'); split; reflexivity.
  - congruence.
Qed.

(** an invalid inner conversion propagates: it cannot be revived by an outer conversion (any target name). *)
Lemma constant_info_conv_none : forall ts e,
  constant_info e = None -> constant_info (Syntax.Convert ts e) = None.
Proof. intros ts e H; simpl; rewrite H; reflexivity. Qed.

(** ---- use-context resolution: one expression-use context and its per-type policy ---- *)
Inductive Use : Type :=
| PrintlnArgument.

(** the exhaustive per-type use policy.  A `println` argument accepts ALL current types — bool, every integer
    member, every float format, every complex format, and string. *)
Inductive Allows : Use -> SemanticType -> Prop :=
| AllowsPrintlnBool    : Allows PrintlnArgument BoolType
| AllowsPrintlnInteger     : forall it, Allows PrintlnArgument (IntegerType it)
| AllowsPrintlnFloat   : forall ft, Allows PrintlnArgument (FloatType ft)
| AllowsPrintlnComplex : forall ct, Allows PrintlnArgument (ComplexType ct)
| AllowsPrintlnString  : Allows PrintlnArgument StringType.

Definition use_allowsb (u : Use) (t : SemanticType) : bool :=
  match u, t with
  | PrintlnArgument, BoolType       => true
  | PrintlnArgument, IntegerType _  => true
  | PrintlnArgument, FloatType _    => true
  | PrintlnArgument, ComplexType _  => true
  | PrintlnArgument, StringType     => true
  end.

Lemma use_allowsb_iff : forall u t, use_allowsb u t = true <-> Allows u t.
Proof.
  intros [] [| it | ft | ct |]; simpl; split; intro H; try constructor; try reflexivity; inversion H.
Qed.

(** the declarative resolved typing of ONE expression in a use context: the expression analyzes to a
    constant-status [ci], which RESOLVES ([resolve_constant_info]) to a validated typed constant [rc] — a bare
    literal defaults, a typed constant packs unchanged — whose INTRINSIC type [resolved_constant_type rc] the
    context ALLOWS.  There is NO [ci_ok]: validity is carried by the typed constant itself.  No
    typed-expression AST, no copied "resolved expression" — a relation over the raw syntax driven by
    [constant_info]/[resolve_constant_info]. *)
Inductive Resolve : Use -> Syntax.Expr -> SemanticType -> Prop :=
| Resolved : forall u e ci rc,
    constant_info e = Some ci ->
    resolve_constant_info ci = Some rc ->
    Allows u (resolved_constant_type rc) ->
    Resolve u e (resolved_constant_type rc).

(** the resolution that EXPOSES the [ResolvedConstant] witness (evaluation and the root theorem consume this). *)
Definition resolve_constant (u : Use) (e : Syntax.Expr) : option ResolvedConstant :=
  match constant_info e with
  | None => None
  | Some ci =>
      match resolve_constant_info ci with
      | None => None
      | Some rc => if use_allowsb u (resolved_constant_type rc) then Some rc else None
      end
  end.

Definition resolve (u : Use) (e : Syntax.Expr) : option SemanticType :=
  option_map resolved_constant_type (resolve_constant u e).

Lemma resolve_constant_sound : forall u e rc,
  resolve_constant u e = Some rc ->
  exists ci, constant_info e = Some ci /\ resolve_constant_info ci = Some rc
             /\ Allows u (resolved_constant_type rc).
Proof.
  intros u e rc H; unfold resolve_constant in H.
  destruct (constant_info e) as [ci|] eqn:Hci; [| discriminate].
  destruct (resolve_constant_info ci) as [rc'|] eqn:Hrc; [| discriminate].
  destruct (use_allowsb u (resolved_constant_type rc')) eqn:Hua; [| discriminate].
  injection H as ->. exists ci; split; [ reflexivity | split; [ exact Hrc | apply use_allowsb_iff; exact Hua ] ].
Qed.

Lemma resolve_sound : forall u e t, resolve u e = Some t -> Resolve u e t.
Proof.
  intros u e t H. unfold resolve in H.
  destruct (resolve_constant u e) as [rc|] eqn:Hrc; cbn [option_map] in H; [| discriminate].
  injection H as <-. destruct (resolve_constant_sound u e rc Hrc) as [ci [Hci [Hri Hua]]].
  eapply Resolved; [ exact Hci | exact Hri | exact Hua ].
Qed.

Lemma resolve_complete : forall u e t, Resolve u e t -> resolve u e = Some t.
Proof.
  intros u e t H; destruct H as [ u0 e0 ci rc Hci Hrc Hua ].
  apply use_allowsb_iff in Hua.
  unfold resolve, resolve_constant; rewrite Hci, Hrc, Hua; reflexivity.
Qed.

Lemma resolve_deterministic : forall u e t1 t2, Resolve u e t1 -> Resolve u e t2 -> t1 = t2.
Proof.
  intros u e t1 t2 H1 H2.
  apply resolve_complete in H1; apply resolve_complete in H2.
  rewrite H1 in H2; injection H2 as <-; reflexivity.
Qed.

(** an expression is typed in a use context iff it resolves to SOME type there. *)
Definition expression_typedb (u : Use) (e : Syntax.Expr) : bool :=
  match resolve u e with Some _ => true | None => false end.

Lemma expression_typedb_iff : forall u e, expression_typedb u e = true <-> exists t, Resolve u e t.
Proof.
  intros u e; unfold expression_typedb; destruct (resolve u e) as [ t | ] eqn:Hr; split.
  - intros _; exists t; apply resolve_sound; exact Hr.
  - intros _; reflexivity.
  - intro H; discriminate H.
  - intros [t' Ht]; apply resolve_complete in Ht; rewrite Ht in Hr; discriminate.
Qed.

(** ---- whole-current-fragment typing judgments ---- *)

Inductive Stmt : Syntax.Stmt -> Prop :=
| TypedPrintln : forall args,
    Forall (fun e => exists t, Resolve PrintlnArgument e t) args -> Stmt (Syntax.Println args).

Inductive Decl : Syntax.Decl -> Prop :=
| TypedMain : forall body, Forall Stmt body -> Decl (Syntax.Main body).

Definition File (decls : list Syntax.Decl) : Prop := Forall Decl decls.
Definition SourceFile (sf : Syntax.File) : Prop := File (Syntax.declarations sf).

(** whole-program typing is MAP-BASED — quantified over the standard map's [MapsTo], NOT over an
    input-order list.  Every source file bound in the forest is typed. *)
Definition Program (p : Syntax.Program) : Prop :=
  forall path sf, Syntax.maps_to_file path sf (Syntax.files p) -> SourceFile sf.

Definition stmt_typedb (s : Syntax.Stmt) : bool :=
  match s with Syntax.Println args => forallb (expression_typedb PrintlnArgument) args end.
Definition decl_typedb (d : Syntax.Decl) : bool :=
  match d with Syntax.Main body => forallb stmt_typedb body end.
Definition file_typedb (decls : list Syntax.Decl) : bool := forallb decl_typedb decls.
Definition source_file_typedb (sf : Syntax.File) : bool := file_typedb (Syntax.declarations sf).
(** the executable checker traverses the standard map's CANONICAL derived enumeration ([elements]). *)
Definition program_typedb (p : Syntax.Program) : bool :=
  forallb (fun b => source_file_typedb (snd b)) (Syntax.file_bindings (Syntax.files p)).

Lemma forallb_iff_forall {X} : forall (f : X -> bool) (P : X -> Prop) (l : list X),
  (forall x, f x = true <-> P x) -> (forallb f l = true <-> Forall P l).
Proof.
  intros f P l Hpt; induction l as [ | x l' IH ]; simpl.
  - split; [ constructor | reflexivity ].
  - rewrite Bool.andb_true_iff, Hpt, IH.
    split; [ intros [Hx Hl]; constructor; assumption
           | intro H; inversion H; subst; split; assumption ].
Qed.

Lemma stmt_typedb_iff : forall s, stmt_typedb s = true <-> Stmt s.
Proof.
  intros [args]; simpl.
  rewrite (forallb_iff_forall (expression_typedb PrintlnArgument) (fun e => exists t, Resolve PrintlnArgument e t)
             args (fun e => expression_typedb_iff PrintlnArgument e)).
  split; [ intro H; constructor; exact H | intro H; inversion H; subst; assumption ].
Qed.

Lemma decl_typedb_iff : forall d, decl_typedb d = true <-> Decl d.
Proof.
  intros [body]; simpl. rewrite (forallb_iff_forall stmt_typedb Stmt body stmt_typedb_iff).
  split; [ intro H; constructor; exact H | intro H; inversion H; subst; assumption ].
Qed.

Lemma file_typedb_iff : forall f, file_typedb f = true <-> File f.
Proof. intro f; unfold file_typedb, File; apply forallb_iff_forall; exact decl_typedb_iff. Qed.

Lemma source_file_typedb_iff : forall sf, source_file_typedb sf = true <-> SourceFile sf.
Proof. intro sf; apply file_typedb_iff. Qed.

(** the map-based judgment reflects the executable checker: [forallb] over the canonical [elements] is
    exactly the [MapsTo]-quantified typing (the standard map bridges [elements] and [MapsTo]). *)
Lemma program_typedb_iff : forall p, program_typedb p = true <-> Program p.
Proof.
  intro p. unfold program_typedb, Program.
  rewrite (forallb_iff_forall (fun b => source_file_typedb (snd b)) (fun b => SourceFile (snd b))
             (Syntax.file_bindings (Syntax.files p)) (fun b => source_file_typedb_iff (snd b))).
  unfold Syntax.maps_to_file, Syntax.file_bindings. split.
  - intros H path sf Hmt.
    apply Syntax.FileFacts.elements_mapsto_iff, InA_alt in Hmt.
    destruct Hmt as [[k' e'] [Heq Hin]]. destruct Heq as [_ He]. cbn in *.
    rewrite Forall_forall in H. specialize (H (k', e') Hin). cbn in H. rewrite He. exact H.
  - intros H. apply Forall_forall. intros [k e] Hin. cbn.
    apply (H k e), Syntax.FileFacts.elements_mapsto_iff, InA_alt.
    exists (k, e). split; [ split; reflexivity | exact Hin ].
Qed.

(** ---- ORDER-INDEPENDENCE / EXTENSIONALITY: whole-program typing is a property of the file MAP, never
    of a construction-order list.  It respects semantic map equality both as a [Prop] and reflected as a
    [bool], and is therefore invariant under reordered [build_program] construction. ---- *)

(** [Program] respects [FilesEqual] (semantic map equality) — equal maps type identically. *)
Lemma program_equal : forall p1 p2,
  Syntax.FilesEqual (Syntax.files p1) (Syntax.files p2) -> Program p1 -> Program p2.
Proof.
  intros p1 p2 Heq Ht path sf Hmt. apply (Ht path sf). unfold Syntax.maps_to_file in *.
  apply Syntax.FileFacts.find_mapsto_iff. rewrite (Heq path). apply Syntax.FileFacts.find_mapsto_iff. exact Hmt.
Qed.

(** the reflected checker agrees on [FilesEqual] maps — no dependence on the backing tree's element order. *)
Lemma program_typedb_equal : forall p1 p2,
  Syntax.FilesEqual (Syntax.files p1) (Syntax.files p2) -> program_typedb p1 = program_typedb p2.
Proof.
  intros p1 p2 Heq.
  destruct (program_typedb p1) eqn:E1; destruct (program_typedb p2) eqn:E2; try reflexivity.
  - exfalso. apply program_typedb_iff in E1.
    assert (program_typedb p2 = true)
      by (apply program_typedb_iff; exact (program_equal p1 p2 Heq E1)).
    rewrite E2 in H; discriminate.
  - exfalso. apply program_typedb_iff in E2.
    assert (program_typedb p1 = true)
      by (apply program_typedb_iff;
          exact (program_equal p2 p1 (Syntax.files_equal_sym _ _ Heq) E2)).
    rewrite E1 in H; discriminate.
Qed.

(** reordered construction types identically: a permuted node list builds a [FilesEqual] map, so its
    whole-program typing result is the same. *)
Theorem program_typedb_build_permutation : forall ms nodes1 nodes2 p1 p2,
  Permutation nodes1 nodes2 ->
  build_program ms nodes1 = Some p1 -> build_program ms nodes2 = Some p2 ->
  program_typedb p1 = program_typedb p2.
Proof.
  intros ms nodes1 nodes2 p1 p2 Hperm Hb1 Hb2. apply program_typedb_equal.
  unfold build_program in *.
  destruct (Syntax.files_of_nodes nodes1) as [fm1|] eqn:F1; [ | discriminate ].
  destruct (Syntax.files_of_nodes nodes2) as [fm2|] eqn:F2; [ | discriminate ].
  injection Hb1 as <-. injection Hb2 as <-. cbn [Syntax.files].
  exact (Syntax.files_of_nodes_permutation nodes1 nodes2 fm1 fm2 Hperm F1 F2).
Qed.

(** the empty file is typed vacuously; so is the empty program. *)
Lemma empty_file_typed : File [].
Proof. constructor. Qed.

End TypingResolver.

(** ---- rt-free shared constant fixtures ----

    The canonical integer literal and the decimal / decimal-complex constants below are referenced by
    [Property] / [Render] / the e2e witnesses and by the concrete typing witnesses re-established, with the
    predeclared resolver, in [Admissible].  They carry no source type name and so need no resolver.  The
    concrete source-name conversion witnesses (every [resolve] / [constant_info] over an [Syntax.Convert], the
    per-type boundary theorems, and the double-round scars) live in [Admissible], the SOLE owner of the
    source-name-to-[SemanticType] resolver (§7, §9) — never here. *)
Definition integer_literal (z : Z) : Syntax.Expr :=
  if Z.leb 0 z then Syntax.IntegerLiteral (Z.to_N z) else Syntax.NegatedIntegerLiteral (Z.to_N (- z)).

(** decimal / decimal-complex constant fixtures shared with Property / Render / the e2e witnesses. *)
Definition decimal_15em1 : Float.Decimal := Float.make_decimal 15 (-1) eq_refl.   (* 1.5 *)
Definition decimal_3    : Float.Decimal := Float.make_decimal 3 0 eq_refl.        (* 3.0 *)
Definition decimal_35em1 : Float.Decimal := Float.make_decimal 35 (-1) eq_refl.   (* 3.5 *)
Definition decimal_128  : Float.Decimal := Float.make_decimal 128 0 eq_refl.      (* 128.0 *)
Definition decimal_m1   : Float.Decimal := Float.make_decimal (-1) 0 eq_refl.     (* -1.0 *)
Definition decimal_single_rounding : Float.Decimal := Float.make_decimal 2305843146652647425 0 eq_refl.
Definition decimal_m25em1 : Float.Decimal := Float.make_decimal (-25) (-1) eq_refl.  (* -2.5 *)
Definition decimal_127_0  : Float.Decimal := Float.make_decimal 127 0 eq_refl.
Definition decimal_1_0    : Float.Decimal := Float.make_decimal 1 0 eq_refl.
Definition decimal_m1_0   : Float.Decimal := Float.make_decimal (-1) 0 eq_refl.
Definition decimal_0_0    : Float.Decimal := Float.make_decimal 0 0 eq_refl.
Definition decimal_complex_1p5_m2p5 : Complex.Decimal := Complex.make_decimal decimal_15em1 decimal_m25em1.
Definition decimal_tiny_imaginary : Float.Decimal := Float.make_decimal 1 (-50) eq_refl.   (* 1e-50: nonzero, underflows binary32 -> +0 *)

(** typed-constant MISMATCH is UNREPRESENTABLE — the dependent index + carried range proof make an
    ill-typed / out-of-range typed constant impossible to CONSTRUCT ([Fail] adds nothing to the env). *)
Fail Definition mismatch_string_carrying_int : TypedConstant StringType := TypedInteger Integer.Int 3 eq_refl.
Fail Definition mismatch_int_out_of_range : TypedConstant (IntegerType Integer.Int8) := TypedInteger Integer.Int8 128 eq_refl.
Fail Definition mismatch_float_carrying_bool : TypedConstant (FloatType F64) := TypedBool true.

(** every string literal is representable at [StringType], for ARBITRARY finite byte sequences. *)
Lemma string_representable : forall s, ConstantRepresentable StringType (StringConstant s).
Proof. intro s; exists (TypedString s); reflexivity. Qed.
Lemma string_representableb : forall s, constant_representableb StringType (StringConstant s) = true.
Proof. reflexivity. Qed.

(* GENERIC [forallb] HELPERS for the whole-program typing folds.

   Typing owns the type/constant relation ONLY — never any occurrence/index traversal.  The per-occurrence
   typing predicate ([Compilable.occurrence_arg_typedb]) and its occurrence-stream aggregation chain ([occs_*_typedb_eq]) live in
   Admissible — the SOLE meeting point of Index identity and Typing semantics — so Typing needs no Index
   import.  These two lemmas are index-free [forallb] plumbing reused by that chain (in Admissible) and by the
   whole-program folds here. *)

Lemma forallb_ext_in {A} (f g : A -> bool) (l : list A) :
  (forall x, In x l -> f x = g x) -> forallb f l = forallb g l.
Proof.
  induction l as [|a l IH]; simpl; intros H; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), IH; [reflexivity | intros x Hx; apply H; right; exact Hx].
Qed.

Lemma forallb_map_snd {A B} (f : B -> bool) (l : list (A * B)) :
  forallb (fun x => f (snd x)) l = forallb f (map snd l).
Proof. induction l as [|a l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.
