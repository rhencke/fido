(** GoTypes — the ONE Go type-system authority for the current bool/integer/float/complex/string fragment.  It
    is EVIDENCE over the ONE raw [GoAST], never a second (typed) AST: raw [GoExpr] stays untyped syntax, and
    typing is a judgment over that same syntax.

    The permanent type universe here is [TBool], the INTEGER FAMILY [TInteger it] over the one [IntegerType]
    descriptor (ten live Go integer types), the FLOAT FAMILY [TFloat ft] over the one [FloatType] descriptor
    (float32/float64), the COMPLEX FAMILY [TComplex ct] over the one [ComplexType] descriptor (complex64/
    complex128, whose real/imaginary components are float32/float64 via [complex_component_type]), and
    [TString].  Each landed TOGETHER with its syntax and complete semantics (static typing + representability +
    compiler facts + safety + rendering + tests + docs); there are no placeholder constructors ahead of the
    syntax that needs them.

    The foundational distinction (Go's own): a raw literal denotes an EXACT UNTYPED CONSTANT value
    ([GoConst] — ints arbitrary-precision [Z], floats an exact rational [FloatConst], a complex an exact PAIR
    of rational components [ComplexConst], strings exact byte sequences), independent of any width.  An
    explicit conversion [EConvert ts e] names a SOURCE type ([ts]); the semantic target [GoType] is the
    compiler-owned resolution [rt ts] (§7 — the resolver lives in [GoCompile], never here), and the value
    routes through the ONE [convert_const] authority at that target: an integer target does NOT change the
    value (range-checked at the integer type); a float target ROUNDS the value ONCE at the destination format;
    a complex target rounds EACH component ONCE at the format's component precision.  In a USE CONTEXT that
    requires a typed value, an UNTYPED
    constant is given a DEFAULT TYPE (int constants default to [TInteger IInt], floats to [TFloat F64], complex
    to [TComplex C128]) and REPRESENTABILITY is checked (for a numeric target BY the SAME [convert_const], so
    representability and conversion never disagree), while a TYPED constant RETAINS its type and value (it is
    NOT defaulted again; its validity is INTRINSIC — carried by the dependently-typed [TypedConst]
    constructor's own proof — so there is nothing to re-check).  This is the single authority every later
    feature (assignments, variables, arguments, arithmetic, more numeric types) builds on. *)
From Stdlib Require Import NArith ZArith List Bool String Ascii Lia.
From Stdlib Require Import SetoidList Permutation.
From Fido Require Import Ints Floats Complexes GoAST.
Import ListNotations.
Open Scope Z_scope.

(** The semantic value of a Go string is an EXACT BYTE SEQUENCE.  We use Rocq [string] directly (a sequence
    of [ascii] bytes) as that value, with exactly that meaning — it is NOT Unicode scalar values / code
    points / UTF-8-decoded characters / source-literal spelling (the canonical source spelling is a separate
    proved encoding in [GoRender]).  No wrapper and no invariant are needed: every finite byte sequence is a
    valid Go string value in represented scope (no length limit, no well-formedness side condition). *)

(** ---- the one type universe: bool, the integer FAMILY, the float FAMILY, the complex FAMILY, and string ---- *)
Inductive GoType : Type :=
| TBool
| TInteger : IntegerType -> GoType
| TFloat   : FloatType -> GoType
| TComplex : ComplexType -> GoType
| TString.

Definition gotype_eqb (a b : GoType) : bool :=
  match a, b with
  | TBool, TBool => true
  | TInteger it1, TInteger it2 => integer_type_eqb it1 it2
  | TFloat ft1, TFloat ft2 => float_type_eqb ft1 ft2
  | TComplex ct1, TComplex ct2 => complex_type_eqb ct1 ct2
  | TString, TString => true
  | _, _ => false
  end.

Lemma gotype_eqb_eq : forall a b, gotype_eqb a b = true <-> a = b.
Proof.
  intros [| it1 | ft1 | ct1 |] [| it2 | ft2 | ct2 |]; simpl; split; intro H;
    try reflexivity; try discriminate.
  - apply integer_type_eqb_eq in H; subst; reflexivity.
  - injection H as Heq; subst; apply integer_type_eqb_eq; reflexivity.
  - apply float_type_eqb_eq in H; subst; reflexivity.
  - injection H as Heq; subst; apply float_type_eqb_eq; reflexivity.
  - apply complex_type_eqb_eq in H; subst; reflexivity.
  - injection H as Heq; subst; apply complex_type_eqb_eq; reflexivity.
Qed.

(** ---- exact untyped constant values of the current raw literals ---- *)
Inductive GoConst : Type :=
| CBool    : bool -> GoConst
| CInt     : Z -> GoConst
| CFloat   : FloatConst -> GoConst
| CComplex : ComplexConst -> GoConst
| CString  : string -> GoConst.

(** the exact integer VALUE of a floating constant, if it denotes one exactly (a fractional constant has
    none) — the sole float->integer bridge, used by [convert_const]. *)
Definition fc_to_int (q : FloatConst) : option Z :=
  if Z.eqb (Z.rem (fc_num q) (Zpos (fc_den q))) 0
  then Some (fc_num q / Zpos (fc_den q)) else None.

(** decidable equality of float formats — reduces to [left eq_refl] on equal concrete formats, so a same-format
    conversion computes to the identity (see [same_ft_identity]). *)
Definition float_type_eq_dec (a b : FloatType) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

(** decidable equality of complex formats — the [same_ct_identity] analogue of [float_type_eq_dec]. *)
Definition complex_type_eq_dec (a b : ComplexType) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

(** INTRINSIC TYPED CONSTANTS — a genuinely [GoType]-indexed family.  A typed constant cannot exist
    without the structural evidence its type requires: an integer carries a proof it is representable at its
    type, a float carries a [TypedFloatConst] (exact rounded rational + canonical runtime value + coherence).
    The loose [(GoType, GoConst)] pair is GONE — a mismatched or out-of-range typed constant is
    UNREPRESENTABLE, not merely rejected, and no [ci_ok := True] convention is needed. *)
Inductive TypedConst : GoType -> Type :=
| TCBool    : bool -> TypedConst TBool
| TCInteger : forall (it : IntegerType) (z : Z), integer_representableb it z = true -> TypedConst (TInteger it)
| TCFloat   : forall (ft : FloatType), TypedFloatConst ft -> TypedConst (TFloat ft)
| TCComplex : forall (ct : ComplexType), TypedComplexConst ct -> TypedConst (TComplex ct)
| TCString  : string -> TypedConst TString.

(** exact-value erasure: forget the type, keep the exact mathematical constant.  It reads the stored data —
    it NEVER inspects source syntax and NEVER re-rounds a float (a float's exact value is the already-rounded
    [tfc_exact]; a complex's is the pair of already-rounded component exacts, [typed_complex_exact]). *)
Definition typed_const_exact {t : GoType} (tc : TypedConst t) : GoConst :=
  match tc with
  | TCBool b        => CBool b
  | TCInteger _ z _ => CInt z
  | TCFloat _ tfc   => CFloat (tfc_exact tfc)
  | TCComplex _ tcc => CComplex (typed_complex_exact tcc)
  | TCString s      => CString s
  end.

(** extract the intrinsic [TypedFloatConst] / [TypedComplexConst] from a typed constant KNOWN (by its index)
    to be at a float / complex type — an index-annotated match (axiom-free; no dependent destruction / UIP).
    Used ONLY by the same-component reuse paths ([reuse_float_as_complex] / [reuse_complex_as_float]). *)
Definition typed_const_float {ft : FloatType} (tc : TypedConst (TFloat ft)) : TypedFloatConst ft :=
  match tc in TypedConst t return match t with TFloat f => TypedFloatConst f | _ => unit end with
  | TCFloat _ tfc => tfc
  | TCBool _ => tt | TCInteger _ _ _ => tt | TCComplex _ _ => tt | TCString _ => tt
  end.

Definition typed_const_complex {ct : ComplexType} (tc : TypedConst (TComplex ct)) : TypedComplexConst ct :=
  match tc in TypedConst t return match t with TComplex c => TypedComplexConst c | _ => unit end with
  | TCComplex _ tcc => tcc
  | TCBool _ => tt | TCInteger _ _ _ => tt | TCFloat _ _ => tt | TCString _ => tt
  end.

(** a decidable bool guard carrying its own proof — avoids a dependent [if]-convoy in [typed_integer_of_Z]. *)
Definition bool_true_dec (b : bool) : {b = true} + {b = false} :=
  match b with true => left eq_refl | false => right eq_refl end.

(** construct a typed integer constant at [it] iff [z] is representable there — carries the range proof. *)
Definition typed_integer_of_Z (it : IntegerType) (z : Z) : option (TypedConst (TInteger it)) :=
  match bool_true_dec (integer_representableb it z) with
  | left H  => Some (TCInteger it z H)
  | right _ => None
  end.

(** construct a typed float constant at [ft] by the ONE [round_typed_float] authority. *)
Definition typed_float_of_const (ft : FloatType) (q : FloatConst) : option (TypedConst (TFloat ft)) :=
  option_map (TCFloat ft) (round_typed_float ft q).

(** construct a typed complex constant at [ct] by the ONE [round_typed_complex] authority (each component
    rounds ONCE at [complex_component_type ct]; either component's overflow rejects the whole). *)
Definition typed_complex_of_const (ct : ComplexType) (c : ComplexConst) : option (TypedConst (TComplex ct)) :=
  option_map (TCComplex ct) (round_typed_complex ct c).

(** the exact NUMERIC embedding of a constant into the exact complex plane (a pure exact helper — NO rounding):
    an integer / float embeds as a real component with exact zero imaginary; a complex is itself; bool/string
    have none.  [convert_to_complex] rounds the result at the destination component format. *)
Definition numeric_const_to_complex (c : GoConst) : option ComplexConst :=
  match c with
  | CInt z     => Some (complex_of_real (fc_of_Z z))
  | CFloat q   => Some (complex_of_real q)
  | CComplex c => Some c
  | _          => None
  end.

(** the ONE constant interpretation of the raw expressions — PARTIAL, because an explicit conversion may be
    compiler-invalid (out-of-range / fractional-to-integer / float overflow) and thus denote NO value.  A raw
    literal is an EXACT value (a bare float is its EXACT rational, unrounded — no range check here); an
    explicit conversion routes through the ONE [convert_const] authority (integer conversions preserve the
    value when it fits; float conversions round ONCE at the destination). *)
(** The exact value of an expression is [const_info_exact] applied to [const_info] — there is NO separate
    [const_value] construction path (which would re-do conversion/rounding and be a second authority). *)

(** one constant-status analysis over the same raw AST (Go's own lattice): a raw literal is an UNTYPED
    constant ([CIUntyped]); an explicit conversion is a TYPED constant ([CITyped] carrying the INTRINSIC
    [TypedConst] — its validity is in its type, so no [ci_ok] convention).  A conversion of a bool/string
    constant is unrepresentable; an invalid inner conversion returns [None] and cannot be revived (the value
    is checked at EVERY layer). *)
Inductive ConstInfo : Type :=
| CIUntyped : GoConst -> ConstInfo
| CITyped   : forall (t : GoType), TypedConst t -> ConstInfo.

(** exact-value projection: an untyped constant is its own exact value; a typed constant's is its
    intrinsic [typed_const_exact].  There is no "type of an untyped constant" here — an untyped status has no
    assigned type yet (a DEFAULT is a separate query, [default_const]). *)
Definition const_info_exact (ci : ConstInfo) : GoConst :=
  match ci with CIUntyped c => c | CITyped _ tc => typed_const_exact tc end.

(** the packed typed result of resolving ONE expression: existential semantic evidence, NOT a typed AST
    and NOT a copy of the raw expression. *)
Inductive ResolvedConst : Type :=
| pack_resolved : forall (t : GoType), TypedConst t -> ResolvedConst.

Definition resolved_const_type (rc : ResolvedConst) : GoType :=
  match rc with pack_resolved t _ => t end.
Definition resolved_const_exact (rc : ResolvedConst) : GoConst :=
  match rc with pack_resolved _ tc => typed_const_exact tc end.

(** same-format float identity: converting a typed float constant to its OWN format returns the existing
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

(** same-format complex identity: converting a typed complex constant to its OWN format returns the
    existing [TypedComplexConst] unchanged (no reround) — the [same_ft_identity] analogue. *)
Definition same_ct_identity (ct : ComplexType) (ci : ConstInfo) : option (TypedConst (TComplex ct)) :=
  match ci with
  | CITyped (TComplex ct') tc =>
      match complex_type_eq_dec ct' ct with
      | left Heq => Some (eq_rect (TComplex ct') (fun T => TypedConst T) tc (TComplex ct) (f_equal TComplex Heq))
      | right _  => None
      end
  | _ => None
  end.

(** component reuse (typed float -> matching complex): a typed float constant whose format equals the
    complex component format becomes the REAL component DIRECTLY (no reround); the imaginary component is the
    constructed positive zero. *)
Definition reuse_float_as_complex (ct : ComplexType) (ci : ConstInfo) : option (TypedConst (TComplex ct)) :=
  match ci with
  | CITyped (TFloat ft') tc =>
      match float_type_eq_dec ft' (complex_component_type ct) with
      | left Heq =>
          option_map
            (fun imz => TCComplex ct
               (mkTCC (eq_rect ft' (fun f => TypedFloatConst f) (typed_const_float tc)
                              (complex_component_type ct) Heq) imz))
            (round_typed_float (complex_component_type ct) fc_zero)
      | right _ => None
      end
  | _ => None
  end.

(** component projection (typed complex -> matching float): a typed complex constant whose component
    format equals the float destination AND whose EXACT imaginary component is zero projects its EXISTING real
    [TypedFloatConst] DIRECTLY (no reround). *)
Definition reuse_complex_as_float (ft : FloatType) (ci : ConstInfo) : option (TypedConst (TFloat ft)) :=
  match ci with
  | CITyped (TComplex ct') tc =>
      match float_type_eq_dec (complex_component_type ct') ft with
      | left Heq =>
          if cc_imag_is_zero (typed_complex_exact (typed_const_complex tc))
          then Some (eq_rect (complex_component_type ct') (fun f => TypedConst (TFloat f))
                             (TCFloat (complex_component_type ct') (tcc_real (typed_const_complex tc)))
                             ft Heq)
          else None
      | right _ => None
      end
  | _ => None
  end.

(** + float-target conversion: same-format float returns the identity; a matching-component
    zero-imaginary typed complex projects its real component; otherwise round the exact source value ONCE at
    the destination (a different-format typed source rounds its [tfc_exact], preserving the explicit
    conversion boundary — the double-rounding scar).  A complex source needs exact-zero imaginary. *)
Definition convert_to_float (ft : FloatType) (ci : ConstInfo) : option (TypedConst (TFloat ft)) :=
  match same_ft_identity ft ci with
  | Some tc => Some tc
  | None =>
  match reuse_complex_as_float ft ci with
  | Some tc => Some tc
  | None =>
      match const_info_exact ci with
      | CInt z    => typed_float_of_const ft (fc_of_Z z)
      | CFloat q  => typed_float_of_const ft q
      | CComplex c => match complex_real_if_imag_zero c with
                      | Some q => typed_float_of_const ft q
                      | None   => None end
      | _         => None
      end
  end end.

(** complex-target conversion: same-format complex returns the identity; a matching-component typed
    float reuses that float as the real component (positive-zero imaginary); otherwise embed the exact source
    numerically ([numeric_const_to_complex]) and round each component ONCE at the destination component format
    (a different-format complex source rounds its two [typed_complex_exact] components — the component-level
    double-rounding boundary). *)
Definition convert_to_complex (ct : ComplexType) (ci : ConstInfo) : option (TypedConst (TComplex ct)) :=
  match same_ct_identity ct ci with
  | Some tc => Some tc
  | None =>
  match reuse_float_as_complex ct ci with
  | Some tc => Some tc
  | None =>
      match numeric_const_to_complex (const_info_exact ci) with
      | Some c => typed_complex_of_const ct c
      | None   => None
      end
  end end.

(** the ONE target-directed constant-conversion authority: it CONSUMES the source constant
    status and produces an INTRINSIC typed constant at the destination.  Integer target: the exact source (an
    integer, a float's integral exact value, or a zero-imaginary complex's integral real) must be
    representable.  Float target: [convert_to_float].  Complex target: [convert_to_complex].  bool/string
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
      | CComplex c => match complex_real_if_imag_zero c with
                      | Some q => match fc_to_int q with
                                  | Some z => typed_integer_of_Z it z
                                  | None => None end
                      | None => None end
      | _ => None
      end
  | TFloat ft => convert_to_float ft ci
  | TComplex ct => convert_to_complex ct ci
  end.

(** the SINGLE typing/defaulting construction for an UNTYPED constant at a REQUESTED type: bool/string
    at their own type; every NUMERIC target ROUTES THROUGH the ONE [convert_const] authority applied to the
    untyped status — so untyped representability AGREES with explicit conversion BY CONSTRUCTION (no second
    range/rounding/dispatch table).  A numeric constant at a bool/string target, or bool/string at a numeric
    target, is [None]. *)
Definition type_untyped_const_at (t : GoType) (c : GoConst) : option (TypedConst t) :=
  match t with
  | TBool       => match c with CBool b   => Some (TCBool b)  | _ => None end
  | TString     => match c with CString s => Some (TCString s) | _ => None end
  | TInteger it => convert_const (TInteger it) (CIUntyped c)
  | TFloat ft   => convert_const (TFloat ft) (CIUntyped c)
  | TComplex ct => convert_const (TComplex ct) (CIUntyped c)
  end.

(** representability is DERIVED from successful typing at the requested type — and for numeric targets that
    typing IS [convert_const], so representability and explicit conversion cannot disagree. *)
Definition ConstRepresentable (t : GoType) (c : GoConst) : Prop :=
  exists tc : TypedConst t, type_untyped_const_at t c = Some tc.

Definition const_representableb (t : GoType) (c : GoConst) : bool :=
  match type_untyped_const_at t c with Some _ => true | None => false end.

Lemma const_representableb_iff : forall t c, const_representableb t c = true <-> ConstRepresentable t c.
Proof.
  intros t c; unfold const_representableb, ConstRepresentable.
  destruct (type_untyped_const_at t c) as [tc|] eqn:E; split.
  - intros _; exists tc; reflexivity.
  - intros _; reflexivity.
  - discriminate.
  - intros [tc' H]; discriminate.
Qed.

(** untyped representability of a NUMERIC target is DEFINITIONALLY [convert_const] of the untyped status — the
    representability relation and the explicit-conversion authority never disagree. *)
Lemma type_untyped_int_convert : forall it c,
  type_untyped_const_at (TInteger it) c = convert_const (TInteger it) (CIUntyped c).
Proof. reflexivity. Qed.
Lemma type_untyped_float_convert : forall ft c,
  type_untyped_const_at (TFloat ft) c = convert_const (TFloat ft) (CIUntyped c).
Proof. reflexivity. Qed.
Lemma type_untyped_complex_convert : forall ct c,
  type_untyped_const_at (TComplex ct) c = convert_const (TComplex ct) (CIUntyped c).
Proof. reflexivity. Qed.

(** ---- the index-free typing specification, parameterized by ONE source-name resolver ----

    A conversion node carries a SOURCE type name ([GoAST.TypeSyntax]); the semantic target [GoType] is obtained
    by resolving that name in the current predeclared context.  That resolution is compiler-owned (§7): its ONE
    authority — the source-name-to-[GoType] table — lives in [GoCompile], NEVER here.  So the whole index-free
    typing spec ([const_info] … [ProgramTyped]) is parameterized by a total resolver [rt : TypeSyntax -> GoType]
    that [GoCompile] supplies and against which the production occurrence pass is proved exact.  The single
    target-directed conversion authority [convert_const] is unchanged: it still receives a semantic [GoType]
    ([rt ts]) and never inspects a source name or a rendered string. *)
Section TypingResolver.
Variable rt : GoAST.TypeSyntax -> GoType.

Fixpoint const_info (e : GoExpr) : option ConstInfo :=
  match e with
  | EBool b   => Some (CIUntyped (CBool b))
  | EInt n    => Some (CIUntyped (CInt (Z.of_N n)))
  | ENeg n    => Some (CIUntyped (CInt (- Z.of_N n)))
  | EString s => Some (CIUntyped (CString s))
  | EFloat d  => Some (CIUntyped (CFloat (decimal_value d)))
  | EComplex dc => Some (CIUntyped (CComplex (decimal_complex_value dc)))
  | EConvert ts x =>
      match const_info x with
      | Some ci => option_map (CITyped (rt ts)) (convert_const (rt ts) ci)
      | None => None
      end
  end.

(** the ONE-NODE semantic layer: the constant status of a SINGLE expression node, given the ALREADY
    COMPUTED status of its one current expression child (None for a leaf, or a conversion whose child failed).
    A leaf constructs its exact untyped value (the child input is irrelevant); a conversion consumes the child
    status and calls the SAME [convert_const] — no duplicated conversion/range/rounding logic, no second
    classifier.  A bottom-up analysis applies this once per occurrence, reading the child status from a map
    instead of recomputing [const_info] over the whole subtree. *)
Definition const_info_step (e : GoExpr) (child : option ConstInfo) : option ConstInfo :=
  match e with
  | EBool b     => Some (CIUntyped (CBool b))
  | EInt n      => Some (CIUntyped (CInt (Z.of_N n)))
  | ENeg n      => Some (CIUntyped (CInt (- Z.of_N n)))
  | EString s   => Some (CIUntyped (CString s))
  | EFloat d    => Some (CIUntyped (CFloat (decimal_value d)))
  | EComplex dc => Some (CIUntyped (CComplex (decimal_complex_value dc)))
  | EConvert ts _ =>
      match child with Some ci => option_map (CITyped (rt ts)) (convert_const (rt ts) ci) | None => None end
  end.

(** the one current expression child of a node (the conversion operand); [None] for leaves. *)
Definition expr_child (e : GoExpr) : option GoExpr :=
  match e with
  | EConvert _ e' => Some e'
  | _ => None
  end.

(** the ONE recursive authority reflects the one-node step: [const_info] of a node is [const_info_step] applied
    to the status of its current child.  So [const_info] and the bottom-up analysis use the SAME step. *)
Lemma const_info_step_reflect : forall e,
  const_info e = const_info_step e (match expr_child e with Some c => const_info c | None => None end).
Proof. intro e; destruct e; reflexivity. Qed.

(** defaulting: an UNTYPED constant becomes a validated typed constant in a use context — bool/string
    always; an int defaults to platform [int] iff representable; a bare float performs its ONE F64 rounding
    (via [round_typed_float]).  A bare overflowing float has no default typed constant. *)
Definition default_const (c : GoConst) : option ResolvedConst :=
  match c with
  | CBool b    => Some (pack_resolved TBool (TCBool b))
  | CInt z     => option_map (pack_resolved (TInteger IInt)) (typed_integer_of_Z IInt z)
  | CFloat q   => option_map (pack_resolved (TFloat F64)) (typed_float_of_const F64 q)
  | CComplex c => option_map (pack_resolved (TComplex C128)) (typed_complex_of_const C128 c)
  | CString s  => Some (pack_resolved TString (TCString s))
  end.

(** resolve a constant status to a validated typed constant: an untyped status defaults; a typed status is
    packed unchanged (its validity is intrinsic — no [ci_ok], no "typed constants are trusted" branch). *)
Definition resolve_const_info (ci : ConstInfo) : option ResolvedConst :=
  match ci with
  | CIUntyped c  => default_const c
  | CITyped t tc => Some (pack_resolved t tc)
  end.

(** a successful constant-status resolution is deterministic (a function of the syntax). *)
Lemma const_info_deterministic : forall e ci1 ci2,
  const_info e = Some ci1 -> const_info e = Some ci2 -> ci1 = ci2.
Proof. intros e ci1 ci2 H1 H2; rewrite H1 in H2; injection H2 as <-; reflexivity. Qed.

(** [EInt 0] and [ENeg 0] denote the SAME untyped constant (signed zero is one value). *)
Lemma const_info_zero_sign : const_info (EInt 0) = const_info (ENeg 0).
Proof. reflexivity. Qed.

(** SAME-FORMAT FLOAT IDENTITY (LOAD-BEARING): converting a typed float constant to its OWN format
    returns the EXISTING [TypedFloatConst] unchanged — no reround, no reconstruction.  This is exactly what
    makes nested same-type conversions [float32(float32 q)] / [float64(float64 q)] identities at the typed-
    constant level, so evaluation never rounds a typed float constant a second time. *)
Lemma convert_const_same_float : forall ft (tc : TypedConst (TFloat ft)),
  convert_const (TFloat ft) (CITyped (TFloat ft) tc) = Some tc.
Proof. intros ft tc; destruct ft; reflexivity. Qed.

(** SAME-FORMAT COMPLEX IDENTITY (LOAD-BEARING, UNIVERSAL): converting a typed complex constant to its
    OWN format returns the EXISTING [TypedComplexConst] unchanged — no reround, no component reconstruction,
    the same stored runtime component objects.  This is what makes [complex64(complex64 ...)] /
    [complex128(complex128 ...)] identities at the typed-constant level. *)
Lemma convert_const_same_complex : forall ct (tc : TypedConst (TComplex ct)),
  convert_const (TComplex ct) (CITyped (TComplex ct) tc) = Some tc.
Proof. intros ct tc; destruct ct; reflexivity. Qed.

(** COMPONENT REUSE (LOAD-BEARING, UNIVERSAL): converting a typed FLOAT constant whose format is the
    complex component format to that complex type REUSES the existing [TypedFloatConst] as the REAL component
    (the SAME object [typed_const_float tc], no reround); the imaginary component is the constructed +0. *)
Lemma convert_complex_reuses_float_component : forall ct (tc : TypedConst (TFloat (complex_component_type ct))),
  exists tcc, convert_const (TComplex ct) (CITyped (TFloat (complex_component_type ct)) tc)
                = Some (TCComplex ct tcc)
           /\ tcc_real tcc = typed_const_float tc.
Proof.
  intros ct tc; destruct ct.
  - destruct (round_typed_float F32 fc_zero) as [imz|] eqn:Hz; [ | vm_compute in Hz; discriminate ].
    exists (mkTCC (typed_const_float tc) imz); split; [ | reflexivity ].
    unfold convert_const, convert_to_complex, same_ct_identity, reuse_float_as_complex;
      cbn [complex_component_type float_type_eq_dec eq_rect option_map]; rewrite Hz; reflexivity.
  - destruct (round_typed_float F64 fc_zero) as [imz|] eqn:Hz; [ | vm_compute in Hz; discriminate ].
    exists (mkTCC (typed_const_float tc) imz); split; [ | reflexivity ].
    unfold convert_const, convert_to_complex, same_ct_identity, reuse_float_as_complex;
      cbn [complex_component_type float_type_eq_dec eq_rect option_map]; rewrite Hz; reflexivity.
Qed.

(** COMPONENT PROJECTION (LOAD-BEARING, UNIVERSAL): converting a typed COMPLEX constant whose EXACT
    imaginary component is zero to its matching component float PROJECTS the existing real [TypedFloatConst]
    DIRECTLY (the SAME object [tcc_real (typed_const_complex tc)], no reround). *)
Lemma convert_float_reuses_complex_component : forall ct (tc : TypedConst (TComplex ct)),
  cc_imag_is_zero (typed_complex_exact (typed_const_complex tc)) = true ->
  convert_const (TFloat (complex_component_type ct)) (CITyped (TComplex ct) tc)
    = Some (TCFloat (complex_component_type ct) (tcc_real (typed_const_complex tc))).
Proof.
  intros ct tc Hz; destruct ct;
    unfold convert_const, convert_to_float, same_ft_identity, reuse_complex_as_float;
    cbn [complex_component_type float_type_eq_dec eq_rect]; rewrite Hz; reflexivity.
Qed.

(** the exact value of an INTEGER-typed constant is an in-range [CInt] — extracted via an index-annotated
    match (axiom-free; no dependent destruction / UIP). *)
Lemma typed_const_int_value : forall it (tc : TypedConst (TInteger it)),
  exists z, typed_const_exact tc = CInt z /\ integer_representableb it z = true.
Proof.
  intros it tc.
  refine (match tc as tc0 in TypedConst t
          return (match t with
                  | TInteger it' => exists z, typed_const_exact tc0 = CInt z /\ integer_representableb it' z = true
                  | _ => True end)
          with
          | TCInteger it0 z0 Hpf => _
          | _ => I
          end).
  exists z0; split; [ reflexivity | exact Hpf ].
Qed.

(** the UNIVERSAL integer same-type identity: converting a typed integer constant to its OWN type
    PRESERVES the exact value and type (an identity up to the proof-irrelevant range proof). *)
Lemma convert_const_same_int : forall it (tc : TypedConst (TInteger it)),
  exists tc', convert_const (TInteger it) (CITyped (TInteger it) tc) = Some tc'
           /\ typed_const_exact tc' = typed_const_exact tc.
Proof.
  intros it tc.
  destruct (typed_const_int_value it tc) as [ z [ Hexact Hz ] ].
  cbn [convert_const const_info_exact]; rewrite Hexact.
  unfold typed_integer_of_Z; destruct (bool_true_dec (integer_representableb it z)) as [H'|H'].
  - exists (TCInteger it z H'); split; reflexivity.
  - congruence.
Qed.

(** an invalid inner conversion propagates: it cannot be revived by an outer conversion (any target name). *)
Lemma const_info_conv_none : forall ts e,
  const_info e = None -> const_info (EConvert ts e) = None.
Proof. intros ts e H; simpl; rewrite H; reflexivity. Qed.

(** ---- use-context resolution: one expression-use context and its per-type policy ---- *)
Inductive ExprUse : Type :=
| UsePrintlnArg.

(** the exhaustive per-type use policy.  A `println` argument accepts ALL current types — bool, every integer
    member, every float format, every complex format, and string. *)
Inductive UseAllows : ExprUse -> GoType -> Prop :=
| UAPrintlnBool    : UseAllows UsePrintlnArg TBool
| UAPrintlnInt     : forall it, UseAllows UsePrintlnArg (TInteger it)
| UAPrintlnFloat   : forall ft, UseAllows UsePrintlnArg (TFloat ft)
| UAPrintlnComplex : forall ct, UseAllows UsePrintlnArg (TComplex ct)
| UAPrintlnString  : UseAllows UsePrintlnArg TString.

Definition use_allowsb (u : ExprUse) (t : GoType) : bool :=
  match u, t with
  | UsePrintlnArg, TBool       => true
  | UsePrintlnArg, TInteger _  => true
  | UsePrintlnArg, TFloat _    => true
  | UsePrintlnArg, TComplex _  => true
  | UsePrintlnArg, TString     => true
  end.

Lemma use_allowsb_iff : forall u t, use_allowsb u t = true <-> UseAllows u t.
Proof.
  intros [] [| it | ft | ct |]; simpl; split; intro H; try constructor; try reflexivity; inversion H.
Qed.

(** the declarative resolved typing of ONE expression in a use context: the expression analyzes to a
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

Definition FileTyped (decls : list GoDecl) : Prop := Forall DeclTyped decls.
Definition SourceFileTyped (sf : GoSourceFile) : Prop := FileTyped (source_decls sf).

(** whole-program typing is MAP-BASED — quantified over the standard map's [MapsTo], NOT over an
    input-order list.  Every source file bound in the forest is typed. *)
Definition ProgramTyped (p : GoProgram) : Prop :=
  forall path sf, GoAST.maps_to_file path sf (prog_files p) -> SourceFileTyped sf.

Definition stmt_typedb (s : GoStmt) : bool :=
  match s with SPrintln args => forallb (expr_typedb UsePrintlnArg) args end.
Definition decl_typedb (d : GoDecl) : bool :=
  match d with DMain body => forallb stmt_typedb body end.
Definition file_typedb (decls : list GoDecl) : bool := forallb decl_typedb decls.
Definition source_file_typedb (sf : GoSourceFile) : bool := file_typedb (source_decls sf).
(** the executable checker traverses the standard map's CANONICAL derived enumeration ([elements]). *)
Definition program_typedb (p : GoProgram) : bool :=
  forallb (fun b => source_file_typedb (snd b)) (GoAST.file_bindings (prog_files p)).

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

Lemma source_file_typedb_iff : forall sf, source_file_typedb sf = true <-> SourceFileTyped sf.
Proof. intro sf; apply file_typedb_iff. Qed.

(** the map-based judgment reflects the executable checker: [forallb] over the canonical [elements] is
    exactly the [MapsTo]-quantified typing (the standard map bridges [elements] and [MapsTo]). *)
Lemma program_typedb_iff : forall p, program_typedb p = true <-> ProgramTyped p.
Proof.
  intro p. unfold program_typedb, ProgramTyped.
  rewrite (forallb_Forall (fun b => source_file_typedb (snd b)) (fun b => SourceFileTyped (snd b))
             (GoAST.file_bindings (prog_files p)) (fun b => source_file_typedb_iff (snd b))).
  unfold GoAST.maps_to_file, GoAST.file_bindings. split.
  - intros H path sf Hmt.
    apply GoAST.FMF.elements_mapsto_iff, InA_alt in Hmt.
    destruct Hmt as [[k' e'] [Heq Hin]]. destruct Heq as [_ He]. cbn in *.
    rewrite Forall_forall in H. specialize (H (k', e') Hin). cbn in H. rewrite He. exact H.
  - intros H. apply Forall_forall. intros [k e] Hin. cbn.
    apply (H k e), GoAST.FMF.elements_mapsto_iff, InA_alt.
    exists (k, e). split; [ split; reflexivity | exact Hin ].
Qed.

(** ---- ORDER-INDEPENDENCE / EXTENSIONALITY: whole-program typing is a property of the file MAP, never
    of a construction-order list.  It respects semantic map equality both as a [Prop] and reflected as a
    [bool], and is therefore invariant under reordered [build_program] construction. ---- *)

(** [ProgramTyped] respects [FilesEqual] (semantic map equality) — equal maps type identically. *)
Lemma ProgramTyped_Equal : forall p1 p2,
  GoAST.FilesEqual (prog_files p1) (prog_files p2) -> ProgramTyped p1 -> ProgramTyped p2.
Proof.
  intros p1 p2 Heq Ht path sf Hmt. apply (Ht path sf). unfold GoAST.maps_to_file in *.
  apply GoAST.FMF.find_mapsto_iff. rewrite (Heq path). apply GoAST.FMF.find_mapsto_iff. exact Hmt.
Qed.

(** the reflected checker agrees on [FilesEqual] maps — no dependence on the backing tree's element order. *)
Lemma program_typedb_Equal : forall p1 p2,
  GoAST.FilesEqual (prog_files p1) (prog_files p2) -> program_typedb p1 = program_typedb p2.
Proof.
  intros p1 p2 Heq.
  destruct (program_typedb p1) eqn:E1; destruct (program_typedb p2) eqn:E2; try reflexivity.
  - exfalso. apply program_typedb_iff in E1.
    assert (program_typedb p2 = true)
      by (apply program_typedb_iff; exact (ProgramTyped_Equal p1 p2 Heq E1)).
    rewrite E2 in H; discriminate.
  - exfalso. apply program_typedb_iff in E2.
    assert (program_typedb p1 = true)
      by (apply program_typedb_iff;
          exact (ProgramTyped_Equal p2 p1 (GoAST.FilesEqual_sym _ _ Heq) E2)).
    rewrite E1 in H; discriminate.
Qed.

(** reordered construction types identically: a permuted node list builds a [FilesEqual] map, so its
    whole-program typing result is the same. *)
Theorem program_typedb_build_permutation : forall ms nodes1 nodes2 p1 p2,
  Permutation nodes1 nodes2 ->
  build_program ms nodes1 = Some p1 -> build_program ms nodes2 = Some p2 ->
  program_typedb p1 = program_typedb p2.
Proof.
  intros ms nodes1 nodes2 p1 p2 Hperm Hb1 Hb2. apply program_typedb_Equal.
  unfold build_program in *.
  destruct (filemap_of_nodes nodes1) as [fm1|] eqn:F1; [ | discriminate ].
  destruct (filemap_of_nodes nodes2) as [fm2|] eqn:F2; [ | discriminate ].
  injection Hb1 as <-. injection Hb2 as <-. cbn [prog_files].
  exact (filemap_of_nodes_permutation nodes1 nodes2 fm1 fm2 Hperm F1 F2).
Qed.

(** the empty file is typed vacuously; so is the empty program. *)
Lemma empty_file_typed : FileTyped [].
Proof. constructor. Qed.

End TypingResolver.

(** ---- rt-free shared constant fixtures ----

    The canonical integer literal and the decimal / decimal-complex constants below are referenced by
    [GoSafe] / [GoRender] / the e2e witnesses and by the concrete typing witnesses re-established, with the
    predeclared resolver, in [GoCompile].  They carry no source type name and so need no resolver.  The
    concrete source-name conversion witnesses (every [resolve_expr] / [const_info] over an [EConvert], the
    per-type boundary theorems, and the double-round scars) live in [GoCompile], the SOLE owner of the
    source-name-to-[GoType] resolver (§7, §9) — never here. *)
Definition int_lit (z : Z) : GoExpr :=
  if Z.leb 0 z then EInt (Z.to_N z) else ENeg (Z.to_N (- z)).

(** decimal / decimal-complex constant fixtures shared with GoSafe / GoRender / the e2e witnesses. *)
Definition d_15em1 : DecimalFloat := mkDecimal 15 (-1) eq_refl.   (* 1.5 *)
Definition d_3    : DecimalFloat := mkDecimal 3 0 eq_refl.        (* 3.0 *)
Definition d_35em1 : DecimalFloat := mkDecimal 35 (-1) eq_refl.   (* 3.5 *)
Definition d_128  : DecimalFloat := mkDecimal 128 0 eq_refl.      (* 128.0 *)
Definition d_m1   : DecimalFloat := mkDecimal (-1) 0 eq_refl.     (* -1.0 *)
Definition d_scar : DecimalFloat := mkDecimal 2305843146652647425 0 eq_refl.
Definition d_m25em1 : DecimalFloat := mkDecimal (-25) (-1) eq_refl.  (* -2.5 *)
Definition d_127_0  : DecimalFloat := mkDecimal 127 0 eq_refl.
Definition d_1_0    : DecimalFloat := mkDecimal 1 0 eq_refl.
Definition d_m1_0   : DecimalFloat := mkDecimal (-1) 0 eq_refl.
Definition d_0_0    : DecimalFloat := mkDecimal 0 0 eq_refl.
Definition dc_1p5_m2p5 : DecimalComplex := mkDC d_15em1 d_m25em1.
Definition d_tiny_imag : DecimalFloat := mkDecimal 1 (-50) eq_refl.   (* 1e-50: nonzero, underflows binary32 -> +0 *)

(** typed-constant MISMATCH is UNREPRESENTABLE — the dependent index + carried range proof make an
    ill-typed / out-of-range typed constant impossible to CONSTRUCT ([Fail] adds nothing to the env). *)
Fail Definition mismatch_string_carrying_int : TypedConst TString := TCInteger IInt 3 eq_refl.
Fail Definition mismatch_int_out_of_range : TypedConst (TInteger IInt8) := TCInteger IInt8 128 eq_refl.
Fail Definition mismatch_float_carrying_bool : TypedConst (TFloat F64) := TCBool true.

(** every string literal is representable at [TString], for ARBITRARY finite byte sequences. *)
Lemma str_representable : forall s, ConstRepresentable TString (CString s).
Proof. intro s; exists (TCString s); reflexivity. Qed.
Lemma str_representableb : forall s, const_representableb TString (CString s) = true.
Proof. reflexivity. Qed.

(* GENERIC [forallb] HELPERS for the whole-program typing folds.

   GoTypes owns the type/constant relation ONLY — never any occurrence/index traversal.  The per-occurrence
   typing predicate ([occ_arg_typedb]) and its occurrence-stream aggregation chain ([occs_*_typedb_eq]) live in
   GoCompile — the SOLE meeting point of GoIndex identity and GoTypes semantics — so GoTypes needs no GoIndex
   import.  These two lemmas are index-free [forallb] plumbing reused by that chain (in GoCompile) and by the
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
