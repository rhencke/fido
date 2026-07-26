(** Property — the exact ABSTRACT println-trace semantics of the admitted fragment, and [Program], the
    permanent safety capability boundary over a [Compilable.Program].

    This is NOT a full Go operational semantics — it is a deterministic abstract-trace mapping for the
    current fragment: values are REAL Go values ([BoolValue] / [IntegerValue : Integer.Kind -> Z] carrying the exact
    mathematical value at its exact integer type / [FloatValue : forall ft, Float.Value ft] carrying a canonical
    binary [spec_float] at its format / [ComplexValue : forall ct, Complex.Value ct] a PAIR of general
    [Float.Value] components (so a RUNTIME complex MAY carry -0/inf/NaN, though a typed complex CONSTANT cannot)
    / [StringValue : exact bytes], not source spelling — so [Syntax.IntegerLiteral 0] and
    [Syntax.NegatedIntegerLiteral 0] evaluate equal), and a file's behaviour is the ordered sequence of its [println] calls (each the
    list of its argument VALUES).  Runtime values carry the SAME [Typing.SemanticType] authority as the compiler/type
    system ([value_type]; there is no separate runtime type universe), and every runtime value is
    WELL-FORMED ([ValueWellFormed] — [IntegerValue it z] iff [z] fits [it]; a [FloatValue] / [ComplexValue] is canonical by construction, so
    True).  A float/complex constant ROUNDS ONCE into its canonical [Float.Value] component(s); constant evaluation produces only
    finite/+0 (never -0/inf/NaN).  Because raw syntax can now contain a compiler-invalid integer/float/complex
    conversion (a component overflow, a nonzero-imaginary complex->scalar, a fractional or out-of-range
    float/complex->integer, or a wrong-type conversion), evaluation is PARTIAL ([eval_expr : Syntax.Expr -> option Value]) and
    is DERIVED from the one constant-status analysis ([Typing.constant_info]) — it invents no second
    conversion/type/value authority.  A resolved expression always evaluates to a well-formed value of its
    resolved [Typing.SemanticType] ([eval_expr_resolved]).  There is no panic/blocking/scheduler/heap algebra: no admitted
    operation can panic or diverge (a constant conversion failure is a COMPILE-TIME typing failure, not a
    runtime panic), so predeclaring one would be scaffolding.

    [Program] is the PERMANENT home for guarantees BEYOND compiler acceptance (nil-deref / bounds /
    panic-freedom / happens-before / race- or deadlock-freedom subsets / termination / protocol invariants /
    user- or LLM-added refinements).  [Property cp := True] is honest TODAY only because every
    [Compilable.Program] representable in this fragment satisfies the current safety floor — NOT by circular
    reference to compilation.  Stronger proofs REFINE it over the same [Compilable.Program]; they never fork
    the compiler, AST, renderer, or semantics. *)
From Stdlib Require Import ZArith List Bool String.
From Stdlib Require Import Floats.SpecFloat.
From Fido Require Import Integer Float Complex Syntax Typing Compilable.
Import ListNotations.

(** Evaluation reads the one constant-status analysis at the compiler-owned predeclared resolver
    ([Compilable.predeclared_type], §7); these parsing notations specialize the [Typing] index-free spec at
    that ONE resolver so evaluation stays derived from — never a second authority over — the same analysis. *)
Local Notation constant_info        := (Typing.constant_info Compilable.predeclared_type) (only parsing).
Local Notation resolve_constant := (Typing.resolve_constant Compilable.predeclared_type) (only parsing).
Local Notation resolve      := (Typing.resolve Compilable.predeclared_type) (only parsing).
Local Notation Resolve       := (Typing.Resolve Compilable.predeclared_type) (only parsing).

Inductive Value : Type :=
| BoolValue    : bool -> Value
| IntegerValue : Integer.Kind -> Z -> Value
| FloatValue   : forall ft, Float.Value ft -> Value
| ComplexValue : forall ct, Complex.Value ct -> Value
| StringValue  : string -> Value.

(** The runtime type of a value — the SAME [Typing.SemanticType] authority ([Typing]) the compiler/type system uses; an
    integer value carries its exact [Integer.Kind], a float value its [Float.Kind], a complex value its
    [Complex.Kind] (same component mapping).  A [StringValue] is the EXACT runtime byte sequence. *)
Definition value_type (v : Value) : Typing.SemanticType :=
  match v with
  | BoolValue _ => Typing.BoolType | IntegerValue it _ => Typing.IntegerType it | FloatValue ft _ => Typing.FloatType ft
  | ComplexValue ct _ => Typing.ComplexType ct | StringValue _ => Typing.StringType
  end.

(** value well-formedness: an integer value's magnitude fits its type; a float / complex value is canonical
    for its format BY CONSTRUCTION (the invariant lives in [Float.Value] / its component [Float.Value]s), so no
    extra side condition. *)
Definition ValueWellFormed (v : Value) : Prop :=
  match v with
  | BoolValue _ => True | IntegerValue it z => Integer.Representable it z
  | FloatValue _ _ => True | ComplexValue _ _ => True | StringValue _ => True
  end.
Definition value_well_formedb (v : Value) : bool :=
  match v with
  | BoolValue _ => true | IntegerValue it z => Integer.representableb it z
  | FloatValue _ _ => true | ComplexValue _ _ => true | StringValue _ => true
  end.

Lemma value_well_formedb_iff : forall v, value_well_formedb v = true <-> ValueWellFormed v.
Proof.
  intros [ b | it z | ft fv | ct cv | s ]; simpl.
  - split; [ intros _; exact I | intros _; reflexivity ].
  - apply Integer.representableb_spec.
  - split; [ intros _; exact I | intros _; reflexivity ].
  - split; [ intros _; exact I | intros _; reflexivity ].
  - split; [ intros _; exact I | intros _; reflexivity ].
Qed.

(** the intrinsic typed constant PROJECTS to a runtime value.  There is NO total runtime->constant
    fallback: NaN / infinity / negative-zero runtime values are not constants (an honest RELATION describes
    when a value denotes a constant). *)

(** the ONE total typed-constant-to-runtime map: bool/int/string are direct; a FLOAT PROJECTS its stored
    [Float.runtime] — it does NOT round again (no [Float.round_ieee]/[Float.round_constant]/[round_typed_float]).  A
    typed integer's carried range proof makes the value well-formed by construction. *)
Definition typed_constant_to_value {t : Typing.SemanticType} (tc : Typing.TypedConstant t) : Value :=
  match tc with
  | Typing.TypedBool b         => BoolValue b
  | Typing.TypedInteger it z _ => IntegerValue it z
  | Typing.TypedFloat ft tfc   => FloatValue ft (Float.runtime tfc)
  | Typing.TypedComplex ct tcc => ComplexValue ct (Complex.typed_runtime tcc)
  | Typing.TypedString s       => StringValue s
  end.

(** the projection has the intrinsic type and is well-formed by construction (short projections). *)
Lemma typed_constant_to_value_type : forall t (tc : Typing.TypedConstant t), value_type (typed_constant_to_value tc) = t.
Proof. intros t tc; destruct tc; reflexivity. Qed.

Lemma typed_constant_to_value_well_formed : forall t (tc : Typing.TypedConstant t), ValueWellFormed (typed_constant_to_value tc).
Proof.
  intros t tc; destruct tc as [ b | it z Hpf | ft tfc | ct tcc | s ]; cbn [typed_constant_to_value ValueWellFormed].
  - exact I.
  - apply Integer.representableb_spec; exact Hpf.
  - exact I.
  - exact I.
  - exact I.
Qed.

(** no second rounding: evaluating a typed float / complex constant PROJECTS its stored runtime,
    reflexively (a complex projects its pair of stored component runtimes). *)
Lemma typed_constant_to_value_float : forall ft (tfc : Float.TypedConstant ft),
  typed_constant_to_value (Typing.TypedFloat ft tfc) = FloatValue ft (Float.runtime tfc).
Proof. reflexivity. Qed.
Lemma typed_constant_to_value_complex : forall ct (tcc : Complex.TypedConstant ct),
  typed_constant_to_value (Typing.TypedComplex ct tcc) = ComplexValue ct (Complex.typed_runtime tcc).
Proof. reflexivity. Qed.

(** an HONEST value/constant denotation relation.  The float case is phrased through [Float.TypedConstant]
    coherence: a typed-float-constant runtime denotes its exact [Float.exact].  A standalone NaN / infinity /
    negative-zero runtime value has NO constructor here, so it denotes NO constant. *)
Inductive ValueDenotesConstant : Value -> Typing.Constant -> Prop :=
| DenotesBool    : forall b, ValueDenotesConstant (BoolValue b) (Typing.BoolConstant b)
| DenotesInteger     : forall it z, Integer.Representable it z -> ValueDenotesConstant (IntegerValue it z) (Typing.IntegerConstant z)
| DenotesFloat   : forall ft (tfc : Float.TypedConstant ft),
    ValueDenotesConstant (FloatValue ft (Float.runtime tfc)) (Typing.FloatConstant (Float.exact tfc))
| DenotesComplex : forall ct (tcc : Complex.TypedConstant ct),
    ValueDenotesConstant (ComplexValue ct (Complex.typed_runtime tcc)) (Typing.ComplexConstant (Complex.typed_exact tcc))
| DenotesString  : forall s, ValueDenotesConstant (StringValue s) (Typing.StringConstant s).

(** the projected runtime value denotes the typed constant's exact value, by construction. *)
Lemma typed_constant_to_value_denotes : forall t (tc : Typing.TypedConstant t),
  ValueDenotesConstant (typed_constant_to_value tc) (Typing.typed_exact tc).
Proof.
  intros t tc; destruct tc as [ b | it z Hpf | ft tfc | ct tcc | s ];
    cbn [typed_constant_to_value Typing.typed_exact].
  - constructor.
  - constructor; apply Integer.representableb_spec; exact Hpf.
  - constructor.
  - constructor.
  - constructor.
Qed.

(** a denoting float value's runtime is +0-or-finite: the ONLY float denotation is through
    [Float.TypedConstant] coherence. *)
Lemma value_denotes_constant_runtime : forall v c,
  ValueDenotesConstant v c ->
  match v with FloatValue _ fv => Float.constant_runtimeb (Float.ieee fv) = true | _ => True end.
Proof.
  intros v c H; destruct H as [ b | it z Hr | ft tfc | ct tcc | s ]; try exact I; apply (Float.shape tfc).
Qed.

(** a NaN / infinity / negative-zero runtime value has NO typed-constant denotation (there is no total
    runtime->constant fallback). *)
Lemma float_nonconstant_no_denotes : forall ft (fv : Float.Value ft) c,
  Float.constant_runtimeb (Float.ieee fv) = false -> ~ ValueDenotesConstant (FloatValue ft fv) c.
Proof.
  intros ft fv c Hshape H.
  pose proof (value_denotes_constant_runtime _ _ H) as Hs; cbn in Hs.
  rewrite Hshape in Hs; discriminate.
Qed.

(** the three concrete non-constant runtime values (canonical general-domain [Float.Value]s) that inhabit the
    runtime domain yet denote NO constant — NaN, +infinity, negative zero. *)
Example nan_f64_no_denotes : forall c, ~ ValueDenotesConstant (FloatValue F64 (Float.value_nan F64)) c.
Proof. intro c; apply float_nonconstant_no_denotes; reflexivity. Qed.
Example inf_f64_no_denotes : forall c, ~ ValueDenotesConstant (FloatValue F64 (Float.value_inf F64 false)) c.
Proof. intro c; apply float_nonconstant_no_denotes; reflexivity. Qed.
Example neg_zero_f64_no_denotes : forall c, ~ ValueDenotesConstant (FloatValue F64 Float.value_neg_zero_F64) c.
Proof. intro c; apply float_nonconstant_no_denotes; reflexivity. Qed.

(** a runtime complex value whose real OR imaginary component is not +0/finite (NaN, infinity, or
    negative zero) denotes NO constant — the ONLY complex denotation is through [Complex.TypedConstant] component
    coherence (both components +0/finite by [Float.shape]). *)
Lemma value_denotes_complex_runtime : forall v c,
  ValueDenotesConstant v c ->
  match v with
  | ComplexValue _ cv => Float.constant_runtimeb (Float.ieee (Complex.runtime_real cv)) = true
                     /\ Float.constant_runtimeb (Float.ieee (Complex.runtime_imaginary cv)) = true
  | _ => True
  end.
Proof.
  intros v c H; destruct H as [ b | it z Hr | ft tfc | ct tcc | s ]; try exact I; cbn.
  split; [ apply (Complex.typed_runtime_real_shape ct tcc)
         | apply (Complex.typed_runtime_imaginary_shape ct tcc) ].
Qed.

Lemma complex_nonconstant_no_denotes : forall ct (cv : Complex.Value ct) c,
  Float.constant_runtimeb (Float.ieee (Complex.runtime_real cv)) = false
  \/ Float.constant_runtimeb (Float.ieee (Complex.runtime_imaginary cv)) = false ->
  ~ ValueDenotesConstant (ComplexValue ct cv) c.
Proof.
  intros ct cv c Hbad H.
  pose proof (value_denotes_complex_runtime _ _ H) as Hs; cbn in Hs.
  destruct Hs as [Hr Hi]; destruct Hbad as [Hb|Hb]; congruence.
Qed.

(** concrete general-domain complex runtime values that denote NO constant: a NaN real component, an infinity
    imaginary component, a negative-zero component (item 48). *)
Example complex_nan_real_no_denotes : forall c,
  ~ ValueDenotesConstant (ComplexValue C128 (@Complex.make_value C128 (Float.value_nan F64) (Float.value_inf F64 false))) c.
Proof. intro c; apply complex_nonconstant_no_denotes; left; reflexivity. Qed.
Example complex_inf_imag_no_denotes : forall c,
  ~ ValueDenotesConstant (ComplexValue C128 (@Complex.make_value C128 Float.value_neg_zero_F64 (Float.value_inf F64 true))) c.
Proof. intro c; apply complex_nonconstant_no_denotes; right; reflexivity. Qed.
Example complex_neg_zero_no_denotes : forall c,
  ~ ValueDenotesConstant (ComplexValue C128 (@Complex.make_value C128 Float.value_neg_zero_F64 (Float.value_nan F64))) c.
Proof. intro c; apply complex_nonconstant_no_denotes; left; reflexivity. Qed.

(** Evaluation IS the one constant-status analysis RESOLVED to a validated typed constant and PROJECTED —
    no second case analysis over the raw syntax, no second conversion/representability decision, no second
    float rounding.  Partial: an invalid (nested) conversion or an out-of-range/overflowing default constant
    has NO value. *)
Definition eval_expr (e : Syntax.Expr) : option Value :=
  match constant_info e with
  | None => None
  | Some ci =>
      match Typing.resolve_constant_info ci with
      | None => None
      | Some (pack_resolved _ tc) => Some (typed_constant_to_value tc)
      end
  end.

(** the runtime value STORED IN a resolved typed constant — evaluation returns EXACTLY this, no re-derivation:
    for a float it is the packaged [Float.runtime], never a second rounding. *)
Definition resolved_constant_value (rc : Typing.ResolvedConstant) : Value :=
  match rc with pack_resolved _ tc => typed_constant_to_value tc end.

Lemma resolved_constant_value_float : forall ft (tfc : Float.TypedConstant ft),
  resolved_constant_value (pack_resolved (Typing.FloatType ft) (Typing.TypedFloat ft tfc)) = FloatValue ft (Float.runtime tfc).
Proof. intros ft tfc; cbn [resolved_constant_value]; apply typed_constant_to_value_float. Qed.

Lemma resolved_constant_value_complex : forall ct (tcc : Complex.TypedConstant ct),
  resolved_constant_value (pack_resolved (Typing.ComplexType ct) (Typing.TypedComplex ct tcc)) = ComplexValue ct (Complex.typed_runtime tcc).
Proof. intros ct tcc; cbn [resolved_constant_value]; apply typed_constant_to_value_complex. Qed.

(** A RESOLVED expression always evaluates to a well-formed value whose runtime type is EXACTLY the resolved
    [Typing.SemanticType] — the compiler's static resolution and the runtime value agree (one [Typing.SemanticType] authority). *)
Lemma eval_expr_resolved : forall u e t,
  Resolve u e t -> exists v, eval_expr e = Some v /\ value_type v = t /\ ValueWellFormed v.
Proof.
  intros u e t H; destruct H as [ u0 e0 ci rc Hci Hrc Hua ].
  unfold eval_expr; rewrite Hci, Hrc.
  destruct rc as [ t' tc ]; cbn [Typing.resolved_constant_type].
  exists (typed_constant_to_value tc).
  split; [ reflexivity | split; [ apply typed_constant_to_value_type | apply typed_constant_to_value_well_formed ] ].
Qed.

(** the resolved value has exactly the resolved type (gate-named corollary of [eval_expr_resolved]). *)
Lemma eval_expr_resolved_type : forall u e t,
  Resolve u e t -> exists v, eval_expr e = Some v /\ value_type v = t.
Proof.
  intros u e t H; destruct (eval_expr_resolved u e t H) as [ v [ Hev [ Hvt _ ] ] ];
    exists v; split; assumption.
Qed.

(** evaluation returns EXACTLY [typed_constant_to_value] of the SAME resolved typed constant that proves
    typing: [eval_expr] and [resolve_constant] walk the one [constant_info]->[Typing.resolve_constant_info] path, so a
    resolved value is precisely the [resolved_constant_value] of the resolved constant — a resolved float projects
    its packaged [Float.runtime], never a re-rounded value. *)
Lemma eval_expr_resolved_value : forall u e rc,
  resolve_constant u e = Some rc -> eval_expr e = Some (resolved_constant_value rc).
Proof.
  intros u e rc H.
  destruct (Typing.resolve_constant_sound Compilable.predeclared_type u e rc H) as [ ci [ Hci [ Hri _ ] ] ].
  destruct rc as [ t tc ]; unfold eval_expr; rewrite Hci, Hri; reflexivity.
Qed.

(** (float) evaluation projects the SAME STORED RUNTIME: a resolved typed FLOAT constant evaluates to
    exactly its packaged [Float.runtime] — the value built at the single construction rounding, never rounded
    again. *)
Corollary eval_projects_stored_float_runtime : forall u e ft (tfc : Float.TypedConstant ft),
  resolve_constant u e = Some (pack_resolved (Typing.FloatType ft) (Typing.TypedFloat ft tfc)) ->
  eval_expr e = Some (FloatValue ft (Float.runtime tfc)).
Proof.
  intros u e ft tfc H.
  rewrite (eval_expr_resolved_value u e _ H), resolved_constant_value_float; reflexivity.
Qed.

(** (complex) evaluation projects the SAME STORED RUNTIME: a resolved typed COMPLEX constant evaluates to
    exactly its packaged pair of component [Float.runtime]s ([Complex.typed_runtime]) — no component is
    reconstructed or re-rounded. *)
Corollary eval_projects_stored_complex_runtime : forall u e ct (tcc : Complex.TypedConstant ct),
  resolve_constant u e = Some (pack_resolved (Typing.ComplexType ct) (Typing.TypedComplex ct tcc)) ->
  eval_expr e = Some (ComplexValue ct (Complex.typed_runtime tcc)).
Proof.
  intros u e ct tcc H.
  rewrite (eval_expr_resolved_value u e _ H), resolved_constant_value_complex; reflexivity.
Qed.

(** the resolved runtime value IS [resolved_constant_value] of the resolved constant (point 5) AND DENOTES
    the resolved exact constant — the runtime/constant tie, phrased through the honest relation (never a total
    fallback). *)
Lemma eval_expr_denotes : forall u e t,
  Resolve u e t ->
  exists rc v, resolve_constant u e = Some rc /\ eval_expr e = Some v
            /\ v = resolved_constant_value rc
            /\ value_type v = Typing.resolved_constant_type rc /\ ValueWellFormed v
            /\ ValueDenotesConstant v (Typing.resolved_constant_exact rc).
Proof.
  intros u e t H; destruct H as [ u0 e0 ci rc Hci Hrc Hua ].
  apply use_allowsb_iff in Hua.
  destruct rc as [ t' tc ]; cbn [Typing.resolved_constant_type Typing.resolved_constant_exact] in *.
  exists (pack_resolved t' tc), (typed_constant_to_value tc).
  assert (Hrec : resolve_constant u0 e0 = Some (pack_resolved t' tc)).
  { unfold Typing.resolve_constant; rewrite Hci, Hrc; cbn [Typing.resolved_constant_type]; rewrite Hua; reflexivity. }
  unfold eval_expr; rewrite Hci, Hrc.
  split; [ exact Hrec | split; [ reflexivity |
    split; [ reflexivity |
    split; [ apply typed_constant_to_value_type |
    split; [ apply typed_constant_to_value_well_formed | apply typed_constant_to_value_denotes ] ] ] ] ].
Qed.

(** By VALUE, not spelling: a zero literal and a negated zero evaluate to the SAME value. *)
Lemma eval_zero_sign_agnostic : eval_expr (Syntax.IntegerLiteral 0) = eval_expr (Syntax.NegatedIntegerLiteral 0).
Proof. reflexivity. Qed.

(** the string VALUE: a string literal evaluates to the EXACT runtime byte sequence, whose runtime type is
    [Typing.StringType]. *)
Lemma eval_string_value : forall s, eval_expr (Syntax.StringLiteral s) = Some (StringValue s).
Proof. reflexivity. Qed.
Lemma eval_string_resolved_type : forall s t,
  Resolve Typing.PrintlnArgument (Syntax.StringLiteral s) t -> exists v, eval_expr (Syntax.StringLiteral s) = Some v /\ value_type v = t.
Proof. intros s t H; exact (eval_expr_resolved_type Typing.PrintlnArgument (Syntax.StringLiteral s) t H). Qed.

(** ---- the file's abstract behaviour: the ordered println calls (partial per argument — an ill-typed
    argument has no value; for a [Program] every argument resolves, so every option is [Some]) ---- *)
Definition eval_stmt (s : Syntax.Stmt) : list (option Value) :=
  match s with Syntax.Println args => map eval_expr args end.
Definition eval_decl (d : Syntax.Decl) : list (list (option Value)) :=
  match d with Syntax.Main body => map eval_stmt body end.
Definition eval_file (decls : list Syntax.Decl) : list (list (option Value)) := flat_map eval_decl decls.

(** ---- concrete evaluation fixtures ---- *)
Example eval_int8_127  : eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 127)) = Some (IntegerValue Integer.Int8 127). Proof. reflexivity. Qed.
Example eval_uint64_2p63 : eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.IntegerLiteral 9223372036854775808)) = Some (IntegerValue Integer.Uint64 9223372036854775808). Proof. reflexivity. Qed.
Example eval_int8_int16_127 : eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.IntegerLiteral 127))) = Some (IntegerValue Integer.Int8 127). Proof. reflexivity. Qed.
Example eval_int8_over_none : eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 128)) = None. Proof. reflexivity. Qed.
Example eval_bare_default : eval_expr (Syntax.IntegerLiteral 42) = Some (IntegerValue Integer.Int 42). Proof. reflexivity. Qed.
Example eval_2p63_none : eval_expr (Syntax.IntegerLiteral 9223372036854775808) = None. Proof. reflexivity. Qed.
Example well_formed_int8_127 : ValueWellFormed (IntegerValue Integer.Int8 127). Proof. simpl; apply Integer.representableb_spec; reflexivity. Qed.

(* ---- float evaluation ---- *)
(* a bare float evaluates to a float64 runtime value; an exact float->int constant to that integer *)
Example eval_float_type : option_map value_type (eval_expr (Syntax.FloatLiteral Typing.decimal_15em1)) = Some (Typing.FloatType F64).
Proof. reflexivity. Qed.
Example eval_int_of_3_0 : eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Int) (Syntax.FloatLiteral Typing.decimal_3)) = Some (IntegerValue Integer.Int 3).
Proof. reflexivity. Qed.
(* ★the direct-vs-nested double-round scar as an EXACT integer observation (no float printing): both
   rounded float32 constants are integer-valued, so uint64(...) yields exact decimal evidence. *)
Example eval_single_rounding_direct :
  eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.FloatLiteral Typing.decimal_single_rounding))) = Some (IntegerValue Integer.Uint64 2305843284091600896).
Proof. reflexivity. Qed.
Example eval_single_rounding_nested :
  eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.Convert (Syntax.type_expr_of_name Names.Float64) (Syntax.FloatLiteral Typing.decimal_single_rounding))))
    = Some (IntegerValue Integer.Uint64 2305843009213693952).
Proof. reflexivity. Qed.
Example eval_single_rounding_differ :
  eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.FloatLiteral Typing.decimal_single_rounding)))
    <> eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.Convert (Syntax.type_expr_of_name Names.Float64) (Syntax.FloatLiteral Typing.decimal_single_rounding)))).
Proof. rewrite eval_single_rounding_direct, eval_single_rounding_nested; discriminate. Qed.
(* the complex COMPONENT scar THROUGH EVALUATION: observing the stored real component of a zero-imaginary
   complex64 as uint64, the DIRECT F32 rounding differs from the NESTED complex128-then-complex64 double round.
   Evaluation PROJECTS the stored runtime component — no hidden reround — so the two stored runtimes differ. *)
Example eval_complex_single_rounding_direct :
  eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.ComplexLiteral (Complex.make_decimal Typing.decimal_single_rounding Typing.decimal_0_0))))
    = Some (IntegerValue Integer.Uint64 2305843284091600896).
Proof. vm_compute. reflexivity. Qed.
Example eval_complex_single_rounding_nested :
  eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.Convert (Syntax.type_expr_of_name Names.Complex128) (Syntax.ComplexLiteral (Complex.make_decimal Typing.decimal_single_rounding Typing.decimal_0_0)))))
    = Some (IntegerValue Integer.Uint64 2305843009213693952).
Proof. vm_compute. reflexivity. Qed.
Example eval_complex_single_rounding_differ :
  eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.ComplexLiteral (Complex.make_decimal Typing.decimal_single_rounding Typing.decimal_0_0))))
    <> eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.Convert (Syntax.type_expr_of_name Names.Complex128) (Syntax.ComplexLiteral (Complex.make_decimal Typing.decimal_single_rounding Typing.decimal_0_0))))).
Proof. rewrite eval_complex_single_rounding_direct, eval_complex_single_rounding_nested; discriminate. Qed.
(* constant underflow produces POSITIVE zero at runtime (never -0) *)
Example eval_underflow_pos_zero :
  option_map (fun v => match v with FloatValue _ fv => Float.ieee fv | _ => S754_nan end)
             (eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Float64) (Syntax.FloatLiteral (Float.make_decimal 1 (-330) eq_refl))))
    = Some (S754_zero false).
Proof. vm_compute. reflexivity. Qed.
(* ★a bare NEGATIVE underflow also produces +0 (never -0) — the constant zero has no sign. *)
Example eval_neg_underflow_pos_zero :
  option_map (fun v => match v with FloatValue _ fv => Float.ieee fv | _ => S754_nan end)
             (eval_expr (Syntax.FloatLiteral (Float.make_decimal (-1) (-330) eq_refl)))
    = Some (S754_zero false).
Proof. vm_compute. reflexivity. Qed.

(** ---- the safety certificate ---- *)

(** Trivial TODAY (the fragment has no unsafe operation), kept as the permanent extension point. *)
Definition Property (cp : Compilable.Program) : Prop := True.

Record Program : Type := make {
  compiled : Compilable.Program;
  proof     : Property compiled
}.

(** A compilation certificate suffices for the current fragment; [compiled] carries the genuine
    whole-program compile proof, so nothing uncompilable is certified. *)
Definition certify (cp : Compilable.Program) : Program := make cp I.

(** The certified program (what the public renderer/emitter traverse — only through Program). *)
Definition source (sp : Program) : Syntax.Program := Compilable.source (compiled sp).

(** RETENTION ACROSS THE SAFETY BOUNDARY: safety wraps the capability, so a [Program]
    transitively retains the EXACT [Compilable.Core] that justified admissibility — [certify] passes the object
    through untouched and [core] projects it.  A future safety proof therefore consumes the accepted causal
    object directly; it never re-elaborates to recover one.  Both facts hold by [reflexivity]. *)
Definition core (sp : Program) : Compilable.Core (source sp) := Compilable.core (compiled sp).

Theorem certify_retains_capability : forall cp, compiled (certify cp) = cp.
Proof. reflexivity. Qed.

Theorem certify_retains_core : forall cp, core (certify cp) = Compilable.core cp.
Proof. reflexivity. Qed.

(** (The package name is no longer a compiler-derived fact: each file's package clause is SOURCE-owned
    ([Syntax.package]) and rendered by [Render].  There is no [sp_pkg_name]/[cf_pkg_name].) *)
