(** GoSafe — the exact ABSTRACT println-trace semantics of the admitted fragment, and [SafeProgram], the
    permanent safety capability boundary over a [CompilableProgram].

    This is NOT a full Go operational semantics — it is a deterministic abstract-trace mapping for the
    current fragment: values are REAL Go values ([VBool] / [VInteger : IntegerType -> Z] carrying the exact
    mathematical value at its exact integer type / [VFloat : forall ft, FloatValue ft] carrying a canonical
    binary [spec_float] at its format / [VComplex : forall ct, ComplexValue ct] a PAIR of general
    [FloatValue] components (so a RUNTIME complex MAY carry -0/inf/NaN, though a typed complex CONSTANT cannot)
    / [VString : exact bytes], not source spelling — so [EInt 0] and
    [ENeg 0] evaluate equal), and a file's behaviour is the ordered sequence of its [println] calls (each the
    list of its argument VALUES).  Runtime values carry the SAME [GoType] authority as the compiler/type
    system ([value_type]; there is no separate runtime type universe), and every runtime value is
    WELL-FORMED ([ValueWF] — [VInteger it z] iff [z] fits [it]; a [VFloat] / [VComplex] is canonical by construction, so
    True).  A float/complex constant ROUNDS ONCE into its canonical [FloatValue] component(s); constant evaluation produces only
    finite/+0 (never -0/inf/NaN).  Because raw syntax can now contain a compiler-invalid integer/float/complex
    conversion (a component overflow, a nonzero-imaginary complex->scalar, a fractional or out-of-range
    float/complex->integer, or a wrong-type conversion), evaluation is PARTIAL ([eval_expr : GoExpr -> option GoValue]) and
    is DERIVED from the one constant-status analysis ([GoTypes.const_info]) — it invents no second
    conversion/type/value authority.  A resolved expression always evaluates to a well-formed value of its
    resolved [GoType] ([eval_expr_resolved]).  There is no panic/blocking/scheduler/heap algebra: no admitted
    operation can panic or diverge (a constant conversion failure is a COMPILE-TIME typing failure, not a
    runtime panic), so predeclaring one would be scaffolding.

    [SafeProgram] is the PERMANENT home for guarantees BEYOND compiler acceptance (nil-deref / bounds /
    panic-freedom / happens-before / race- or deadlock-freedom subsets / termination / protocol invariants /
    user- or LLM-added refinements).  [GoSafe cp := True] is honest TODAY only because every
    [CompilableProgram] representable in this fragment satisfies the current safety floor — NOT by circular
    reference to compilation.  Stronger proofs REFINE it over the same [CompilableProgram]; they never fork
    the compiler, AST, renderer, or semantics. *)
From Stdlib Require Import ZArith List Bool String.
From Stdlib Require Import Floats.SpecFloat.
From Fido Require Import Ints Floats Complexes GoAST GoTypes GoCompile.
Import ListNotations.

(** Evaluation reads the one constant-status analysis at the compiler-owned predeclared resolver
    ([GoCompile.predeclared_type], §7); these parsing notations specialize the [GoTypes] index-free spec at
    that ONE resolver so evaluation stays derived from — never a second authority over — the same analysis. *)
Local Notation const_info        := (GoTypes.const_info GoCompile.predeclared_type) (only parsing).
Local Notation resolve_expr_const := (GoTypes.resolve_expr_const GoCompile.predeclared_type) (only parsing).
Local Notation resolve_expr      := (GoTypes.resolve_expr GoCompile.predeclared_type) (only parsing).
Local Notation ResolveExpr       := (GoTypes.ResolveExpr GoCompile.predeclared_type) (only parsing).

Inductive GoValue : Type :=
| VBool    : bool -> GoValue
| VInteger : IntegerType -> Z -> GoValue
| VFloat   : forall ft, FloatValue ft -> GoValue
| VComplex : forall ct, ComplexValue ct -> GoValue
| VString  : string -> GoValue.

(** The runtime type of a value — the SAME [GoType] authority ([GoTypes]) the compiler/type system uses; an
    integer value carries its exact [IntegerType], a float value its [FloatType], a complex value its
    [ComplexType] (same component mapping).  A [VString] is the EXACT runtime byte sequence. *)
Definition value_type (v : GoValue) : GoType :=
  match v with
  | VBool _ => TBool | VInteger it _ => TInteger it | VFloat ft _ => TFloat ft
  | VComplex ct _ => TComplex ct | VString _ => TString
  end.

(** value well-formedness: an integer value's magnitude fits its type; a float / complex value is canonical
    for its format BY CONSTRUCTION (the invariant lives in [FloatValue] / its component [FloatValue]s), so no
    extra side condition. *)
Definition ValueWF (v : GoValue) : Prop :=
  match v with
  | VBool _ => True | VInteger it z => IntRepresentable it z
  | VFloat _ _ => True | VComplex _ _ => True | VString _ => True
  end.
Definition value_wfb (v : GoValue) : bool :=
  match v with
  | VBool _ => true | VInteger it z => integer_representableb it z
  | VFloat _ _ => true | VComplex _ _ => true | VString _ => true
  end.

Lemma value_wfb_iff : forall v, value_wfb v = true <-> ValueWF v.
Proof.
  intros [ b | it z | ft fv | ct cv | s ]; simpl.
  - split; [ intros _; exact I | intros _; reflexivity ].
  - apply integer_representableb_spec.
  - split; [ intros _; exact I | intros _; reflexivity ].
  - split; [ intros _; exact I | intros _; reflexivity ].
  - split; [ intros _; exact I | intros _; reflexivity ].
Qed.

(** the intrinsic typed constant PROJECTS to a runtime value.  There is NO total runtime->constant
    fallback: NaN / infinity / negative-zero runtime values are not constants (an honest RELATION describes
    when a value denotes a constant). *)

(** the ONE total typed-constant-to-runtime map: bool/int/string are direct; a FLOAT PROJECTS its stored
    [tfc_runtime] — it does NOT round again (no [round_float_sf]/[round_float_const]/[round_typed_float]).  A
    typed integer's carried range proof makes the value well-formed by construction. *)
Definition typed_const_to_value {t : GoType} (tc : TypedConst t) : GoValue :=
  match tc with
  | TCBool b         => VBool b
  | TCInteger it z _ => VInteger it z
  | TCFloat ft tfc   => VFloat ft (tfc_runtime tfc)
  | TCComplex ct tcc => VComplex ct (typed_complex_runtime tcc)
  | TCString s       => VString s
  end.

(** the projection has the intrinsic type and is well-formed by construction (short projections). *)
Lemma typed_const_to_value_type : forall t (tc : TypedConst t), value_type (typed_const_to_value tc) = t.
Proof. intros t tc; destruct tc; reflexivity. Qed.

Lemma typed_const_to_value_wf : forall t (tc : TypedConst t), ValueWF (typed_const_to_value tc).
Proof.
  intros t tc; destruct tc as [ b | it z Hpf | ft tfc | ct tcc | s ]; cbn [typed_const_to_value ValueWF].
  - exact I.
  - apply integer_representableb_spec; exact Hpf.
  - exact I.
  - exact I.
  - exact I.
Qed.

(** no second rounding: evaluating a typed float / complex constant PROJECTS its stored runtime,
    reflexively (a complex projects its pair of stored component runtimes). *)
Lemma typed_const_to_value_float : forall ft (tfc : TypedFloatConst ft),
  typed_const_to_value (TCFloat ft tfc) = VFloat ft (tfc_runtime tfc).
Proof. reflexivity. Qed.
Lemma typed_const_to_value_complex : forall ct (tcc : TypedComplexConst ct),
  typed_const_to_value (TCComplex ct tcc) = VComplex ct (typed_complex_runtime tcc).
Proof. reflexivity. Qed.

(** an HONEST value/constant denotation relation.  The float case is phrased through [TypedFloatConst]
    coherence: a typed-float-constant runtime denotes its exact [tfc_exact].  A standalone NaN / infinity /
    negative-zero runtime value has NO constructor here, so it denotes NO constant. *)
Inductive ValueDenotesConst : GoValue -> GoConst -> Prop :=
| VDBool    : forall b, ValueDenotesConst (VBool b) (CBool b)
| VDInt     : forall it z, IntRepresentable it z -> ValueDenotesConst (VInteger it z) (CInt z)
| VDFloat   : forall ft (tfc : TypedFloatConst ft),
    ValueDenotesConst (VFloat ft (tfc_runtime tfc)) (CFloat (tfc_exact tfc))
| VDComplex : forall ct (tcc : TypedComplexConst ct),
    ValueDenotesConst (VComplex ct (typed_complex_runtime tcc)) (CComplex (typed_complex_exact tcc))
| VDString  : forall s, ValueDenotesConst (VString s) (CString s).

(** the projected runtime value denotes the typed constant's exact value, by construction. *)
Lemma typed_const_to_value_denotes : forall t (tc : TypedConst t),
  ValueDenotesConst (typed_const_to_value tc) (typed_const_exact tc).
Proof.
  intros t tc; destruct tc as [ b | it z Hpf | ft tfc | ct tcc | s ];
    cbn [typed_const_to_value typed_const_exact].
  - constructor.
  - constructor; apply integer_representableb_spec; exact Hpf.
  - constructor.
  - constructor.
  - constructor.
Qed.

(** a denoting float value's runtime is +0-or-finite: the ONLY float denotation is through
    [TypedFloatConst] coherence. *)
Lemma value_denotes_constant_runtime : forall v c,
  ValueDenotesConst v c ->
  match v with VFloat _ fv => float_constant_runtimeb (fv_sf fv) = true | _ => True end.
Proof.
  intros v c H; destruct H as [ b | it z Hr | ft tfc | ct tcc | s ]; try exact I; apply (tfc_shape tfc).
Qed.

(** a NaN / infinity / negative-zero runtime value has NO typed-constant denotation (there is no total
    runtime->constant fallback). *)
Lemma float_nonconstant_no_denotes : forall ft (fv : FloatValue ft) c,
  float_constant_runtimeb (fv_sf fv) = false -> ~ ValueDenotesConst (VFloat ft fv) c.
Proof.
  intros ft fv c Hshape H.
  pose proof (value_denotes_constant_runtime _ _ H) as Hs; cbn in Hs.
  rewrite Hshape in Hs; discriminate.
Qed.

(** the three concrete non-constant runtime values (canonical general-domain [FloatValue]s) that inhabit the
    runtime domain yet denote NO constant — NaN, +infinity, negative zero. *)
Example nan_f64_no_denotes : forall c, ~ ValueDenotesConst (VFloat F64 (fv_nan F64)) c.
Proof. intro c; apply float_nonconstant_no_denotes; reflexivity. Qed.
Example inf_f64_no_denotes : forall c, ~ ValueDenotesConst (VFloat F64 (fv_inf F64 false)) c.
Proof. intro c; apply float_nonconstant_no_denotes; reflexivity. Qed.
Example neg_zero_f64_no_denotes : forall c, ~ ValueDenotesConst (VFloat F64 fv_neg_zero_F64) c.
Proof. intro c; apply float_nonconstant_no_denotes; reflexivity. Qed.

(** a runtime complex value whose real OR imaginary component is not +0/finite (NaN, infinity, or
    negative zero) denotes NO constant — the ONLY complex denotation is through [TypedComplexConst] component
    coherence (both components +0/finite by [tfc_shape]). *)
Lemma value_denotes_complex_runtime : forall v c,
  ValueDenotesConst v c ->
  match v with
  | VComplex _ cv => float_constant_runtimeb (fv_sf (cv_real cv)) = true
                     /\ float_constant_runtimeb (fv_sf (cv_imag cv)) = true
  | _ => True
  end.
Proof.
  intros v c H; destruct H as [ b | it z Hr | ft tfc | ct tcc | s ]; try exact I; cbn.
  split; [ apply (typed_complex_runtime_real_shape ct tcc)
         | apply (typed_complex_runtime_imag_shape ct tcc) ].
Qed.

Lemma complex_nonconstant_no_denotes : forall ct (cv : ComplexValue ct) c,
  float_constant_runtimeb (fv_sf (cv_real cv)) = false
  \/ float_constant_runtimeb (fv_sf (cv_imag cv)) = false ->
  ~ ValueDenotesConst (VComplex ct cv) c.
Proof.
  intros ct cv c Hbad H.
  pose proof (value_denotes_complex_runtime _ _ H) as Hs; cbn in Hs.
  destruct Hs as [Hr Hi]; destruct Hbad as [Hb|Hb]; congruence.
Qed.

(** concrete general-domain complex runtime values that denote NO constant: a NaN real component, an infinity
    imaginary component, a negative-zero component (item 48). *)
Example complex_nan_real_no_denotes : forall c,
  ~ ValueDenotesConst (VComplex C128 (@mkCV C128 (fv_nan F64) (fv_inf F64 false))) c.
Proof. intro c; apply complex_nonconstant_no_denotes; left; reflexivity. Qed.
Example complex_inf_imag_no_denotes : forall c,
  ~ ValueDenotesConst (VComplex C128 (@mkCV C128 fv_neg_zero_F64 (fv_inf F64 true))) c.
Proof. intro c; apply complex_nonconstant_no_denotes; right; reflexivity. Qed.
Example complex_neg_zero_no_denotes : forall c,
  ~ ValueDenotesConst (VComplex C128 (@mkCV C128 fv_neg_zero_F64 (fv_nan F64))) c.
Proof. intro c; apply complex_nonconstant_no_denotes; left; reflexivity. Qed.

(** Evaluation IS the one constant-status analysis RESOLVED to a validated typed constant and PROJECTED —
    no second case analysis over the raw syntax, no second conversion/representability decision, no second
    float rounding.  Partial: an invalid (nested) conversion or an out-of-range/overflowing default constant
    has NO value. *)
Definition eval_expr (e : GoExpr) : option GoValue :=
  match const_info e with
  | None => None
  | Some ci =>
      match resolve_const_info ci with
      | None => None
      | Some (pack_resolved _ tc) => Some (typed_const_to_value tc)
      end
  end.

(** the runtime value STORED IN a resolved typed constant — evaluation returns EXACTLY this, no re-derivation:
    for a float it is the packaged [tfc_runtime], never a second rounding. *)
Definition resolved_const_value (rc : ResolvedConst) : GoValue :=
  match rc with pack_resolved _ tc => typed_const_to_value tc end.

Lemma resolved_const_value_float : forall ft (tfc : TypedFloatConst ft),
  resolved_const_value (pack_resolved (TFloat ft) (TCFloat ft tfc)) = VFloat ft (tfc_runtime tfc).
Proof. intros ft tfc; cbn [resolved_const_value]; apply typed_const_to_value_float. Qed.

Lemma resolved_const_value_complex : forall ct (tcc : TypedComplexConst ct),
  resolved_const_value (pack_resolved (TComplex ct) (TCComplex ct tcc)) = VComplex ct (typed_complex_runtime tcc).
Proof. intros ct tcc; cbn [resolved_const_value]; apply typed_const_to_value_complex. Qed.

(** A RESOLVED expression always evaluates to a well-formed value whose runtime type is EXACTLY the resolved
    [GoType] — the compiler's static resolution and the runtime value agree (one [GoType] authority). *)
Lemma eval_expr_resolved : forall u e t,
  ResolveExpr u e t -> exists v, eval_expr e = Some v /\ value_type v = t /\ ValueWF v.
Proof.
  intros u e t H; destruct H as [ u0 e0 ci rc Hci Hrc Hua ].
  unfold eval_expr; rewrite Hci, Hrc.
  destruct rc as [ t' tc ]; cbn [resolved_const_type].
  exists (typed_const_to_value tc).
  split; [ reflexivity | split; [ apply typed_const_to_value_type | apply typed_const_to_value_wf ] ].
Qed.

(** the resolved value has exactly the resolved type (gate-named corollary of [eval_expr_resolved]). *)
Lemma eval_expr_resolved_type : forall u e t,
  ResolveExpr u e t -> exists v, eval_expr e = Some v /\ value_type v = t.
Proof.
  intros u e t H; destruct (eval_expr_resolved u e t H) as [ v [ Hev [ Hvt _ ] ] ];
    exists v; split; assumption.
Qed.

(** evaluation returns EXACTLY [typed_const_to_value] of the SAME resolved typed constant that proves
    typing: [eval_expr] and [resolve_expr_const] walk the one [const_info]->[resolve_const_info] path, so a
    resolved value is precisely the [resolved_const_value] of the resolved constant — a resolved float projects
    its packaged [tfc_runtime], never a re-rounded value. *)
Lemma eval_expr_resolved_value : forall u e rc,
  resolve_expr_const u e = Some rc -> eval_expr e = Some (resolved_const_value rc).
Proof.
  intros u e rc H.
  destruct (resolve_expr_const_sound GoCompile.predeclared_type u e rc H) as [ ci [ Hci [ Hri _ ] ] ].
  destruct rc as [ t tc ]; unfold eval_expr; rewrite Hci, Hri; reflexivity.
Qed.

(** (float) evaluation projects the SAME STORED RUNTIME: a resolved typed FLOAT constant evaluates to
    exactly its packaged [tfc_runtime] — the value built at the single construction rounding, never rounded
    again. *)
Corollary eval_projects_stored_float_runtime : forall u e ft (tfc : TypedFloatConst ft),
  resolve_expr_const u e = Some (pack_resolved (TFloat ft) (TCFloat ft tfc)) ->
  eval_expr e = Some (VFloat ft (tfc_runtime tfc)).
Proof.
  intros u e ft tfc H.
  rewrite (eval_expr_resolved_value u e _ H), resolved_const_value_float; reflexivity.
Qed.

(** (complex) evaluation projects the SAME STORED RUNTIME: a resolved typed COMPLEX constant evaluates to
    exactly its packaged pair of component [tfc_runtime]s ([typed_complex_runtime]) — no component is
    reconstructed or re-rounded. *)
Corollary eval_projects_stored_complex_runtime : forall u e ct (tcc : TypedComplexConst ct),
  resolve_expr_const u e = Some (pack_resolved (TComplex ct) (TCComplex ct tcc)) ->
  eval_expr e = Some (VComplex ct (typed_complex_runtime tcc)).
Proof.
  intros u e ct tcc H.
  rewrite (eval_expr_resolved_value u e _ H), resolved_const_value_complex; reflexivity.
Qed.

(** the resolved runtime value IS [resolved_const_value] of the resolved constant (point 5) AND DENOTES
    the resolved exact constant — the runtime/constant tie, phrased through the honest relation (never a total
    fallback). *)
Lemma eval_expr_denotes : forall u e t,
  ResolveExpr u e t ->
  exists rc v, resolve_expr_const u e = Some rc /\ eval_expr e = Some v
            /\ v = resolved_const_value rc
            /\ value_type v = resolved_const_type rc /\ ValueWF v
            /\ ValueDenotesConst v (resolved_const_exact rc).
Proof.
  intros u e t H; destruct H as [ u0 e0 ci rc Hci Hrc Hua ].
  apply use_allowsb_iff in Hua.
  destruct rc as [ t' tc ]; cbn [resolved_const_type resolved_const_exact] in *.
  exists (pack_resolved t' tc), (typed_const_to_value tc).
  assert (Hrec : resolve_expr_const u0 e0 = Some (pack_resolved t' tc)).
  { unfold GoTypes.resolve_expr_const; rewrite Hci, Hrc; cbn [resolved_const_type]; rewrite Hua; reflexivity. }
  unfold eval_expr; rewrite Hci, Hrc.
  split; [ exact Hrec | split; [ reflexivity |
    split; [ reflexivity |
    split; [ apply typed_const_to_value_type |
    split; [ apply typed_const_to_value_wf | apply typed_const_to_value_denotes ] ] ] ] ].
Qed.

(** By VALUE, not spelling: a zero literal and a negated zero evaluate to the SAME value. *)
Lemma eval_zero_sign_agnostic : eval_expr (EInt 0) = eval_expr (ENeg 0).
Proof. reflexivity. Qed.

(** the string VALUE: a string literal evaluates to the EXACT runtime byte sequence, whose runtime type is
    [TString]. *)
Lemma eval_string_value : forall s, eval_expr (EString s) = Some (VString s).
Proof. reflexivity. Qed.
Lemma eval_string_resolved_type : forall s t,
  ResolveExpr UsePrintlnArg (EString s) t -> exists v, eval_expr (EString s) = Some v /\ value_type v = t.
Proof. intros s t H; exact (eval_expr_resolved_type UsePrintlnArg (EString s) t H). Qed.

(** ---- the file's abstract behaviour: the ordered println calls (partial per argument — an ill-typed
    argument has no value; for a [SafeProgram] every argument resolves, so every option is [Some]) ---- *)
Definition eval_stmt (s : GoStmt) : list (option GoValue) :=
  match s with SPrintln args => map eval_expr args end.
Definition eval_decl (d : GoDecl) : list (list (option GoValue)) :=
  match d with DMain body => map eval_stmt body end.
Definition eval_file (decls : list GoDecl) : list (list (option GoValue)) := flat_map eval_decl decls.

(** ---- concrete evaluation fixtures ---- *)
Example eval_int8_127  : eval_expr (EConvert (GoAST.tsyn GoNames.TNint8) (EInt 127)) = Some (VInteger IInt8 127). Proof. reflexivity. Qed.
Example eval_uint64_2p63 : eval_expr (EConvert (GoAST.tsyn GoNames.TNuint64) (EInt 9223372036854775808)) = Some (VInteger IUint64 9223372036854775808). Proof. reflexivity. Qed.
Example eval_int8_int16_127 : eval_expr (EConvert (GoAST.tsyn GoNames.TNint8) (EConvert (GoAST.tsyn GoNames.TNint16) (EInt 127))) = Some (VInteger IInt8 127). Proof. reflexivity. Qed.
Example eval_int8_over_none : eval_expr (EConvert (GoAST.tsyn GoNames.TNint8) (EInt 128)) = None. Proof. reflexivity. Qed.
Example eval_bare_default : eval_expr (EInt 42) = Some (VInteger IInt 42). Proof. reflexivity. Qed.
Example eval_2p63_none : eval_expr (EInt 9223372036854775808) = None. Proof. reflexivity. Qed.
Example wf_int8_127 : ValueWF (VInteger IInt8 127). Proof. simpl; apply integer_representableb_spec; reflexivity. Qed.

(* ---- float evaluation ---- *)
(* a bare float evaluates to a float64 runtime value; an exact float->int constant to that integer *)
Example eval_float_type : option_map value_type (eval_expr (EFloat d_15em1)) = Some (TFloat F64).
Proof. reflexivity. Qed.
Example eval_int_of_3_0 : eval_expr (EConvert (GoAST.tsyn GoNames.TNint) (EFloat d_3)) = Some (VInteger IInt 3).
Proof. reflexivity. Qed.
(* ★the direct-vs-nested double-round scar as an EXACT integer observation (no float printing): both
   rounded float32 constants are integer-valued, so uint64(...) yields exact decimal evidence. *)
Example eval_scar_direct :
  eval_expr (EConvert (GoAST.tsyn GoNames.TNuint64) (EConvert (GoAST.tsyn GoNames.TNfloat32) (EFloat d_scar))) = Some (VInteger IUint64 2305843284091600896).
Proof. reflexivity. Qed.
Example eval_scar_nested :
  eval_expr (EConvert (GoAST.tsyn GoNames.TNuint64) (EConvert (GoAST.tsyn GoNames.TNfloat32) (EConvert (GoAST.tsyn GoNames.TNfloat64) (EFloat d_scar))))
    = Some (VInteger IUint64 2305843009213693952).
Proof. reflexivity. Qed.
Example eval_scar_differ :
  eval_expr (EConvert (GoAST.tsyn GoNames.TNuint64) (EConvert (GoAST.tsyn GoNames.TNfloat32) (EFloat d_scar)))
    <> eval_expr (EConvert (GoAST.tsyn GoNames.TNuint64) (EConvert (GoAST.tsyn GoNames.TNfloat32) (EConvert (GoAST.tsyn GoNames.TNfloat64) (EFloat d_scar)))).
Proof. rewrite eval_scar_direct, eval_scar_nested; discriminate. Qed.
(* the complex COMPONENT scar THROUGH EVALUATION: observing the stored real component of a zero-imaginary
   complex64 as uint64, the DIRECT F32 rounding differs from the NESTED complex128-then-complex64 double round.
   Evaluation PROJECTS the stored runtime component — no hidden reround — so the two stored runtimes differ. *)
Example eval_cplx_scar_direct :
  eval_expr (EConvert (GoAST.tsyn GoNames.TNuint64) (EConvert (GoAST.tsyn GoNames.TNcomplex64) (EComplex (mkDC d_scar d_0_0))))
    = Some (VInteger IUint64 2305843284091600896).
Proof. vm_compute. reflexivity. Qed.
Example eval_cplx_scar_nested :
  eval_expr (EConvert (GoAST.tsyn GoNames.TNuint64) (EConvert (GoAST.tsyn GoNames.TNcomplex64) (EConvert (GoAST.tsyn GoNames.TNcomplex128) (EComplex (mkDC d_scar d_0_0)))))
    = Some (VInteger IUint64 2305843009213693952).
Proof. vm_compute. reflexivity. Qed.
Example eval_cplx_scar_differ :
  eval_expr (EConvert (GoAST.tsyn GoNames.TNuint64) (EConvert (GoAST.tsyn GoNames.TNcomplex64) (EComplex (mkDC d_scar d_0_0))))
    <> eval_expr (EConvert (GoAST.tsyn GoNames.TNuint64) (EConvert (GoAST.tsyn GoNames.TNcomplex64) (EConvert (GoAST.tsyn GoNames.TNcomplex128) (EComplex (mkDC d_scar d_0_0))))).
Proof. rewrite eval_cplx_scar_direct, eval_cplx_scar_nested; discriminate. Qed.
(* constant underflow produces POSITIVE zero at runtime (never -0) *)
Example eval_underflow_pos_zero :
  option_map (fun v => match v with VFloat _ fv => fv_sf fv | _ => S754_nan end)
             (eval_expr (EConvert (GoAST.tsyn GoNames.TNfloat64) (EFloat (mkDecimal 1 (-330) eq_refl))))
    = Some (S754_zero false).
Proof. vm_compute. reflexivity. Qed.
(* ★a bare NEGATIVE underflow also produces +0 (never -0) — the constant zero has no sign. *)
Example eval_neg_underflow_pos_zero :
  option_map (fun v => match v with VFloat _ fv => fv_sf fv | _ => S754_nan end)
             (eval_expr (EFloat (mkDecimal (-1) (-330) eq_refl)))
    = Some (S754_zero false).
Proof. vm_compute. reflexivity. Qed.

(** ---- the safety certificate ---- *)

(** Trivial TODAY (the fragment has no unsafe operation), kept as the permanent extension point. *)
Definition GoSafe (cp : CompilableProgram) : Prop := True.

Record SafeProgram : Type := mkSafe {
  sp_compiled : CompilableProgram;
  sp_safe     : GoSafe sp_compiled
}.

(** A compilation certificate suffices for the current fragment; [sp_compiled] carries the genuine
    whole-program compile proof, so nothing uncompilable is certified. *)
Definition certify (cp : CompilableProgram) : SafeProgram := mkSafe cp I.

(** The certified program (what the public renderer/emitter traverse — only through SafeProgram). *)
Definition sp_program (sp : SafeProgram) : GoProgram := cp_program (sp_compiled sp).

(** (The package name is no longer a compiler-derived fact: each file's package clause is SOURCE-owned
    ([source_package]) and rendered by [GoRender].  There is no [sp_pkg_name]/[cf_pkg_name].) *)
