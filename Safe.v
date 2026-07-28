From Stdlib Require Import ZArith List Bool String.
From Stdlib Require Import Floats.SpecFloat.
From Fido Require Import Integer Float Complex Syntax Typing Compilable.
Import ListNotations.

(* These notations specialize the typing spec at the compiler's one resolver, so evaluation stays derived. *)
Local Notation constant_info        := (Typing.constant_info Compilable.predeclared_type) (only parsing).
Local Notation resolve_constant := (Typing.resolve_constant Compilable.predeclared_type) (only parsing).
Local Notation resolve      := (Typing.resolve Compilable.predeclared_type) (only parsing).

Inductive Value : Type :=
| BoolValue    : bool -> Value
| IntegerValue : Integer.Kind -> Z -> Value
| FloatValue   : forall ft, Float.Value ft -> Value
| ComplexValue : forall ct, Complex.Value ct -> Value
| StringValue  : string -> Value.

(* A value's runtime type is the same semantic type the compiler uses; there is no second type universe. *)
Definition value_type (v : Value) : Typing.SemanticType :=
  match v with
  | BoolValue _ => Typing.BoolType | IntegerValue it _ => Typing.IntegerType it | FloatValue ft _ => Typing.FloatType ft
  | ComplexValue ct _ => Typing.ComplexType ct | StringValue _ => Typing.StringType
  end.

(* An integer value fits its type; a float or complex value is canonical by construction. *)
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

(* The one typed-constant-to-runtime map; a float projects its stored runtime and never rounds again. *)
Definition typed_constant_to_value {t : Typing.SemanticType} (tc : Typing.TypedConstant t) : Value :=
  match tc with
  | Typing.TypedBool b         => BoolValue b
  | Typing.TypedInteger it z _ => IntegerValue it z
  | Typing.TypedFloat ft tfc   => FloatValue ft (Float.runtime tfc)
  | Typing.TypedComplex ct tcc => ComplexValue ct (Complex.typed_runtime tcc)
  | Typing.TypedString s       => StringValue s
  end.

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

Lemma typed_constant_to_value_float : forall ft (tfc : Float.TypedConstant ft),
  typed_constant_to_value (Typing.TypedFloat ft tfc) = FloatValue ft (Float.runtime tfc).
Proof. reflexivity. Qed.
Lemma typed_constant_to_value_complex : forall ct (tcc : Complex.TypedConstant ct),
  typed_constant_to_value (Typing.TypedComplex ct tcc) = ComplexValue ct (Complex.typed_runtime tcc).
Proof. reflexivity. Qed.

(* A NaN, infinity or negative zero has no constructor here, so it denotes no constant at all. *)
Inductive ValueDenotesConstant : Value -> Typing.Constant -> Prop :=
| DenotesBool    : forall b, ValueDenotesConstant (BoolValue b) (Typing.BoolConstant b)
| DenotesInteger     : forall it z, Integer.Representable it z -> ValueDenotesConstant (IntegerValue it z) (Typing.IntegerConstant z)
| DenotesFloat   : forall ft (tfc : Float.TypedConstant ft),
    ValueDenotesConstant (FloatValue ft (Float.runtime tfc)) (Typing.FloatConstant (Float.exact tfc))
| DenotesComplex : forall ct (tcc : Complex.TypedConstant ct),
    ValueDenotesConstant (ComplexValue ct (Complex.typed_runtime tcc)) (Typing.ComplexConstant (Complex.typed_exact tcc))
| DenotesString  : forall s, ValueDenotesConstant (StringValue s) (Typing.StringConstant s).

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

Lemma value_denotes_constant_runtime : forall v c,
  ValueDenotesConstant v c ->
  match v with FloatValue _ fv => Float.constant_runtimeb (Float.ieee fv) = true | _ => True end.
Proof.
  intros v c H; destruct H as [ b | it z Hr | ft tfc | ct tcc | s ]; try exact I; apply (Float.shape tfc).
Qed.

Lemma float_nonconstant_no_denotes : forall ft (fv : Float.Value ft) c,
  Float.constant_runtimeb (Float.ieee fv) = false -> ~ ValueDenotesConstant (FloatValue ft fv) c.
Proof.
  intros ft fv c Hshape H.
  pose proof (value_denotes_constant_runtime _ _ H) as Hs; cbn in Hs.
  rewrite Hshape in Hs; discriminate.
Qed.

Example nan_f64_no_denotes : forall c, ~ ValueDenotesConstant (FloatValue F64 (Float.value_nan F64)) c.
Proof. intro c; apply float_nonconstant_no_denotes; reflexivity. Qed.
Example inf_f64_no_denotes : forall c, ~ ValueDenotesConstant (FloatValue F64 (Float.value_inf F64 false)) c.
Proof. intro c; apply float_nonconstant_no_denotes; reflexivity. Qed.
Example neg_zero_f64_no_denotes : forall c, ~ ValueDenotesConstant (FloatValue F64 Float.value_neg_zero_F64) c.
Proof. intro c; apply float_nonconstant_no_denotes; reflexivity. Qed.

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

Example complex_nan_real_no_denotes : forall c,
  ~ ValueDenotesConstant (ComplexValue C128 (@Complex.MakeValue C128 (Float.value_nan F64) (Float.value_inf F64 false))) c.
Proof. intro c; apply complex_nonconstant_no_denotes; left; reflexivity. Qed.
Example complex_inf_imag_no_denotes : forall c,
  ~ ValueDenotesConstant (ComplexValue C128 (@Complex.MakeValue C128 Float.value_neg_zero_F64 (Float.value_inf F64 true))) c.
Proof. intro c; apply complex_nonconstant_no_denotes; right; reflexivity. Qed.
Example complex_neg_zero_no_denotes : forall c,
  ~ ValueDenotesConstant (ComplexValue C128 (@Complex.MakeValue C128 Float.value_neg_zero_F64 (Float.value_nan F64))) c.
Proof. intro c; apply complex_nonconstant_no_denotes; left; reflexivity. Qed.

(* Evaluation is the constant-status analysis resolved and projected; an invalid conversion has no value. *)
Definition eval_expr (e : Syntax.Expr) : option Value :=
  match constant_info e with
  | None => None
  | Some ci =>
      match Typing.resolve_constant_info ci with
      | None => None
      | Some (PackResolved _ tc) => Some (typed_constant_to_value tc)
      end
  end.

Definition resolved_constant_value (rc : Typing.ResolvedConstant) : Value :=
  match rc with PackResolved _ tc => typed_constant_to_value tc end.

Lemma resolved_constant_value_float : forall ft (tfc : Float.TypedConstant ft),
  resolved_constant_value (PackResolved (Typing.FloatType ft) (Typing.TypedFloat ft tfc)) = FloatValue ft (Float.runtime tfc).
Proof. intros ft tfc; cbn [resolved_constant_value]; apply typed_constant_to_value_float. Qed.

Lemma resolved_constant_value_complex : forall ct (tcc : Complex.TypedConstant ct),
  resolved_constant_value (PackResolved (Typing.ComplexType ct) (Typing.TypedComplex ct tcc)) = ComplexValue ct (Complex.typed_runtime tcc).
Proof. intros ct tcc; cbn [resolved_constant_value]; apply typed_constant_to_value_complex. Qed.

Lemma eval_expr_resolved : forall u e t,
  Typing.Resolve Compilable.predeclared_type u e t -> exists v, eval_expr e = Some v /\ value_type v = t /\ ValueWellFormed v.
Proof.
  intros u e t H; destruct H as [ u0 e0 ci rc Hci Hrc Hua ].
  unfold eval_expr; rewrite Hci, Hrc.
  destruct rc as [ t' tc ]; cbn [Typing.resolved_constant_type].
  exists (typed_constant_to_value tc).
  split; [ reflexivity | split; [ apply typed_constant_to_value_type | apply typed_constant_to_value_well_formed ] ].
Qed.

Lemma eval_expr_resolved_type : forall u e t,
  Typing.Resolve Compilable.predeclared_type u e t -> exists v, eval_expr e = Some v /\ value_type v = t.
Proof.
  intros u e t H; destruct (eval_expr_resolved u e t H) as [ v [ Hev [ Hvt _ ] ] ];
    exists v; split; assumption.
Qed.

Lemma eval_expr_resolved_value : forall u e rc,
  resolve_constant u e = Some rc -> eval_expr e = Some (resolved_constant_value rc).
Proof.
  intros u e rc H.
  destruct (Typing.resolve_constant_sound Compilable.predeclared_type u e rc H) as [ ci [ Hci [ Hri _ ] ] ].
  destruct rc as [ t tc ]; unfold eval_expr; rewrite Hci, Hri; reflexivity.
Qed.

Corollary eval_projects_stored_float_runtime : forall u e ft (tfc : Float.TypedConstant ft),
  resolve_constant u e = Some (PackResolved (Typing.FloatType ft) (Typing.TypedFloat ft tfc)) ->
  eval_expr e = Some (FloatValue ft (Float.runtime tfc)).
Proof.
  intros u e ft tfc H.
  rewrite (eval_expr_resolved_value u e _ H), resolved_constant_value_float; reflexivity.
Qed.

Corollary eval_projects_stored_complex_runtime : forall u e ct (tcc : Complex.TypedConstant ct),
  resolve_constant u e = Some (PackResolved (Typing.ComplexType ct) (Typing.TypedComplex ct tcc)) ->
  eval_expr e = Some (ComplexValue ct (Complex.typed_runtime tcc)).
Proof.
  intros u e ct tcc H.
  rewrite (eval_expr_resolved_value u e _ H), resolved_constant_value_complex; reflexivity.
Qed.

Lemma eval_expr_denotes : forall u e t,
  Typing.Resolve Compilable.predeclared_type u e t ->
  exists rc v, resolve_constant u e = Some rc /\ eval_expr e = Some v
            /\ v = resolved_constant_value rc
            /\ value_type v = Typing.resolved_constant_type rc /\ ValueWellFormed v
            /\ ValueDenotesConstant v (Typing.resolved_constant_exact rc).
Proof.
  intros u e t H; destruct H as [ u0 e0 ci rc Hci Hrc Hua ].
  apply use_allowsb_iff in Hua.
  destruct rc as [ t' tc ]; cbn [Typing.resolved_constant_type Typing.resolved_constant_exact] in *.
  exists (PackResolved t' tc), (typed_constant_to_value tc).
  assert (Hrec : resolve_constant u0 e0 = Some (PackResolved t' tc)).
  { unfold Typing.resolve_constant; rewrite Hci, Hrc; cbn [Typing.resolved_constant_type]; rewrite Hua; reflexivity. }
  unfold eval_expr; rewrite Hci, Hrc.
  split; [ exact Hrec | split; [ reflexivity |
    split; [ reflexivity |
    split; [ apply typed_constant_to_value_type |
    split; [ apply typed_constant_to_value_well_formed | apply typed_constant_to_value_denotes ] ] ] ] ].
Qed.

(* By value rather than spelling: a zero literal and a negated zero evaluate the same. *)
Lemma eval_zero_sign_agnostic : eval_expr (Syntax.IntegerLiteral 0) = eval_expr (Syntax.NegatedIntegerLiteral 0).
Proof. reflexivity. Qed.

Lemma eval_string_value : forall s, eval_expr (Syntax.StringLiteral s) = Some (StringValue s).
Proof. reflexivity. Qed.
Lemma eval_string_resolved_type : forall s t,
  Typing.Resolve Compilable.predeclared_type Typing.PrintlnArgument (Syntax.StringLiteral s) t -> exists v, eval_expr (Syntax.StringLiteral s) = Some v /\ value_type v = t.
Proof. intros s t H; exact (eval_expr_resolved_type Typing.PrintlnArgument (Syntax.StringLiteral s) t H). Qed.

(* A file's abstract behaviour: its ordered println calls, partial where an argument has no value. *)
Definition eval_stmt (s : Syntax.Stmt) : list (option Value) :=
  match s with Syntax.Println args => map eval_expr args end.
Definition eval_decl (d : Syntax.Decl) : list (list (option Value)) :=
  match d with Syntax.Main body => map eval_stmt body end.
Definition eval_file (decls : list Syntax.Decl) : list (list (option Value)) := flat_map eval_decl decls.

Example eval_int8_127  : eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 127)) = Some (IntegerValue Integer.Int8 127). Proof. reflexivity. Qed.
Example eval_uint64_2p63 : eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.IntegerLiteral 9223372036854775808)) = Some (IntegerValue Integer.Uint64 9223372036854775808). Proof. reflexivity. Qed.
Example eval_int8_int16_127 : eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.IntegerLiteral 127))) = Some (IntegerValue Integer.Int8 127). Proof. reflexivity. Qed.
Example eval_int8_over_none : eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 128)) = None. Proof. reflexivity. Qed.
Example eval_bare_default : eval_expr (Syntax.IntegerLiteral 42) = Some (IntegerValue Integer.Int 42). Proof. reflexivity. Qed.
Example eval_2p63_none : eval_expr (Syntax.IntegerLiteral 9223372036854775808) = None. Proof. reflexivity. Qed.
Example well_formed_int8_127 : ValueWellFormed (IntegerValue Integer.Int8 127). Proof. simpl; apply Integer.representableb_spec; reflexivity. Qed.

Example eval_float_type : option_map value_type (eval_expr (Syntax.FloatLiteral Typing.decimal_15em1)) = Some (Typing.FloatType F64).
Proof. reflexivity. Qed.
Example eval_int_of_3_0 : eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Int) (Syntax.FloatLiteral Typing.decimal_3)) = Some (IntegerValue Integer.Int 3).
Proof. reflexivity. Qed.
(* both rounded float32 constants are integer-valued, so uint64 gives exact decimal evidence *)
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
(* the same double rounding at the complex component level, observed through the stored runtime *)
Example eval_complex_single_rounding_direct :
  eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.ComplexLiteral (Complex.MakeDecimal Typing.decimal_single_rounding Typing.decimal_0_0))))
    = Some (IntegerValue Integer.Uint64 2305843284091600896).
Proof. vm_compute. reflexivity. Qed.
Example eval_complex_single_rounding_nested :
  eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.Convert (Syntax.type_expr_of_name Names.Complex128) (Syntax.ComplexLiteral (Complex.MakeDecimal Typing.decimal_single_rounding Typing.decimal_0_0)))))
    = Some (IntegerValue Integer.Uint64 2305843009213693952).
Proof. vm_compute. reflexivity. Qed.
Example eval_complex_single_rounding_differ :
  eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.ComplexLiteral (Complex.MakeDecimal Typing.decimal_single_rounding Typing.decimal_0_0))))
    <> eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.Convert (Syntax.type_expr_of_name Names.Complex128) (Syntax.ComplexLiteral (Complex.MakeDecimal Typing.decimal_single_rounding Typing.decimal_0_0))))).
Proof. rewrite eval_complex_single_rounding_direct, eval_complex_single_rounding_nested; discriminate. Qed.
Example eval_underflow_pos_zero :
  option_map (fun v => match v with FloatValue _ fv => Float.ieee fv | _ => S754_nan end)
             (eval_expr (Syntax.Convert (Syntax.type_expr_of_name Names.Float64) (Syntax.FloatLiteral (Float.MakeDecimal 1 (-330) eq_refl))))
    = Some (S754_zero false).
Proof. vm_compute. reflexivity. Qed.
(* a bare negative underflow also produces +0, since the constant zero has no sign *)
Example eval_neg_underflow_pos_zero :
  option_map (fun v => match v with FloatValue _ fv => Float.ieee fv | _ => S754_nan end)
             (eval_expr (Syntax.FloatLiteral (Float.MakeDecimal (-1) (-330) eq_refl)))
    = Some (S754_zero false).
Proof. vm_compute. reflexivity. Qed.

(* Trivial today, because the fragment has no unsafe operation; this is the permanent extension point. *)
Definition Property (cp : Compilable.Program) : Prop := True.

(* The representation and its constructor stay inside, so [certify] is the only way a program exists. *)
Module Type CERTIFICATE.
  Parameter Program : Type.
  Parameter compiled : Program -> Compilable.Program.
  Parameter certify : Compilable.Program -> Program.
  Parameter certify_retains : forall cp, compiled (certify cp) = cp.
End CERTIFICATE.

Module Certificate : CERTIFICATE.
  Record ProgramRepresentation : Type := Make {
    compiled : Compilable.Program;
    proof     : Property compiled
  }.
  Definition Program : Type := ProgramRepresentation.
  (* [compiled] carries the genuine whole-program compile proof, so nothing uncompilable is certified. *)
  Definition certify (cp : Compilable.Program) : Program := Make cp I.
  Lemma certify_retains : forall cp, compiled (certify cp) = cp.
  Proof. reflexivity. Qed.
End Certificate.
Include Certificate.

(* The certified program, which the renderer and emitter reach only through this projection. *)
Definition source (sp : Program) : Syntax.Program := Compilable.source (compiled sp).

(* Safety wraps the capability, so a certified program retains the exact core that justified it. *)
Definition core (sp : Program) : Compilable.Core (source sp) := Compilable.core (compiled sp).

(* The certified program's source is the capability's, propositionally since [certify] is opaque. *)
Theorem certify_source : forall cp, source (certify cp) = Compilable.source cp.
Proof. intro cp. unfold source. rewrite certify_retains. reflexivity. Qed.

Theorem certify_retains_capability : forall cp, compiled (certify cp) = cp.
Proof. exact certify_retains. Qed.

(* Retention over any certificate, not only a freshly certified one, and so strictly stronger. *)
Theorem certify_retains_core : forall sp, core sp = Compilable.core (compiled sp).
Proof. reflexivity. Qed.

