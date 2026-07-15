(** ============================================================================
    GoSafe — the exact ABSTRACT println-trace semantics of the admitted fragment, and [SafeProgram], the
    permanent safety capability boundary over a [CompilableProgram].

    This is NOT a full Go operational semantics — it is a deterministic abstract-trace mapping for the
    current fragment: values are REAL Go values ([VBool] / [VInteger : IntegerType -> Z] carrying the exact
    mathematical value at its exact integer type / [VString : exact bytes], not source spelling — so [EInt 0]
    and [ENeg 0] evaluate equal), and a file's behaviour is the ordered sequence of its [println] calls (each
    the list of its argument VALUES).  Runtime values carry the SAME [GoType] authority as the compiler/type
    system ([value_type]; there is no separate runtime type universe), and every runtime integer value is
    RANGE-WELL-FORMED ([ValueWF] — [VInteger it z] iff [z] fits [it]).  Because raw syntax can now contain a
    compiler-invalid integer conversion, evaluation is PARTIAL ([eval_expr : GoExpr -> option GoValue]) and
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
    the compiler, AST, renderer, or semantics.
    ============================================================================ *)
From Stdlib Require Import ZArith List Bool String.
From Fido Require Import Ints Floats GoAST GoTypes GoCompile.
Import ListNotations.

Inductive GoValue : Type :=
| VBool    : bool -> GoValue
| VInteger : IntegerType -> Z -> GoValue
| VFloat   : forall ft, FloatValue ft -> GoValue
| VString  : string -> GoValue.

(** The runtime type of a value — the SAME [GoType] authority ([GoTypes]) the compiler/type system uses; an
    integer value carries its exact [IntegerType], a float value its [FloatType].  A [VString] is the EXACT
    runtime byte sequence. *)
Definition value_type (v : GoValue) : GoType :=
  match v with
  | VBool _ => TBool | VInteger it _ => TInteger it | VFloat ft _ => TFloat ft | VString _ => TString
  end.

(** value well-formedness: an integer value's magnitude fits its type; a float value is canonical for its
    format BY CONSTRUCTION (the invariant lives in [FloatValue] itself), so no extra side condition. *)
Definition ValueWF (v : GoValue) : Prop :=
  match v with
  | VBool _ => True | VInteger it z => IntRepresentable it z | VFloat _ _ => True | VString _ => True
  end.
Definition value_wfb (v : GoValue) : bool :=
  match v with
  | VBool _ => true | VInteger it z => integer_representableb it z | VFloat _ _ => true | VString _ => true
  end.

Lemma value_wfb_iff : forall v, value_wfb v = true <-> ValueWF v.
Proof.
  intros [ b | it z | ft fv | s ]; simpl.
  - split; [ intros _; exact I | intros _; reflexivity ].
  - apply integer_representableb_spec.
  - split; [ intros _; exact I | intros _; reflexivity ].
  - split; [ intros _; exact I | intros _; reflexivity ].
Qed.

(** the exact untyped constant carried by a runtime value (its data, forgetting the integer/float type).  A
    float value's exact rational is read back from its canonical [spec_float]. *)
Definition fv_to_const {ft : FloatType} (fv : FloatValue ft) : FloatConst :=
  match sf_to_FloatConst (fv_sf fv) with Some q => q | None => fc_zero end.
Definition value_const (v : GoValue) : GoConst :=
  match v with
  | VBool b => CBool b | VInteger _ z => CInt z | VFloat _ fv => CFloat (fv_to_const fv) | VString s => CString s
  end.

(** The one bridge from a RESOLVED type + exact untyped constant ([GoTypes.GoConst]) to a runtime value.  The
    integer/float type comes from the resolution/conversion result — never invented here.  A float constant
    ROUNDS ONCE at its format into a canonical [FloatValue]; a type/constant mismatch is [None]. *)
Definition const_to_value (t : GoType) (c : GoConst) : option GoValue :=
  match t, c with
  | TBool,       CBool b   => Some (VBool b)
  | TInteger it, CInt z    => Some (VInteger it z)
  | TFloat ft,   CFloat q  => Some (VFloat ft (float_value_of_const ft q))
  | TString,     CString s => Some (VString s)
  | _, _ => None
  end.

Lemma const_to_value_representable : forall t c,
  ConstRepresentable t c -> exists v, const_to_value t c = Some v /\ value_type v = t /\ ValueWF v.
Proof.
  intros t c H; destruct H as [ b | it z Hir | ft q Hfr | s ]; simpl.
  - exists (VBool b);      split; [ reflexivity | split; [ reflexivity | exact I ] ].
  - exists (VInteger it z); split; [ reflexivity | split; [ reflexivity | exact Hir ] ].
  - exists (VFloat ft (float_value_of_const ft q));
      split; [ reflexivity | split; [ reflexivity | exact I ] ].
  - exists (VString s);    split; [ reflexivity | split; [ reflexivity | exact I ] ].
Qed.

(** evaluation of the one constant-status result: an UNTYPED constant is given its default type and must be
    representable there (a bare [2^63] has no [int] value; a bare overflowing float has no [float64] value);
    a TYPED constant is already validated at its format by [const_info]/[convert_const] and maps directly (its
    value is [None] only on a bool/string target, which no conversion produces). *)
Definition info_to_value (ci : ConstInfo) : option GoValue :=
  match ci with
  | UntypedConst c => if const_representableb (const_default_type c) c
                      then const_to_value (const_default_type c) c else None
  | TypedConst t c => const_to_value t c
  end.

(** for any successfully-evaluated constant status, the value IS the resolved-type interpretation of its
    carried constant ([const_to_value] of [info_type]/[ci_const]) — the uniform runtime/analysis bridge. *)
Lemma info_to_value_const_to_value : forall ci v,
  info_to_value ci = Some v -> const_to_value (info_type ci) (ci_const ci) = Some v.
Proof.
  intros [c | t c] v H; simpl in H |- *.
  - destruct (const_representableb (const_default_type c) c); [ exact H | discriminate ].
  - exact H.
Qed.

(** Evaluation IS the one constant-status analysis mapped to a value — no second case analysis over the raw
    syntax, no second conversion/representability authority.  Partial: an invalid (nested) conversion or an
    out-of-range/overflowing default constant has NO value. *)
Definition eval_expr (e : GoExpr) : option GoValue :=
  match const_info e with Some ci => info_to_value ci | None => None end.

(** A RESOLVED expression always evaluates to a well-formed value whose runtime type is EXACTLY the resolved
    [GoType] — the compiler's static resolution and the runtime value agree (one [GoType] authority). *)
Lemma eval_expr_resolved : forall u e t,
  ResolveExpr u e t -> exists v, eval_expr e = Some v /\ value_type v = t /\ ValueWF v.
Proof.
  intros u e t H; induction H as [ u0 e0 ci t0 Hci Htype Hu Hok ].
  unfold eval_expr; rewrite Hci.
  destruct ci as [ c | ty c ]; cbn [info_type] in Htype; subst t0.
  - (* untyped: use-ready = representable at the default type *)
    cbn [ci_ok] in Hok. unfold info_to_value.
    apply const_representableb_iff in Hok as Hokb. rewrite Hokb.
    apply const_to_value_representable; exact Hok.
  - (* typed: already validated at its NUMERIC format by const_info *)
    unfold info_to_value.
    destruct ty as [| it | ft |].
    + destruct (const_info_typed_numeric _ _ _ Hci) as [[it Hc]|[ft Hc]]; discriminate Hc.
    + destruct (const_info_typed_int_representable _ _ _ Hci) as [z [-> Hz]].
      exists (VInteger it z); cbn [const_to_value value_type ValueWF].
      split; [ reflexivity | split; [ reflexivity | apply integer_representableb_spec; exact Hz ] ].
    + destruct (const_info_typed_float_shape _ _ _ Hci) as [q ->].
      exists (VFloat ft (float_value_of_const ft q)); cbn [const_to_value value_type ValueWF].
      split; [ reflexivity | split; [ reflexivity | exact I ] ].
    + destruct (const_info_typed_numeric _ _ _ Hci) as [[it Hc]|[ft Hc]]; discriminate Hc.
Qed.

(** the resolved value has exactly the resolved type (gate-named corollary of [eval_expr_resolved]). *)
Lemma eval_expr_resolved_type : forall u e t,
  ResolveExpr u e t -> exists v, eval_expr e = Some v /\ value_type v = t.
Proof.
  intros u e t H; destruct (eval_expr_resolved u e t H) as [ v [ Hev [ Hvt _ ] ] ];
    exists v; split; assumption.
Qed.

(** the evaluated runtime value IS the resolved-type interpretation of the analyzed constant — for an
    integer/bool/string that is the exact carried constant; for a float it is the value ROUNDED once at its
    format (so a bare float rounds to its default, a conversion to its target).  This is the ONE bridge; the
    exact "value preserved" story holds for the non-float constants (a float value is the rounding, never the
    exact rational — [const_to_value] rounds). *)
Lemma eval_const_to_value : forall e ci v,
  const_info e = Some ci -> eval_expr e = Some v -> const_to_value (info_type ci) (ci_const ci) = Some v.
Proof.
  intros e ci v Hci H; unfold eval_expr in H; rewrite Hci in H.
  apply info_to_value_const_to_value; exact H.
Qed.

(** an explicit INTEGER conversion evaluates to a [VInteger] carrying exactly the conversion's constant value
    (§14): [const_value] of the conversion is [Some (value_const v)] — the integer value the (possibly float)
    operand converts to, kept exact through nesting.  (A float operand truncates; an int operand is
    value-preserving — both captured by [convert_const].) *)
Lemma eval_convert_preserves_value : forall it e v,
  eval_expr (EIntConvert it e) = Some v -> const_value (EIntConvert it e) = Some (value_const v).
Proof.
  intros it e v H; unfold eval_expr in H.
  destruct (const_info (EIntConvert it e)) as [ci|] eqn:Hci; [| discriminate].
  destruct (const_info_int_convert_shape it e ci Hci) as [z [-> Hz]].
  cbn [info_to_value const_to_value] in H. injection H as <-.
  cbn [value_const].
  rewrite (const_info_value _ _ Hci); reflexivity.
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
Definition eval_file (f : GoFileAST) : list (list (option GoValue)) := flat_map eval_decl f.

(** ---- concrete evaluation fixtures ---- *)
Example eval_int8_127  : eval_expr (EIntConvert IInt8 (EInt 127)) = Some (VInteger IInt8 127). Proof. reflexivity. Qed.
Example eval_uint64_2p63 : eval_expr (EIntConvert IUint64 (EInt 9223372036854775808)) = Some (VInteger IUint64 9223372036854775808). Proof. reflexivity. Qed.
Example eval_int8_int16_127 : eval_expr (EIntConvert IInt8 (EIntConvert IInt16 (EInt 127))) = Some (VInteger IInt8 127). Proof. reflexivity. Qed.
Example eval_int8_over_none : eval_expr (EIntConvert IInt8 (EInt 128)) = None. Proof. reflexivity. Qed.
Example eval_bare_default : eval_expr (EInt 42) = Some (VInteger IInt 42). Proof. reflexivity. Qed.
Example eval_2p63_none : eval_expr (EInt 9223372036854775808) = None. Proof. reflexivity. Qed.
Example wf_int8_127 : ValueWF (VInteger IInt8 127). Proof. simpl; apply integer_representableb_spec; reflexivity. Qed.

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

(** The compiler-derived package name the renderer emits for this program's files. *)
Definition sp_pkg_name (sp : SafeProgram) : string := cf_pkg_name (cp_facts (sp_compiled sp)).
