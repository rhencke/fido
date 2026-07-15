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
From Fido Require Import Ints GoAST GoTypes GoCompile.
Import ListNotations.

Inductive GoValue : Type :=
| VBool    : bool -> GoValue
| VInteger : IntegerType -> Z -> GoValue
| VString  : string -> GoValue.

(** The runtime type of a value — the SAME [GoType] authority ([GoTypes]) the compiler/type system uses; an
    integer value carries its exact [IntegerType].  A [VString] is the EXACT runtime byte sequence. *)
Definition value_type (v : GoValue) : GoType :=
  match v with VBool _ => TBool | VInteger it _ => TInteger it | VString _ => TString end.

(** value well-formedness: the ONE runtime range invariant — an integer value's magnitude fits its type. *)
Definition ValueWF (v : GoValue) : Prop :=
  match v with VBool _ => True | VInteger it z => IntRepresentable it z | VString _ => True end.
Definition value_wfb (v : GoValue) : bool :=
  match v with VBool _ => true | VInteger it z => integer_representableb it z | VString _ => true end.

Lemma value_wfb_iff : forall v, value_wfb v = true <-> ValueWF v.
Proof.
  intros [ b | it z | s ]; simpl.
  - split; [ intros _; exact I | intros _; reflexivity ].
  - apply integer_representableb_spec.
  - split; [ intros _; exact I | intros _; reflexivity ].
Qed.

(** the exact untyped constant carried by a runtime value (its data, forgetting the integer type). *)
Definition value_const (v : GoValue) : GoConst :=
  match v with VBool b => CBool b | VInteger _ z => CInt z | VString s => CString s end.

(** The one bridge from a RESOLVED type + exact untyped constant ([GoTypes.GoConst]) to a runtime value.  The
    integer type comes from the resolution/conversion result — never invented here; a type/constant mismatch
    is [None] (unreachable once the constant is representable at the type). *)
Definition const_to_value (t : GoType) (c : GoConst) : option GoValue :=
  match t, c with
  | TBool,       CBool b   => Some (VBool b)
  | TInteger it, CInt z    => Some (VInteger it z)
  | TString,     CString s => Some (VString s)
  | _, _ => None
  end.

Lemma const_to_value_const : forall t c v, const_to_value t c = Some v -> value_const v = c.
Proof.
  intros t c v H; destruct t as [| it |]; destruct c as [ b | z | s ]; simpl in H;
    try discriminate; injection H as <-; reflexivity.
Qed.

Lemma const_to_value_representable : forall t c,
  ConstRepresentable t c -> exists v, const_to_value t c = Some v /\ value_type v = t /\ ValueWF v.
Proof.
  intros t c H; destruct H as [ b | it z Hir | s ]; simpl.
  - exists (VBool b);      split; [ reflexivity | split; [ reflexivity | exact I ] ].
  - exists (VInteger it z); split; [ reflexivity | split; [ reflexivity | exact Hir ] ].
  - exists (VString s);    split; [ reflexivity | split; [ reflexivity | exact I ] ].
Qed.

(** evaluation of the one constant-status result: a value exists exactly when the carried constant is
    representable at the analyzed type (a typed constant always is; an untyped constant must fit its default
    type — e.g. bare [2^63] has no [int] value). *)
Definition info_to_value (ci : ConstInfo) : option GoValue :=
  if const_representableb (info_type ci) (ci_const ci)
  then const_to_value (info_type ci) (ci_const ci)
  else None.

(** Evaluation IS the one constant-status analysis mapped to a value — no second case analysis over the raw
    syntax, no second conversion/representability authority.  Partial: an invalid (nested) integer conversion
    or an out-of-range default-int constant has NO value. *)
Definition eval_expr (e : GoExpr) : option GoValue :=
  match const_info e with Some ci => info_to_value ci | None => None end.

(** A RESOLVED expression always evaluates to a well-formed value whose runtime type is EXACTLY the resolved
    [GoType] — the compiler's static resolution and the runtime value agree (one [GoType] authority). *)
Lemma eval_expr_resolved : forall u e t,
  ResolveExpr u e t -> exists v, eval_expr e = Some v /\ value_type v = t /\ ValueWF v.
Proof.
  intros u e t H; induction H as [ u0 e0 ci t0 Hci Htype Hu Hr ].
  unfold eval_expr; rewrite Hci; unfold info_to_value; rewrite Htype.
  assert (Hrep : const_representableb t0 (ci_const ci) = true) by (apply const_representableb_iff; exact Hr).
  rewrite Hrep. apply const_to_value_representable; exact Hr.
Qed.

(** the resolved value has exactly the resolved type (gate-named corollary of [eval_expr_resolved]). *)
Lemma eval_expr_resolved_type : forall u e t,
  ResolveExpr u e t -> exists v, eval_expr e = Some v /\ value_type v = t.
Proof.
  intros u e t H; destruct (eval_expr_resolved u e t H) as [ v [ Hev [ Hvt _ ] ] ];
    exists v; split; assumption.
Qed.

(** the evaluated value carries EXACTLY the expression's exact constant value (no wrap, no re-decode). *)
Lemma eval_expr_value_const : forall e v, eval_expr e = Some v -> value_const v = const_value e.
Proof.
  intros e v H; unfold eval_expr in H.
  destruct (const_info e) as [ci|] eqn:Hci; [| discriminate].
  unfold info_to_value in H.
  destruct (const_representableb (info_type ci) (ci_const ci)); [| discriminate].
  apply const_to_value_const in H; rewrite H; apply (const_info_value e ci Hci).
Qed.

(** an explicit integer conversion PRESERVES the exact mathematical value (§14): the evaluated value of the
    conversion carries the same constant as the operand.  (Nested conversions preserve it transitively — this
    holds for the operand [e] whatever its own shape.) *)
Lemma eval_convert_preserves_value : forall it e v,
  eval_expr (EIntConvert it e) = Some v -> value_const v = const_value e.
Proof.
  intros it e v H; rewrite <- (const_value_convert it e); apply eval_expr_value_const; exact H.
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
