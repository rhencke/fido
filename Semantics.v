(** ============================================================================
    Semantics — the STRUCTURED observation semantics of the checkpoint-66 slice.

    The observable meaning of a program is a trace of EVENTS ([EPrintln] over primitive
    VALUES) — deliberately NOT output bytes: Go's bootstrapping [println] has
    implementation-specific formatting, so the exact text is a pinned-toolchain
    integration fact (captured in .golden files), never a portable theorem.

    The slice is straight-line literal evaluation, so the semantics is a TOTAL FUNCTION:
    termination and determinism hold by construction (stated below as theorems so the
    claims are pinned, not prose); no panic outcome EXISTS in the value/event types
    (panics are unrepresentable in this slice, not merely unreachable).
    ============================================================================ *)
From Stdlib Require Import String ZArith List.
From Fido Require Import TargetConfig CoreType TypedIR.
Import ListNotations.
Open Scope Z_scope.

Inductive PrimValue : Type :=
| VBool   : bool -> PrimValue
| VInt    : Z -> PrimValue
| VString : string -> PrimValue.

Definition value_type (v : PrimValue) : CoreType :=
  match v with VBool _ => PBool | VInt _ => PInt | VString _ => PString end.

Inductive Event : Type :=
| EPrintln : list PrimValue -> Event.

(** Evaluation — total by structure. *)
Definition eval_expr (e : TypedPrimExpr) : PrimValue :=
  match e with
  | TEBool b      => VBool b
  | TEStr s _     => VString s
  | TEIntLit n _  => VInt n
  | TENeg n _     => VInt (- n)
  end.

Definition eval_stmt (s : TypedStmt) : Event :=
  match s with TPrintln args => EPrintln (map eval_expr args) end.

Definition eval_program (p : TypedProgram) : list Event :=
  map eval_stmt (tp_body p).

(** The evaluation JUDGMENT is the function's graph; determinism and totality are then
    theorems (trivial by construction — stated so the claim is a theorem, not prose). *)
Definition EvalProgram (p : TypedProgram) (tr : list Event) : Prop := eval_program p = tr.

Theorem eval_deterministic : forall p t1 t2, EvalProgram p t1 -> EvalProgram p t2 -> t1 = t2.
Proof. unfold EvalProgram. congruence. Qed.

Theorem eval_total : forall p, exists tr, EvalProgram p tr.
Proof. intro p. exists (eval_program p). reflexivity. Qed.

(** TYPE PRESERVATION — every expression evaluates to a value of its certified type
    (the semantics' value classification is the SAME [CoreType] descriptor, no parallel
    tag universe). *)
Theorem eval_expr_type : forall e, value_type (eval_expr e) = type_of e.
Proof. intros []; reflexivity. Qed.

(** Every admitted integer expression's VALUE fits the pinned target [int] — the semantic
    face of the no-constant-overflow guarantee. *)
Theorem eval_int_in_range : forall e n,
  eval_expr e = VInt n -> int_min <= n <= int_max.
Proof.
  intros e n H. destruct e as [ b | s Hs | m Hm | m Hm ]; simpl in H; try discriminate.
  - injection H as <-. exact (int_lit_ok_in_range m Hm).
  - injection H as <-. exact (neg_lit_ok_in_range m Hm).
Qed.
