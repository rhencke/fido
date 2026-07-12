(** ============================================================================
    CompileEnv — the declarative compile environment for the checkpoint-66 slice.

    The predeclared universe scope.  For this slice it contains exactly one binding:
    the bootstrapping builtin [println] (present on the pinned target —
    TargetConfig.[tc_println_builtin]).  Name RESOLUTION happens here and only here:
    the typed IR never identifies a builtin by string ([TypedIR.TPrintln] is the
    resolved form), and emission never recognizes names.  A name this environment does
    not bind does not resolve — elaboration rejects the candidate.
    ============================================================================ *)
From Stdlib Require Import String.
From Fido Require Import TargetConfig.

Inductive Builtin : Type := BPrintln.

(** The one predeclared lookup.  [println] is admitted only because the pinned target
    provides the bootstrapping builtin (a TargetConfig fact, consumed here, not assumed
    downstream). *)
Definition lookup_predeclared (s : string) : option Builtin :=
  if andb (String.eqb s "println") (tc_println_builtin target)
  then Some BPrintln else None.

Lemma lookup_println : lookup_predeclared "println" = Some BPrintln.
Proof. reflexivity. Qed.

Lemma lookup_predeclared_inv : forall s b,
  lookup_predeclared s = Some b -> s = "println"%string /\ b = BPrintln.
Proof.
  intros s b H. unfold lookup_predeclared in H.
  destruct (String.eqb s "println") eqn:E; simpl in H; [ | discriminate ].
  apply String.eqb_eq in E. destruct b. auto.
Qed.
