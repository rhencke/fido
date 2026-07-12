(** ============================================================================
    Literals — the admitted literal FORMS and their target-representability, factored
    OUT of the type universe (CoreType owns type structure only).

    - [str_ok]: the admitted string-payload charset (printable ASCII + tab + newline);
      a control byte or a byte > 127 (which could break source UTF-8) is rejected, never
      approximated — Unicode payloads are an explicit unsupported frontier.
    - [int_lit_ok] / [neg_lit_ok]: an integer literal is lexically NONNEGATIVE (Go has no
      signed literal — [-5] is unary minus over [5]).  Used as a [println] operand it takes
      default type [int], so it must fit the pinned target's [int] (TargetConfig, the one
      width authority): a bare literal needs [0 <= n <= int_max]; a negated literal needs
      [0 <= n <= -int_min] (so [-(2^63)] is admitted while bare [2^63] is not — constant
      overflow is a COMPILE error and must be rejected before any [.go] exists).

    These predicates back the evidence carried by the intrinsically-typed IR constructors
    (TypedIR) and the target static judgment (GoStatic); the type universe never sees them.
    ============================================================================ *)
From Stdlib Require Import String Ascii ZArith Bool.
From Fido Require Import TargetConfig.
Open Scope Z_scope.

Definition str_char_ok (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (Nat.eqb n 9) || (Nat.eqb n 10) || ((Nat.leb 32 n) && (Nat.leb n 126)).

Fixpoint str_ok (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => str_char_ok c && str_ok s'
  end.

Definition int_lit_ok (n : Z) : bool := (0 <=? n) && (n <=? int_max).
Definition neg_lit_ok (n : Z) : bool := (0 <=? n) && (n <=? - int_min).

Lemma int_lit_ok_range : forall n, int_lit_ok n = true <-> 0 <= n <= int_max.
Proof.
  intro n. unfold int_lit_ok. rewrite andb_true_iff, Z.leb_le, Z.leb_le. reflexivity.
Qed.

Lemma neg_lit_ok_range : forall n, neg_lit_ok n = true <-> 0 <= n <= - int_min.
Proof.
  intro n. unfold neg_lit_ok. rewrite andb_true_iff, Z.leb_le, Z.leb_le. reflexivity.
Qed.

(** Every admitted literal's VALUE lies in the pinned [int] range (the negated form denotes
    [-n]) — the fact that keeps emitted constants compilable (consumed by GoStatic and by
    the semantics' range theorem). *)
Lemma int_lit_ok_in_range : forall n, int_lit_ok n = true -> int_min <= n <= int_max.
Proof.
  intros n H. apply int_lit_ok_range in H. destruct H as [H0 H1].
  split; [ | exact H1 ].
  apply Z.le_trans with (m := 0); [ | exact H0 ].
  rewrite int_min_val. discriminate.
Qed.

Lemma neg_lit_ok_in_range : forall n, neg_lit_ok n = true -> int_min <= - n <= int_max.
Proof.
  intros n H. apply neg_lit_ok_range in H. destruct H as [H0 H1].
  split.
  - apply Z.opp_le_mono in H1. rewrite Z.opp_involutive in H1. exact H1.
  - apply Z.le_trans with (m := 0).
    + apply Z.opp_nonpos_nonneg. exact H0.
    + rewrite int_max_val. discriminate.
Qed.
