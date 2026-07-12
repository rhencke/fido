(** ============================================================================
    CoreType — the ONE certified primitive-type universe for the checkpoint-66 slice.

    A CLOSED descriptor: [PBool | PInt | PString].  Everything type-shaped in the slice
    DERIVES from this one inductive — decidable identity ([core_eqb]), admitted literal
    forms ([str_ok]/[int_lit_ok]/[neg_lit_ok], with int bounds from TargetConfig, the one
    width authority), and [println] argument admissibility ([println_arg_ok], exhaustive
    per-constructor so a NEW type is forced to decide it).  There is NO parallel runtime
    tag universe: the semantics' value type (Semantics.[PrimValue]) is indexed back to
    THIS descriptor by [Semantics.eval_expr_type] (type preservation).
    ============================================================================ *)
From Stdlib Require Import String Ascii ZArith Bool.
From Fido Require Import TargetConfig.
Open Scope Z_scope.

Inductive CoreType : Type := PBool | PInt | PString.

Definition core_eqb (a b : CoreType) : bool :=
  match a, b with
  | PBool, PBool | PInt, PInt | PString, PString => true
  | _, _ => false
  end.

Lemma core_eqb_eq : forall a b, core_eqb a b = true <-> a = b.
Proof. intros [] []; simpl; split; congruence. Qed.

Lemma core_eq_dec : forall a b : CoreType, {a = b} + {a <> b}.
Proof. decide equality. Defined.

(** [println] admissibility, per constructor (all three primitive classes are admitted —
    the pinned implementations support bool/numeric/string operands). *)
Definition println_arg_ok (t : CoreType) : bool :=
  match t with PBool => true | PInt => true | PString => true end.

Lemma println_arg_ok_all : forall t, println_arg_ok t = true.
Proof. intros []; reflexivity. Qed.

(** ---- Admitted literal forms ----

    STRING payloads: printable ASCII (32..126) plus tab (9) and newline (10).  This keeps
    the source-escaping story exact and total: outside bytes (control chars, byte >127 —
    which could make the emitted source invalid UTF-8) are REJECTED at elaboration, never
    approximated.  Unicode strings are an explicit unsupported frontier. *)
Definition str_char_ok (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (Nat.eqb n 9) || (Nat.eqb n 10) || ((Nat.leb 32 n) && (Nat.leb n 126)).

Fixpoint str_ok (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => str_char_ok c && str_ok s'
  end.

(** INT literals: a source literal is lexically NONNEGATIVE (Go has no signed integer
    literal — [-5] is unary minus applied to [5]).  An untyped integer constant used as a
    [println] operand takes default type [int], so it must fit the pinned target's [int]:
      - a bare literal   [n]  needs [0 <= n <= int_max];
      - a negated literal [-n] needs [0 <= n <= -int_min]  (so [-(2^63)] is admitted — it
        is valid Go — while [2^63] bare is not; constant overflow is a COMPILE error and
        must be unrepresentable downstream, per the no-expected-Go-failure rule). *)
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
    [-n]) — the fact that keeps emitted constants compilable. *)
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
