(** ============================================================================
    TypedIR — the elaborated IR for the checkpoint-66 slice: STATIC INVALIDITY IS
    UNREPRESENTABLE.

    Every inhabitant of this type corresponds to a compilable member of the admitted
    subset.  There is no constructor for: an import, an unresolved name, a call in value
    position, a negative-literal node (negation is its own form over a NONNEGATIVE
    payload), an out-of-range constant (the bool evidence fields make one impossible to
    build), a return from main, raw program text.  [println] is NOT identified by string
    here — [TPrintln] is the resolved builtin, produced only by elaboration through the
    predeclared CompileEnv.

    Evidence fields are BOOLEAN equalities ([_ = true]) so their proofs are unique
    (decidable equality; see [TypedIR_uip] users) — two IR values agreeing on payloads are
    equal, which keeps elaboration completeness and renderer injectivity proof-friendly.
    ============================================================================ *)
From Stdlib Require Import String ZArith List.
From Fido Require Import TargetConfig CoreType.
Import ListNotations.

Inductive TypedPrimExpr : Type :=
| TEBool   : bool -> TypedPrimExpr
| TEStr    : forall s : string, str_ok s = true -> TypedPrimExpr
| TEIntLit : forall n : Z, int_lit_ok n = true -> TypedPrimExpr   (* nonneg decimal literal *)
| TENeg    : forall n : Z, neg_lit_ok n = true -> TypedPrimExpr.  (* unary minus over the nonneg literal [n]; denotes [-n] *)

(** The certified type of every expression — total, back into the ONE descriptor. *)
Definition type_of (e : TypedPrimExpr) : CoreType :=
  match e with
  | TEBool _     => PBool
  | TEStr _ _    => PString
  | TEIntLit _ _ => PInt
  | TENeg _ _    => PInt
  end.

(** Every typed expression is an admissible [println] operand — by the descriptor's
    exhaustive admissibility, not by a per-node check. *)
Lemma type_of_println_ok : forall e, println_arg_ok (type_of e) = true.
Proof. intro e. apply println_arg_ok_all. Qed.

Inductive TypedStmt : Type :=
| TPrintln : list TypedPrimExpr -> TypedStmt.      (* the RESOLVED builtin; zero args is valid Go *)

(** A typed program IS the body of [func main()] in [package main] — the package name and
    the single parameterless, valueless main are by-construction, so a wrong package or a
    second function is unrepresentable, not rejected. *)
Record TypedProgram : Type := mkTypedProgram {
  tp_body : list TypedStmt
}.
