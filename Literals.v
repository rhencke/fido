(** ============================================================================
    Literals — the admitted STRING-payload charset (the one literal authority not carried
    structurally elsewhere).

    [str_ok] fixes the admitted string-payload charset: printable ASCII + tab + newline.
    A control byte or a byte > 127 (which could break source UTF-8) is REJECTED, never
    approximated — Unicode payloads are an explicit unsupported frontier.  It is the
    evidence carried by [GoAST.EStr] / [GoCompile.CStr], and it is what makes the renderer's
    escaping total and all-ASCII.

    Integer representability is NOT here: it lives INTRINSICALLY on the compiled constructors
    ([GoCompile.CInt]/[CNeg] carry [Z.of_N n <=? int_max]/[<=? - int_min]), consuming the one
    width authority [TargetConfig.int_max]/[int_min] directly.  A magnitude is an unsigned
    [N], so no lower-bound check is needed — there is no separate signed-literal predicate.
    ============================================================================ *)
From Stdlib Require Import String Ascii Bool.

Definition str_char_ok (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (Nat.eqb n 9) || (Nat.eqb n 10) || ((Nat.leb 32 n) && (Nat.leb n 126)).

Fixpoint str_ok (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => str_char_ok c && str_ok s'
  end.
