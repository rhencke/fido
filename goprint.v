(** ============================================================================
    THE VERIFIED PRINTER — slice 1 (the gap #10 / review #12 path).

    The trusted/unverified part of Fido is the hand-written OCaml in [plugin/go.ml]: no theorem relates
    the Go string it emits to the source term.  The agreed fix (no more raw OCaml): the PRINTER moves
    INTO Rocq — a Go AST + a pretty-printer defined here as Rocq functions — is EXTRACTED to OCaml (so
    the plugin runs the SAME function Rocq reasons about, not a hand-written re-implementation), and
    CORRECTNESS theorems are layered atop it.  This file is the foundation; later slices grow the AST to
    cover the emitted fragment, rewire [go.ml] to call the extracted printer, and delete the raw OCaml.

    Slice 1: the Go TYPE sub-language.  [print_ty] renders a [GoTy] to Go source; [print_ty_inj] proves
    it is INJECTIVE on the structural fragment — distinct Go types render to distinct strings, so the
    printer can NEVER conflate two types (the property every [v.(T)] cast / tag rendering depends on).
    [Extraction "printer.ml"] emits the OCaml the plugin will call. *)

From Stdlib Require Import String List Ascii ZArith Lia Bool.
Import ListNotations.
Open Scope string_scope.

(** A Go type, as the plugin renders them.  Note [GTInt] (Go's platform [int], the [GoInt]/[TInt64]
    tag) is DISTINCT from [GTInt64] (the full-width [int64], the [GoI64]/[TI64] tag) — conflating them
    is exactly the kind of bug the verified printer rules out (it caught one in the first integration). *)
Inductive GoTy : Type :=
  | GTInt     : GoTy
  | GTInt64   : GoTy
  | GTBool    : GoTy
  | GTString  : GoTy
  | GTFloat64 : GoTy
  | GTFloat32 : GoTy
  | GTUint    : GoTy
  | GTU8      : GoTy
  | GTI8      : GoTy
  | GTU16     : GoTy
  | GTI16     : GoTy
  | GTU32     : GoTy
  | GTI32     : GoTy
  | GTU64     : GoTy
  | GTPtr     : GoTy -> GoTy
  | GTSlice   : GoTy -> GoTy
  | GTChan    : GoTy -> GoTy
  | GTMap     : GoTy -> GoTy -> GoTy
  | GTNamed   : string -> GoTy.

(** The pretty-printer: a Go type to its source text. *)
Fixpoint print_ty (t : GoTy) : string :=
  match t with
  | GTInt     => "int"
  | GTInt64   => "int64"
  | GTBool    => "bool"
  | GTString  => "string"
  | GTFloat64 => "float64"
  | GTFloat32 => "float32"
  | GTUint    => "uint"
  | GTU8      => "uint8"
  | GTI8      => "int8"
  | GTU16     => "uint16"
  | GTI16     => "int16"
  | GTU32     => "uint32"
  | GTI32     => "int32"
  | GTU64     => "uint64"
  | GTPtr u   => "*"  ++ print_ty u
  | GTSlice u => "[]" ++ print_ty u
  | GTChan u  => "chan " ++ print_ty u
  | GTMap k v => "map[" ++ print_ty k ++ "]" ++ print_ty v
  | GTNamed n => n
  end.

(** STRUCTURAL = no nominal [GTNamed] anywhere (a named type can legally shadow a built-in's rendering
    — Go forbids it too — so injectivity is stated on the shadow-free fragment).  MAPS are now INCLUDED:
    even though the "]" between key and value looks like it could clash with a "[]" slice, the parser
    [parse_ty] disambiguates by RECURSIVELY consuming the key type (the closing "]" is the one after the
    key's full parse), so the round-trip below covers maps too. *)
Fixpoint structural (t : GoTy) : bool :=
  match t with
  | GTNamed _  => false
  | GTMap k v  => structural k && structural v
  | GTPtr u    => structural u
  | GTSlice u  => structural u
  | GTChan u   => structural u
  | _          => true
  end.

(** FAITHFULNESS — the type printer is INJECTIVE on the structural fragment (two structural Go types
    that print alike ARE the same type, so the emitted type text never conflates [int64] with [bool],
    [*int64] with [[]int64], [map[int]int] with [map[int8]int], etc.).  Now DERIVED below as a corollary
    of the print-parse round-trip [parse_print_ty] — which covers maps as well, so injectivity does too;
    only nominal [GTNamed] (inherently ambiguous) stays out of the fragment. *)

(** PRINT-PARSE ROUND-TRIP — the deeper faithfulness: a PARSER recovers the type from its printed
    text.  So the type printer is not just injective but UNAMBIGUOUSLY DECODABLE — the emitted text
    denotes exactly the source type, no information lost or aliased.  Stated in the PREFIX form
    ([parse_ty] consumes exactly [print_ty t], leaving any trailing [rest]) so the cases compose —
    crucially the map case, where the key type is followed by "]" and the value type. *)
Fixpoint strip (p s : string) : option string :=
  match p with
  | EmptyString  => Some s
  | String pc p' => match s with
                    | String sc s' => if Ascii.eqb pc sc then strip p' s' else None
                    | EmptyString  => None
                    end
  end.

(** Keyword scalars — LONGEST first (so [int8] is read before [int], etc.). *)
Definition kw_match (s : string) : option (GoTy * string) :=
  match strip "int64" s   with Some r => Some (GTInt64, r)   | None =>
  match strip "int32" s   with Some r => Some (GTI32, r)     | None =>
  match strip "int16" s   with Some r => Some (GTI16, r)     | None =>
  match strip "int8" s    with Some r => Some (GTI8, r)      | None =>
  match strip "int" s     with Some r => Some (GTInt, r)     | None =>
  match strip "uint64" s  with Some r => Some (GTU64, r)     | None =>
  match strip "uint32" s  with Some r => Some (GTU32, r)     | None =>
  match strip "uint16" s  with Some r => Some (GTU16, r)     | None =>
  match strip "uint8" s   with Some r => Some (GTU8, r)      | None =>
  match strip "uint" s    with Some r => Some (GTUint, r)    | None =>
  match strip "bool" s    with Some r => Some (GTBool, r)    | None =>
  match strip "string" s  with Some r => Some (GTString, r)  | None =>
  match strip "float64" s with Some r => Some (GTFloat64, r) | None =>
  match strip "float32" s with Some r => Some (GTFloat32, r) | None =>
  None end end end end end end end end end end end end end end.

Fixpoint parse_ty (fuel : nat) (s : string) : option (GoTy * string) :=
  match fuel with
  | O   => None
  | S f =>
    match strip "*" s with
    | Some r => match parse_ty f r with Some (u, r') => Some (GTPtr u, r') | None => None end
    | None =>
    match strip "[]" s with
    | Some r => match parse_ty f r with Some (u, r') => Some (GTSlice u, r') | None => None end
    | None =>
    match strip "chan " s with
    | Some r => match parse_ty f r with Some (u, r') => Some (GTChan u, r') | None => None end
    | None =>
    match strip "map[" s with
    | Some r => match parse_ty f r with
                | Some (k, r1) =>
                    match strip "]" r1 with
                    | Some r2 => match parse_ty f r2 with
                                 | Some (v, r3) => Some (GTMap k v, r3)
                                 | None => None end
                    | None => None end
                | None => None end
    | None => kw_match s
    end end end end
  end.

Fixpoint ty_depth (t : GoTy) : nat :=
  match t with
  | GTPtr u | GTSlice u | GTChan u => S (ty_depth u)
  | GTMap a b => S (Nat.max (ty_depth a) (ty_depth b))
  | _ => O
  end.

(** Append is associative and right-unital on strings, and a literal prefix strips off cleanly. *)
Lemma sapp_assoc : forall a b c, ((a ++ b) ++ c)%string = (a ++ (b ++ c))%string.
Proof. induction a as [ | x a IH ]; intros b c; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.
Lemma sapp_nil_r : forall s, (s ++ "")%string = s.
Proof. induction s as [ | x s IH ]; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.
(** A type is only ever followed (within [print_ty]) by end-of-string or a "]" (the map key→value
    boundary).  [rbound] captures that: such a [rest] cannot extend the just-parsed token (the only
    keyword extensions are digits, and "]" is not one), so the parse is unambiguous. *)
Definition rbound (rest : string) : Prop := rest = ""%string \/ exists r, rest = ("]" ++ r)%string.

(** PRINT-PARSE ROUND-TRIP (prefix form): [parse_ty] consumes EXACTLY [print_ty t], leaving [rest].
    The map case needs the prefix generality (after the key comes "]" then the value), and it carries
    the [rbound] discipline so the maximal-munch leaf parse stays correct. *)
Theorem parse_print_ty : forall t f rest,
  structural t = true -> ty_depth t < f -> rbound rest ->
  parse_ty f (print_ty t ++ rest) = Some (t, rest).
Proof.
  induction t as [ | | | | | | | | | | | | | | u IH | u IH | u IH | a IHa b IHb | n ];
    intros f rest Hs Hf Hrb;
    try (cbn in Hs; discriminate Hs);
    destruct f as [ | f ]; cbn [ty_depth] in Hf; try lia.
  (* 14 scalar leaves: [print_ty] is a complete keyword; with [rest] empty or "]"-led the whole parse
     is concrete (the longer-keyword strips fail on a concrete char), so cbn + reflexivity closes it *)
  all: try (destruct Hrb as [-> | [r ->]]; cbn; reflexivity).
  - (* GTPtr u *)  cbn [structural] in Hs. cbn. rewrite (IH f rest Hs ltac:(lia) Hrb). reflexivity.
  - (* GTSlice u *) cbn [structural] in Hs. cbn. rewrite (IH f rest Hs ltac:(lia) Hrb). reflexivity.
  - (* GTChan u *)  cbn [structural] in Hs. cbn. rewrite (IH f rest Hs ltac:(lia) Hrb). reflexivity.
  - (* GTMap a b *) cbn [structural] in Hs. apply andb_prop in Hs. destruct Hs as [Hsa Hsb].
    (* the key parses leaving "]" ++ value ++ rest (a CONCRETE "]"-led remainder, so the inner
       [strip "]"] reduces); the value parses leaving rest *)
    assert (Hk : parse_ty f (print_ty a ++ ("]" ++ (print_ty b ++ rest)))
               = Some (a, "]" ++ (print_ty b ++ rest)))
      by (apply IHa; [ exact Hsa | lia | right; eexists; reflexivity ]).
    assert (Hv : parse_ty f (print_ty b ++ rest) = Some (b, rest))
      by (apply IHb; [ exact Hsb | lia | exact Hrb ]).
    cbn [print_ty]. rewrite !sapp_assoc. cbn in Hk |- *.
    rewrite Hk. cbn. rewrite Hv. reflexivity.
Qed.

(** FAITHFULNESS COROLLARY — INJECTIVITY on the structural fragment (now INCLUDING maps), derived from
    the round-trip: two structural types that print alike parse to the same tree, hence are equal. *)
Corollary print_ty_inj : forall t1 t2,
  structural t1 = true -> structural t2 = true -> print_ty t1 = print_ty t2 -> t1 = t2.
Proof.
  intros t1 t2 H1 H2 He.
  set (f := S (Nat.max (ty_depth t1) (ty_depth t2))).
  assert (R1 : parse_ty f (print_ty t1) = Some (t1, "")).
  { rewrite <- (sapp_nil_r (print_ty t1)).
    apply parse_print_ty; [ exact H1 | unfold f; lia | left; reflexivity ]. }
  assert (R2 : parse_ty f (print_ty t2) = Some (t2, "")).
  { rewrite <- (sapp_nil_r (print_ty t2)).
    apply parse_print_ty; [ exact H2 | unfold f; lia | left; reflexivity ]. }
  rewrite He in R1. rewrite R1 in R2. injection R2 as Ht. exact Ht.
Qed.

(** ---- INTEGER LITERALS ---- the decimal rendering of a [Z] value (replacing go.ml's raw
    [Printf.sprintf "%Ld"/"%Lu"]).  Magnitude is carried by [Z], so this is faithful for the FULL
    int64 AND uint64 ranges (the unsigned [2^63,2^64) values that wrap as a negative [Int64.t] are
    just large [Zpos] here — no special-casing). *)
Definition dec_digit (n : nat) : ascii := ascii_of_nat (48 + n).
Fixpoint z_digits (fuel : nat) (z : Z) (acc : string) : string :=
  match fuel with
  | O    => acc
  | S f  => let d := dec_digit (Z.to_nat (z mod 10)) in
            if (z / 10 =? 0)%Z then String d acc
            else z_digits f (z / 10)%Z (String d acc)
  end.
(** Adaptive fuel — at least as many steps as [z] has decimal digits, so [z_digits] NEVER truncates a
    large input (the old fixed [64] silently dropped digits for |z| >= 10^64 — accepted arbitrary [Z] but
    was correct only under a bound).  [Z.log2 z + 1] is the BIT width, which exceeds the decimal-digit
    count (since 10 > 2), so it is always enough; and it is cheap (no astronomically large [nat]).  Only
    ever applied to [z > 0] ([print_Z] special-cases 0 and negates negatives). *)
Definition digit_fuel (z : Z) : nat := S (Z.to_nat (Z.log2 z)).
Definition print_Z (z : Z) : string :=
  if (z =? 0)%Z then "0"
  else if (z <? 0)%Z then ("-" ++ z_digits (digit_fuel (- z)) (- z) "")%string
  else z_digits (digit_fuel z) z "".

(** Computational checks: the decimal printer is correct on samples spanning the int64/uint64 range
    (incl. the unsigned value [2^63] that an [Int64.t]-based printer renders only via [%Lu]). *)
Example print_Z_0    : print_Z 0 = "0".                                       Proof. reflexivity. Qed.
Example print_Z_42   : print_Z 42 = "42".                                     Proof. reflexivity. Qed.
Example print_Z_neg  : print_Z (-7) = "-7".                                   Proof. reflexivity. Qed.
Example print_Z_imax : print_Z 9223372036854775807 = "9223372036854775807".  Proof. reflexivity. Qed.
Example print_Z_u63  : print_Z 9223372036854775808 = "9223372036854775808".  Proof. reflexivity. Qed.

(** ---- INTEGER FAITHFULNESS (round-trip) ---- a decimal PARSER recovers the [Z] from [print_Z]'s
    output, so the emitted integer literal denotes EXACTLY the source value over the whole modelled
    range (|z| < 10^64 — far beyond the int64/uint64 values [print_Z] is ever called with).  The
    analog of [parse_print_ty] / [esc_string_roundtrip] for integer literals — the most-emitted leaf. *)
Definition dval (c : ascii) : Z := Z.of_nat (nat_of_ascii c - 48).
Fixpoint parseZ_pos (acc : Z) (s : string) : Z :=
  match s with EmptyString => acc | String c s' => parseZ_pos (acc * 10 + dval c)%Z s' end.
Definition parse_Z (s : string) : Z :=
  match s with
  | EmptyString  => 0%Z
  | String c s'  => if Ascii.eqb c (ascii_of_nat 45) then (- parseZ_pos 0 s')%Z else parseZ_pos 0 s
  end.

(** [dval] inverts [dec_digit] on a single decimal digit. *)
Lemma dval_dec_digit : forall n, (n < 10)%nat -> dval (dec_digit n) = Z.of_nat n.
Proof.
  intros n H. unfold dval, dec_digit. rewrite Ascii.nat_ascii_embedding by lia. f_equal. lia.
Qed.

(** KEY LEMMA — parsing [z_digits]' output from accumulator 0 recovers [z] into the running fold: the
    digit-count shift would be [a * 10^k] but [a = 0] kills it, so NO power arithmetic is needed. *)
Lemma parseZ_pos_z_digits : forall fuel z acc,
  (0 <= z)%Z -> (z < 10 ^ Z.of_nat fuel)%Z -> parseZ_pos 0 (z_digits fuel z acc) = parseZ_pos z acc.
Proof.
  induction fuel as [ | f IH ]; intros z acc Hz Hb.
  - cbn [z_digits]. assert (z = 0%Z) by (cbn in Hb; lia). subst z. reflexivity.
  - cbn [z_digits].
    pose proof (Z.mod_pos_bound z 10 ltac:(lia)) as Hmod.
    assert (Hk : (Z.to_nat (z mod 10) < 10)%nat) by lia.
    destruct (Z.eqb (z / 10) 0) eqn:E.
    + apply Z.eqb_eq in E.
      cbn [parseZ_pos]. rewrite dval_dec_digit by exact Hk. rewrite Z2Nat.id by lia.
      replace (0 * 10 + z mod 10)%Z with z by (pose proof (Z.div_mod z 10 ltac:(lia)); lia).
      reflexivity.
    + apply Z.eqb_neq in E.
      assert (Hdpos : (0 <= z / 10)%Z) by (apply Z.div_pos; lia).
      assert (Hdlt : (z / 10 < 10 ^ Z.of_nat f)%Z).
      { apply Z.div_lt_upper_bound; [ lia | ].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hb by lia. lia. }
      rewrite (IH (z / 10)%Z (String (dec_digit (Z.to_nat (z mod 10))) acc) Hdpos Hdlt).
      cbn [parseZ_pos]. rewrite dval_dec_digit by exact Hk. rewrite Z2Nat.id by lia.
      replace (z / 10 * 10 + z mod 10)%Z with z by (pose proof (Z.div_mod z 10 ltac:(lia)); lia).
      reflexivity.
Qed.

(** The first character [z_digits] emits is a decimal digit (so, for a POSITIVE [z], it is never the
    leading "-" — which lets [parse_Z] take the unsigned branch). *)
Lemma z_digits_head : forall f z acc, (0 < f)%nat ->
  exists k r, (k < 10)%nat /\ z_digits f z acc = String (dec_digit k) r.
Proof.
  induction f as [ | f IH ]; intros z acc Hf; [ lia | ].
  cbn [z_digits]. pose proof (Z.mod_pos_bound z 10 ltac:(lia)) as Hmod.
  assert (Hk : (Z.to_nat (z mod 10) < 10)%nat) by lia.
  destruct (Z.eqb (z / 10) 0) eqn:E.
  - exists (Z.to_nat (z mod 10)), acc; split; [ exact Hk | reflexivity ].
  - destruct f as [ | f' ].
    + exists (Z.to_nat (z mod 10)), acc; split; [ exact Hk | reflexivity ].
    + destruct (IH (z / 10)%Z (String (dec_digit (Z.to_nat (z mod 10))) acc) ltac:(lia))
        as [k [r [Hk2 Hr]]].
      exists k, r; split; [ exact Hk2 | exact Hr ].
Qed.

Lemma dec_digit_ne_minus : forall k, (k < 10)%nat -> Ascii.eqb (dec_digit k) (ascii_of_nat 45) = false.
Proof.
  intros k Hk. apply Bool.not_true_iff_false. intro H. apply Ascii.eqb_eq in H.
  unfold dec_digit in H. apply (f_equal nat_of_ascii) in H.
  rewrite !Ascii.nat_ascii_embedding in H by lia. lia.
Qed.

Lemma parse_Z_neg : forall X, parse_Z (String (ascii_of_nat 45) X) = (- parseZ_pos 0 X)%Z.
Proof. intro X. cbn [parse_Z]. rewrite Ascii.eqb_refl. reflexivity. Qed.
Lemma parse_Z_nonminus : forall c X, Ascii.eqb c (ascii_of_nat 45) = false ->
  parse_Z (String c X) = parseZ_pos 0 (String c X).
Proof. intros c X H. cbn [parse_Z]. rewrite H. reflexivity. Qed.

(** The adaptive fuel is always enough for ANY base [b >= 2]: [z < b ^ digit_fuel z] for [z > 0].
    [digit_fuel z] is the bit width [Z.log2 z + 1]; [z < 2^(log2 z + 1)] and [2^k <= b^k], so
    [z < b^(log2 z + 1)].  (Instantiated at b=10 for [print_Z], b=16 for [print_hex].) *)
Lemma z_lt_pow_digit_fuel : forall b z, (2 <= b)%Z -> (0 < z)%Z -> (z < b ^ Z.of_nat (digit_fuel z))%Z.
Proof.
  intros b z Hb Hz. unfold digit_fuel.
  rewrite Nat2Z.inj_succ, Z2Nat.id by apply Z.log2_nonneg.
  apply Z.lt_le_trans with (2 ^ Z.succ (Z.log2 z))%Z.
  - apply (proj2 (Z.log2_spec z Hz)).
  - apply Z.pow_le_mono_l; lia.
Qed.

(** FAITHFULNESS, now UNCONDITIONAL — with the adaptive fuel [print_Z] never truncates, so the round-trip
    holds for EVERY [z] (no |z| < 10^64 side condition). *)
Theorem print_parse_Z : forall z, parse_Z (print_Z z) = z.
Proof.
  intro z. unfold print_Z.
  destruct (Z.eqb z 0) eqn:E0; [ apply Z.eqb_eq in E0; subst z; reflexivity | ].
  apply Z.eqb_neq in E0. destruct (Z.ltb z 0) eqn:Eneg.
  - (* z < 0 *) apply Z.ltb_lt in Eneg.
    replace (("-" ++ z_digits (digit_fuel (- z)) (- z) "")%string)
       with (String (ascii_of_nat 45) (z_digits (digit_fuel (- z)) (- z) "")) by reflexivity.
    rewrite parse_Z_neg.
    rewrite parseZ_pos_z_digits by (try (apply (z_lt_pow_digit_fuel 10)); lia).
    cbn [parseZ_pos]. lia.
  - (* z > 0 *) apply Z.ltb_ge in Eneg. assert (Hz : (0 < z)%Z) by lia.
    destruct (z_digits_head (digit_fuel z) z "" ltac:(unfold digit_fuel; lia)) as [k [r [Hk Hr]]].
    rewrite Hr, (parse_Z_nonminus _ _ (dec_digit_ne_minus k Hk)), <- Hr.
    rewrite parseZ_pos_z_digits by (try (apply (z_lt_pow_digit_fuel 10)); lia).
    cbn [parseZ_pos]. reflexivity.
Qed.

(** ---- STRING LITERALS ---- escape a Go double-quoted string literal (replacing go.ml's raw
    [go_string_lit]): wrap in dquotes, escape dquote/backslash/newline/tab/CR, pass printable ASCII
    through, and emit a hex escape (backslash-x, lowercase, 2 digits) for everything else.  ASCII
    codes: 34 dquote, 92 backslash, 10 newline, 9 tab, 13 CR, 110 n, 116 t, 114 r, 120 x. *)
Definition ch (n : nat) : ascii := ascii_of_nat n.
Definition hexdig (n : nat) : ascii := ascii_of_nat (if Nat.ltb n 10 then 48 + n else 87 + n).
Definition esc_byte (b : nat) (acc : string) : string :=
  if Nat.eqb b 34 then String (ch 92) (String (ch 34) acc)
  else if Nat.eqb b 92 then String (ch 92) (String (ch 92) acc)
  else if Nat.eqb b 10 then String (ch 92) (String (ch 110) acc)
  else if Nat.eqb b 9  then String (ch 92) (String (ch 116) acc)
  else if Nat.eqb b 13 then String (ch 92) (String (ch 114) acc)
  else if andb (Nat.leb 32 b) (Nat.ltb b 127) then String (ch b) acc
  else String (ch 92) (String (ch 120)
         (String (hexdig (Nat.div b 16)) (String (hexdig (Nat.modulo b 16)) acc))).
Fixpoint esc_string (s : string) : string :=
  match s with
  | EmptyString   => EmptyString
  | String c rest => esc_byte (nat_of_ascii c) (esc_string rest)
  end.
Definition print_string_lit (s : string) : string :=
  String (ch 34) (esc_string s ++ String (ch 34) EmptyString).

Example psl_empty : print_string_lit "" = String (ch 34) (String (ch 34) ""). Proof. reflexivity. Qed.
Example psl_fido  : print_string_lit "fido" = String (ch 34) ("fido" ++ String (ch 34) ""). Proof. reflexivity. Qed.

(** ---- STRING-LITERAL FAITHFULNESS (round-trip) ---- the escaping is LOSSLESS: a decoder [unescape]
    recovers the exact original bytes from [esc_string], so [print_string_lit] denotes precisely its
    argument — no byte dropped, merged, or corrupted by an escape.  This is the data-faithfulness
    property for string literals (the analog of [parse_print_ty] for the type sub-language). *)
Lemma nat_of_ascii_lt_256 : forall c, nat_of_ascii c < 256.
Proof. intro c. destruct c. repeat match goal with b : bool |- _ => destruct b end; cbn; lia. Qed.
Lemma nat_of_ch : forall n, n < 256 -> nat_of_ascii (ch n) = n.
Proof. intros n H. unfold ch. apply Ascii.nat_ascii_embedding. exact H. Qed.
Lemma ch_nat : forall c, ch (nat_of_ascii c) = c.
Proof. intro c. unfold ch. apply Ascii.ascii_nat_embedding. Qed.

(** Inverse of [hexdig] on a single hex nibble. *)
Definition unhex (c : ascii) : nat :=
  let v := nat_of_ascii c in if Nat.leb v 57 then v - 48 else v - 87.
Lemma unhex_hexdig : forall k, k < 16 -> unhex (hexdig k) = k.
Proof.
  intros k H. unfold unhex, hexdig. destruct (Nat.ltb k 10) eqn:E.
  - apply Nat.ltb_lt in E. rewrite Ascii.nat_ascii_embedding by lia.
    destruct (Nat.leb (48 + k) 57) eqn:E2; [ lia | apply Nat.leb_gt in E2; lia ].
  - apply Nat.ltb_ge in E. rewrite Ascii.nat_ascii_embedding by lia.
    destruct (Nat.leb (87 + k) 57) eqn:E2; [ apply Nat.leb_le in E2; lia | lia ].
Qed.

(** The decoder: reverse [esc_byte].  A backslash (92) introduces an escape — the next byte selects
    the special char or, for "x" (120), the two hex nibbles; any other byte is itself.  Structural on
    sub-terms of [s] (so no fuel needed). *)
Fixpoint unescape (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c1 rest =>
      if Nat.eqb (nat_of_ascii c1) 92 then
        match rest with
        | EmptyString => EmptyString
        | String c2 rest2 =>
            let d := nat_of_ascii c2 in
            if Nat.eqb d 34 then String (ch 34) (unescape rest2)
            else if Nat.eqb d 92 then String (ch 92) (unescape rest2)
            else if Nat.eqb d 110 then String (ch 10) (unescape rest2)
            else if Nat.eqb d 116 then String (ch 9) (unescape rest2)
            else if Nat.eqb d 114 then String (ch 13) (unescape rest2)
            else if Nat.eqb d 120 then
              match rest2 with
              | String h1 (String h2 rest3) => String (ch (16 * unhex h1 + unhex h2)) (unescape rest3)
              | _ => EmptyString
              end
            else EmptyString
        end
      else String c1 (unescape rest)
  end.

(* Keep [ch]/[nat_of_ascii]/[unhex]/[hexdig] opaque so [cbn] reduces only the [Nat.eqb] dispatch and
   the matches, leaving [ch <v>] / [nat_of_ascii (ch _)] / [unhex (hexdig _)] symbolic for the rewrites. *)
Local Opaque ch nat_of_ascii unhex hexdig Nat.div Nat.modulo.
Lemma unescape_esc_byte : forall c X, unescape (esc_byte (nat_of_ascii c) X) = String c (unescape X).
Proof.
  intros c X. assert (Hc : nat_of_ascii c < 256) by apply nat_of_ascii_lt_256.
  unfold esc_byte.
  destruct (Nat.eqb (nat_of_ascii c) 34) eqn:E34.
  { apply Nat.eqb_eq in E34.
    cbn [unescape]. rewrite (nat_of_ch 92) by lia. cbn. rewrite (nat_of_ch 34) by lia. cbn.
    rewrite <- E34, ch_nat. reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 92) eqn:E92.
  { apply Nat.eqb_eq in E92.
    cbn [unescape]. rewrite (nat_of_ch 92) by lia. cbn.
    rewrite <- E92, ch_nat. reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 10) eqn:E10.
  { apply Nat.eqb_eq in E10.
    cbn [unescape]. rewrite (nat_of_ch 92) by lia. cbn. rewrite (nat_of_ch 110) by lia. cbn.
    rewrite <- E10, ch_nat. reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 9) eqn:E9.
  { apply Nat.eqb_eq in E9.
    cbn [unescape]. rewrite (nat_of_ch 92) by lia. cbn. rewrite (nat_of_ch 116) by lia. cbn.
    rewrite <- E9, ch_nat. reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 13) eqn:E13.
  { apply Nat.eqb_eq in E13.
    cbn [unescape]. rewrite (nat_of_ch 92) by lia. cbn. rewrite (nat_of_ch 114) by lia. cbn.
    rewrite <- E13, ch_nat. reflexivity. }
  destruct (andb (Nat.leb 32 (nat_of_ascii c)) (Nat.ltb (nat_of_ascii c) 127)) eqn:Eprint.
  { (* printable byte: emitted as-is, decoded as-is (not a backslash since c <> 92 by E92) *)
    cbn [unescape]. rewrite (nat_of_ch (nat_of_ascii c)) by exact Hc.
    rewrite E92. cbn. rewrite ch_nat. reflexivity. }
  { (* hex escape: \xHL with H = b/16, L = b mod 16; 16*H + L = b *)
    cbn [unescape]. rewrite (nat_of_ch 92) by lia. cbn. rewrite (nat_of_ch 120) by lia. cbn. f_equal.
    rewrite (unhex_hexdig (Nat.div (nat_of_ascii c) 16)) by (apply Nat.Div0.div_lt_upper_bound; lia).
    rewrite (unhex_hexdig (Nat.modulo (nat_of_ascii c) 16)) by (apply Nat.mod_upper_bound; lia).
    transitivity (ch (nat_of_ascii c));
      [ f_equal; pose proof (Nat.div_mod_eq (nat_of_ascii c) 16); lia | apply ch_nat ]. }
Qed.
Local Transparent ch nat_of_ascii unhex hexdig Nat.div Nat.modulo.

Theorem esc_string_roundtrip : forall s, unescape (esc_string s) = s.
Proof.
  induction s as [ | c rest IH ]; [ reflexivity | ].
  cbn [esc_string]. rewrite unescape_esc_byte, IH. reflexivity.
Qed.

(** ---- HEX LITERALS ---- [0x]-prefixed lowercase hex (replacing go.ml's [Printf.sprintf "0x%x"] for
    fixed-width bit masks / sign bits). *)
Fixpoint hex_digits (fuel : nat) (z : Z) (acc : string) : string :=
  match fuel with
  | O   => acc
  | S f => let d := hexdig (Z.to_nat (z mod 16)) in
           if (z / 16 =? 0)%Z then String d acc else hex_digits f (z / 16)%Z (String d acc)
  end.
Definition print_hex (z : Z) : string :=
  ("0x" ++ (if (z =? 0)%Z then "0" else hex_digits (digit_fuel z) z ""))%string.
Example ph_ff : print_hex 255 = "0xff". Proof. reflexivity. Qed.
Example ph_0  : print_hex 0   = "0x0".  Proof. reflexivity. Qed.
Example ph_80 : print_hex 128 = "0x80". Proof. reflexivity. Qed.

(** ---- HEX FAITHFULNESS (round-trip) ---- the analog of [print_parse_Z] for the [0x]-hex printer
    ([hex_digits] is structurally [z_digits] in base 16; [unhex]/[unhex_hexdig] from the string section
    already invert [hexdig]).  [print_hex] is only ever called on NON-NEGATIVE values (bit masks), so the
    statement is for [0 <= z < 16^64] — again far beyond any fixed-width mask. *)
Fixpoint parseHex_pos (acc : Z) (s : string) : Z :=
  match s with EmptyString => acc | String c s' => parseHex_pos (acc * 16 + Z.of_nat (unhex c))%Z s' end.
Definition parse_hex (s : string) : Z :=
  match s with String _ (String _ rest) => parseHex_pos 0 rest | _ => 0%Z end.

Lemma parse_hex_0x : forall X, parse_hex ("0x" ++ X)%string = parseHex_pos 0 X.
Proof. intro X. reflexivity. Qed.
Lemma print_hex_pos : forall z, (z <> 0)%Z -> print_hex z = ("0x" ++ hex_digits (digit_fuel z) z "")%string.
Proof. intros z H. apply Z.eqb_neq in H. unfold print_hex. rewrite H. reflexivity. Qed.

Lemma parseHex_pos_hex_digits : forall fuel z acc,
  (0 <= z)%Z -> (z < 16 ^ Z.of_nat fuel)%Z -> parseHex_pos 0 (hex_digits fuel z acc) = parseHex_pos z acc.
Proof.
  induction fuel as [ | f IH ]; intros z acc Hz Hb.
  - cbn [hex_digits]. assert (z = 0%Z) by (cbn in Hb; lia). subst z. reflexivity.
  - cbn [hex_digits].
    pose proof (Z.mod_pos_bound z 16 ltac:(lia)) as Hmod.
    assert (Hk : (Z.to_nat (z mod 16) < 16)%nat) by lia.
    destruct (Z.eqb (z / 16) 0) eqn:E.
    + apply Z.eqb_eq in E.
      cbn [parseHex_pos]. rewrite unhex_hexdig by exact Hk. rewrite Z2Nat.id by lia.
      replace (0 * 16 + z mod 16)%Z with z by (pose proof (Z.div_mod z 16 ltac:(lia)); lia).
      reflexivity.
    + apply Z.eqb_neq in E.
      assert (Hdpos : (0 <= z / 16)%Z) by (apply Z.div_pos; lia).
      assert (Hdlt : (z / 16 < 16 ^ Z.of_nat f)%Z).
      { apply Z.div_lt_upper_bound; [ lia | ].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hb by lia. lia. }
      rewrite (IH (z / 16)%Z (String (hexdig (Z.to_nat (z mod 16))) acc) Hdpos Hdlt).
      cbn [parseHex_pos]. rewrite unhex_hexdig by exact Hk. rewrite Z2Nat.id by lia.
      replace (z / 16 * 16 + z mod 16)%Z with z by (pose proof (Z.div_mod z 16 ltac:(lia)); lia).
      reflexivity.
Qed.

(** UNCONDITIONAL for every non-negative [z] (the adaptive fuel never truncates). *)
Theorem print_parse_hex : forall z, (0 <= z)%Z -> parse_hex (print_hex z) = z.
Proof.
  intros z Hlo. destruct (Z.eqb z 0) eqn:E0.
  - apply Z.eqb_eq in E0; subst z. reflexivity.
  - apply Z.eqb_neq in E0. rewrite print_hex_pos by exact E0. rewrite parse_hex_0x.
    rewrite parseHex_pos_hex_digits by (try (apply (z_lt_pow_digit_fuel 16)); lia).
    cbn [parseHex_pos]. reflexivity.
Qed.

(** ---- FLOAT-HEX LITERAL ---- the IEEE [spec_float] finite value ±m·2^e emits as Go's hex float
    [±0x<m>p<e>].  Slice 15 verified the mantissa/exponent PIECES (print_hex / print_Z); this moves the
    ASSEMBLY into Rocq too (the last leaf whose glue was raw OCaml [^]).  [sign] = sign, [mant] =
    mantissa (rendered hex), [exp] = exponent (signed decimal). *)
Definition print_float_hex (sign : bool) (mant exp : Z) : string :=
  ((if sign then "-" else "") ++ print_hex mant ++ "p" ++ print_Z exp)%string.

Example pfh_pos : print_float_hex false 24 (-52) = "0x18p-52". Proof. reflexivity. Qed.
Example pfh_neg : print_float_hex true 18 51   = "-0x12p51". Proof. reflexivity. Qed.

(** FAITHFULNESS — the float literal round-trips: a parser recovers [(sign, mant, exp)] EXACTLY.  The
    "p" delimiter is unambiguous because the mantissa render [print_hex] contains no "p" (hex digits are
    0-9a-f); [split_p] cuts there, then [parse_hex] / [parse_Z] recover the parts (slices 20/21). *)
Definition is_p (c : ascii) : bool := Ascii.eqb c (ascii_of_nat 112).  (* 'p' = 112 *)
Fixpoint no_p (s : string) : Prop :=
  match s with EmptyString => True | String c s' => is_p c = false /\ no_p s' end.
Lemma no_p_app : forall a b, no_p a -> no_p b -> no_p (a ++ b).
Proof.
  induction a as [ | c a IH ]; intros b Ha Hb; [ exact Hb | ].
  cbn [no_p append] in *. destruct Ha as [Hc Ha]. split; [ exact Hc | apply IH; assumption ].
Qed.

Lemma is_p_hexdig : forall k, (k < 16)%nat -> is_p (hexdig k) = false.
Proof.
  intros k Hk. unfold is_p, hexdig.
  destruct (Nat.ltb k 10) eqn:E; cbv iota;
    [ apply Nat.ltb_lt in E | apply Nat.ltb_ge in E ];
    apply Bool.not_true_iff_false; intro H; apply Ascii.eqb_eq in H;
    apply (f_equal nat_of_ascii) in H; rewrite !Ascii.nat_ascii_embedding in H by lia; lia.
Qed.

Lemma hex_digits_no_p : forall fuel z acc, no_p acc -> no_p (hex_digits fuel z acc).
Proof.
  induction fuel as [ | f IH ]; intros z acc Hacc; [ exact Hacc | ].
  cbn [hex_digits]. pose proof (Z.mod_pos_bound z 16 ltac:(lia)) as Hmod.
  assert (Hk : (Z.to_nat (z mod 16) < 16)%nat) by lia.
  destruct (Z.eqb (z / 16) 0).
  - cbn [no_p]. split; [ apply is_p_hexdig; exact Hk | exact Hacc ].
  - apply IH. cbn [no_p]. split; [ apply is_p_hexdig; exact Hk | exact Hacc ].
Qed.

Lemma no_p_print_hex : forall z, no_p (print_hex z).
Proof.
  intro z. unfold print_hex. apply no_p_app.
  - cbn [no_p]. repeat split; (reflexivity || exact I).
  - destruct (Z.eqb z 0); [ cbn [no_p]; repeat split; (reflexivity || exact I)
                          | apply hex_digits_no_p; exact I ].
Qed.

Fixpoint split_p (s : string) : string * string :=
  match s with
  | EmptyString  => (""%string, ""%string)
  | String c s'  => if is_p c then (""%string, s') else let (a, b) := split_p s' in (String c a, b)
  end.
Lemma split_p_app : forall pre suf, no_p pre ->
  split_p (pre ++ String (ascii_of_nat 112) suf) = (pre, suf).
Proof.
  induction pre as [ | c pre IH ]; intros suf Hnp.
  - cbn. reflexivity.
  - cbn [no_p] in Hnp. destruct Hnp as [Hc Hnp].
    cbn [split_p append]. rewrite Hc, (IH suf Hnp). reflexivity.
Qed.

(** [print_hex mant ++ "p" ++ print_Z exp] (optionally prefixed by a "p"-free [pre]) splits at the
    delimiter into the mantissa render and the exponent render. *)
Lemma split_p_float : forall pre mant exp, no_p pre ->
  split_p (pre ++ print_hex mant ++ "p" ++ print_Z exp)%string
    = ((pre ++ print_hex mant)%string, print_Z exp).
Proof.
  intros pre mant exp Hpre.
  assert (Heq : (pre ++ print_hex mant ++ "p" ++ print_Z exp)%string
              = ((pre ++ print_hex mant) ++ String (ascii_of_nat 112) (print_Z exp))%string)
    by (rewrite !sapp_assoc; reflexivity).
  rewrite Heq. apply split_p_app. apply no_p_app; [ exact Hpre | apply no_p_print_hex ].
Qed.

(** [print_hex] always begins with the digit "0" (of its "0x" prefix), so a positive float's mantissa
    part never looks like the leading "-". *)
Lemma print_hex_head : forall z, exists rest, print_hex z = String (ascii_of_nat 48) rest.
Proof. intro z. unfold print_hex. eexists. reflexivity. Qed.

Definition parse_float_hex (s : string) : bool * Z * Z :=
  let (mpart, epart) := split_p s in
  let e := parse_Z epart in
  match mpart with
  | String c rest => if Ascii.eqb c (ascii_of_nat 45) then (true, parse_hex rest, e)
                     else (false, parse_hex mpart, e)
  | EmptyString => (false, 0%Z, e)
  end.
Lemma parse_float_hex_eq : forall s mpart epart, split_p s = (mpart, epart) ->
  parse_float_hex s =
    (match mpart with
     | String c rest => if Ascii.eqb c (ascii_of_nat 45) then (true, parse_hex rest, parse_Z epart)
                        else (false, parse_hex mpart, parse_Z epart)
     | EmptyString => (false, 0%Z, parse_Z epart)
     end).
Proof. intros s mpart epart H. unfold parse_float_hex. rewrite H. reflexivity. Qed.

Local Opaque print_hex print_Z parse_hex parse_Z.
(** UNCONDITIONAL but for the mantissa's non-negativity (hex is unsigned); [exp] is any [Z]. *)
Theorem print_parse_float_hex : forall sign mant exp,
  (0 <= mant)%Z ->
  parse_float_hex (print_float_hex sign mant exp) = (sign, mant, exp).
Proof.
  intros sign mant exp Hm.
  assert (Hmrt : parse_hex (print_hex mant) = mant) by (apply print_parse_hex; lia).
  assert (Hert : parse_Z (print_Z exp) = exp) by (apply print_parse_Z).
  unfold print_float_hex. destruct sign; cbv iota.
  - (* sign = true: prefix "-" *)
    rewrite (parse_float_hex_eq _ _ _
              (split_p_float "-" mant exp ltac:(cbn [no_p]; repeat split; (reflexivity || exact I)))).
    cbn. rewrite Hmrt, Hert. reflexivity.
  - (* sign = false: empty prefix *)
    destruct (print_hex_head mant) as [rest Hph].
    rewrite (parse_float_hex_eq _ _ _ (split_p_float "" mant exp ltac:(exact I))).
    cbn [append]. rewrite Hph at 1. cbn. rewrite Hmrt, Hert. reflexivity.
Qed.
Local Transparent print_hex print_Z parse_hex parse_Z.

(** ---- PROOFS ATOP THE PRINTERS ---- WELL-FORMEDNESS: every printer yields a NON-EMPTY string, so no
    emitted token is ever blank (which would be malformed Go).  [print_ty] on the structural fragment,
    and the literal printers unconditionally.  (Injectivity AND the print-parse round-trip are already
    proved above for the full structural fragment, maps included — [print_ty_inj] / [parse_print_ty].) *)
Lemma print_ty_nonempty : forall t, structural t = true -> print_ty t <> ""%string.
Proof. induction t; intro H; cbn in *; try discriminate; intro Hc; discriminate Hc. Qed.
Lemma print_string_lit_nonempty : forall s, print_string_lit s <> ""%string.
Proof. intros s Hc. unfold print_string_lit in Hc. discriminate Hc. Qed.
Lemma print_hex_nonempty : forall z, print_hex z <> ""%string.
Proof. intros z Hc. unfold print_hex in Hc. discriminate Hc. Qed.

(** [z_digits] with a non-empty accumulator stays non-empty; hence [print_Z] is never blank. *)
Lemma z_digits_acc_nonempty : forall fuel z c rest, z_digits fuel z (String c rest) <> ""%string.
Proof.
  induction fuel as [ | f IH ]; intros z c rest; cbn [z_digits]; [ discriminate | ].
  destruct (z / 10 =? 0)%Z; [ discriminate | apply IH ].
Qed.
(* one unfold step, with the fuel kept ABSTRACT (so cbn does not expand all 64 nested levels) *)
Lemma z_digits_first_nonempty : forall f z, z_digits (S f) z ""%string <> ""%string.
Proof.
  intros f z. cbn [z_digits].
  destruct (z / 10 =? 0)%Z; [ discriminate | apply z_digits_acc_nonempty ].
Qed.
Lemma print_Z_nonempty : forall z, print_Z z <> ""%string.
Proof.
  intro z. unfold print_Z.
  destruct (z =? 0)%Z. { discriminate. }
  destruct (z <? 0)%Z.
  - intro Hc. discriminate Hc.            (* "-" ++ … reduces (whnf) to String "-" … *)
  - apply z_digits_first_nonempty.        (* z_digits 64 z "" = z_digits (S 63) z "" *)
Qed.

(** ============================================================================
    ---- EXPRESSIONS: OPERATOR PRECEDENCE ---- the first STRUCTURAL (recursive) piece of the printer to
    move into Rocq.  [go.ml]'s [pp_prec] renders a binary-operator tree, inserting parentheses ONLY
    where an operand's operator binds LOOSER than its context — get this wrong and [(a+b)*c] misprints
    as [a+b*c], silently changing the program's meaning.  This is the hardest correctness property of the
    structural printer, so it is the right first target.

    [GoExpr] models the binary-operator tree the plugin assembles.  CRUCIALLY the operator text and its
    precedence are NOT supplied by the caller — they are DERIVED from a [BinOp] constructor, so a caller
    cannot mis-state them.  (The old [GEBin (p:nat) (op:string) …] let a caller pass " * " at precedence 5
    with a looser raw operand — e.g. [GEBin 5 " * " (GERaw "a + b") (GERaw "c")] — which printed
    [a + b * c] for what should be [(a + b) * c]: the balance theorem held yet the parse was wrong.)
    [EAtom s] is a pre-rendered ATOM — an operand that binds tightest (literal / variable / call / field /
    index); [EBin o l r] is a LEFT-ASSOCIATIVE binary operator [o].  [print_expr ctx e] renders [e] where
    the context demands precedence >= [ctx]: an [EBin] of precedence [binop_prec o] is parenthesized
    exactly when that [< ctx]; operands recurse at [p] (left) and [S p] (right, one tighter — left
    associativity), MIRRORING the plugin's [pp_prec] byte-for-byte. *)
Inductive BinOp : Type :=
  (* Go precedence 5: *  /  %  <<  >>  &  &^ *)
  | BMul | BDiv | BRem | BShl | BShr | BAnd | BAndNot
  (* Go precedence 4: +  -  |  ^ *)
  | BAdd | BSub | BOr | BXor
  (* Go precedence 3: ==  !=  <  <=  >  >= *)
  | BEq | BNe | BLt | BLe | BGt | BGe
  (* Go precedence 2 / 1: &&  || *)
  | BLAnd | BLOr.

(** Operator precedence and surface text DERIVED from the constructor — the single source of truth. *)
Definition binop_prec (o : BinOp) : nat :=
  match o with
  | BMul | BDiv | BRem | BShl | BShr | BAnd | BAndNot => 5
  | BAdd | BSub | BOr | BXor => 4
  | BEq | BNe | BLt | BLe | BGt | BGe => 3
  | BLAnd => 2
  | BLOr => 1
  end.
Definition binop_text (o : BinOp) : string :=
  match o with
  | BMul => " * "  | BDiv => " / "  | BRem => " % "  | BShl => " << " | BShr => " >> "
  | BAnd => " & "  | BAndNot => " &^ "
  | BAdd => " + "  | BSub => " - "  | BOr  => " | "  | BXor => " ^ "
  | BEq  => " == " | BNe  => " != " | BLt  => " < "  | BLe  => " <= " | BGt => " > " | BGe => " >= "
  | BLAnd => " && " | BLOr => " || "
  end.

Inductive GoExpr : Type :=
  | EAtom : string -> GoExpr
  | EBin  : BinOp -> GoExpr -> GoExpr -> GoExpr.

Fixpoint print_expr (ctx : nat) (e : GoExpr) : string :=
  match e with
  | EAtom s => s
  | EBin o l r =>
      let p := binop_prec o in
      let inner := (print_expr p l ++ binop_text o ++ print_expr (S p) r)%string in
      if Nat.ltb p ctx then ("(" ++ inner ++ ")")%string else inner
  end.

(** CHARACTERIZATION — exact behaviour and the byte-identical basis vs [pp_prec]: an atom prints
    verbatim; a binop wraps iff [binop_prec o < ctx]. *)
Lemma print_expr_atom : forall ctx s, print_expr ctx (EAtom s) = s.
Proof. reflexivity. Qed.
Lemma print_expr_unwrapped : forall o l r ctx, Nat.ltb (binop_prec o) ctx = false ->
  print_expr ctx (EBin o l r)
    = (print_expr (binop_prec o) l ++ binop_text o ++ print_expr (S (binop_prec o)) r)%string.
Proof. intros o l r ctx H. cbn [print_expr]. rewrite H. reflexivity. Qed.
Lemma print_expr_wrapped : forall o l r ctx, Nat.ltb (binop_prec o) ctx = true ->
  print_expr ctx (EBin o l r)
    = ("(" ++ (print_expr (binop_prec o) l ++ binop_text o ++ print_expr (S (binop_prec o)) r) ++ ")")%string.
Proof. intros o l r ctx H. cbn [print_expr]. rewrite H. reflexivity. Qed.

(** SAFETY — [print_prec] emits WELL-BRACKETED Go: scanning the output left to right, the parenthesis
    depth never goes negative and ends at zero (so no dangling/unmatched paren — always syntactically
    valid bracketing), PROVIDED every atom and operator string is itself well-bracketed (Go operands and
    operators are — calls like [f(a, b)] balance their own parens).  This certifies the parenthesization
    DISCIPLINE: the only parens [print_prec] adds are matched pairs around a balanced inner string. *)
Definition pv (c : ascii) : Z :=
  if Ascii.eqb c (ascii_of_nat 40) then 1%Z         (* '(' *)
  else if Ascii.eqb c (ascii_of_nat 41) then (-1)%Z (* ')' *)
  else 0%Z.
Fixpoint depth (d : Z) (s : string) : Z :=
  match s with EmptyString => d | String c s' => depth (d + pv c)%Z s' end.
Fixpoint nneg (d : Z) (s : string) : Prop :=
  match s with EmptyString => True | String c s' => (0 <= d + pv c)%Z /\ nneg (d + pv c)%Z s' end.
Definition balanced (s : string) : Prop := depth 0 s = 0%Z /\ nneg 0 s.

(** [depth]/[nneg] are homomorphic over append, and tolerant of a raised starting floor. *)
Lemma depth_app : forall a b d, depth d (a ++ b) = depth (depth d a) b.
Proof. induction a as [ | c a IH ]; intros b d; [ reflexivity | cbn; apply IH ]. Qed.
Lemma depth_shift : forall s d, depth d s = (d + depth 0 s)%Z.
Proof.
  induction s as [ | c s IH ]; intro d; cbn [depth].
  - lia.
  - rewrite (IH (d + pv c)%Z), (IH (0 + pv c)%Z). lia.
Qed.
Lemma nneg_app : forall a b d, nneg d (a ++ b) <-> nneg d a /\ nneg (depth d a) b.
Proof.
  induction a as [ | c a IH ]; intros b d; cbn.
  - intuition.
  - rewrite IH. intuition.
Qed.
Lemma nneg_raise : forall s d d', (d <= d')%Z -> nneg d s -> nneg d' s.
Proof.
  induction s as [ | c s IH ]; intros d d' Hle Hn; cbn in *; [ exact I | ].
  destruct Hn as [Hpos Hrest]. split.
  - lia.
  - apply (IH (d + pv c)%Z); [ lia | exact Hrest ].
Qed.

(** Every operator render is paren-free, hence balanced — so [wf] need only constrain the ATOMS. *)
Lemma binop_text_balanced : forall o, balanced (binop_text o).
Proof. intro o. destruct o; unfold balanced; cbn; repeat split; (lia || exact I). Qed.

(** A well-bracketed-atoms predicate over the tree: every [EAtom] string is balanced (operators are
    derived and provably balanced, so they need no hypothesis). *)
Fixpoint wf (e : GoExpr) : Prop :=
  match e with
  | EAtom s => balanced s
  | EBin _ l r => wf l /\ wf r
  end.

(** The single ascii of "(" / ")" scans as depth +1 / -1, and the matching non-negativity facts. *)
Lemma depth_lparen : forall d, depth d "(" = (d + 1)%Z.
Proof. intro d. reflexivity. Qed.
Lemma depth_rparen : forall d, depth d ")" = (d - 1)%Z.
Proof. intro d. cbn. lia. Qed.
Lemma nneg_lparen : forall d, (0 <= d)%Z -> nneg d "(".
Proof. intros d Hd. cbn. split; [ lia | exact I ]. Qed.
Lemma nneg_rparen : forall d, (1 <= d)%Z -> nneg d ")".
Proof. intros d Hd. cbn. split; [ lia | exact I ]. Qed.

(** Wrapping a string in a matched paren pair leaves its net depth-change unchanged, and preserves
    non-negativity when the inner string is itself net-zero and balanced ([s] abstract → the inner
    appends stay opaque, so these don't decompose the operand). *)
Lemma depth_wrap : forall d s, depth d ("(" ++ s ++ ")") = depth d s.
Proof.
  intros d s. rewrite !depth_app, depth_lparen, depth_rparen,
                      (depth_shift s (d + 1)%Z), (depth_shift s d). lia.
Qed.
Lemma nneg_wrap : forall d s, (0 <= d)%Z -> depth 0 s = 0%Z -> nneg d s -> nneg d ("(" ++ s ++ ")").
Proof.
  intros d s Hd Hs Hn. rewrite nneg_app. split; [ apply nneg_lparen; lia | ].
  rewrite depth_lparen, nneg_app. split.
  - apply (nneg_raise s d (d + 1)%Z); [ lia | exact Hn ].
  - rewrite (depth_shift s (d + 1)%Z), Hs. apply nneg_rparen. lia.
Qed.

(** Core: from any non-negative starting depth, printing a well-formed expr returns to that exact depth
    and never dips below it.  Generalized over [ctx] and [d] so the recursive sub-calls (at [p], [S p],
    and inside the wrap) are covered by the IH.  Uses the [print_prec_wrapped]/[_unwrapped]
    characterization to expose the printed string without fighting [cbn]. *)
Lemma print_expr_depth_nneg : forall e ctx d, (0 <= d)%Z -> wf e ->
  depth d (print_expr ctx e) = d /\ nneg d (print_expr ctx e).
Proof.
  induction e as [ s | o l IHl r IHr ]; intros ctx d Hd Hwf.
  - (* EAtom s *) cbn [print_expr wf] in *. destruct Hwf as [Hz Hn]. split.
    + rewrite depth_shift, Hz. lia.
    + apply (nneg_raise s 0 d); [ lia | exact Hn ].
  - (* EBin o l r *)
    cbn [wf] in Hwf. destruct Hwf as [Hwl Hwr].
    destruct (binop_text_balanced o) as [Hopz Hopn].
    destruct (IHl (binop_prec o) d Hd Hwl) as [Hld Hln].
    destruct (IHr (S (binop_prec o)) d Hd Hwr) as [Hrd Hrn].
    (* the inner string [l ++ binop_text o ++ r] returns to [d] and never dips below it *)
    assert (Hinner_d : depth d (print_expr (binop_prec o) l ++ binop_text o
                                ++ print_expr (S (binop_prec o)) r) = d).
    { rewrite !depth_app, Hld, (depth_shift (binop_text o) d), Hopz, Z.add_0_r, Hrd. reflexivity. }
    assert (Hinner0 : depth 0 (print_expr (binop_prec o) l ++ binop_text o
                               ++ print_expr (S (binop_prec o)) r) = 0%Z)
      by (rewrite depth_shift in Hinner_d; lia).
    assert (Hinner_n : nneg d (print_expr (binop_prec o) l ++ binop_text o
                               ++ print_expr (S (binop_prec o)) r)).
    { rewrite !nneg_app. split; [ exact Hln | ]. rewrite Hld. split.
      - apply (nneg_raise (binop_text o) 0 d); [ lia | exact Hopn ].
      - rewrite (depth_shift (binop_text o) d), Hopz, Z.add_0_r. exact Hrn. }
    destruct (Nat.ltb (binop_prec o) ctx) eqn:E.
    + (* wrapped: "(" ++ inner ++ ")" *)
      rewrite (print_expr_wrapped o l r ctx E). split.
      * rewrite depth_wrap. exact Hinner_d.
      * apply nneg_wrap; [ lia | exact Hinner0 | exact Hinner_n ].
    + (* not wrapped *)
      rewrite (print_expr_unwrapped o l r ctx E).
      split; [ exact Hinner_d | exact Hinner_n ].
Qed.

Theorem print_expr_balanced : forall e ctx, wf e -> balanced (print_expr ctx e).
Proof.
  intros e ctx Hwf. unfold balanced.
  destruct (print_expr_depth_nneg e ctx 0 (Z.le_refl 0) Hwf) as [Hd Hn].
  split; assumption.
Qed.

(** ============================================================================
    ---- EXPRESSION PRINT-PARSE ROUND-TRIP (the formal Go-operator grammar) ---- the balance theorem
    above proves the output is WELL-BRACKETED but NOT that Go re-parses it to the INTENDED tree.  This
    section models Go's binary-operator grammar (the same 5 precedence levels, left-associative) as a
    parser and proves [parse_expr 0 (print_expr 0 e) = Some (e, "")] — so [print_expr] emits text that
    parses BACK to [e]: the parenthesisation is precedence-CORRECT, not merely balanced.  (That is the
    guarantee the balance theorem could not give — e.g. it would have accepted a looser-operator atom.) *)

(** The [BinOp] whose surface text is a prefix of [s] (no [binop_text] is a prefix of another — the
    trailing space disambiguates — so at most one matches), paired with the remainder after it. *)
Definition op_match (s : string) : option (BinOp * string) :=
  match strip " << " s with Some r => Some (BShl, r)    | None =>
  match strip " >> " s with Some r => Some (BShr, r)    | None =>
  match strip " &^ " s with Some r => Some (BAndNot, r) | None =>
  match strip " && " s with Some r => Some (BLAnd, r)   | None =>
  match strip " || " s with Some r => Some (BLOr, r)    | None =>
  match strip " == " s with Some r => Some (BEq, r)     | None =>
  match strip " != " s with Some r => Some (BNe, r)     | None =>
  match strip " <= " s with Some r => Some (BLe, r)     | None =>
  match strip " >= " s with Some r => Some (BGe, r)     | None =>
  match strip " * " s  with Some r => Some (BMul, r)    | None =>
  match strip " / " s  with Some r => Some (BDiv, r)    | None =>
  match strip " % " s  with Some r => Some (BRem, r)    | None =>
  match strip " & " s  with Some r => Some (BAnd, r)    | None =>
  match strip " + " s  with Some r => Some (BAdd, r)    | None =>
  match strip " - " s  with Some r => Some (BSub, r)    | None =>
  match strip " | " s  with Some r => Some (BOr, r)     | None =>
  match strip " ^ " s  with Some r => Some (BXor, r)    | None =>
  match strip " < " s  with Some r => Some (BLt, r)     | None =>
  match strip " > " s  with Some r => Some (BGt, r)     | None =>
  None end end end end end end end end end end end end end end end end end end end.

(** [op_match] recovers exactly the printed operator and its remainder. *)
Lemma op_match_binop : forall o rest, op_match (binop_text o ++ rest)%string = Some (o, rest).
Proof. intros o rest. destruct o; reflexivity. Qed.

Example op_match_ident : op_match "foo" = None. Proof. reflexivity. Qed.
Example op_match_plus  : op_match (" + " ++ "x") = Some (BAdd, "x"). Proof. reflexivity. Qed.

Definition is_open  (c : ascii) : bool := Ascii.eqb c (ascii_of_nat 40).  (* '(' *)
Definition is_close (c : ascii) : bool := Ascii.eqb c (ascii_of_nat 41).  (* ')' *)
Definition opens (s : string) : bool := match op_match s with Some _ => true | None => false end.

(** Read a primary's ATOM: from paren-depth [d], stop (returning the unconsumed remainder) at a depth-0
    operator or a depth-0 ")" or end-of-string; otherwise consume the char, tracking paren depth.  Since
    an [atomic] operand has no depth-0 operator and is paren-balanced, this consumes EXACTLY the atom. *)
Fixpoint scan_atom (d : nat) (s : string) : string * string :=
  match s with
  | EmptyString => (EmptyString, EmptyString)
  | String c s' =>
      if andb (Nat.eqb d 0) (orb (opens (String c s')) (is_close c))
      then (EmptyString, String c s')
      else let d' := if is_open c then S d else if is_close c then Nat.pred d else d in
           let (a, rest) := scan_atom d' s' in (String c a, rest)
  end.

(** [atomic s] — [s] is a legal primary atom: non-empty, not "("-led (else it is a parenthesised group),
    paren-balanced, and with NO depth-0 operator (so [scan_atom] consumes it whole and the operator that
    follows is unambiguously the parent's).  The plugin's rendered operands satisfy this: any operator
    inside is within the operand's own parens, or written space-free (the typed-IIFE "x+y"). *)
Fixpoint atomic_from (d : nat) (s : string) : bool :=
  match s with
  | EmptyString => Nat.eqb d 0
  | String c s' =>
      if andb (Nat.eqb d 0) (orb (opens (String c s')) (is_close c))
      then false
      else atomic_from (if is_open c then S d else if is_close c then Nat.pred d else d) s'
  end.
Definition atomic (s : string) : bool :=
  match s with EmptyString => false | String c _ => andb (negb (is_open c)) (atomic_from 0 s) end.

(** The precedence-climbing parser (Go's binary-operator grammar): [parse_expr k] reads the maximal
    expression whose operators all bind at precedence [>= k]; [parse_primary] reads an atom or a
    "("-delimited sub-expression; [parse_climb] left-folds operators of precedence [>= k].  Fuel bounds
    the recursion (every call strictly decreases it). *)
Fixpoint parse_expr (fuel k : nat) (s : string) : option (GoExpr * string) :=
  match fuel with
  | O => None
  | S f => match parse_primary f s with Some (l, s1) => parse_climb f k l s1 | None => None end
  end
with parse_primary (fuel : nat) (s : string) : option (GoExpr * string) :=
  match fuel with
  | O => None
  | S f =>
    match s with
    | EmptyString => None
    | String c s' =>
        if is_open c then
          match parse_expr f 0 s' with
          | Some (e, s1) => match s1 with
                            | String c1 s2 => if is_close c1 then Some (e, s2) else None
                            | EmptyString => None end
          | None => None end
        else match scan_atom 0 s with
             | (EmptyString, _) => None
             | (a, rest) => Some (EAtom a, rest) end
    end
  end
with parse_climb (fuel k : nat) (l : GoExpr) (s : string) : option (GoExpr * string) :=
  match fuel with
  | O => None
  | S f =>
    match op_match s with
    | Some (o, s1) =>
        if Nat.leb k (binop_prec o)
        then match parse_expr f (S (binop_prec o)) s1 with
             | Some (r, s2) => parse_climb f k (EBin o l r) s2
             | None => None end
        else Some (l, s)
    | None => Some (l, s)
    end
  end.

(** Concrete round-trips — including the precedence cases the balance theorem could NOT distinguish:
    [a + b * c] keeps [b * c] grouped, [(a + b) * c] keeps the parens. *)
Example rt_atom : parse_expr 9 0 (print_expr 0 (EAtom "a")) = Some (EAtom "a", "").
Proof. reflexivity. Qed.
Example rt_add : parse_expr 9 0 (print_expr 0 (EBin BAdd (EAtom "a") (EAtom "b")))
              = Some (EBin BAdd (EAtom "a") (EAtom "b"), "").
Proof. reflexivity. Qed.
Example rt_prec : parse_expr 9 0 (print_expr 0 (EBin BAdd (EAtom "a") (EBin BMul (EAtom "b") (EAtom "c"))))
               = Some (EBin BAdd (EAtom "a") (EBin BMul (EAtom "b") (EAtom "c")), "").
Proof. reflexivity. Qed.
Example rt_wrap : parse_expr 9 0 (print_expr 0 (EBin BMul (EBin BAdd (EAtom "a") (EAtom "b")) (EAtom "c")))
               = Some (EBin BMul (EBin BAdd (EAtom "a") (EAtom "b")) (EAtom "c"), "").
Proof. reflexivity. Qed.
Example rt_leftassoc : parse_expr 9 0 (print_expr 0 (EBin BSub (EBin BSub (EAtom "a") (EAtom "b")) (EAtom "c")))
                     = Some (EBin BSub (EBin BSub (EAtom "a") (EAtom "b")) (EAtom "c"), "").
Proof. reflexivity. Qed.

(** ============================================================================
    ---- SEPARATED LISTS ---- the OTHER pervasive structural primitive: a comma-joined sequence
    (function arguments, composite-literal elements, type-argument lists, multi-return values, struct
    fields).  [go.ml] rendered these with Coq's [prlist_with_sep]; [print_sep] is the verified
    replacement — it joins the already-rendered pieces with [sep], NO leading or trailing separator
    (the off-by-one a hand-rolled join gets wrong).  The empty list prints empty, a singleton prints
    itself, and only INTERIOR gaps get a separator. *)
Fixpoint print_sep (sep : string) (xs : list string) : string :=
  match xs with
  | []        => ""
  | x :: xs'  => match xs' with
                 | []     => x
                 | _ :: _ => (x ++ sep ++ print_sep sep xs')%string
                 end
  end.

Example print_sep_empty  : print_sep ", " [] = "".              Proof. reflexivity. Qed.
Example print_sep_single : print_sep ", " ["a"] = "a".          Proof. reflexivity. Qed.
Example print_sep_three  : print_sep ", " ["a"; "b"; "c"] = "a, b, c". Proof. reflexivity. Qed.

(** Concatenation of two balanced strings is balanced (depth/nneg are homomorphic over append). *)
Lemma balanced_app : forall a b, balanced a -> balanced b -> balanced (a ++ b).
Proof.
  intros a b [Ha Hna] [Hb Hnb]. unfold balanced. split.
  - rewrite depth_app, Ha. exact Hb.
  - rewrite nneg_app, Ha. split; assumption.
Qed.

(** SAFETY — a separated list of well-bracketed pieces (and a well-bracketed separator) is itself
    well-bracketed: [print_sep] never introduces an unmatched paren. *)
Theorem print_sep_balanced : forall xs sep,
  balanced sep -> (forall x, In x xs -> balanced x) -> balanced (print_sep sep xs).
Proof.
  induction xs as [ | x xs IH ]; intros sep Hsep Hall.
  - (* [] *) unfold balanced; cbn [print_sep depth nneg]. split; [ reflexivity | exact I ].
  - (* x :: xs *) destruct xs as [ | y xs' ].
    + (* singleton *) cbn [print_sep]. apply Hall. left. reflexivity.
    + (* x :: y :: xs' *) cbn [print_sep].
      apply balanced_app; [ apply Hall; left; reflexivity | ].
      apply balanced_app; [ exact Hsep | ].
      apply IH; [ exact Hsep | ]. intros z Hz. apply Hall. right. exact Hz.
Qed.

(** GATE — goprint.v is part of the trust base: the EXTRACTED printer is governed by these theorems, so
    they MUST be axiom-free.  The build (Dockerfile prover stage) compiles goprint.v standalone and FAILS
    if any of these rests on an unproved assumption (a non-empty Axioms section in its Print Assumptions).
    Keep this list in sync with the headline results below. *)
Print Assumptions parse_print_ty.
Print Assumptions print_ty_inj.
Print Assumptions esc_string_roundtrip.
Print Assumptions print_parse_Z.
Print Assumptions print_parse_hex.
Print Assumptions print_parse_float_hex.
Print Assumptions print_expr_balanced.
Print Assumptions print_sep_balanced.

(** Extract the Rocq printers to the OCaml the plugin calls. *)
Require Import Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "printer.ml" print_ty print_Z print_string_lit print_hex print_expr print_sep print_float_hex.
