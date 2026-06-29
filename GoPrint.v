(** ============================================================================
    THE VERIFIED PRINTER — slice 1 (the gap #10 / review #12 path).

    The trusted/unverified part of Fido is the hand-written OCaml in [plugin/go.ml]: no theorem relates
    the Go string it emits to the source term.  The agreed fix (no more raw OCaml): the PRINTER moves
    INTO Rocq — a Go AST + a pretty-printer defined here as Rocq functions — is EXTRACTED to OCaml (so
    the plugin runs the SAME function Rocq reasons about, not a hand-written re-implementation), and
    CORRECTNESS theorems are layered atop it.  This file is the foundation; later slices grow the AST to
    cover the emitted fragment, rewire [go.ml] to call the extracted printer, and delete the raw OCaml.

    ⚠️ HONEST SCOPE OF "VERIFIED" (review #7 item 3) — "verified printer" here means: the printer is
    verified AGAINST THE Rocq PARSER in this file (a printer/parser round-trip + injectivity for THIS
    Rocq grammar), NOT against Go's own parser.  There is NO theorem yet that Go's compiler reads the
    emitted text as the same AST — that Go-subset RECOGNITION theorem (emitted grammar ⊆ Go grammar) is
    the remaining gap (#10).  So [parse_print_roundtrip] / [print_ty_inj] are ROCQ-GRAMMAR self-consistency
    results, and must not be read as "Go printer correctness."  (The plugin → emitted-bytes path also has
    a trusted [gofmt] post-step — see the Makefile — so even the byte-exact final text is not yet in-proof.)

    Slice 1: the Go TYPE sub-language.  [print_ty] renders a [GoTy] to Go source; [print_ty_inj] proves
    it is INJECTIVE over ALL of [GoTy] unconditionally (nominal names carry a validated [Ident], so an
    invalid name is unrepresentable) — distinct Go types render to distinct strings, so the printer can
    NEVER conflate two types (the property every [v.(T)] cast / tag rendering depends on).
    [Extraction "printer.ml"] emits the OCaml the plugin will call. *)

From Stdlib Require Import String List Ascii ZArith Lia Bool Eqdep_dec.
Import ListNotations.
Open Scope string_scope.

(* SYNTAX lives in GoAst.v; this file (the old GoPrint, now flattened) is GoPrint: printers + lexer + parser + round-trips. *)
From Fido Require Import GoAst.


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
  | GTNamed n => proj1_sig n
  end.



(** [scan_id] consumes the maximal run of identifier characters (so it stops at "]", a space, or
    end-of-string — exactly the boundaries [print_ty] places after a type), and [classify] maps a complete
    token to its scalar type (or [None] for a nominal name).  Token-FIRST parsing (scan the run, then
    classify) gives maximal munch for free: "int8x" scans whole and classifies as nominal, never as
    [int8] + "x".  ([is_idc]/[is_idstart]/[all_idc]/[is_type_keyword]/[valid_ident]/[Ident] are defined
    above [GoTy], since [GTNamed] carries an [Ident].) *)
Fixpoint scan_id (s : string) : string * string :=
  match s with
  | EmptyString => (EmptyString, EmptyString)
  | String c s' => if is_idc c then let (tok, rest) := scan_id s' in (String c tok, rest)
                   else (EmptyString, s)
  end.
Definition classify (s : string) : option GoTy :=
       if String.eqb s "int64"   then Some GTInt64
  else if String.eqb s "int32"   then Some GTI32
  else if String.eqb s "int16"   then Some GTI16
  else if String.eqb s "int8"    then Some GTI8
  else if String.eqb s "int"     then Some GTInt
  else if String.eqb s "uint64"  then Some GTU64
  else if String.eqb s "uint32"  then Some GTU32
  else if String.eqb s "uint16"  then Some GTU16
  else if String.eqb s "uint8"   then Some GTU8
  else if String.eqb s "uint"    then Some GTUint
  else if String.eqb s "bool"    then Some GTBool
  else if String.eqb s "string"  then Some GTString
  else if String.eqb s "float64" then Some GTFloat64
  else if String.eqb s "float32" then Some GTFloat32
  else None.


(** Append is associative on strings (used by a [gtokens_ty] length seam below). *)
Lemma sapp_assoc : forall a b c, ((a ++ b) ++ c)%string = (a ++ (b ++ c))%string.
Proof. induction a as [ | x a IH ]; intros b c; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.


(** A non-keyword name classifies as nominal and is neither the [chan] nor [map] keyword.  Bridges the
    [GoTy]-independent [is_type_keyword] (which gates [Ident]) to [classify] (which assigns the [GoTy]):
    if [s] is none of the 16 keyword strings, then [classify s = None] and [s] is not [chan]/[map]. *)
Lemma kw_false_classify : forall s, is_type_keyword s = false ->
  classify s = None /\ String.eqb s "chan" = false /\ String.eqb s "map" = false.
Proof.
  intros s H. unfold is_type_keyword in H. cbn [existsb] in H.
  apply orb_false_iff in H; destruct H as [ Hi64 H ].
  apply orb_false_iff in H; destruct H as [ Hi32 H ].
  apply orb_false_iff in H; destruct H as [ Hi16 H ].
  apply orb_false_iff in H; destruct H as [ Hi8  H ].
  apply orb_false_iff in H; destruct H as [ Hint H ].
  apply orb_false_iff in H; destruct H as [ Hu64 H ].
  apply orb_false_iff in H; destruct H as [ Hu32 H ].
  apply orb_false_iff in H; destruct H as [ Hu16 H ].
  apply orb_false_iff in H; destruct H as [ Hu8  H ].
  apply orb_false_iff in H; destruct H as [ Hu   H ].
  apply orb_false_iff in H; destruct H as [ Hbool   H ].
  apply orb_false_iff in H; destruct H as [ Hstr    H ].
  apply orb_false_iff in H; destruct H as [ Hf64    H ].
  apply orb_false_iff in H; destruct H as [ Hf32    H ].
  apply orb_false_iff in H; destruct H as [ Hchan   H ].
  apply orb_false_iff in H; destruct H as [ Hmap    _ ].
  unfold classify.
  rewrite Hi64, Hi32, Hi16, Hi8, Hint, Hu64, Hu32, Hu16, Hu8, Hu, Hbool, Hstr, Hf64, Hf32.
  split; [ reflexivity | split; [ exact Hchan | exact Hmap ] ].
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
    analog of [parse_print_ty] / [esc_string_roundtrip_opt] for integer literals — the most-emitted leaf. *)
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

(** ---- STRING-LITERAL FAITHFULNESS (round-trip) ---- the escaping is LOSSLESS: a VALIDATING decoder
    [unescape_opt] recovers the exact original bytes from [esc_string] (as [Some s]), so [print_string_lit]
    denotes precisely its argument — no byte dropped, merged, or corrupted by an escape.  This is the
    data-faithfulness property for string literals (the analog of [parse_print_ty] for the type sub-language).
    [unescape_opt] is also FAIL-CLOSED: it returns [None] on any malformed escape, so the lexer rejects
    ill-formed string syntax instead of normalizing it (see the [lex_bad_*] negative examples below). *)
Lemma nat_of_ascii_lt_256 : forall c, nat_of_ascii c < 256.
Proof. intro c. destruct c. repeat match goal with b : bool |- _ => destruct b end; cbn; lia. Qed.
Lemma nat_of_ch : forall n, n < 256 -> nat_of_ascii (ch n) = n.
Proof. intros n H. unfold ch. apply Ascii.nat_ascii_embedding. exact H. Qed.
Lemma ch_nat : forall c, ch (nat_of_ascii c) = c.
Proof. intro c. unfold ch. apply Ascii.ascii_nat_embedding. Qed.

(** Inverse of [hexdig] on a single hex nibble.  Decodes the LOWER-CASE spellings only — [0-9] (48-57) and
    [a-f] (97-102) — exactly the bytes [is_hex] accepts; [hexdig] emits only this lower-case form (and
    [esc_string] only emits via [hexdig]), so this is its faithful inverse over the printer image. *)
Definition unhex (c : ascii) : nat :=
  let v := nat_of_ascii c in
  if Nat.leb v 57 then v - 48          (* '0'-'9' *)
  else v - 87.                         (* 'a'-'f' *)
Lemma unhex_hexdig : forall k, k < 16 -> unhex (hexdig k) = k.
Proof.
  intros k H. unfold unhex, hexdig. destruct (Nat.ltb k 10) eqn:E.
  - apply Nat.ltb_lt in E. rewrite Ascii.nat_ascii_embedding by lia.
    destruct (Nat.leb (48 + k) 57) eqn:E2; [ lia | apply Nat.leb_gt in E2; lia ].
  - apply Nat.ltb_ge in E. rewrite Ascii.nat_ascii_embedding by lia.
    destruct (Nat.leb (87 + k) 57) eqn:E2; [ apply Nat.leb_le in E2; lia | lia ].
Qed.

(** A hex digit: [0-9] / [a-f] — LOWER-CASE only, since [esc_string] emits only lower-case [\x] escapes.
    Used by the VALIDATING decoder [unescape_opt] to REJECT a [\x] escape whose two characters are not both
    hex (a non-hex — or upper-case — [\x] is not part of the printer image and must fail to lex, not decode to
    a byte the printer would never have emitted).  [unhex] above inverts every byte this accepts. *)
Definition is_hex (c : ascii) : bool :=
  let v := nat_of_ascii c in
  orb (andb (Nat.leb 48 v) (Nat.leb v 57))            (* '0'-'9' *)
      (andb (Nat.leb 97 v) (Nat.leb v 102)).          (* 'a'-'f' *)
Lemma is_hex_hexdig : forall k, k < 16 -> is_hex (hexdig k) = true.
Proof.
  intros k H. unfold is_hex, hexdig. destruct (Nat.ltb k 10) eqn:E.
  - apply Nat.ltb_lt in E. rewrite Ascii.nat_ascii_embedding by lia.
    apply Bool.orb_true_iff; left. apply Bool.andb_true_iff.
    split; apply Nat.leb_le; lia.
  - apply Nat.ltb_ge in E. rewrite Ascii.nat_ascii_embedding by lia.
    apply Bool.orb_true_iff; right.
    apply Bool.andb_true_iff. split; apply Nat.leb_le; lia.
Qed.

(** The bytes whose CANONICAL [esc_byte] form is the [\xHH] hex fallback: NOT a named-escape byte
    (34 dquote / 92 backslash / 10 nl / 9 tab / 13 cr) and NOT printable [32,126].  This is EXACTLY the set
    [esc_byte]'s final branch covers (bytes [< 32] except 9/10/13, and [>= 127]); the [\x] arm of the decoder
    [unescape_opt] requires it so a [\xHH] is accepted ONLY when [esc_byte] would actually have EMITTED that
    [\xHH] — e.g. a hex escape of printable 'A' (65), or of the named dquote (34), is REJECTED, since [esc_string]
    prints those raw / as a named escape, never as hex (the Codex 2026-06-29 superset fix). *)
Definition hex_escaped_byte (b : nat) : bool :=
  negb (orb (orb (Nat.eqb b 34) (orb (Nat.eqb b 92) (orb (Nat.eqb b 10) (orb (Nat.eqb b 9) (Nat.eqb b 13)))))
            (andb (Nat.leb 32 b) (Nat.ltb b 127))).
(** Introduction form, proved here (where [hex_escaped_byte] is still transparent) so the round-trip proof
    [unescape_opt_esc_byte] can discharge the [\xHH]-fallback guard while keeping [hex_escaped_byte] OPAQUE for
    [cbn] (it must stay folded across that proof). *)
Lemma hex_escaped_byte_true_intro : forall b,
  Nat.eqb b 34 = false -> Nat.eqb b 92 = false -> Nat.eqb b 10 = false ->
  Nat.eqb b 9 = false -> Nat.eqb b 13 = false ->
  andb (Nat.leb 32 b) (Nat.ltb b 127) = false ->
  hex_escaped_byte b = true.
Proof.
  intros b H34 H92 H10 H9 H13 Hr. unfold hex_escaped_byte.
  rewrite H34, H92, H10, H9, H13, Hr. reflexivity.
Qed.

(** The VALIDATING decoder: reverse [esc_byte], FAIL-CLOSED.  Returns [option string] and accepts EXACTLY the
    PRINTER IMAGE — the byte set [esc_string] can emit — and nothing else (accepted == emitted, now PROVEN by
    [unescape_opt_image] below: every accepted [body] is the canonical [esc_string] of its decode); it is [None]
    on every other spelling, so the lexer (which threads this [option]) REJECTS non-printer-image string syntax
    at tokenization instead of normalizing it into a value.  The accepted alphabet is precisely: the five named
    escapes (the escaped dquote, the escaped backslash, [\n] [\t] [\r]), a [\xHH] escape whose two digits are
    both [is_hex] (LOWER-CASE hex) AND whose decoded byte [hex_escaped_byte]s (so [esc_byte] really takes its
    hex fallback on it), and a RAW body byte in [32,126] minus the dquote (34) and the backslash (92).
    Everything else is [None]: a TRUNCATED escape (a backslash at end of body), an UNKNOWN escape (any other byte
    after a backslash), a [\x] with fewer than two following chars or whose two chars are not both [is_hex] (so an
    UPPER-CASE [\xAF] is rejected — [esc_string] emits only lower-case), a [\xHH] whose byte is a named-escape /
    printable one (a hex escape of 'A' or of the dquote — NOT [esc_byte]'s image), and a RAW byte outside [32,126]
    minus {34,92} (a raw tab/CR/control/high byte/newline — each of which [esc_byte] would have ESCAPED, so a raw
    one is not in the image).  Structural on sub-terms of [s] (so no fuel needed); ONE decode authority (the old
    total [unescape] is gone). *)
Fixpoint unescape_opt (s : string) : option string :=
  match s with
  | EmptyString => Some EmptyString
  | String c1 rest =>
      if Nat.eqb (nat_of_ascii c1) 92 then
        match rest with
        | EmptyString => None                                  (* truncated: backslash at end of body *)
        | String c2 rest2 =>
            let d := nat_of_ascii c2 in
            if Nat.eqb d 34 then option_map (String (ch 34)) (unescape_opt rest2)
            else if Nat.eqb d 92 then option_map (String (ch 92)) (unescape_opt rest2)
            else if Nat.eqb d 110 then option_map (String (ch 10)) (unescape_opt rest2)
            else if Nat.eqb d 116 then option_map (String (ch 9)) (unescape_opt rest2)
            else if Nat.eqb d 114 then option_map (String (ch 13)) (unescape_opt rest2)
            else if Nat.eqb d 120 then
              match rest2 with
              | String h1 (String h2 rest3) =>
                  if andb (andb (is_hex h1) (is_hex h2))
                          (hex_escaped_byte (16 * unhex h1 + unhex h2))
                  then option_map (String (ch (16 * unhex h1 + unhex h2))) (unescape_opt rest3)
                  else None                                    (* \x with a non-hex digit, or a byte esc_byte would NOT hex-escape *)
              | _ => None                                      (* truncated \x escape (< 2 chars) *)
              end
            else None                                          (* unknown escape *)
        end
      else if andb (andb (Nat.leb 32 (nat_of_ascii c1)) (Nat.ltb (nat_of_ascii c1) 127))
                   (negb (Nat.eqb (nat_of_ascii c1) 34))
           then option_map (String c1) (unescape_opt rest)      (* raw body byte: printable [32,126], not a dquote (backslash handled above) *)
           else None                                            (* outside the printer image: tab/CR/control/high/newline/raw dquote *)
  end.

(* Keep [ch]/[nat_of_ascii]/[unhex]/[hexdig]/[is_hex]/[option_map] opaque so [cbn] reduces only the [Nat.eqb]
   dispatch and the matches, leaving [ch <v>] / [nat_of_ascii (ch _)] / [unhex (hexdig _)] / [is_hex (hexdig _)]
   and the [option_map] wrappers symbolic for the rewrites. *)
Local Opaque ch nat_of_ascii unhex hexdig is_hex hex_escaped_byte option_map Nat.div Nat.modulo Nat.mul.
Lemma unescape_opt_esc_byte : forall c X,
  unescape_opt (esc_byte (nat_of_ascii c) X) = option_map (String c) (unescape_opt X).
Proof.
  intros c X. assert (Hc : nat_of_ascii c < 256) by apply nat_of_ascii_lt_256.
  unfold esc_byte.
  destruct (Nat.eqb (nat_of_ascii c) 34) eqn:E34.
  { apply Nat.eqb_eq in E34.
    cbn [unescape_opt]. rewrite (nat_of_ch 92) by lia. cbn. rewrite (nat_of_ch 34) by lia. cbn.
    rewrite <- E34, ch_nat. reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 92) eqn:E92.
  { apply Nat.eqb_eq in E92.
    cbn [unescape_opt]. rewrite (nat_of_ch 92) by lia. cbn.
    rewrite <- E92, ch_nat. reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 10) eqn:E10.
  { apply Nat.eqb_eq in E10.
    cbn [unescape_opt]. rewrite (nat_of_ch 92) by lia. cbn. rewrite (nat_of_ch 110) by lia. cbn.
    rewrite <- E10, ch_nat. reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 9) eqn:E9.
  { apply Nat.eqb_eq in E9.
    cbn [unescape_opt]. rewrite (nat_of_ch 92) by lia. cbn. rewrite (nat_of_ch 116) by lia. cbn.
    rewrite <- E9, ch_nat. reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 13) eqn:E13.
  { apply Nat.eqb_eq in E13.
    cbn [unescape_opt]. rewrite (nat_of_ch 92) by lia. cbn. rewrite (nat_of_ch 114) by lia. cbn.
    rewrite <- E13, ch_nat. reflexivity. }
  destruct (andb (Nat.leb 32 (nat_of_ascii c)) (Nat.ltb (nat_of_ascii c) 127)) eqn:Eprint.
  { (* printable byte: emitted as-is, decoded as-is — not a backslash (E92), printable (Eprint), not a dquote (E34) *)
    cbn [unescape_opt]. rewrite (nat_of_ch (nat_of_ascii c)) by exact Hc.
    rewrite E92, Eprint, E34, ch_nat. cbn [andb negb]. reflexivity. }
  { (* hex escape: \xHL with H = b/16, L = b mod 16; both nibbles are [is_hex], 16*H + L = b, and
       [hex_escaped_byte b = true] — b is neither a named-escape byte nor printable (from the false
       hypotheses E34/E92/E10/E9/E13/Eprint above), so [esc_byte] really took its [\xHH] fallback. *)
    assert (Hhe : hex_escaped_byte (nat_of_ascii c) = true)
      by (apply hex_escaped_byte_true_intro; assumption).
    cbn [unescape_opt]. rewrite (nat_of_ch 92) by lia. cbn. rewrite (nat_of_ch 120) by lia. cbn.
    rewrite (is_hex_hexdig (Nat.div (nat_of_ascii c) 16)) by (apply Nat.Div0.div_lt_upper_bound; lia).
    rewrite (is_hex_hexdig (Nat.modulo (nat_of_ascii c) 16)) by (apply Nat.mod_upper_bound; lia).
    rewrite (unhex_hexdig (Nat.div (nat_of_ascii c) 16)) by (apply Nat.Div0.div_lt_upper_bound; lia).
    rewrite (unhex_hexdig (Nat.modulo (nat_of_ascii c) 16)) by (apply Nat.mod_upper_bound; lia).
    replace (16 * Nat.div (nat_of_ascii c) 16 + Nat.modulo (nat_of_ascii c) 16) with (nat_of_ascii c)
      by (pose proof (Nat.div_mod_eq (nat_of_ascii c) 16); lia).
    rewrite Hhe. cbn [andb]. rewrite ch_nat. reflexivity. }
Qed.
Local Transparent ch nat_of_ascii unhex hexdig is_hex hex_escaped_byte option_map Nat.div Nat.modulo Nat.mul.

(** ★ THE STRING-LITERAL ROUND-TRIP — the (now VALIDATING) decoder recovers EXACTLY what [esc_string] emits, so
    [print_string_lit] denotes precisely its argument and the lexer's [TStr] is faithful.  Crucially the option
    decoder ACCEPTS every byte [esc_string] can produce (the proof of [unescape_opt_esc_byte] discharges the
    [is_hex]/printable-range guards on those bytes), so tightening the decoder to accept EXACTLY the printer image
    (accepted == emitted) cost the round-trip nothing. *)
Theorem esc_string_roundtrip_opt : forall s, unescape_opt (esc_string s) = Some s.
Proof.
  induction s as [ | c rest IH ]; [ reflexivity | ].
  cbn [esc_string]. rewrite unescape_opt_esc_byte, IH. reflexivity.
Qed.

(** ★ THE STRING-LITERAL REVERSE-IMAGE THEOREM (the EXACTNESS deliverable) — every body the decoder ACCEPTS is
    EXACTLY the canonical [esc_string] escaping of its decode, so the accepted language is precisely the printer
    IMAGE: accepted == emitted, PROVEN (not asserted).  With [esc_string_roundtrip_opt] (emitted ⊆ accepted)
    this is a two-way exactness: [unescape_opt body = Some s  ↔  body = esc_string s].  It is the property that
    kills the Codex 2026-06-29 superset hole — without the [hex_escaped_byte] guard a hex escape of a printable
    or named byte (a hex 'A' decoding to the one-byte string A, which [esc_string] prints RAW) would be accepted
    though never emitted.  Helper lemmas first, then the theorem by strong induction on the body length. *)
Lemma option_map_Some_inv : forall (A B : Type) (f : A -> B) (x : option A) (y : B),
  option_map f x = Some y -> exists z, x = Some z /\ y = f z.
Proof.
  intros A B f x y H. destruct x as [z|]; cbn in H.
  - injection H as <-. exists z. split; reflexivity.
  - discriminate H.
Qed.

Lemma unhex_lt_16 : forall c, is_hex c = true -> unhex c < 16.
Proof.
  intros c H. unfold is_hex in H. apply Bool.orb_true_iff in H. unfold unhex.
  destruct H as [H|H]; apply Bool.andb_true_iff in H; destruct H as [Hl Hr];
    apply Nat.leb_le in Hl, Hr.
  - destruct (Nat.leb (nat_of_ascii c) 57) eqn:E; [ lia | apply Nat.leb_gt in E; lia ].
  - destruct (Nat.leb (nat_of_ascii c) 57) eqn:E; [ apply Nat.leb_le in E; lia | lia ].
Qed.

(** The forward inverse of [hexdig] over the LOWER-CASE hex alphabet [is_hex] accepts (the reverse of
    [unhex_hexdig]): an accepted [\xHH] re-emits its two digits unchanged. *)
Lemma hexdig_unhex : forall c, is_hex c = true -> hexdig (unhex c) = c.
Proof.
  intros c H. unfold is_hex in H. apply Bool.orb_true_iff in H.
  assert (Hinner : (if Nat.ltb (unhex c) 10 then 48 + unhex c else 87 + unhex c) = nat_of_ascii c).
  { unfold unhex; cbv zeta.
    destruct H as [H|H]; apply Bool.andb_true_iff in H; destruct H as [Hl Hr];
      apply Nat.leb_le in Hl, Hr.
    - destruct (Nat.leb (nat_of_ascii c) 57) eqn:E.
      + destruct (Nat.ltb (nat_of_ascii c - 48) 10) eqn:E2; [ lia | apply Nat.ltb_ge in E2; lia ].
      + apply Nat.leb_gt in E; lia.
    - destruct (Nat.leb (nat_of_ascii c) 57) eqn:E.
      + apply Nat.leb_le in E; lia.
      + destruct (Nat.ltb (nat_of_ascii c - 87) 10) eqn:E2; [ apply Nat.ltb_lt in E2; lia | lia ]. }
  unfold hexdig. rewrite Hinner. apply Ascii.ascii_nat_embedding.
Qed.

(** When [hex_escaped_byte b] holds, [esc_byte] takes its [\xHH] hex fallback (all five named-escape tests and
    the printable test fail), so the byte's image is exactly the four-char hex escape. *)
Lemma esc_byte_hex : forall b acc, hex_escaped_byte b = true ->
  esc_byte b acc =
    String (ch 92) (String (ch 120)
      (String (hexdig (Nat.div b 16)) (String (hexdig (Nat.modulo b 16)) acc))).
Proof.
  intros b acc H. unfold hex_escaped_byte in H.
  apply Bool.negb_true_iff in H. apply Bool.orb_false_iff in H. destruct H as [Ho Eand].
  apply Bool.orb_false_iff in Ho. destruct Ho as [Q34 Ho].
  apply Bool.orb_false_iff in Ho. destruct Ho as [Q92 Ho].
  apply Bool.orb_false_iff in Ho. destruct Ho as [Q10 Ho].
  apply Bool.orb_false_iff in Ho. destruct Ho as [Q9 Q13].
  unfold esc_byte. rewrite Q34, Q92, Q10, Q9, Q13, Eand. reflexivity.
Qed.

Theorem unescape_opt_image : forall body s, unescape_opt body = Some s -> body = esc_string s.
Proof.
  (* strong induction on the body length, so the IH reaches [rest2] / [rest3] (the tail of a 2-/4-byte
     escape), not just the immediate tail [rest]. *)
  assert (HH : forall n body s, String.length body <= n -> unescape_opt body = Some s -> body = esc_string s).
  { induction n as [ | n IH ]; intros body s Hlen H.
    - destruct body as [ | c1 rest ].
      + cbn [unescape_opt] in H. injection H as <-. reflexivity.
      + cbn in Hlen. lia.
    - destruct body as [ | c1 rest ].
      + cbn [unescape_opt] in H. injection H as <-. reflexivity.
      + cbn [unescape_opt] in H.
        destruct (Nat.eqb (nat_of_ascii c1) 92) eqn:Eb; cbn [unescape_opt] in H.
        * (* leading backslash: a named escape, a \xHH hex escape, or rejected *)
          apply Nat.eqb_eq in Eb.
          destruct rest as [ | c2 rest2 ]; cbn [unescape_opt] in H; [ discriminate H | ].
          destruct (Nat.eqb (nat_of_ascii c2) 34) eqn:E34; cbn [unescape_opt] in H.
          { apply Nat.eqb_eq in E34.
            apply option_map_Some_inv in H; destruct H as [z [Hz Hs]].
            pose proof (IH rest2 z ltac:(cbn in Hlen; lia) Hz) as Himg.
            subst s; rewrite Himg.
            cbn [esc_string]; rewrite (nat_of_ch 34) by lia.
            unfold esc_byte; cbn [Nat.eqb].
            rewrite <- (ch_nat c1), Eb. rewrite <- (ch_nat c2), E34. reflexivity. }
          destruct (Nat.eqb (nat_of_ascii c2) 92) eqn:E92; cbn [unescape_opt] in H.
          { apply Nat.eqb_eq in E92.
            apply option_map_Some_inv in H; destruct H as [z [Hz Hs]].
            pose proof (IH rest2 z ltac:(cbn in Hlen; lia) Hz) as Himg.
            subst s; rewrite Himg.
            cbn [esc_string]; rewrite (nat_of_ch 92) by lia.
            unfold esc_byte; cbn [Nat.eqb].
            rewrite <- (ch_nat c1), Eb. rewrite <- (ch_nat c2), E92. reflexivity. }
          destruct (Nat.eqb (nat_of_ascii c2) 110) eqn:E110; cbn [unescape_opt] in H.
          { apply Nat.eqb_eq in E110.
            apply option_map_Some_inv in H; destruct H as [z [Hz Hs]].
            pose proof (IH rest2 z ltac:(cbn in Hlen; lia) Hz) as Himg.
            subst s; rewrite Himg.
            cbn [esc_string]; rewrite (nat_of_ch 10) by lia.
            unfold esc_byte; cbn [Nat.eqb].
            rewrite <- (ch_nat c1), Eb. rewrite <- (ch_nat c2), E110. reflexivity. }
          destruct (Nat.eqb (nat_of_ascii c2) 116) eqn:E116; cbn [unescape_opt] in H.
          { apply Nat.eqb_eq in E116.
            apply option_map_Some_inv in H; destruct H as [z [Hz Hs]].
            pose proof (IH rest2 z ltac:(cbn in Hlen; lia) Hz) as Himg.
            subst s; rewrite Himg.
            cbn [esc_string]; rewrite (nat_of_ch 9) by lia.
            unfold esc_byte; cbn [Nat.eqb].
            rewrite <- (ch_nat c1), Eb. rewrite <- (ch_nat c2), E116. reflexivity. }
          destruct (Nat.eqb (nat_of_ascii c2) 114) eqn:E114; cbn [unescape_opt] in H.
          { apply Nat.eqb_eq in E114.
            apply option_map_Some_inv in H; destruct H as [z [Hz Hs]].
            pose proof (IH rest2 z ltac:(cbn in Hlen; lia) Hz) as Himg.
            subst s; rewrite Himg.
            cbn [esc_string]; rewrite (nat_of_ch 13) by lia.
            unfold esc_byte; cbn [Nat.eqb].
            rewrite <- (ch_nat c1), Eb. rewrite <- (ch_nat c2), E114. reflexivity. }
          destruct (Nat.eqb (nat_of_ascii c2) 120) eqn:E120; cbn [unescape_opt] in H; [ | discriminate H ].
          (* \xHH hex escape: both nibbles [is_hex] and the decoded byte [hex_escaped_byte]s *)
          apply Nat.eqb_eq in E120.
          destruct rest2 as [ | h1 [ | h2 rest3 ] ]; cbn [unescape_opt] in H; try discriminate H.
          destruct (andb (andb (is_hex h1) (is_hex h2)) (hex_escaped_byte (16 * unhex h1 + unhex h2))) eqn:Eg;
            cbn [unescape_opt] in H; [ | discriminate H ].
          apply Bool.andb_true_iff in Eg; destruct Eg as [Ehh Ehe].
          apply Bool.andb_true_iff in Ehh; destruct Ehh as [Eh1 Eh2].
          apply option_map_Some_inv in H; destruct H as [z [Hz Hs]].
          pose proof (IH rest3 z ltac:(cbn in Hlen; lia) Hz) as Himg.
          subst s; rewrite Himg.
          assert (Hb1 : unhex h1 < 16) by (apply unhex_lt_16; exact Eh1).
          assert (Hb2 : unhex h2 < 16) by (apply unhex_lt_16; exact Eh2).
          assert (Hb : 16 * unhex h1 + unhex h2 < 256) by lia.
          cbn [esc_string]. rewrite (nat_of_ch (16 * unhex h1 + unhex h2) Hb).
          rewrite (esc_byte_hex (16 * unhex h1 + unhex h2) (esc_string z) Ehe).
          assert (Hdiv : Nat.div (16 * unhex h1 + unhex h2) 16 = unhex h1).
          { replace (16 * unhex h1 + unhex h2) with (unhex h1 * 16 + unhex h2) by lia.
            rewrite Nat.div_add_l by lia. rewrite (Nat.div_small (unhex h2) 16 Hb2). lia. }
          assert (Hmod : Nat.modulo (16 * unhex h1 + unhex h2) 16 = unhex h2).
          { pose proof (Nat.div_mod_eq (16 * unhex h1 + unhex h2) 16) as Hdm.
            rewrite Hdiv in Hdm. lia. }
          rewrite Hdiv, Hmod, (hexdig_unhex h1 Eh1), (hexdig_unhex h2 Eh2).
          rewrite <- (ch_nat c1), Eb. rewrite <- (ch_nat c2), E120. reflexivity.
        * (* no leading backslash: a raw printable body byte, or rejected *)
          destruct (andb (andb (Nat.leb 32 (nat_of_ascii c1)) (Nat.ltb (nat_of_ascii c1) 127))
                         (negb (Nat.eqb (nat_of_ascii c1) 34))) eqn:Eraw;
            cbn [unescape_opt] in H; [ | discriminate H ].
          apply Bool.andb_true_iff in Eraw; destruct Eraw as [Erange Endq].
          apply Bool.andb_true_iff in Erange; destruct Erange as [El Eh].
          apply Nat.leb_le in El. apply Nat.ltb_lt in Eh. apply Bool.negb_true_iff in Endq.
          apply option_map_Some_inv in H; destruct H as [z [Hz Hs]].
          pose proof (IH rest z ltac:(cbn in Hlen; lia) Hz) as Himg.
          subst s; rewrite Himg.
          cbn [esc_string]. unfold esc_byte.
          assert (Q9  : Nat.eqb (nat_of_ascii c1) 9  = false) by (apply Nat.eqb_neq; lia).
          assert (Q10 : Nat.eqb (nat_of_ascii c1) 10 = false) by (apply Nat.eqb_neq; lia).
          assert (Q13 : Nat.eqb (nat_of_ascii c1) 13 = false) by (apply Nat.eqb_neq; lia).
          assert (Eprint : andb (Nat.leb 32 (nat_of_ascii c1)) (Nat.ltb (nat_of_ascii c1) 127) = true)
            by (apply Bool.andb_true_iff; split; [ apply Nat.leb_le | apply Nat.ltb_lt ]; lia).
          rewrite Endq, Eb, Q10, Q9, Q13, Eprint, (ch_nat c1). reflexivity. }
  intros body s. apply (HH (String.length body) body s). lia.
Qed.

(** ---- STRING-LITERAL LEXING ---- [scan_quote] locates the CLOSING dquote of a Go interpreted-string body,
    returning the (still-ESCAPED) body and the REST after the quote.  A backslash (92) escapes the NEXT byte
    (so an escaped dquote, backslash-then-34, is consumed, never mistaken for the terminator); a bare dquote
    (34) closes; any other byte is body.  This only SPLITS at the terminator — DECODING reuses [unescape_opt]
    (via [esc_string_roundtrip_opt]), so there is exactly ONE un-escaper (no second, possibly-divergent decoder).
    Structural on [s] (each recursive call is on a sub-term), so no fuel is needed (like [unescape_opt]). *)
Fixpoint scan_quote (s : string) : option (string * string) :=
  match s with
  | EmptyString => None                                            (* unterminated literal *)
  | String c1 rest =>
      if Nat.eqb (nat_of_ascii c1) 34 then Some (EmptyString, rest)  (* closing dquote *)
      else if Nat.eqb (nat_of_ascii c1) 92 then                      (* backslash: the next byte is part of the escape *)
        match rest with
        | EmptyString => None
        | String c2 rest2 =>
            match scan_quote rest2 with
            | Some (body, r) => Some (String c1 (String c2 body), r)
            | None => None
            end
        end
      else
        match scan_quote rest with
        | Some (body, r) => Some (String c1 body, r)
        | None => None
        end
  end.

(** [esc_byte] prepends a FIXED prefix to its accumulator, so it commutes with a trailing append. *)
Lemma esc_byte_app : forall b X Y, (esc_byte b X ++ Y)%string = esc_byte b (X ++ Y)%string.
Proof.
  intros b X Y. unfold esc_byte.
  destruct (Nat.eqb b 34); [ reflexivity | ].
  destruct (Nat.eqb b 92); [ reflexivity | ].
  destruct (Nat.eqb b 10); [ reflexivity | ].
  destruct (Nat.eqb b 9);  [ reflexivity | ].
  destruct (Nat.eqb b 13); [ reflexivity | ].
  destruct (andb (Nat.leb 32 b) (Nat.ltb b 127)); reflexivity.
Qed.

(** A hex nibble's escaped byte ([hexdig k], k<16, in [0-9a-f] = codes 48-57/97-102) is never the dquote (34)
    nor the backslash (92), so [scan_quote] treats it as an ordinary body byte (used in the hex-escape case). *)
Lemma hexdig_not_special : forall k, k < 16 ->
  Nat.eqb (nat_of_ascii (hexdig k)) 34 = false /\ Nat.eqb (nat_of_ascii (hexdig k)) 92 = false.
Proof.
  intros k Hk. unfold hexdig. destruct (Nat.ltb k 10) eqn:E.
  - apply Nat.ltb_lt in E. rewrite Ascii.nat_ascii_embedding by lia.
    split; apply Nat.eqb_neq; lia.
  - apply Nat.ltb_ge in E. rewrite Ascii.nat_ascii_embedding by lia.
    split; apply Nat.eqb_neq; lia.
Qed.

(** [scan_quote] step lemmas: an ORDINARY byte (neither dquote nor backslash) is prepended to the body; a
    BACKSLASH consumes itself and the next byte and prepends both. *)
Lemma scan_quote_ord : forall c1 rest,
  Nat.eqb (nat_of_ascii c1) 34 = false -> Nat.eqb (nat_of_ascii c1) 92 = false ->
  scan_quote (String c1 rest) =
    match scan_quote rest with Some (body, r) => Some (String c1 body, r) | None => None end.
Proof. intros c1 rest H34 H92. cbn [scan_quote]. rewrite H34, H92. reflexivity. Qed.
Lemma scan_quote_bsl : forall c2 rest2,
  scan_quote (String (ch 92) (String c2 rest2)) =
    match scan_quote rest2 with Some (body, r) => Some (String (ch 92) (String c2 body), r) | None => None end.
Proof. intros c2 rest2. cbn [scan_quote]. rewrite (nat_of_ch 92) by lia. reflexivity. Qed.

(** [scan_quote] walks through ONE escaped byte exactly as it walks through its decoded source: it prepends
    [esc_byte (nat_of_ascii c)] to whatever the rest yields.  (The per-byte analogue of [unescape_opt_esc_byte].) *)
Lemma scan_quote_esc_byte : forall c X,
  scan_quote (esc_byte (nat_of_ascii c) X)
  = match scan_quote X with Some (body, r) => Some (esc_byte (nat_of_ascii c) body, r) | None => None end.
Proof.
  intros c X. assert (Hc : nat_of_ascii c < 256) by apply nat_of_ascii_lt_256.
  unfold esc_byte.
  destruct (Nat.eqb (nat_of_ascii c) 34) eqn:E34.
  { rewrite scan_quote_bsl. destruct (scan_quote X) as [ [body r] | ]; reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 92) eqn:E92.
  { rewrite scan_quote_bsl. destruct (scan_quote X) as [ [body r] | ]; reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 10) eqn:E10.
  { rewrite scan_quote_bsl. destruct (scan_quote X) as [ [body r] | ]; reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 9) eqn:E9.
  { rewrite scan_quote_bsl. destruct (scan_quote X) as [ [body r] | ]; reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 13) eqn:E13.
  { rewrite scan_quote_bsl. destruct (scan_quote X) as [ [body r] | ]; reflexivity. }
  destruct (andb (Nat.leb 32 (nat_of_ascii c)) (Nat.ltb (nat_of_ascii c) 127)) eqn:Eprint.
  { (* printable byte: emitted as itself, neither dquote (E34) nor backslash (E92) *)
    rewrite scan_quote_ord.
    - destruct (scan_quote X) as [ [body r] | ]; reflexivity.
    - rewrite nat_of_ch by lia. exact E34.
    - rewrite nat_of_ch by lia. exact E92. }
  { (* hex escape \xHL: backslash + 'x', then two hex nibbles (each an ordinary body byte) *)
    rewrite scan_quote_bsl.
    assert (Hd1 : Nat.div (nat_of_ascii c) 16 < 16) by (apply Nat.Div0.div_lt_upper_bound; lia).
    assert (Hd2 : Nat.modulo (nat_of_ascii c) 16 < 16) by (apply Nat.mod_upper_bound; lia).
    destruct (hexdig_not_special _ Hd1) as [H1a H1b].
    destruct (hexdig_not_special _ Hd2) as [H2a H2b].
    rewrite (scan_quote_ord (hexdig (Nat.div (nat_of_ascii c) 16)) _ H1a H1b).
    rewrite (scan_quote_ord (hexdig (Nat.modulo (nat_of_ascii c) 16)) X H2a H2b).
    destruct (scan_quote X) as [ [body r] | ]; reflexivity. }
Qed.

(** ★ THE STRING-BODY RECOVER LEMMA — [scan_quote] over [esc_string s] (the escaped body) and the closing
    dquote splits EXACTLY back into [esc_string s] and the rest.  Composed with [esc_string_roundtrip_opt]
    ([unescape_opt (esc_string s) = Some s]) this is what makes [lex (print_string_lit s)] recover [TStr s]. *)
Lemma scan_quote_esc_string : forall s rest,
  scan_quote (esc_string s ++ String (ch 34) rest) = Some (esc_string s, rest).
Proof.
  induction s as [ | c rest0 IH ]; intro rest.
  - cbn [esc_string append scan_quote]. rewrite (nat_of_ch 34) by lia. reflexivity.
  - cbn [esc_string]. rewrite esc_byte_app, scan_quote_esc_byte, IH. reflexivity.
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
    emitted token is ever blank (which would be malformed Go).  [print_ty] UNCONDITIONALLY now (a nominal
    name is a validated [Ident], hence non-empty), and the literal printers too.  (Injectivity AND the
    print-parse round-trip are likewise unconditional — [print_ty_inj] / [parse_print_ty].) *)
Lemma print_ty_nonempty : forall t, print_ty t <> ""%string.
Proof.
  induction t as [ | | | | | | | | | | | | | | | | | | i ]; cbn [print_ty];
    try (intro Hc; discriminate Hc).
  (* GTNamed i : the [Ident] proof forces the name non-empty *)
  destruct i as [ s Hs ]. cbn [proj1_sig].
  destruct s as [ | c n' ]; [ cbn in Hs; discriminate Hs | intro Hc; discriminate Hc ].
Qed.
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

    [BinOp] is the operator enum; [binop_prec] / [binop_text] DERIVE its precedence and surface text from
    the constructor — the single source of truth, so no caller can mis-pair an operator with the wrong
    precedence.  Consumed by [GoPrint]'s [gprint] (the verified frontend below), which parenthesises a
    sub-expression exactly when its [binop_prec] is looser than the context.  (The plugin's trusted OCaml
    [pp_prec] renders the same binary-operator tree as strings; [GoPrint] is being built to replace it.) *)

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

(** UNARY operators: not / bitwise-complement / dereference / address-of / negate.  Single-char prefixes
    (Go: [!b] [^x] [*p] [&x] [-x]), binding TIGHTER than every binary operator.  ([+] unary is omitted — the
    plugin never emits it.)  [unop_text] gives the surface text; consumed by [GoPrint]'s [gprint].
    [UNeg] (unary [-]) prints PARENTHESISED — [-(x)] — because a bare [-x] would collide with the [-5]
    negative literal, and [GoPrint]'s parser dispatches the unambiguous two-char prefix [-(] to it (the other
    four print bare). *)
Definition unop_text (o : UnaryOp) : string :=
  match o with UNot => "!" | UXor => "^" | UDeref => "*" | UAddr => "&" | UNeg => "-" end.
Definition is_space (c : ascii) : bool := Ascii.eqb c (ascii_of_nat 32).  (* ' ' *)
Definition is_dec_char (c : ascii) : bool :=
  andb (Nat.leb 48 (nat_of_ascii c)) (Nat.leb (nat_of_ascii c) 57).
Fixpoint all_dec (s : string) : bool :=
  match s with EmptyString => true | String c s' => andb (is_dec_char c) (all_dec s') end.
Fixpoint print_sep (sep : string) (xs : list string) : string :=
  match xs with
  | []        => ""
  | x :: xs'  => match xs' with
                 | []     => x
                 | _ :: _ => (x ++ sep ++ print_sep sep xs')%string
                 end
  end.

(** ---- TOKENS ---- the lexer's output alphabet.  Ambiguous operator chars ([* & ^ -]) are ONE token each;
    the PARSER decides prefix(unary)/infix(binary) by position (Wirth: the scanner classifies, the parser
    disambiguates).  Literals carry their SEMANTIC value ([Z]); identifiers carry a validated [Ident]. *)
Inductive Token : Type :=
  | TId  : Ident -> Token | TInt : Z -> Token | TStr : string -> Token  (* [TStr] carries the UNESCAPED string-literal content *)
  | TPlus | TMinus | TStar | TSlash | TPercent | TAmp | TPipe | TCaret | TBang
  | TShl | TShr | TAndNot | TEq | TNe | TLt | TLe | TGt | TGe | TLand | TLor
  | TLP | TRP | TLB | TRB | TLC | TRC | TComma | TColon | TDot
  | TFunc | TReturn | TChan | TMap.   (* [chan]/[map] are Go RESERVED WORDS (not [go_ident]s), so they are
                                          dedicated keyword tokens — needed for [chan T] / [map[K]V] types. *)

(** scan a maximal run of decimal digits off the head. *)
Fixpoint scan_digits (s : string) : string * string :=
  match s with
  | String c s' => if is_dec_char c then let (d, r) := scan_digits s' in (String c d, r) else (EmptyString, s)
  | EmptyString => (EmptyString, EmptyString)
  end.

(** the operator / delimiter scanner: MAXIMAL-MUNCH the token at the head [String c s'], return (token, rest). *)
Definition lex_op (c : ascii) (s' : string) : option (Token * string) :=
  if Ascii.eqb c (ch 40) then Some (TLP, s') else if Ascii.eqb c (ch 41) then Some (TRP, s')
  else if Ascii.eqb c (ch 91) then Some (TLB, s') else if Ascii.eqb c (ch 93) then Some (TRB, s')
  else if Ascii.eqb c (ch 123) then Some (TLC, s') else if Ascii.eqb c (ch 125) then Some (TRC, s')
  else if Ascii.eqb c (ch 44) then Some (TComma, s') else if Ascii.eqb c (ch 58) then Some (TColon, s')
  else if Ascii.eqb c (ch 46) then Some (TDot, s')
  else if Ascii.eqb c (ch 43) then Some (TPlus, s') else if Ascii.eqb c (ch 42) then Some (TStar, s')
  else if Ascii.eqb c (ch 47) then Some (TSlash, s') else if Ascii.eqb c (ch 37) then Some (TPercent, s')
  else if Ascii.eqb c (ch 94) then Some (TCaret, s') else if Ascii.eqb c (ch 45) then Some (TMinus, s')
  else if Ascii.eqb c (ch 60) then
    match s' with String d s'' => if Ascii.eqb d (ch 60) then Some (TShl, s'')
                                  else if Ascii.eqb d (ch 61) then Some (TLe, s'') else Some (TLt, s')
                | EmptyString => Some (TLt, s') end
  else if Ascii.eqb c (ch 62) then
    match s' with String d s'' => if Ascii.eqb d (ch 62) then Some (TShr, s'')
                                  else if Ascii.eqb d (ch 61) then Some (TGe, s'') else Some (TGt, s')
                | EmptyString => Some (TGt, s') end
  else if Ascii.eqb c (ch 61) then
    match s' with String d s'' => if Ascii.eqb d (ch 61) then Some (TEq, s'') else None | _ => None end
  else if Ascii.eqb c (ch 33) then
    match s' with String d s'' => if Ascii.eqb d (ch 61) then Some (TNe, s'') else Some (TBang, s')
                | _ => Some (TBang, s') end
  else if Ascii.eqb c (ch 38) then
    match s' with String d s'' => if Ascii.eqb d (ch 38) then Some (TLand, s'')
                                  else if Ascii.eqb d (ch 94) then Some (TAndNot, s'') else Some (TAmp, s')
                | _ => Some (TAmp, s') end
  else if Ascii.eqb c (ch 124) then
    match s' with String d s'' => if Ascii.eqb d (ch 124) then Some (TLor, s'') else Some (TPipe, s')
                | _ => Some (TPipe, s') end
  else None.

(** classify an identifier RUN: a keyword token ([func]/[return]/[chan]/[map]) or a [go_ident]-validated
    [TId].  [chan]/[map] are Go reserved words (not [go_ident]s), so they get dedicated tokens. *)
Definition lex_ident (tok : string) : option Token :=
  if String.eqb tok "func" then Some TFunc
  else if String.eqb tok "return" then Some TReturn
  else if String.eqb tok "chan" then Some TChan
  else if String.eqb tok "map" then Some TMap
  else match bool_dec (go_ident tok) true with left H => Some (TId (exist _ tok H)) | right _ => None end.

(** THE LEXER.  Skip whitespace; an [is_idstart] head is an identifier/keyword; a digit (or [-]+digit, the
    negative-literal form — binary [-] is always SPACED in the printer) is an integer; otherwise an
    operator/delimiter.  Fuel = input length (each token consumes >= 1 char, so it terminates). *)
Fixpoint lex_aux (fuel : nat) (s : string) : option (list Token) :=
  match fuel with
  | O => None
  | S f =>
    match s with
    | EmptyString => Some nil
    | String c s' =>
        if is_space c then lex_aux f s'
        else if is_idstart c then
          let (tok, rest) := scan_id s in
          match lex_ident tok with
          | Some t => match lex_aux f rest with Some l => Some (t :: l) | None => None end
          | None => None end
        else if is_dec_char c then
          let (num, rest) := scan_digits s in
          match lex_aux f rest with Some l => Some (TInt (parse_Z num) :: l) | None => None end
        else if andb (Ascii.eqb c (ch 45)) (match s' with String d _ => is_dec_char d | _ => false end) then
          let (num, rest) := scan_digits s' in
          match lex_aux f rest with Some l => Some (TInt (parse_Z (String c num)) :: l) | None => None end
        else if Ascii.eqb c (ch 34) then   (* a Go interpreted STRING literal: scan to the closing dquote, then
                                              VALIDATE+decode the body — a malformed escape ([unescape_opt = None])
                                              FAILS the whole lex (fail-closed), never building a [TStr] *)
          match scan_quote s' with
          | Some (body, rest) =>
              match unescape_opt body with
              | Some sdec => match lex_aux f rest with Some l => Some (TStr sdec :: l) | None => None end
              | None => None
              end
          | None => None
          end
        else
          match lex_op c s' with
          | Some (t, rest) => match lex_aux f rest with Some l => Some (t :: l) | None => None end
          | None => None end
    end
  end.
Definition lex (s : string) : option (list Token) := lex_aux (S (String.length s)) s.

(** ---- M5 TYPE-PARSER DEFINITIONS (placed before the expression parser so [parse_postfix] can call
    [parse_gty] for type assertions / conversions; the round-trip PROOFS are below, after the seams). ---- *)
Definition tyname_to_ident (n : TyName) : Ident :=
  mkIdent (proj1_sig n) (proj1 (andb_prop _ _ (proj2_sig n))).
Fixpoint gttokens_ty (t : GoTy) : list Token :=
  match t with
  | GTInt     => TId (mkIdent "int" eq_refl) :: nil
  | GTInt64   => TId (mkIdent "int64" eq_refl) :: nil
  | GTBool    => TId (mkIdent "bool" eq_refl) :: nil
  | GTString  => TId (mkIdent "string" eq_refl) :: nil
  | GTFloat64 => TId (mkIdent "float64" eq_refl) :: nil
  | GTFloat32 => TId (mkIdent "float32" eq_refl) :: nil
  | GTUint    => TId (mkIdent "uint" eq_refl) :: nil
  | GTU8      => TId (mkIdent "uint8" eq_refl) :: nil
  | GTI8      => TId (mkIdent "int8" eq_refl) :: nil
  | GTU16     => TId (mkIdent "uint16" eq_refl) :: nil
  | GTI16     => TId (mkIdent "int16" eq_refl) :: nil
  | GTU32     => TId (mkIdent "uint32" eq_refl) :: nil
  | GTI32     => TId (mkIdent "int32" eq_refl) :: nil
  | GTU64     => TId (mkIdent "uint64" eq_refl) :: nil
  | GTPtr u   => TStar :: gttokens_ty u
  | GTSlice u => TLB :: TRB :: gttokens_ty u
  | GTChan u  => TChan :: gttokens_ty u
  | GTMap k v => TMap :: TLB :: (gttokens_ty k ++ TRB :: gttokens_ty v)
  | GTNamed n => TId (tyname_to_ident n) :: nil
  end.
(* [_ => 1] is the deliberate UNIT size of every leaf type (the 13 primitives + [GTNamed], each one token).
   Unlike a printer default this is FAIL-CLOSED: it feeds only the type-parser FUEL bound, so a future
   COMPOSITE type that this undercounts makes its round-trip proof run out of fuel and FAIL TO COMPILE — loud,
   never wrong output.  (The output side, [print_ty]/[gttokens_ty], is fully exhaustive.) *)
Fixpoint tsize (t : GoTy) : nat :=
  match t with
  | GTPtr u | GTSlice u | GTChan u => S (tsize u)
  | GTMap k v => S (tsize k + tsize v)
  | _ => 1
  end.
(** a type has at least as many tokens as nodes — so [3*length+_]-style fuel always covers [tsize]. *)
Lemma tsize_le_len : forall t, tsize t <= List.length (gttokens_ty t).
Proof.
  induction t as [ | | | | | | | | | | | | | | u IHt | u IHt | u IHt | t1 IHt1 t2 IHt2 | n ].
  1-14: cbn; lia.
  - cbn [tsize gttokens_ty List.length]; lia.
  - cbn [tsize gttokens_ty List.length]; lia.
  - cbn [tsize gttokens_ty List.length]; lia.
  - cbn [tsize gttokens_ty List.length]. rewrite List.length_app. cbn [List.length]; lia.
  - cbn; lia.
Qed.

Fixpoint parse_gty (fuel : nat) (toks : list Token) : option (GoTy * list Token) :=
  match fuel with
  | O => None
  | S f =>
    match toks with
    | TStar :: rest => match parse_gty f rest with Some (u, r) => Some (GTPtr u, r) | None => None end
    | TLB :: TRB :: rest => match parse_gty f rest with Some (u, r) => Some (GTSlice u, r) | None => None end
    | TChan :: rest => match parse_gty f rest with Some (u, r) => Some (GTChan u, r) | None => None end
    | TMap :: TLB :: r0 =>
        match parse_gty f r0 with
        | Some (k, TRB :: r1) => match parse_gty f r1 with Some (v, r2) => Some (GTMap k v, r2) | None => None end
        | _ => None
        end
    | TId i :: rest =>
        match classify (proj1_sig i) with
        | Some t => Some (t, rest)
        | None => match bool_dec (nominal_type_ident (proj1_sig i)) true with
                  | left H => Some (GTNamed (mkTyName (proj1_sig i) H), rest)
                  | right _ => None
                  end
        end
    | _ => None
    end
  end.
Lemma parse_gty_S : forall f toks, parse_gty (S f) toks =
  match toks with
  | TStar :: rest => match parse_gty f rest with Some (u, r) => Some (GTPtr u, r) | None => None end
  | TLB :: TRB :: rest => match parse_gty f rest with Some (u, r) => Some (GTSlice u, r) | None => None end
  | TChan :: rest => match parse_gty f rest with Some (u, r) => Some (GTChan u, r) | None => None end
  | TMap :: TLB :: r0 =>
      match parse_gty f r0 with
      | Some (k, TRB :: r1) => match parse_gty f r1 with Some (v, r2) => Some (GTMap k v, r2) | None => None end
      | _ => None
      end
  | TId i :: rest =>
      match classify (proj1_sig i) with
      | Some t => Some (t, rest)
      | None => match bool_dec (nominal_type_ident (proj1_sig i)) true with
                | left H => Some (GTNamed (mkTyName (proj1_sig i) H), rest)
                | right _ => None
                end
      end
  | _ => None
  end.
Proof. reflexivity. Qed.


Example lex_sum  : lex "a + b" = Some (TId (exist _ "a" eq_refl) :: TPlus :: TId (exist _ "b" eq_refl) :: nil).
Proof. vm_compute; reflexivity. Qed.
Example lex_call : lex "f(x, 42)"
  = Some (TId (exist _ "f" eq_refl) :: TLP :: TId (exist _ "x" eq_refl) :: TComma :: TInt 42 :: TRP :: nil).
Proof. vm_compute; reflexivity. Qed.
Example lex_neg  : lex "-7" = Some (TInt (-7) :: nil). Proof. vm_compute; reflexivity. Qed.
Example lex_ops  : lex "x << 2" = Some (TId (exist _ "x" eq_refl) :: TShl :: TInt 2 :: nil). Proof. vm_compute; reflexivity. Qed.
Example lex_cmp  : lex "a <= b && c"
  = Some (TId (exist _ "a" eq_refl) :: TLe :: TId (exist _ "b" eq_refl) :: TLand :: TId (exist _ "c" eq_refl) :: nil).
Proof. vm_compute; reflexivity. Qed.

(** ---- STRING-LEXER FAIL-CLOSED REGRESSIONS ---- a spelling NOT in the printer image (a malformed escape, or a
    raw byte [esc_byte] would have escaped) must be REJECTED at tokenization ([lex = None]), NOT lossily normalized
    into a [TStr] (the Codex review fail-open).  Inputs are built byte-explicitly with [ch]: [ch 34] = the dquote,
    [ch 92] = the backslash, [ch 10] = newline, [ch 9] = tab.  Six rejected spellings — an UNKNOWN escape, a NON-HEX
    hex escape, an UPPER-CASE hex escape (the printer emits only lower-case), a TRUNCATED hex escape (one hex digit
    before the close), a RAW NEWLINE, and a RAW TAB in the body — each make [lex] (hence [parse_str]) return [None]. *)
Example lex_bad_escape : lex (String (ch 34) (String (ch 92) (String (ch 113) (String (ch 34) "")))) = None.
Proof. vm_compute; reflexivity. Qed.                              (* "\q"  — 'q' = 113, not an accepted escape *)
Example lex_bad_hex : lex (String (ch 34) (String (ch 92) (String (ch 120)
                          (String (ch 90) (String (ch 90) (String (ch 34) "")))))) = None.
Proof. vm_compute; reflexivity. Qed.                              (* "\xZZ" — 'Z' = 90 is not a hex digit *)
Example lex_trunc_hex : lex (String (ch 34) (String (ch 92) (String (ch 120)
                            (String (ch 49) (String (ch 34) ""))))) = None.
Proof. vm_compute; reflexivity. Qed.                              (* "\x1" — only one hex digit before the close *)
Example lex_raw_newline : lex (String (ch 34) (String (ch 10) (String (ch 34) ""))) = None.
Proof. vm_compute; reflexivity. Qed.                              (* a literal newline inside the quotes *)
Example lex_upper_hex : lex (String (ch 34) (String (ch 92) (String (ch 120)
                            (String (ch 65) (String (ch 70) (String (ch 34) "")))))) = None.
Proof. vm_compute; reflexivity. Qed.                              (* upper-case hex escape; 65=A, 70=F — printer emits only lower-case *)
Example lex_raw_tab : lex (String (ch 34) (String (ch 9) (String (ch 34) ""))) = None.
Proof. vm_compute; reflexivity. Qed.                              (* a raw tab byte (9) in the body — the printer escapes it *)
(* SUPERSET REGRESSIONS (Codex 2026-06-29): a SYNTACTICALLY-valid lower-case [\xHH] whose decoded byte is NOT
   one [esc_byte] hex-escapes (it is printable, or a named-escape byte) is NOT in the printer image, so [lex]
   must REJECT it — the old decoder lossily ACCEPTED these (a fail-OPEN superset).  Digits: '0'=48 '1'=49 '2'=50
   '4'=52 '5'=53 '9'=57 'a'=97 'c'=99.  Each byte built explicitly with [ch] (no literal dquote/backslash). *)
Example lex_hex_printable_A : lex (String (ch 34) (String (ch 92) (String (ch 120)
                                 (String (ch 52) (String (ch 49) (String (ch 34) "")))))) = None.
Proof. vm_compute; reflexivity. Qed.                              (* hex 41 = 65 = printable 'A' — printer emits it RAW *)
Example lex_hex_printable_space : lex (String (ch 34) (String (ch 92) (String (ch 120)
                                     (String (ch 50) (String (ch 48) (String (ch 34) "")))))) = None.
Proof. vm_compute; reflexivity. Qed.                              (* hex 20 = 32 = printable space — printer emits it RAW *)
Example lex_hex_dquote : lex (String (ch 34) (String (ch 92) (String (ch 120)
                            (String (ch 50) (String (ch 50) (String (ch 34) "")))))) = None.
Proof. vm_compute; reflexivity. Qed.                              (* hex 22 = 34 = the dquote — printer emits the NAMED escape *)
Example lex_hex_backslash : lex (String (ch 34) (String (ch 92) (String (ch 120)
                               (String (ch 53) (String (ch 99) (String (ch 34) "")))))) = None.
Proof. vm_compute; reflexivity. Qed.                              (* hex 5c = 92 = the backslash — printer emits the NAMED escape *)
Example lex_hex_tab : lex (String (ch 34) (String (ch 92) (String (ch 120)
                         (String (ch 48) (String (ch 57) (String (ch 34) "")))))) = None.
Proof. vm_compute; reflexivity. Qed.                              (* hex 09 = 9 = tab — printer emits the NAMED escape *)
Example lex_hex_newline : lex (String (ch 34) (String (ch 92) (String (ch 120)
                             (String (ch 48) (String (ch 97) (String (ch 34) "")))))) = None.
Proof. vm_compute; reflexivity. Qed.                              (* hex 0a = 10 = newline — printer emits the NAMED escape *)
(* POSITIVE companion: a WELL-FORMED literal still tokenizes to its single [TStr] (the round-trip side; the
   fully-general statement is [gtokens_lex] at [EStr], proved below for EVERY [s]). *)
Example lex_str_pos : lex (print_string_lit "hi") = Some (TStr "hi" :: nil).
Proof. vm_compute; reflexivity. Qed.
Example lex_str_pos_esc : lex (print_string_lit (String (ch 34) (String (ch 92) (String (ch 10) "x"))))
                        = Some (TStr (String (ch 34) (String (ch 92) (String (ch 10) "x"))) :: nil).
Proof. vm_compute; reflexivity. Qed.

(** ---- THE GRAMMAR (EBNF) ---- the exact language GoPrint lexes, parses, and prints.  The AST below,
    the printer [gprint], and the recursive-descent parser [parse] are three views of THIS one grammar, and
    the round-trip theorem [parse_print_roundtrip] proves the printer and parser agree on it.  (Wirth-style:
    state the grammar, then make the code visibly implement it.)  Notation: [{ x }] = zero-or-more,
    [[ x ]] = optional, ["lit"] = a terminal token, [->] names the AST node a production builds.

      Expr     = Primary { InfixOp Primary } .   -- precedence climbing ([parse_climb k]): extend the left
                                                    operand only with operators of precedence >= k, each right
                                                    operand parsed at precedence+1 (so same level is LEFT-assoc,
                                                    higher levels bind tighter)                       -> EBn
      Primary  = Atom { Postfix } .              -- a base, then a left-to-right chain of postfix operators
      Postfix  = "." ident                       -> ESel     selector
               | "." "(" Type ")"                -> EAssert  type assertion  (2nd token "(" vs ident disambiguates)
               | "[" Expr "]"                     -> EIndex   index
               | "[" Expr ":" Expr "]"           -> ESlice   two-bound slice
               | "(" [ Expr { "," Expr } ] ")" . -> ECall    call, variadic arg list
      Atom     = ident                            -> EId
               | int                              -> EInt
               | string                           -> EStr     interpreted string literal: a dquote, a body of
                                                              Escapes (below), a closing dquote; a MALFORMED escape
                                                              FAILS to lex (fail-closed, [unescape_opt = None])
               | "(" Expr ")"                     -- explicit grouping: re-parsed, NOT an AST node (gprint
                                                     re-derives the parens from precedence)
               | ( "!" | "^" | "*" | "&" ) Atom  -> EUn      prefix not / xor / deref / addr (bind to an Atom)
               | "-" "(" Expr ")"                -> EUn UNeg  parenthesised, so it never collides with a -literal
               | ConvType "(" Expr ")"           -> EConv     type-form conversion (a "[]"/"chan"/"map" lead is
                                                              unambiguously a TYPE at atom position)
               | "[]" Type "{" [ Elems ] "}"     -> ESliceLit slice composite literal (shares the "[]"-lead with
                                                              the []-conversion; split by next token "{" vs "(")
               | "map" "[" Type "]" Type "{" [ Pairs ] "}" . -> EMapLit  map composite literal (shares the
                                                              "map"-lead with the map-conversion; "{" vs "(")
      ConvType = "[]" Type | "chan" Type | "map" "[" Type "]" Type .   -- the [ConvTy] subset (the EConv operand type)
      Elems    = Expr { "," Expr } .             -- positional element list ([parse_elems])
      Pairs    = Expr ":" Expr { "," Expr ":" Expr } . -- keyed key:value list ([parse_map_elems])
      strlit   = DQUOTE { Escape | rawbyte } DQUOTE .  -- interpreted literal; rawbyte = printable ASCII 0x20..0x7E
                                                          EXCLUDING the dquote (0x22) and the backslash (0x5C)
      Escape   = BACKSLASH ( DQUOTE | BACKSLASH | n | t | r | x hex hex ) .  -- the EXACT set [esc_string] emits and
      hex      = digit | a..f .                         -- [unescape_opt] accepts (the lexer accepts EXACTLY the
                                                           printer image); any OTHER BACKSLASH-form, an UPPER-CASE
                                                           hex digit, or a raw byte outside that class FAILS to lex
                                                           (fail-closed)
      InfixOp  = "*" | "/" | "%" | "<<" | ">>" | "&" | "&^"   -- precedence 5
               | "+" | "-" | "|" | "^"                        -- precedence 4
               | "==" | "!=" | "<" | "<=" | ">" | ">="        -- precedence 3
               | "&&"                                          -- precedence 2
               | "||" .                                        -- precedence 1
      Type     = "int" | "int64" | "bool" | "string" | "float64" | "float32"           -- primitive
               | "uint" | "uint8" | "int8" | "uint16" | "int16" | "uint32" | "int32" | "uint64"
               | "*" Type | "[]" Type | "chan" Type | "map" "[" Type "]" Type           -- composite
               | ident .                          -> GTNamed  nominal type (the [GoTy] of M5)
      ident    = idstart { idstart | digit } ,  idstart = "_" | "A".."Z" | "a".."z" .   -- a [go_ident]
      int      = [ "-" ] digit { digit } .       -- decimal; the lexer reads a leading "-"<digit> as one [TInt]

    NOT yet in the grammar (the next growth steps): STRUCT / ARRAY composite literals ([N]T{..} / T{..}) and
    func-literals.  A NAMED conversion [T(x)] is currently the call [ECall (EId T) [x]] -- byte-identical, and
    the call/conversion distinction needs a type environment the parser does not have. *)


(** A bare prefix operator applied DIRECTLY to another would be a LEXICAL hazard: [&] then [&] prints "&&"
    which the lexer maximal-munches to [TLand], and [&] then [^] prints "&^" -> [TAndNot] — a token MERGE on
    the LEFT of the seam (the seam is two-sided: a clean right-hand start does not suffice).  So [gprint]
    PARENTHESISES every unary operand — [op(x)] — making the prefix always followed by a single-char ['(']
    that cannot munch into the operator before it.  (UNeg self-parenthesises as [-(x)] for the same reason,
    plus to avoid colliding with the [-5] negative-literal lexing.) *)

(** [op_needs_paren e0] — does a POSTFIX operand [e0] need parentheses?  TRUE for the LOOSE nodes
    ([EUn]/[EBn], which bind looser than a postfix operator); FALSE for every atom / postfix form (they bind
    at least as tightly).  The SINGLE source of truth for operand parenthesisation, used uniformly by
    [gprint]/[gparen]/[gtokens]/[gtparen].  EXHAUSTIVE on purpose — NO [_] catch-all: a default would silently
    classify a future constructor, and the only UNSAFE direction is bare-by-default (a new LOOSE form printed
    without parens = wrong precedence, exactly the "plausible-but-wrong" rule-2 forbids).  So every constructor
    is listed; adding one makes this match non-exhaustive and FAILS THE BUILD until its precedence is declared
    here — fail-loud at the definition, never a silent wrong default.  Inspects only the head constructor (no
    recursion), so it is defined before [gprint]. *)
Definition op_needs_paren (e0 : GExpr) : bool :=
  match e0 with
  | EUn _ _ | EBn _ _ _ => true
  | EId _ | EInt _ | EStr _ | ESel _ _ | EIndex _ _ | ESlice _ _ _ | ECall _ _ | EAssert _ _ | EConv _ _ | ESliceLit _ _ | EMapLit _ _ _ => false
  end.

(** ---- THE PRINTER ---- precedence-correct (reuses [binop_prec]/[binop_text]/[unop_text]); a binop wraps
    in parens exactly when its precedence [< ctx].  Mirrors the legacy [print_expr] over the clean AST. *)
Fixpoint gprint (ctx : nat) (e : GExpr) {struct e} : string :=
  match e with
  | EId i  => proj1_sig i
  | EInt z => print_Z z
  | EStr s => print_string_lit s   (* STRING literal: the verified escaping printer (its round-trip is [esc_string_roundtrip_opt]) *)
  | EUn o e => match o with    (* EXHAUSTIVE (no [_]): a new unary op must declare its printing here, not
                                  silently inherit the parenthesised default — same fail-loud discipline as
                                  [op_needs_paren] *)
               | UNeg => ("-(" ++ gprint 0 e ++ ")")%string
               | UNot | UXor | UDeref | UAddr => (unop_text o ++ "(" ++ gprint 0 e ++ ")")%string
               end
  | EBn o l r =>
      let p := binop_prec o in
      let inner := (gprint p l ++ binop_text o ++ gprint (S p) r)%string in
      if Nat.ltb p ctx then ("(" ++ inner ++ ")")%string else inner
  | ESel e0 f =>
      (* postfix never needs the ctx wrap; the OPERAND is parenthesised iff it is looser than postfix
         (a unary or binary node) — an atom or another postfix form prints bare (see [gparen]). *)
      ((if op_needs_paren e0 then ("(" ++ gprint 0 e0 ++ ")")%string else gprint 0 e0) ++ "." ++ proj1_sig f)%string
  | EIndex e0 i =>
      ((if op_needs_paren e0 then ("(" ++ gprint 0 e0 ++ ")")%string else gprint 0 e0) ++ "[" ++ gprint 0 i ++ "]")%string
  | ESlice e0 lo hi =>
      ((if op_needs_paren e0 then ("(" ++ gprint 0 e0 ++ ")")%string else gprint 0 e0) ++ "[" ++ gprint 0 lo ++ ":" ++ gprint 0 hi ++ "]")%string
  | ECall e0 args =>
      (* the comma-joined arg list is a LOCAL [fix] (calling the enclosing [gprint] on each arg, a subterm)
         — a mutual [with gprint_args] is rejected by the guard checker for a list-element cross-call.  The
         standalone [gprint_args] below mirrors it; [gprint_ECall] bridges them. *)
      ((if op_needs_paren e0 then ("(" ++ gprint 0 e0 ++ ")")%string else gprint 0 e0) ++ "(" ++
       (match args with
        | nil => ""
        | a :: r => (gprint 0 a ++ (fix gat (m : list GExpr) : string :=
                       match m with nil => "" | b :: m' => ("," ++ gprint 0 b ++ gat m')%string end) r)%string
        end)
       ++ ")")%string
  | EAssert e0 T =>
      ((if op_needs_paren e0 then ("(" ++ gprint 0 e0 ++ ")")%string else gprint 0 e0) ++ ".(" ++ print_ty T ++ ")")%string
  | EConv c e0 =>
      (* type-form conversion [T(x)]: the type renders as a prefix, the operand is ALWAYS parenthesised
         (like the prefix unary ops) — so it never needs the [op_needs_paren] dance. *)
      (print_ty (convty_ty c) ++ "(" ++ gprint 0 e0 ++ ")")%string
  | ESliceLit t es =>
      (* slice composite literal [[]T{e1,..,en}]: a type-led PREFIX primary; the brace-delimited element list
         reuses the same LOCAL [fix] comma-join as [ECall] (no trailing comma; gofmt-clean). [gprint_ESliceLit]
         re-folds it onto the standalone [gprint_args]. *)
      ("[]" ++ print_ty t ++ "{" ++
       (match es with
        | nil => ""
        | a :: r => (gprint 0 a ++ (fix gat (m : list GExpr) : string :=
                       match m with nil => "" | b :: m' => ("," ++ gprint 0 b ++ gat m')%string end) r)%string
        end)
       ++ "}")%string
  | EMapLit kt vt kvs =>
      (* map composite literal [map[K]V{k1: v1, .., kn: vn}]: a type-led PREFIX primary; the type prefix is
         [print_ty (GTMap kt vt)], then a brace-delimited list of KEYED elements [key: value], pairs joined by
         ", " — both separators carry a SPACE so the output is gofmt-clean (the lexer skips the spaces, so the
         token list has none).  [gprint_EMapLit] re-folds the local [fix] onto the standalone [gprint_pairs]. *)
      (print_ty (GTMap kt vt) ++ "{" ++
       (match kvs with
        | nil => ""
        | p :: r => let (k, v) := p in
            (gprint 0 k ++ ": " ++ gprint 0 v ++ (fix gpp (m : list (GExpr * GExpr)) : string :=
               match m with nil => "" | q :: m' => let (k', v') := q in (", " ++ gprint 0 k' ++ ": " ++ gprint 0 v' ++ gpp m')%string end) r)%string
        end)
       ++ "}")%string
  end.

(** the comma-joined argument list: head then a comma-prefixed tail (no trailing comma — gofmt-clean).
    Standalone (mirrors the local [fix] in [gprint]'s ECall case); [gprint_ECall] re-folds onto it. *)
Fixpoint gprint_args_tl (args : list GExpr) : string :=
  match args with nil => "" | b :: m => ("," ++ gprint 0 b ++ gprint_args_tl m)%string end.
Definition gprint_args (args : list GExpr) : string :=
  match args with nil => "" | a :: r => (gprint 0 a ++ gprint_args_tl r)%string end.

(** the KEYED, ", "-joined pair list of a map composite literal: head pair [k: v] then a ", "-prefixed tail
    (no trailing comma — gofmt-clean).  Standalone (mirrors the local [fix] in [gprint]'s EMapLit case);
    [gprint_EMapLit] re-folds onto it. *)
Fixpoint gprint_pairs_tl (kvs : list (GExpr * GExpr)) : string :=
  match kvs with nil => "" | p :: m => let (k, v) := p in (", " ++ gprint 0 k ++ ": " ++ gprint 0 v ++ gprint_pairs_tl m)%string end.
Definition gprint_pairs (kvs : list (GExpr * GExpr)) : string :=
  match kvs with nil => "" | p :: r => let (k, v) := p in (gprint 0 k ++ ": " ++ gprint 0 v ++ gprint_pairs_tl r)%string end.

(** [gparen] = a postfix operand's printing rule (bare for an atom/postfix, parenthesised for a unary/
    binary node), factored out so proofs can [destruct e0] over it WITHOUT [cbn] over-reducing [gprint 0 e0];
    [gprint_ESel]/[gprint_EIndex] re-fold the inlined [gprint] cases onto it. *)
Definition gparen (e0 : GExpr) : string :=
  if op_needs_paren e0 then ("(" ++ gprint 0 e0 ++ ")")%string else gprint 0 e0.
Lemma gprint_ESel : forall ctx e0 f, gprint ctx (ESel e0 f) = (gparen e0 ++ "." ++ proj1_sig f)%string.
Proof. reflexivity. Qed.
Lemma gprint_EIndex : forall ctx e0 i, gprint ctx (EIndex e0 i) = (gparen e0 ++ "[" ++ gprint 0 i ++ "]")%string.
Proof. reflexivity. Qed.
Lemma gprint_ESlice : forall ctx e0 lo hi,
  gprint ctx (ESlice e0 lo hi) = (gparen e0 ++ "[" ++ gprint 0 lo ++ ":" ++ gprint 0 hi ++ "]")%string.
Proof. reflexivity. Qed.
Lemma gprint_EAssert : forall ctx e0 T,
  gprint ctx (EAssert e0 T) = (gparen e0 ++ ".(" ++ print_ty T ++ ")")%string.
Proof. reflexivity. Qed.
Lemma gprint_EConv : forall ctx c e0,
  gprint ctx (EConv c e0) = (print_ty (convty_ty c) ++ "(" ++ gprint 0 e0 ++ ")")%string.
Proof. reflexivity. Qed.
(** the local [fix] in [gprint]'s ECall case computes exactly the standalone [gprint_args_tl]. *)
Lemma gat_eq : forall m,
  (fix gat (m0 : list GExpr) : string :=
     match m0 with nil => "" | b :: m' => ("," ++ gprint 0 b ++ gat m')%string end) m = gprint_args_tl m.
Proof. induction m as [ | b m IH ]; [ reflexivity | cbn [gprint_args_tl]; cbn [Datatypes.app]; rewrite <- IH; reflexivity ]. Qed.
Lemma gprint_ECall : forall ctx e0 args,
  gprint ctx (ECall e0 args) = (gparen e0 ++ "(" ++ gprint_args args ++ ")")%string.
Proof.
  intros ctx e0 args. unfold gprint_args.
  change (gprint ctx (ECall e0 args))
    with (gparen e0 ++ "(" ++
          (match args with
           | nil => ""
           | a :: r => (gprint 0 a ++ (fix gat (m : list GExpr) : string :=
                          match m with nil => "" | b :: m' => ("," ++ gprint 0 b ++ gat m')%string end) r)%string
           end) ++ ")")%string.
  destruct args as [ | a r ]; [ reflexivity | rewrite gat_eq; reflexivity ].
Qed.
(** the local [fix] in [gprint]'s ESliceLit case computes exactly the standalone [gprint_args] (same comma-join
    as ECall); [gprint_ESliceLit] re-folds the brace-delimited element list onto it. *)
Lemma gprint_ESliceLit : forall ctx t es,
  gprint ctx (ESliceLit t es) = ("[]" ++ print_ty t ++ "{" ++ gprint_args es ++ "}")%string.
Proof.
  intros ctx t es. unfold gprint_args.
  change (gprint ctx (ESliceLit t es))
    with ("[]" ++ print_ty t ++ "{" ++
          (match es with
           | nil => ""
           | a :: r => (gprint 0 a ++ (fix gat (m : list GExpr) : string :=
                          match m with nil => "" | b :: m' => ("," ++ gprint 0 b ++ gat m')%string end) r)%string
           end) ++ "}")%string.
  destruct es as [ | a r ]; [ reflexivity | rewrite gat_eq; reflexivity ].
Qed.
(** the local [fix] in [gprint]'s EMapLit case computes exactly the standalone [gprint_pairs_tl]. *)
Lemma gpp_eq : forall m,
  (fix gpp (m0 : list (GExpr * GExpr)) : string :=
     match m0 with nil => "" | q :: m' => let (k', v') := q in (", " ++ gprint 0 k' ++ ": " ++ gprint 0 v' ++ gpp m')%string end) m = gprint_pairs_tl m.
Proof. induction m as [ | [k v] m IH ]; [ reflexivity | cbn [gprint_pairs_tl]; rewrite <- IH; reflexivity ]. Qed.
(** the local [fix] in [gprint]'s EMapLit case computes exactly the standalone [gprint_pairs]; [gprint_EMapLit]
    re-folds the brace-delimited KEYED pair list onto it (the type prefix is [print_ty (GTMap kt vt)]). *)
Lemma gprint_EMapLit : forall ctx kt vt kvs,
  gprint ctx (EMapLit kt vt kvs) = (print_ty (GTMap kt vt) ++ "{" ++ gprint_pairs kvs ++ "}")%string.
Proof.
  intros ctx kt vt kvs. unfold gprint_pairs.
  change (gprint ctx (EMapLit kt vt kvs))
    with (print_ty (GTMap kt vt) ++ "{" ++
          (match kvs with
           | nil => ""
           | p :: r => let (k, v) := p in
               (gprint 0 k ++ ": " ++ gprint 0 v ++ (fix gpp (m : list (GExpr * GExpr)) : string :=
                  match m with nil => "" | q :: m' => let (k', v') := q in (", " ++ gprint 0 k' ++ ": " ++ gprint 0 v' ++ gpp m')%string end) r)%string
           end) ++ "}")%string.
  destruct kvs as [ | [k v] r ]; [ reflexivity | rewrite gpp_eq; reflexivity ].
Qed.

(** ---- THE PARSER ---- recursive descent + precedence climbing over the TOKEN stream.  The ambiguous
    operator tokens are resolved by POSITION: a prefix [TStar]/[TAmp]/[TCaret]/[TBang] is a unary op
    ([parse_primary]); an infix one is a binary op ([infix_op] in [parse_climb]).  [TMinus]+[TLP] is the
    parenthesised unary minus [UNeg]; bare negative literals are already [TInt] from the lexer. *)
Definition infix_op (t : Token) : option BinOp :=
  match t with
  | TPlus => Some BAdd | TMinus => Some BSub | TStar => Some BMul | TSlash => Some BDiv
  | TPercent => Some BRem | TShl => Some BShl | TShr => Some BShr | TAmp => Some BAnd
  | TAndNot => Some BAndNot | TPipe => Some BOr | TCaret => Some BXor
  | TEq => Some BEq | TNe => Some BNe | TLt => Some BLt | TLe => Some BLe | TGt => Some BGt | TGe => Some BGe
  | TLand => Some BLAnd | TLor => Some BLOr
  | _ => None
  end.

Fixpoint parse_expr (fuel k : nat) (toks : list Token) : option (GExpr * list Token) :=
  match fuel with
  | O => None
  | S f => match parse_primary f toks with Some (l, r) => parse_climb f k l r | None => None end
  end
(** a PRIMARY = an atom then a left-to-right chain of postfix selectors. *)
with parse_primary (fuel : nat) (toks : list Token) : option (GExpr * list Token) :=
  match fuel with
  | O => None
  | S f => match parse_atom f toks with Some (a, r) => parse_postfix f a r | None => None end
  end
with parse_atom (fuel : nat) (toks : list Token) : option (GExpr * list Token) :=
  match fuel with
  | O => None
  | S f =>
    match toks with
    | TLP :: rest => match parse_expr f 0 rest with Some (e, TRP :: r) => Some (e, r) | _ => None end
    | TBang  :: rest => match parse_atom f rest with Some (e, r) => Some (EUn UNot e, r)   | None => None end
    | TCaret :: rest => match parse_atom f rest with Some (e, r) => Some (EUn UXor e, r)   | None => None end
    | TStar  :: rest => match parse_atom f rest with Some (e, r) => Some (EUn UDeref e, r) | None => None end
    | TAmp   :: rest => match parse_atom f rest with Some (e, r) => Some (EUn UAddr e, r)  | None => None end
    | TMinus :: TLP :: rest => match parse_expr f 0 rest with Some (e, TRP :: r) => Some (EUn UNeg e, r) | _ => None end
    (* type-form CONVERSIONS [T(x)] — at atom position a type-lead ([]/chan/map) is unambiguously a conversion
       (no preceding operand to index/etc.).  Parse the type ([parse_gty], reused from EAssert), require it be
       a conversion head, then the parenthesised operand.  [parse_gty] is defined before this mutual block. *)
    | TLB :: TRB :: _ =>
        match parse_gty f toks with
        | Some (GTSlice u, TLP :: r1) => match parse_expr f 0 r1 with Some (e, TRP :: r2) => Some (EConv (CTSlice u) e, r2) | _ => None end
        (* slice composite literal [[]T{e1,..,en}] — same [[]T] lead as the conversion, disambiguated by the
           NEXT token: '{' (TLC) -> [ESliceLit], '(' (TLP) -> [EConv].  Elements via [parse_elems]. *)
        | Some (GTSlice u, TLC :: r1) => match parse_elems f r1 with Some (es, r2) => Some (ESliceLit u es, r2) | None => None end
        | _ => None end
    | TChan :: _ =>
        match parse_gty f toks with
        | Some (GTChan u, TLP :: r1) => match parse_expr f 0 r1 with Some (e, TRP :: r2) => Some (EConv (CTChan u) e, r2) | _ => None end
        | _ => None end
    | TMap :: _ =>
        match parse_gty f toks with
        | Some (GTMap k v, TLP :: r1) => match parse_expr f 0 r1 with Some (e, TRP :: r2) => Some (EConv (CTMap k v) e, r2) | _ => None end
        (* map composite literal [map[K]V{k1: v1,..,kn: vn}] — same [map[K]V] lead as the conversion,
           disambiguated by the NEXT token: '{' (TLC) -> [EMapLit], '(' (TLP) -> [EConv].  KEYED elements
           via [parse_map_elems]. *)
        | Some (GTMap k v, TLC :: r1) => match parse_map_elems f r1 with Some (kvs, r2) => Some (EMapLit k v kvs, r2) | None => None end
        | _ => None end
    | TId i :: rest  => Some (EId i, rest)
    | TInt z :: rest => Some (EInt z, rest)
    | TStr s :: rest => Some (EStr s, rest)
    | _ => None
    end
  end
with parse_postfix (fuel : nat) (a : GExpr) (toks : list Token) : option (GExpr * list Token) :=
  match fuel with
  | O => None
  | S f =>
    match toks with
    | TDot :: TLP :: rest =>   (* type assertion [.(T)] — disjoint from [.field] (2nd token [TLP] vs [TId]) *)
        match parse_gty f rest with Some (T, TRP :: r) => parse_postfix f (EAssert a T) r | _ => None end
    | TDot :: TId field :: rest => parse_postfix f (ESel a field) rest
    | TLB :: rest =>
        match parse_expr f 0 rest with
        | Some (lo, TColon :: r1) =>
            match parse_expr f 0 r1 with Some (hi, TRB :: r2) => parse_postfix f (ESlice a lo hi) r2 | _ => None end
        | Some (i, TRB :: r) => parse_postfix f (EIndex a i) r
        | _ => None
        end
    | TLP :: rest => match parse_args f rest with Some (args, r) => parse_postfix f (ECall a args) r | None => None end
    | _ => Some (a, toks)
    end
  end
(** an argument list up to and including the closing ')': empty, or a head expr then a comma-led tail. *)
with parse_args (fuel : nat) (toks : list Token) : option (list GExpr * list Token) :=
  match fuel with
  | O => None
  | S f =>
    match toks with
    | TRP :: r => Some (nil, r)
    | _ => match parse_expr f 0 toks with
           | Some (a, r0) => match parse_args_tl f r0 with Some (args, r1) => Some (a :: args, r1) | None => None end
           | None => None
           end
    end
  end
with parse_args_tl (fuel : nat) (toks : list Token) : option (list GExpr * list Token) :=
  match fuel with
  | O => None
  | S f =>
    match toks with
    | TRP :: r => Some (nil, r)
    | TComma :: r => match parse_expr f 0 r with
                     | Some (a, r0) => match parse_args_tl f r0 with Some (args, r1) => Some (a :: args, r1) | None => None end
                     | None => None
                     end
    | _ => None
    end
  end
(** a brace-delimited ELEMENT list up to and including the closing '}' — VERBATIM [parse_args] with the
    terminator token [TRP] replaced by [TRC] (the elements share the comma machinery; only the closer differs). *)
with parse_elems (fuel : nat) (toks : list Token) : option (list GExpr * list Token) :=
  match fuel with
  | O => None
  | S f =>
    match toks with
    | TRC :: r => Some (nil, r)
    | _ => match parse_expr f 0 toks with
           | Some (a, r0) => match parse_elems_tl f r0 with Some (es, r1) => Some (a :: es, r1) | None => None end
           | None => None
           end
    end
  end
with parse_elems_tl (fuel : nat) (toks : list Token) : option (list GExpr * list Token) :=
  match fuel with
  | O => None
  | S f =>
    match toks with
    | TRC :: r => Some (nil, r)
    | TComma :: r => match parse_expr f 0 r with
                     | Some (a, r0) => match parse_elems_tl f r0 with Some (es, r1) => Some (a :: es, r1) | None => None end
                     | None => None
                     end
    | _ => None
    end
  end
(** a brace-delimited KEYED ELEMENT list ([k1: v1, .., kn: vn}]) up to and including the closing '}' — like
    [parse_elems] but each element is a KEY expr, a [TColon], then a VALUE expr (the map literal's [key: value]).
    The colon separates the two children; comma separates pairs; [TRC] closes. *)
with parse_map_elems (fuel : nat) (toks : list Token) : option (list (GExpr * GExpr) * list Token) :=
  match fuel with
  | O => None
  | S f =>
    match toks with
    | TRC :: r => Some (nil, r)
    | _ => match parse_expr f 0 toks with
           | Some (k, TColon :: r0) =>
               match parse_expr f 0 r0 with
               | Some (v, r1) => match parse_map_elems_tl f r1 with Some (kvs, r2) => Some ((k, v) :: kvs, r2) | None => None end
               | None => None
               end
           | _ => None
           end
    end
  end
with parse_map_elems_tl (fuel : nat) (toks : list Token) : option (list (GExpr * GExpr) * list Token) :=
  match fuel with
  | O => None
  | S f =>
    match toks with
    | TRC :: r => Some (nil, r)
    | TComma :: r =>
        match parse_expr f 0 r with
        | Some (k, TColon :: r0) =>
            match parse_expr f 0 r0 with
            | Some (v, r1) => match parse_map_elems_tl f r1 with Some (kvs, r2) => Some ((k, v) :: kvs, r2) | None => None end
            | None => None
            end
        | _ => None
        end
    | _ => None
    end
  end
with parse_climb (fuel k : nat) (l : GExpr) (toks : list Token) : option (GExpr * list Token) :=
  match fuel with
  | O => None
  | S f =>
    match toks with
    | t :: rest =>
        match infix_op t with
        | Some o => if Nat.leb k (binop_prec o)
                    then match parse_expr f (S (binop_prec o)) rest with
                         | Some (r, r2) => parse_climb f k (EBn o l r) r2
                         | None => None end
                    else Some (l, toks)
        | None => Some (l, toks)
        end
    | nil => Some (l, toks)
    end
  end.
Definition parse (toks : list Token) : option (GExpr * list Token) := parse_expr (3 * List.length toks + 4) 0 toks.
(** parse a STRING end-to-end: [lex] then [parse].  The frontend's front door. *)
Definition parse_str (s : string) : option (GExpr * list Token) :=
  match lex s with Some toks => parse toks | None => None end.

(** END-TO-END round-trip by example: [parse_str (gprint 0 e) = Some (e, [])] — the printed AST lexes and
    parses back to itself.  (The general theorem [parse_str (gprint 0 e) = Some (e, [])] is next.) *)
Notation EX a := (EId (exist (fun s : string => go_ident s = true) a eq_refl)) (only parsing).
Example rt_id   : parse_str (gprint 0 (EX "x")) = Some (EX "x", nil). Proof. vm_compute; reflexivity. Qed.
Example rt_int  : parse_str (gprint 0 (EInt 42)) = Some (EInt 42, nil). Proof. vm_compute; reflexivity. Qed.
(* string-literal round-trips ([EStr]): empty, a plain word, and one with escapes (dquote/backslash/newline/
   tab) — the lexer's body scan + [unescape_opt] recovers the EXACT bytes through the full print->lex->parse pipe. *)
Example rt_str0  : parse_str (gprint 0 (EStr "")) = Some (EStr "", nil). Proof. vm_compute; reflexivity. Qed.
Example rt_str   : parse_str (gprint 0 (EStr "hi")) = Some (EStr "hi", nil). Proof. vm_compute; reflexivity. Qed.
Example rt_str_esc : parse_str (gprint 0 (EStr ("a" ++ String (ch 34) (String (ch 92) (String (ch 10) (String (ch 9) "b"))))))
                   = Some (EStr ("a" ++ String (ch 34) (String (ch 92) (String (ch 10) (String (ch 9) "b")))), nil).
Proof. vm_compute; reflexivity. Qed.
Example rt_str_call : parse_str (gprint 0 (ECall (EX "println") (EStr "hi" :: nil)))
                    = Some (ECall (EX "println") (EStr "hi" :: nil), nil).  (* println("hi") *)
Proof. vm_compute; reflexivity. Qed.
(* parse_str inherits the fail-closed rejection (lex feeds parse): a malformed escape never reaches the
   parser — [parse_str] returns [None] (cf. the [lex_bad_*] negative examples). *)
Example parse_bad_escape : parse_str (String (ch 34) (String (ch 92) (String (ch 113) (String (ch 34) "")))) = None.
Proof. vm_compute; reflexivity. Qed.
Example rt_add  : parse_str (gprint 0 (EBn BAdd (EX "a") (EX "b"))) = Some (EBn BAdd (EX "a") (EX "b"), nil).
Proof. vm_compute; reflexivity. Qed.
Example rt_prec : parse_str (gprint 0 (EBn BAdd (EX "a") (EBn BMul (EX "b") (EX "c"))))
                = Some (EBn BAdd (EX "a") (EBn BMul (EX "b") (EX "c")), nil).  (* a + b*c — no parens *)
Proof. vm_compute; reflexivity. Qed.
Example rt_wrap : parse_str (gprint 0 (EBn BMul (EBn BAdd (EX "a") (EX "b")) (EX "c")))
                = Some (EBn BMul (EBn BAdd (EX "a") (EX "b")) (EX "c"), nil).  (* (a + b)*c — parens recovered *)
Proof. vm_compute; reflexivity. Qed.
Example rt_un   : parse_str (gprint 0 (EUn UNot (EBn BEq (EX "a") (EX "b"))))
                = Some (EUn UNot (EBn BEq (EX "a") (EX "b")), nil).  (* !(a == b) *)
Proof. vm_compute; reflexivity. Qed.
Example rt_neg  : parse_str (gprint 0 (EUn UNeg (EX "x"))) = Some (EUn UNeg (EX "x"), nil).  (* -(x) *)
Proof. vm_compute; reflexivity. Qed.
(* the nested-bare-unary LEXICAL HAZARD: without the operand parens these print "&&x"/"&^x" and lex to
   [TLand]/[TAndNot] — a left-side token merge.  With the fix they print "&(&x)"/"&(^x)" and round-trip. *)
Example rt_addr_addr : parse_str (gprint 0 (EUn UAddr (EUn UAddr (EX "x"))))
                     = Some (EUn UAddr (EUn UAddr (EX "x")), nil).
Proof. vm_compute; reflexivity. Qed.
Example rt_addr_xor  : parse_str (gprint 0 (EUn UAddr (EUn UXor (EX "x"))))
                     = Some (EUn UAddr (EUn UXor (EX "x")), nil).
Proof. vm_compute; reflexivity. Qed.
(* ESel (postfix selector): atom operand bare, chain left-assoc, unary/binop operand parenthesised. *)
Example rt_sel    : parse_str (gprint 0 (ESel (EX "x") (exist _ "f" eq_refl)))
                  = Some (ESel (EX "x") (exist _ "f" eq_refl), nil).  (* x.f *)
Proof. vm_compute; reflexivity. Qed.
Example rt_sel_chain : parse_str (gprint 0 (ESel (ESel (EX "x") (exist _ "f" eq_refl)) (exist _ "g" eq_refl)))
                  = Some (ESel (ESel (EX "x") (exist _ "f" eq_refl)) (exist _ "g" eq_refl), nil).  (* x.f.g *)
Proof. vm_compute; reflexivity. Qed.
Example rt_sel_bin : parse_str (gprint 0 (ESel (EBn BAdd (EX "a") (EX "b")) (exist _ "f" eq_refl)))
                  = Some (ESel (EBn BAdd (EX "a") (EX "b")) (exist _ "f" eq_refl), nil).  (* (a + b).f *)
Proof. vm_compute; reflexivity. Qed.
Example rt_sel_in_bin : parse_str (gprint 0 (EBn BAdd (ESel (EX "a") (exist _ "f" eq_refl)) (EX "b")))
                  = Some (EBn BAdd (ESel (EX "a") (exist _ "f" eq_refl)) (EX "b"), nil).  (* a.f + b *)
Proof. vm_compute; reflexivity. Qed.
Example rt_idx     : parse_str (gprint 0 (EIndex (EX "a") (EX "i")))
                  = Some (EIndex (EX "a") (EX "i"), nil).  (* a[i] *)
Proof. vm_compute; reflexivity. Qed.
Example rt_idx_expr : parse_str (gprint 0 (EIndex (EX "a") (EBn BAdd (EX "i") (EInt 1))))
                  = Some (EIndex (EX "a") (EBn BAdd (EX "i") (EInt 1)), nil).  (* a[i + 1] *)
Proof. vm_compute; reflexivity. Qed.
Example rt_idx_sel : parse_str (gprint 0 (ESel (EIndex (ESel (EX "a") (exist _ "b" eq_refl)) (EX "i")) (exist _ "c" eq_refl)))
                  = Some (ESel (EIndex (ESel (EX "a") (exist _ "b" eq_refl)) (EX "i")) (exist _ "c" eq_refl), nil).  (* a.b[i].c *)
Proof. vm_compute; reflexivity. Qed.
Example rt_idx_paren : parse_str (gprint 0 (EIndex (EBn BAdd (EX "x") (EX "y")) (EX "i")))
                  = Some (EIndex (EBn BAdd (EX "x") (EX "y")) (EX "i"), nil).  (* (x + y)[i] *)
Proof. vm_compute; reflexivity. Qed.
Example rt_idx_in_bin : parse_str (gprint 0 (EBn BAdd (EIndex (EX "a") (EX "i")) (EX "b")))
                  = Some (EBn BAdd (EIndex (EX "a") (EX "i")) (EX "b"), nil).  (* a[i] + b *)
Proof. vm_compute; reflexivity. Qed.
Example rt_idx_idx : parse_str (gprint 0 (EIndex (EIndex (EX "m") (EX "i")) (EX "j")))
                  = Some (EIndex (EIndex (EX "m") (EX "i")) (EX "j"), nil).  (* m[i][j] *)
Proof. vm_compute; reflexivity. Qed.
Example rt_slice   : parse_str (gprint 0 (ESlice (EX "a") (EX "lo") (EX "hi")))
                  = Some (ESlice (EX "a") (EX "lo") (EX "hi"), nil).  (* a[lo:hi] *)
Proof. vm_compute; reflexivity. Qed.
Example rt_slice_expr : parse_str (gprint 0 (ESlice (EX "a") (EBn BAdd (EX "i") (EInt 1)) (EX "n")))
                  = Some (ESlice (EX "a") (EBn BAdd (EX "i") (EInt 1)) (EX "n"), nil).  (* a[i + 1:n] *)
Proof. vm_compute; reflexivity. Qed.
Example rt_slice_sel : parse_str (gprint 0 (ESel (ESlice (ESel (EX "a") (exist _ "b" eq_refl)) (EX "i") (EX "j")) (exist _ "c" eq_refl)))
                  = Some (ESel (ESlice (ESel (EX "a") (exist _ "b" eq_refl)) (EX "i") (EX "j")) (exist _ "c" eq_refl), nil).  (* a.b[i:j].c *)
Proof. vm_compute; reflexivity. Qed.
Example rt_slice_paren : parse_str (gprint 0 (ESlice (EBn BAdd (EX "x") (EX "y")) (EX "lo") (EX "hi")))
                  = Some (ESlice (EBn BAdd (EX "x") (EX "y")) (EX "lo") (EX "hi"), nil).  (* (x + y)[lo:hi] *)
Proof. vm_compute; reflexivity. Qed.
Example rt_slice_in_bin : parse_str (gprint 0 (EBn BAdd (ESlice (EX "a") (EX "i") (EX "j")) (EX "b")))
                  = Some (EBn BAdd (ESlice (EX "a") (EX "i") (EX "j")) (EX "b"), nil).  (* a[i:j] + b *)
Proof. vm_compute; reflexivity. Qed.
Example rt_slice_of_idx : parse_str (gprint 0 (ESlice (EIndex (EX "m") (EX "k")) (EX "i") (EX "j")))
                  = Some (ESlice (EIndex (EX "m") (EX "k")) (EX "i") (EX "j"), nil).  (* m[k][i:j] *)
Proof. vm_compute; reflexivity. Qed.
Example rt_call0 : parse_str (gprint 0 (ECall (EX "f") nil))
                  = Some (ECall (EX "f") nil, nil).  (* f() *)
Proof. vm_compute; reflexivity. Qed.
Example rt_call1 : parse_str (gprint 0 (ECall (EX "f") (EX "x" :: nil)))
                  = Some (ECall (EX "f") (EX "x" :: nil), nil).  (* f(x) *)
Proof. vm_compute; reflexivity. Qed.
Example rt_call2 : parse_str (gprint 0 (ECall (EX "f") (EX "x" :: EX "y" :: nil)))
                  = Some (ECall (EX "f") (EX "x" :: EX "y" :: nil), nil).  (* f(x,y) *)
Proof. vm_compute; reflexivity. Qed.
Example rt_call_method : parse_str (gprint 0 (ESel (ECall (ESel (EX "a") (exist _ "b" eq_refl)) (EX "x" :: nil)) (exist _ "c" eq_refl)))
                  = Some (ESel (ECall (ESel (EX "a") (exist _ "b" eq_refl)) (EX "x" :: nil)) (exist _ "c" eq_refl), nil).  (* a.b(x).c *)
Proof. vm_compute; reflexivity. Qed.
Example rt_call_paren : parse_str (gprint 0 (ECall (EBn BAdd (EX "x") (EX "y")) (EX "z" :: nil)))
                  = Some (ECall (EBn BAdd (EX "x") (EX "y")) (EX "z" :: nil), nil).  (* (x + y)(z) *)
Proof. vm_compute; reflexivity. Qed.
Example rt_call_nested : parse_str (gprint 0 (ECall (EX "f") (ECall (EX "g") (EX "x" :: nil) :: EX "y" :: nil)))
                  = Some (ECall (EX "f") (ECall (EX "g") (EX "x" :: nil) :: EX "y" :: nil), nil).  (* f(g(x),y) *)
Proof. vm_compute; reflexivity. Qed.
Example rt_call_binarg : parse_str (gprint 0 (ECall (EX "f") (EBn BAdd (EX "x") (EInt 1) :: nil)))
                  = Some (ECall (EX "f") (EBn BAdd (EX "x") (EInt 1) :: nil), nil).  (* f(x + 1) *)
Proof. vm_compute; reflexivity. Qed.
Example rt_assert_int : parse_str (gprint 0 (EAssert (EX "x") GTInt))
                  = Some (EAssert (EX "x") GTInt, nil).  (* x.(int) *)
Proof. vm_compute; reflexivity. Qed.
Example rt_assert_slice : parse_str (gprint 0 (EAssert (EX "x") (GTSlice GTInt)))
                  = Some (EAssert (EX "x") (GTSlice GTInt), nil).  (* x.([]int) *)
Proof. vm_compute; reflexivity. Qed.
Example rt_assert_ptr : parse_str (gprint 0 (EAssert (EX "x") (GTPtr (GTNamed (mkTyName "Foo" eq_refl)))))
                  = Some (EAssert (EX "x") (GTPtr (GTNamed (mkTyName "Foo" eq_refl))), nil).  (* x.( *Foo ) pointer assert *)
Proof. vm_compute; reflexivity. Qed.
Example rt_assert_named : parse_str (gprint 0 (EAssert (EX "x") (GTNamed (mkTyName "T" eq_refl))))
                  = Some (EAssert (EX "x") (GTNamed (mkTyName "T" eq_refl)), nil).  (* x.(T) *)
Proof. vm_compute; reflexivity. Qed.
Example rt_assert_paren : parse_str (gprint 0 (EAssert (EBn BAdd (EX "x") (EX "y")) (GTNamed (mkTyName "T" eq_refl))))
                  = Some (EAssert (EBn BAdd (EX "x") (EX "y")) (GTNamed (mkTyName "T" eq_refl)), nil).  (* (x + y).(T) *)
Proof. vm_compute; reflexivity. Qed.
Example rt_assert_chain : parse_str (gprint 0 (ESel (EAssert (ESel (EX "a") (exist _ "b" eq_refl)) (GTNamed (mkTyName "T" eq_refl))) (exist _ "c" eq_refl)))
                  = Some (ESel (EAssert (ESel (EX "a") (exist _ "b" eq_refl)) (GTNamed (mkTyName "T" eq_refl))) (exist _ "c" eq_refl), nil).  (* a.b.(T).c *)
Proof. vm_compute; reflexivity. Qed.
Example rt_assert_call : parse_str (gprint 0 (EAssert (ECall (EX "f") (EX "x" :: nil)) (GTNamed (mkTyName "T" eq_refl))))
                  = Some (EAssert (ECall (EX "f") (EX "x" :: nil)) (GTNamed (mkTyName "T" eq_refl)), nil).  (* f(x).(T) *)
Proof. vm_compute; reflexivity. Qed.
(** slice composite literal [[]T{..}] round-trips (the [ESliceLit] node): empty, one/two elements, a binop
    element (printed brace-internal, no parens), and a NESTED slice-of-slices literal. *)
Example rt_slicelit0 : parse_str (gprint 0 (ESliceLit GTInt nil))
                  = Some (ESliceLit GTInt nil, nil).  (* []int{} *)
Proof. vm_compute; reflexivity. Qed.
Example rt_slicelit1 : parse_str (gprint 0 (ESliceLit GTInt (EInt 1 :: nil)))
                  = Some (ESliceLit GTInt (EInt 1 :: nil), nil).  (* []int{1} *)
Proof. vm_compute; reflexivity. Qed.
Example rt_slicelit2 : parse_str (gprint 0 (ESliceLit GTInt (EX "x" :: EX "y" :: nil)))
                  = Some (ESliceLit GTInt (EX "x" :: EX "y" :: nil), nil).  (* []int{x,y} *)
Proof. vm_compute; reflexivity. Qed.
Example rt_slicelit_binarg : parse_str (gprint 0 (ESliceLit GTInt (EBn BAdd (EX "x") (EInt 1) :: nil)))
                  = Some (ESliceLit GTInt (EBn BAdd (EX "x") (EInt 1) :: nil), nil).  (* []int{x + 1} *)
Proof. vm_compute; reflexivity. Qed.
Example rt_slicelit_nested : parse_str (gprint 0 (ESliceLit (GTSlice GTInt) (ESliceLit GTInt (EInt 1 :: nil) :: nil)))
                  = Some (ESliceLit (GTSlice GTInt) (ESliceLit GTInt (EInt 1 :: nil) :: nil), nil).  (* [][]int{[]int{1}} *)
Proof. vm_compute; reflexivity. Qed.
(** map composite literal [map[K]V{..}] round-trips (the [EMapLit] node): empty, one/two KEYED pairs, a binop
    in key/value position, a non-scalar value type, and a NESTED map-valued literal.  The printed `k: v` / `, `
    separators carry spaces (gofmt-clean); the lexer skips them, so the round-trip recovers the AST exactly. *)
Example rt_maplit0 : parse_str (gprint 0 (EMapLit GTInt GTInt nil))
                  = Some (EMapLit GTInt GTInt nil, nil).  (* map[int]int{} *)
Proof. vm_compute; reflexivity. Qed.
Example rt_maplit1 : parse_str (gprint 0 (EMapLit GTInt GTInt ((EInt 1, EInt 2) :: nil)))
                  = Some (EMapLit GTInt GTInt ((EInt 1, EInt 2) :: nil), nil).  (* map[int]int{1: 2} *)
Proof. vm_compute; reflexivity. Qed.
Example rt_maplit2 : parse_str (gprint 0 (EMapLit GTString GTInt ((EX "a", EInt 1) :: (EX "b", EInt 2) :: nil)))
                  = Some (EMapLit GTString GTInt ((EX "a", EInt 1) :: (EX "b", EInt 2) :: nil), nil).  (* map[string]int{a: 1, b: 2} *)
Proof. vm_compute; reflexivity. Qed.
Example rt_maplit_binkv : parse_str (gprint 0 (EMapLit GTInt GTInt ((EBn BAdd (EX "x") (EInt 1), EBn BMul (EX "y") (EInt 2)) :: nil)))
                  = Some (EMapLit GTInt GTInt ((EBn BAdd (EX "x") (EInt 1), EBn BMul (EX "y") (EInt 2)) :: nil), nil).  (* map[int]int{x + 1: y*2} *)
Proof. vm_compute; reflexivity. Qed.
Example rt_maplit_slicev : parse_str (gprint 0 (EMapLit GTString (GTSlice GTInt) ((EX "k", ESliceLit GTInt (EInt 1 :: nil)) :: nil)))
                  = Some (EMapLit GTString (GTSlice GTInt) ((EX "k", ESliceLit GTInt (EInt 1 :: nil)) :: nil), nil).  (* map[string][]int{k: []int{1}} *)
Proof. vm_compute; reflexivity. Qed.
Example rt_maplit_nested : parse_str (gprint 0 (EMapLit GTInt (GTMap GTInt GTInt) ((EInt 1, EMapLit GTInt GTInt ((EInt 2, EInt 3) :: nil)) :: nil)))
                  = Some (EMapLit GTInt (GTMap GTInt GTInt) ((EInt 1, EMapLit GTInt GTInt ((EInt 2, EInt 3) :: nil)) :: nil), nil).  (* map[int]map[int]int{1: map[int]int{2: 3}} *)
Proof. vm_compute; reflexivity. Qed.

(** ---- THE CANONICAL TOKEN LIST ---- [gtokens ctx e] is the token list [gprint ctx e] lexes to.  Mirrors
    [gprint]'s structure exactly; [op_token]/[prefix_token] are the inverses of [infix_op]/[prefix_op].
    This is the bridge for the general round-trip: [lex (gprint ctx e) = Some (gtokens ctx e)] (lexer side)
    and [parse_expr F (gtokens ctx e ++ rest) = Some (e, rest)] (parser side), composed. *)
Definition op_token (o : BinOp) : Token :=
  match o with
  | BAdd => TPlus | BSub => TMinus | BMul => TStar | BDiv => TSlash | BRem => TPercent
  | BShl => TShl | BShr => TShr | BAnd => TAmp | BAndNot => TAndNot | BOr => TPipe | BXor => TCaret
  | BEq => TEq | BNe => TNe | BLt => TLt | BLe => TLe | BGt => TGt | BGe => TGe
  | BLAnd => TLand | BLOr => TLor
  end.
Definition prefix_token (o : UnaryOp) : Token :=
  match o with UNot => TBang | UXor => TCaret | UDeref => TStar | UAddr => TAmp | UNeg => TMinus end.

Fixpoint gtokens (ctx : nat) (e : GExpr) : list Token :=
  match e with
  | EId i  => TId i :: nil
  | EInt z => TInt z :: nil
  | EStr s => TStr s :: nil   (* mirrors [gprint]'s EStr: a string literal lexes to its single [TStr] token *)
  | EUn o e => match o with    (* EXHAUSTIVE (mirrors [gprint]'s EUn): a new unary op declares its tokens here *)
               | UNeg => TMinus :: TLP :: (gtokens 0 e ++ TRP :: nil)
               | UNot | UXor | UDeref | UAddr => prefix_token o :: TLP :: (gtokens 0 e ++ TRP :: nil)
               end
  | EBn o l r =>
      let p := binop_prec o in
      let inner := (gtokens p l ++ op_token o :: gtokens (S p) r)%list in
      if Nat.ltb p ctx then TLP :: (inner ++ TRP :: nil) else inner
  | ESel e0 f =>
      ((if op_needs_paren e0 then (TLP :: (gtokens 0 e0 ++ TRP :: nil))%list else gtokens 0 e0) ++ TDot :: TId f :: nil)%list
  | EIndex e0 i =>
      ((if op_needs_paren e0 then (TLP :: (gtokens 0 e0 ++ TRP :: nil))%list else gtokens 0 e0) ++ TLB :: (gtokens 0 i ++ TRB :: nil))%list
  | ESlice e0 lo hi =>
      ((if op_needs_paren e0 then (TLP :: (gtokens 0 e0 ++ TRP :: nil))%list else gtokens 0 e0) ++ TLB :: (gtokens 0 lo ++ TColon :: (gtokens 0 hi ++ TRB :: nil)))%list
  | ECall e0 args =>
      ((if op_needs_paren e0 then (TLP :: (gtokens 0 e0 ++ TRP :: nil))%list else gtokens 0 e0) ++ TLP :: ((match args with
                         | nil => nil
                         | a :: r => (gtokens 0 a ++ (fix gtt (m : list GExpr) : list Token :=
                                        match m with nil => nil | b :: m' => (TComma :: (gtokens 0 b ++ gtt m'))%list end) r)%list
                         end) ++ TRP :: nil))%list
  | EAssert e0 T =>
      ((if op_needs_paren e0 then (TLP :: (gtokens 0 e0 ++ TRP :: nil))%list else gtokens 0 e0) ++ TDot :: TLP :: (gttokens_ty T ++ TRP :: nil))%list
  | EConv c e0 =>
      (* mirrors [gprint]'s EConv: the conversion type's tokens, then '(' operand ')'. *)
      (gttokens_ty (convty_ty c) ++ TLP :: (gtokens 0 e0 ++ TRP :: nil))%list
  | ESliceLit t es =>
      (* mirrors [gprint]'s ESliceLit: '['']' then the element TYPE tokens, then '{' element-list '}'. The
         element list reuses the same LOCAL [fix] comma-join as [ECall]; [gtokens_ESliceLit] re-folds it onto
         the standalone [gtokens_args]. *)
      (TLB :: TRB :: (gttokens_ty t ++ TLC :: ((match es with
                         | nil => nil
                         | a :: r => (gtokens 0 a ++ (fix gtt (m : list GExpr) : list Token :=
                                        match m with nil => nil | b :: m' => (TComma :: (gtokens 0 b ++ gtt m'))%list end) r)%list
                         end) ++ TRC :: nil)))%list
  | EMapLit kt vt kvs =>
      (* mirrors [gprint]'s EMapLit: the [map[K]V] type tokens ([gttokens_ty (GTMap kt vt)]), then '{' the KEYED
         pair list '}'.  The lexer skips the printed spaces, so the tokens carry NO space — each pair is
         [gtokens 0 k ++ TColon :: gtokens 0 v], comma-joined; [gtokens_EMapLit] re-folds onto [gtokens_pairs]. *)
      (gttokens_ty (GTMap kt vt) ++ TLC :: ((match kvs with
                         | nil => nil
                         | p :: r => let (k, v) := p in (gtokens 0 k ++ TColon :: (gtokens 0 v ++ (fix gtp (m : list (GExpr * GExpr)) : list Token :=
                                        match m with nil => nil | q :: m' => let (k', v') := q in (TComma :: (gtokens 0 k' ++ TColon :: (gtokens 0 v' ++ gtp m')))%list end) r))%list
                         end) ++ TRC :: nil))%list
  end.
(** standalone arg-token list (mirrors the local [fix] in [gtokens]'s ECall case); [gtokens_ECall] bridges. *)
Fixpoint gtokens_args_tl (args : list GExpr) : list Token :=
  match args with nil => nil | b :: m => (TComma :: (gtokens 0 b ++ gtokens_args_tl m))%list end.
Definition gtokens_args (args : list GExpr) : list Token :=
  match args with nil => nil | a :: r => (gtokens 0 a ++ gtokens_args_tl r)%list end.
(** standalone KEYED pair-token list (mirrors the local [fix] in [gtokens]'s EMapLit case): per pair
    [gtokens 0 k ++ TColon :: gtokens 0 v], comma-joined; [gtokens_EMapLit] bridges. *)
Fixpoint gtokens_pairs_tl (kvs : list (GExpr * GExpr)) : list Token :=
  match kvs with nil => nil | p :: m => let (k, v) := p in (TComma :: (gtokens 0 k ++ TColon :: (gtokens 0 v ++ gtokens_pairs_tl m)))%list end.
Definition gtokens_pairs (kvs : list (GExpr * GExpr)) : list Token :=
  match kvs with nil => nil | p :: r => let (k, v) := p in (gtokens 0 k ++ TColon :: (gtokens 0 v ++ gtokens_pairs_tl r))%list end.

(** token analog of [gparen] + the re-fold lemmas (mirror [gprint_ESel]/[gprint_EIndex]). *)
Definition gtparen (e0 : GExpr) : list Token :=
  if op_needs_paren e0 then (TLP :: (gtokens 0 e0 ++ TRP :: nil))%list else gtokens 0 e0.
Lemma gtokens_ESel : forall ctx e0 f, gtokens ctx (ESel e0 f) = (gtparen e0 ++ TDot :: TId f :: nil)%list.
Proof. reflexivity. Qed.
Lemma gtokens_EIndex : forall ctx e0 i, gtokens ctx (EIndex e0 i) = (gtparen e0 ++ TLB :: (gtokens 0 i ++ TRB :: nil))%list.
Proof. reflexivity. Qed.
Lemma gtokens_ESlice : forall ctx e0 lo hi,
  gtokens ctx (ESlice e0 lo hi) = (gtparen e0 ++ TLB :: (gtokens 0 lo ++ TColon :: (gtokens 0 hi ++ TRB :: nil)))%list.
Proof. reflexivity. Qed.
Lemma gtokens_EAssert : forall ctx e0 T,
  gtokens ctx (EAssert e0 T) = (gtparen e0 ++ TDot :: TLP :: (gttokens_ty T ++ TRP :: nil))%list.
Proof. reflexivity. Qed.
Lemma gtokens_EConv : forall ctx c e0,
  gtokens ctx (EConv c e0) = (gttokens_ty (convty_ty c) ++ TLP :: (gtokens 0 e0 ++ TRP :: nil))%list.
Proof. reflexivity. Qed.
Lemma gtt_eq : forall m,
  (fix gtt (m0 : list GExpr) : list Token :=
     match m0 with nil => nil | b :: m' => (TComma :: (gtokens 0 b ++ gtt m'))%list end) m = gtokens_args_tl m.
Proof. induction m as [ | b m IH ]; [ reflexivity | cbn [gtokens_args_tl]; rewrite <- IH; reflexivity ]. Qed.
Lemma gtokens_ECall : forall ctx e0 args,
  gtokens ctx (ECall e0 args) = (gtparen e0 ++ TLP :: (gtokens_args args ++ TRP :: nil))%list.
Proof.
  intros ctx e0 args. unfold gtokens_args.
  change (gtokens ctx (ECall e0 args))
    with (gtparen e0 ++ TLP :: ((match args with
                                 | nil => nil
                                 | a :: r => (gtokens 0 a ++ (fix gtt (m : list GExpr) : list Token :=
                                                match m with nil => nil | b :: m' => (TComma :: (gtokens 0 b ++ gtt m'))%list end) r)%list
                                 end) ++ TRP :: nil))%list.
  destruct args as [ | a r ]; [ reflexivity | rewrite gtt_eq; reflexivity ].
Qed.
(** the local [fix] in [gtokens]'s ESliceLit case computes exactly the standalone [gtokens_args_tl]/[gtokens_args];
    [gtokens_ESliceLit] re-folds the brace-delimited element list onto [gtokens_args]. *)
Lemma gtokens_ESliceLit : forall ctx t es,
  gtokens ctx (ESliceLit t es) = (TLB :: TRB :: (gttokens_ty t ++ TLC :: (gtokens_args es ++ TRC :: nil)))%list.
Proof.
  intros ctx t es. unfold gtokens_args.
  change (gtokens ctx (ESliceLit t es))
    with (TLB :: TRB :: (gttokens_ty t ++ TLC :: ((match es with
                         | nil => nil
                         | a :: r => (gtokens 0 a ++ (fix gtt (m : list GExpr) : list Token :=
                                        match m with nil => nil | b :: m' => (TComma :: (gtokens 0 b ++ gtt m'))%list end) r)%list
                         end) ++ TRC :: nil)))%list.
  destruct es as [ | a r ]; [ reflexivity | rewrite gtt_eq; reflexivity ].
Qed.
(** the local [fix] in [gtokens]'s EMapLit case computes exactly the standalone [gtokens_pairs_tl]/[gtokens_pairs]. *)
Lemma gtp_eq : forall m,
  (fix gtp (m0 : list (GExpr * GExpr)) : list Token :=
     match m0 with nil => nil | q :: m' => let (k', v') := q in (TComma :: (gtokens 0 k' ++ TColon :: (gtokens 0 v' ++ gtp m')))%list end) m = gtokens_pairs_tl m.
Proof. induction m as [ | [k v] m IH ]; [ reflexivity | cbn [gtokens_pairs_tl]; rewrite <- IH; reflexivity ]. Qed.
Lemma gtokens_EMapLit : forall ctx kt vt kvs,
  gtokens ctx (EMapLit kt vt kvs) = (gttokens_ty (GTMap kt vt) ++ TLC :: (gtokens_pairs kvs ++ TRC :: nil))%list.
Proof.
  intros ctx kt vt kvs. unfold gtokens_pairs.
  change (gtokens ctx (EMapLit kt vt kvs))
    with (gttokens_ty (GTMap kt vt) ++ TLC :: ((match kvs with
                         | nil => nil
                         | p :: r => let (k, v) := p in (gtokens 0 k ++ TColon :: (gtokens 0 v ++ (fix gtp (m : list (GExpr * GExpr)) : list Token :=
                                        match m with nil => nil | q :: m' => let (k', v') := q in (TComma :: (gtokens 0 k' ++ TColon :: (gtokens 0 v' ++ gtp m')))%list end) r))%list
                         end) ++ TRC :: nil))%list.
  destruct kvs as [ | [k v] r ]; [ reflexivity | rewrite gtp_eq; reflexivity ].
Qed.

(** [op_token]/[prefix_token] really invert the parser's token classifiers. *)
Lemma infix_op_token : forall o, infix_op (op_token o) = Some o.
Proof. destruct o; reflexivity. Qed.

(** [gtokens] is the RIGHT spec: it is exactly what [lex (gprint ctx e)] yields (validated; the universal
    lemma [lex (gprint ctx e) = Some (gtokens ctx e)] is the next step). *)
Example gtok_add  : lex (gprint 0 (EBn BAdd (EX "a") (EX "b"))) = Some (gtokens 0 (EBn BAdd (EX "a") (EX "b"))).
Proof. vm_compute; reflexivity. Qed.
Example gtok_wrap : lex (gprint 0 (EBn BMul (EBn BAdd (EX "a") (EX "b")) (EX "c")))
                  = Some (gtokens 0 (EBn BMul (EBn BAdd (EX "a") (EX "b")) (EX "c"))).
Proof. vm_compute; reflexivity. Qed.
Example gtok_un   : lex (gprint 0 (EUn UNot (EBn BEq (EX "a") (EX "b"))))
                  = Some (gtokens 0 (EUn UNot (EBn BEq (EX "a") (EX "b")))).
Proof. vm_compute; reflexivity. Qed.
Example gtok_neg  : lex (gprint 0 (EUn UNeg (EX "x"))) = Some (gtokens 0 (EUn UNeg (EX "x"))).
Proof. vm_compute; reflexivity. Qed.
(* the hazard, at the lexer level: [lex (gprint ..)] still equals [gtokens ..] for nested bare unaries —
   the direct witness at each dangerous maximal-munch seam ("&&" -> TLand, "&^" -> TAndNot). *)
Example gtok_addr_addr : lex (gprint 0 (EUn UAddr (EUn UAddr (EX "x"))))
                       = Some (gtokens 0 (EUn UAddr (EUn UAddr (EX "x")))).
Proof. vm_compute; reflexivity. Qed.
Example gtok_addr_xor  : lex (gprint 0 (EUn UAddr (EUn UXor (EX "x"))))
                       = Some (gtokens 0 (EUn UAddr (EUn UXor (EX "x")))).
Proof. vm_compute; reflexivity. Qed.

(** ---- M3b GROUNDWORK: lexer fuel MONOTONICITY ---- adding fuel never changes a [Some] answer.  Needed to
    bridge the fuel when composing [lex] over a concatenation (the per-token decrement makes [S (length s)]
    exact, so a sub-lex with more-than-enough fuel still agrees).  Induction on [f]; each char-step recurses
    with the same discriminants, so the [Some] result is preserved by the IH on the tail. *)
Lemma lex_aux_mono : forall f s ts f',
  lex_aux f s = Some ts -> f <= f' -> lex_aux f' s = Some ts.
Proof.
  induction f as [ | f IH ]; intros s ts f' H Hle; [ discriminate H | ].
  destruct f' as [ | f' ]; [ lia | ].
  assert (Hle' : f <= f') by lia.
  destruct s as [ | c s' ]; [ exact H | ].
  cbn [lex_aux] in H |- *.
  destruct (is_space c).
  { exact (IH _ _ _ H Hle'). }
  destruct (is_idstart c).
  { destruct (scan_id (String c s')) as [tok rest].
    destruct (lex_ident tok) as [t | ]; [ | exact H ].
    destruct (lex_aux f rest) as [l | ] eqn:E; [ | discriminate H ].
    rewrite (IH _ _ _ E Hle'); exact H. }
  destruct (is_dec_char c).
  { destruct (scan_digits (String c s')) as [num rest].
    destruct (lex_aux f rest) as [l | ] eqn:E; [ | discriminate H ].
    rewrite (IH _ _ _ E Hle'); exact H. }
  destruct (andb (Ascii.eqb c (ch 45)) (match s' with String d _ => is_dec_char d | _ => false end)).
  { destruct (scan_digits s') as [num rest].
    destruct (lex_aux f rest) as [l | ] eqn:E; [ | discriminate H ].
    rewrite (IH _ _ _ E Hle'); exact H. }
  destruct (Ascii.eqb c (ch 34)).
  { (* string-literal branch: the body scan + the fail-closed [unescape_opt] are fuel-independent, only the
       tail re-lex uses the IH (a malformed body gives [None] regardless of fuel) *)
    destruct (scan_quote s') as [[body rest] | ]; [ | exact H ].
    destruct (unescape_opt body) as [sdec | ]; [ | exact H ].
    destruct (lex_aux f rest) as [l | ] eqn:E; [ | discriminate H ].
    rewrite (IH _ _ _ E Hle'); exact H. }
  { destruct (lex_op c s') as [[t rest] | ]; [ | exact H ].
    destruct (lex_aux f rest) as [l | ] eqn:E; [ | discriminate H ].
    rewrite (IH _ _ _ E Hle'); exact H. }
Qed.

(** ---- M3b: the LEXER ROUND-TRIP groundwork ---- the seam predicate + the scanner-splitting lemmas.
    [clean_start rest] = the next char cannot EXTEND an identifier/number token (it is not an id-char), so
    a token ending just before [rest] is complete — exactly the boundary [gprint] emits between subtrees
    (a space, a ')', or end-of-string).  This is the two-sided seam condition the round-trip needs. *)
Definition clean_start (rest : string) : bool :=
  match rest with EmptyString => true | String c _ => negb (is_idc c) end.

Lemma is_dec_char_is_idc : forall c, is_dec_char c = true -> is_idc c = true.
Proof.
  intro c. unfold is_dec_char, is_idc. intro H. apply andb_prop in H.
  destruct H as [H1 H2]. rewrite H1, H2. reflexivity.
Qed.

(** A clean-start string scans NO identifier / NO digit run — the scanners stop immediately. *)
Lemma scan_id_clean : forall b, clean_start b = true -> scan_id b = (EmptyString, b).
Proof.
  intros [ | c b' ] H; [ reflexivity | ].
  unfold clean_start in H. cbn [scan_id]. destruct (is_idc c); [ discriminate H | reflexivity ].
Qed.

Lemma scan_digits_clean : forall b, clean_start b = true -> scan_digits b = (EmptyString, b).
Proof.
  intros [ | c b' ] H; [ reflexivity | ].
  unfold clean_start in H. cbn [scan_digits]. destruct (is_dec_char c) eqn:E; [ | reflexivity ].
  apply is_dec_char_is_idc in E. rewrite E in H. discriminate H.
Qed.

(** [scan_id] / [scan_digits] split an all-id / all-decimal PREFIX off a clean-start REST exactly. *)
Lemma scan_id_app : forall a b, all_idc a = true -> clean_start b = true -> scan_id (a ++ b) = (a, b).
Proof.
  induction a as [ | c a' IH ]; intros b Ha Hb.
  - apply scan_id_clean; exact Hb.
  - cbn [all_idc] in Ha. apply andb_prop in Ha. destruct Ha as [Hc Ha'].
    cbn [String.append scan_id]. rewrite Hc. rewrite (IH b Ha' Hb). reflexivity.
Qed.

Lemma scan_digits_app : forall a b, all_dec a = true -> clean_start b = true -> scan_digits (a ++ b) = (a, b).
Proof.
  induction a as [ | c a' IH ]; intros b Ha Hb.
  - apply scan_digits_clean; exact Hb.
  - cbn [all_dec] in Ha. apply andb_prop in Ha. destruct Ha as [Hc Ha'].
    cbn [String.append scan_digits]. rewrite Hc. rewrite (IH b Ha' Hb). reflexivity.
Qed.

(** An identifier-start char is never a space. *)
Lemma is_idstart_not_space : forall c, is_idstart c = true -> is_space c = false.
Proof.
  intro c. unfold is_space. intro H.
  destruct (Ascii.eqb c (ascii_of_nat 32)) eqn:E; [ | reflexivity ].
  exfalso. apply Ascii.eqb_eq in E. subst c. vm_compute in H. discriminate H.
Qed.

(** [lex_ident] on a [go_ident] string yields exactly [TId] of that ident (the keyword guards do not fire
    — a [go_ident] is never a keyword — and the [bool_dec] proof equals the carried one by UIP-on-bool). *)
Lemma lex_ident_go : forall s (Hs : go_ident s = true), lex_ident s = Some (TId (exist _ s Hs)).
Proof.
  intros s Hs. unfold lex_ident.
  destruct (String.eqb s "func") eqn:Ef.
  { apply String.eqb_eq in Ef. subst s. vm_compute in Hs. discriminate Hs. }
  destruct (String.eqb s "return") eqn:Er.
  { apply String.eqb_eq in Er. subst s. vm_compute in Hs. discriminate Hs. }
  destruct (String.eqb s "chan") eqn:Ec.
  { apply String.eqb_eq in Ec. subst s. vm_compute in Hs. discriminate Hs. }
  destruct (String.eqb s "map") eqn:Em.
  { apply String.eqb_eq in Em. subst s. vm_compute in Hs. discriminate Hs. }
  destruct (bool_dec (go_ident s) true) as [H | H].
  - assert (E : H = Hs) by apply (Eqdep_dec.UIP_dec bool_dec). rewrite E. reflexivity.
  - exfalso. apply H. exact Hs.
Qed.

(** LEAF (identifier): lexing [gprint (EId i) ++ rest = proj1_sig i ++ rest] yields [TId i] then [rest]'s
    tokens — given a clean seam and enough fuel.  ([gtokens (EId i) = [TId i]].) *)
Lemma lex_gprint_id : forall (i : Ident) rest fuel tr,
  clean_start rest = true ->
  lex_aux (S (String.length rest)) rest = Some tr ->
  S (String.length (proj1_sig i) + String.length rest) <= fuel ->
  lex_aux fuel (proj1_sig i ++ rest) = Some (TId i :: tr).
Proof.
  intros [s Hs] rest fuel tr Hclean Hrest Hfuel. simpl proj1_sig in *.
  destruct s as [ | c0 s0 ]; [ vm_compute in Hs; discriminate Hs | ].
  destruct fuel as [ | f ]; [ cbn in Hfuel; lia | ].
  pose proof Hs as Hgo. unfold go_ident in Hgo. apply andb_prop in Hgo. destruct Hgo as [Hia _].
  apply andb_prop in Hia. destruct Hia as [Hidstart Hallidc].
  cbn [lex_aux String.append].
  rewrite (is_idstart_not_space _ Hidstart), Hidstart.
  replace (scan_id (String c0 (s0 ++ rest))) with (String c0 s0, rest)
    by (symmetry; apply (scan_id_app (String c0 s0) rest Hallidc Hclean)).
  rewrite (lex_ident_go (String c0 s0) Hs).
  assert (Hle : S (String.length rest) <= f) by (cbn in Hfuel; lia).
  rewrite (lex_aux_mono _ _ _ _ Hrest Hle). reflexivity.
Qed.

(** Digit-shape facts for the integer leaf (proved from scratch for GoPrint). *)
Lemma is_dec_char_dec_digit : forall n, (n < 10)%nat -> is_dec_char (dec_digit n) = true.
Proof.
  intros n Hn. unfold dec_digit, is_dec_char.
  rewrite Ascii.nat_ascii_embedding by lia.
  apply andb_true_intro. split; apply Nat.leb_le; lia.
Qed.

Lemma all_dec_z_digits : forall fuel z acc, (0 <= z)%Z -> all_dec acc = true ->
  all_dec (z_digits fuel z acc) = true.
Proof.
  induction fuel as [ | f IH ]; intros z acc Hz Hacc; [ exact Hacc | ].
  cbn [z_digits].
  assert (Hd : is_dec_char (dec_digit (Z.to_nat (z mod 10))) = true).
  { apply is_dec_char_dec_digit.
    assert (0 <= z mod 10 < 10)%Z by (apply Z.mod_pos_bound; lia). lia. }
  destruct (z / 10 =? 0)%Z.
  - cbn [all_dec]. rewrite Hd. exact Hacc.
  - apply IH; [ apply Z.div_pos; lia | cbn [all_dec]; rewrite Hd; exact Hacc ].
Qed.

Lemma is_dec_char_not_idstart : forall c, is_dec_char c = true -> is_idstart c = false.
Proof.
  intros c H. unfold is_dec_char in H. apply andb_prop in H. destruct H as [H1 H2].
  apply Nat.leb_le in H1, H2. unfold is_idstart; cbv zeta.
  assert (E1 : Nat.leb 65 (nat_of_ascii c) = false) by (apply Nat.leb_gt; lia).
  assert (E2 : Nat.leb 97 (nat_of_ascii c) = false) by (apply Nat.leb_gt; lia).
  assert (E3 : Nat.eqb (nat_of_ascii c) 95 = false) by (apply Nat.eqb_neq; lia).
  rewrite E1, E2, E3. reflexivity.
Qed.

Lemma is_dec_char_not_space : forall c, is_dec_char c = true -> is_space c = false.
Proof.
  intros c H. unfold is_dec_char in H. apply andb_prop in H. destruct H as [H1 H2].
  apply Nat.leb_le in H1. unfold is_space.
  destruct (Ascii.eqb c (ascii_of_nat 32)) eqn:E; [ | reflexivity ].
  exfalso. apply Ascii.eqb_eq in E. subst c.
  rewrite Ascii.nat_ascii_embedding in H1 by lia. lia.
Qed.

(** [z_digits] (with [S]-fuel from an empty accumulator) is non-empty — every print_Z digit run has a
    leading digit, so the lexer's first-char dispatch sees a [is_dec_char]. *)
Lemma z_digits_acc_ne : forall f z acc, acc <> EmptyString -> z_digits f z acc <> EmptyString.
Proof.
  induction f as [ | f IH ]; intros z acc Hacc; [ exact Hacc | ].
  cbn [z_digits]. destruct (z / 10 =? 0)%Z; [ discriminate | apply IH; discriminate ].
Qed.

Lemma z_digits_S_ne : forall f z, z_digits (S f) z EmptyString <> EmptyString.
Proof.
  intros f z. cbn [z_digits]. destruct (z / 10 =? 0)%Z; [ discriminate | apply z_digits_acc_ne; discriminate ].
Qed.

(** Lexing a non-empty all-decimal run [D] (no leading '-') yields [TInt (parse_Z D)] then [rest]. *)
Lemma lex_pos_dec : forall D rest fuel tr,
  all_dec D = true -> D <> EmptyString -> clean_start rest = true ->
  lex_aux (S (String.length rest)) rest = Some tr ->
  S (String.length D + String.length rest) <= fuel ->
  lex_aux fuel (D ++ rest) = Some (TInt (parse_Z D) :: tr).
Proof.
  intros D rest fuel tr Hdec Hne Hclean Hrest Hfuel.
  destruct D as [ | d0 D' ]; [ contradiction | ].
  cbn [all_dec] in Hdec. apply andb_prop in Hdec. destruct Hdec as [Hd0 HD'].
  destruct fuel as [ | f ]; [ cbn in Hfuel; lia | ].
  assert (HdecD : all_dec (String d0 D') = true) by (cbn [all_dec]; rewrite Hd0; exact HD').
  cbn [lex_aux String.append].
  rewrite (is_dec_char_not_space _ Hd0), (is_dec_char_not_idstart _ Hd0), Hd0.
  replace (scan_digits (String d0 (D' ++ rest))) with (String d0 D', rest)
    by (symmetry; change (String d0 (D' ++ rest)) with ((String d0 D') ++ rest);
        apply (scan_digits_app (String d0 D') rest HdecD Hclean)).
  assert (Hle : S (String.length rest) <= f) by (cbn in Hfuel; lia).
  rewrite (lex_aux_mono _ _ _ _ Hrest Hle). reflexivity.
Qed.

(** Lexing a NEGATIVE literal ['-' ++ D] (D a non-empty all-decimal run) yields [TInt (parse_Z ('-'++D))]
    via the lexer's negative-literal branch (binary '-' is always SPACED in the printer, so an unspaced
    '-'+digit is unambiguously a literal). *)
Lemma lex_neg_dec : forall D rest fuel tr,
  all_dec D = true -> D <> EmptyString -> clean_start rest = true ->
  lex_aux (S (String.length rest)) rest = Some tr ->
  S (S (String.length D) + String.length rest) <= fuel ->
  lex_aux fuel (String (ch 45) D ++ rest) = Some (TInt (parse_Z (String (ch 45) D)) :: tr).
Proof.
  intros D rest fuel tr Hdec Hne Hclean Hrest Hfuel.
  destruct D as [ | d0 D' ]; [ contradiction | ].
  cbn [all_dec] in Hdec. apply andb_prop in Hdec. destruct Hdec as [Hd0 HD'].
  destruct fuel as [ | f ]; [ cbn in Hfuel; lia | ].
  assert (HdecD : all_dec (String d0 D') = true) by (cbn [all_dec]; rewrite Hd0; exact HD').
  cbn [lex_aux String.append].
  replace (is_space (ch 45)) with false by reflexivity.
  replace (is_idstart (ch 45)) with false by reflexivity.
  replace (is_dec_char (ch 45)) with false by reflexivity.
  replace (Ascii.eqb (ch 45) (ch 45)) with true by reflexivity.
  rewrite Hd0.
  replace (scan_digits (String d0 (D' ++ rest))) with (String d0 D', rest)
    by (symmetry; change (String d0 (D' ++ rest)) with ((String d0 D') ++ rest);
        apply (scan_digits_app (String d0 D') rest HdecD Hclean)).
  assert (Hle : S (String.length rest) <= f) by (cbn in Hfuel; lia).
  rewrite (lex_aux_mono _ _ _ _ Hrest Hle). reflexivity.
Qed.

(** LEAF (integer): lexing [gprint (EInt z) ++ rest = print_Z z ++ rest] yields [TInt z] then [rest].
    Case on [print_Z]'s shape (0 / positive digits / '-'+digits) via the reflect views (which also reduce
    the [if]s); recover [z] from the scanned run by [print_parse_Z]. *)
Lemma lex_gprint_int : forall z rest fuel tr,
  clean_start rest = true ->
  lex_aux (S (String.length rest)) rest = Some tr ->
  S (String.length (print_Z z) + String.length rest) <= fuel ->
  lex_aux fuel (print_Z z ++ rest) = Some (TInt z :: tr).
Proof.
  intros z rest fuel tr Hclean Hrest Hfuel.
  replace (TInt z) with (TInt (parse_Z (print_Z z))) by (rewrite print_parse_Z; reflexivity).
  unfold print_Z in *.
  destruct (Z.eqb_spec z 0) as [Heq | Hne].
  - apply lex_pos_dec; [ reflexivity | discriminate | exact Hclean | exact Hrest | exact Hfuel ].
  - destruct (Z.ltb_spec z 0) as [Hlt | Hge].
    + change (("-" ++ z_digits (digit_fuel (- z)) (- z) "")%string)
        with (String (ch 45) (z_digits (digit_fuel (- z)) (- z) "")) in *.
      apply lex_neg_dec;
        [ apply all_dec_z_digits; [ lia | reflexivity ]
        | unfold digit_fuel; apply z_digits_S_ne | exact Hclean | exact Hrest | exact Hfuel ].
    + apply lex_pos_dec;
        [ apply all_dec_z_digits; [ lia | reflexivity ]
        | unfold digit_fuel; apply z_digits_S_ne | exact Hclean | exact Hrest | exact Hfuel ].
Qed.

(** BINOP SEAM: [binop_text o] is [" op "] (spaced both sides), so lexing [binop_text o ++ X] skips the
    leading space, lexes the operator to [op_token o], skips the trailing space, and continues on [X] —
    3 lexer steps, then [X].  The trailing space isolates [X] (no constraint on its head). *)
Lemma lex_binop_app : forall o X fuel tX,
  lex_aux (S (String.length X)) X = Some tX ->
  S (String.length (binop_text o) + String.length X) <= fuel ->
  lex_aux fuel (binop_text o ++ X) = Some (op_token o :: tX).
Proof.
  intros o X fuel tX HX Hfuel.
  destruct o; cbn [binop_text] in Hfuel;
    do 3 (destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ]);
    cbn;
    rewrite (lex_aux_mono _ _ _ _ HX) by (cbn in Hfuel; lia);
    reflexivity.
Qed.

(** Single-char delimiter seams: '(' -> TLP, ')' -> TRP (one lexer step), and the [UNeg] prefix "-(" ->
    TMinus, TLP (two steps — '-' followed by '(' is NOT a negative literal, so it lexes as TMinus). *)
Lemma lex_lparen_app : forall X fuel tX,
  lex_aux (S (String.length X)) X = Some tX -> S (S (String.length X)) <= fuel ->
  lex_aux fuel (String (ch 40) X) = Some (TLP :: tX).
Proof.
  intros X fuel tX HX Hfuel. destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ].
  cbn. rewrite (lex_aux_mono _ _ _ _ HX) by (cbn in Hfuel; lia). reflexivity.
Qed.

Lemma lex_rparen_app : forall X fuel tX,
  lex_aux (S (String.length X)) X = Some tX -> S (S (String.length X)) <= fuel ->
  lex_aux fuel (String (ch 41) X) = Some (TRP :: tX).
Proof.
  intros X fuel tX HX Hfuel. destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ].
  cbn. rewrite (lex_aux_mono _ _ _ _ HX) by (cbn in Hfuel; lia). reflexivity.
Qed.

Lemma lex_minuslp_app : forall X fuel tX,
  lex_aux (S (String.length X)) X = Some tX -> S (S (S (String.length X))) <= fuel ->
  lex_aux fuel (String (ch 45) (String (ch 40) X)) = Some (TMinus :: TLP :: tX).
Proof.
  intros X fuel tX HX Hfuel. do 2 (destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ]).
  cbn. rewrite (lex_aux_mono _ _ _ _ HX) by (cbn in Hfuel; lia). reflexivity.
Qed.

(** KEYWORD SEAM: the printed prefix "return " lexes to the reserved [TReturn] token (scan_id reads the
    maximal idc run "return", [lex_ident] classifies it as the keyword, then the trailing space is skipped) —
    so the rest [X] lexes unchanged after it.  This is the [GsReturnVal] analogue of [lex_binop_app]; it is
    what makes a [return e] statement DISJOINT from any expression statement at the lexer level (the leading
    [TReturn] is rejected by the expression parser). *)
Lemma lex_return_app : forall X fuel tX,
  lex_aux (S (String.length X)) X = Some tX ->
  S (String.length ("return " ++ X)) <= fuel ->
  lex_aux fuel ("return " ++ X)%string = Some (TReturn :: tX).
Proof.
  intros X fuel tX HX Hfuel.
  assert (Hr : is_idstart "r"%char = true) by (vm_compute; reflexivity).
  assert (Hsp : is_space " "%char = true) by (vm_compute; reflexivity).
  do 2 (destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ]).
  (* keep "return" and the trailing space as appends so [scan_id_app] applies (don't fully unfold append) *)
  change ("return " ++ X)%string with (String "r"%char ("eturn" ++ String " "%char X))%string.
  cbn [lex_aux].
  rewrite (is_idstart_not_space _ Hr), Hr.
  replace (scan_id (String "r"%char ("eturn" ++ String " "%char X)))
     with ("return"%string, String " "%char X)
     by (symmetry; apply (scan_id_app "return"%string (String " "%char X) eq_refl eq_refl)).
  cbn [lex_aux lex_ident String.eqb Ascii.eqb].
  rewrite Hsp.
  rewrite (lex_aux_mono _ _ _ _ HX) by (cbn in Hfuel; lia). reflexivity.
Qed.

(** BARE-UNOP SEAM (after the [gprint] change to always parenthesise a bare-unary operand): [unop_text o]
    (o <> UNeg) is a single char ['!'/'^'/'*'/'&'] ALWAYS followed by '(' — a CONCRETE char that can never
    maximal-munch into a 2-char operator — so it lexes to [prefix_token o] then TLP then [X].  No
    first-char side condition is needed because the next char is fixed. *)
Lemma lex_unop_lp_app : forall o X fuel tX,
  o <> UNeg ->
  lex_aux (S (String.length X)) X = Some tX ->
  S (S (S (String.length X))) <= fuel ->
  lex_aux fuel (unop_text o ++ String (ch 40) X) = Some (prefix_token o :: TLP :: tX).
Proof.
  intros o X fuel tX HoNeg HX Hfuel.
  destruct o; try (exfalso; apply HoNeg; reflexivity);
    do 2 (destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ]);
    cbn; rewrite (lex_aux_mono _ _ _ _ HX) by (cbn in Hfuel; lia); reflexivity.
Qed.

Lemma length_app : forall a b, String.length (a ++ b) = String.length a + String.length b.
Proof. induction a as [ | c a' IH ]; intro b; [ reflexivity | cbn; rewrite IH; reflexivity ]. Qed.

(** Every [binop_text] starts with a space, so the seam after it is clean. *)
Lemma clean_start_binop : forall o X, clean_start (binop_text o ++ X) = true.
Proof. destruct o; reflexivity. Qed.

Lemma str_app_assoc : forall a b c, ((a ++ b) ++ c = a ++ (b ++ c))%string.
Proof. induction a as [ | x a' IH ]; intros b c; [ reflexivity | cbn; rewrite IH; reflexivity ]. Qed.

Lemma str_app_nil_r : forall s, (s ++ "" = s)%string.
Proof. induction s as [ | c s' IH ]; [ reflexivity | cbn; rewrite IH; reflexivity ]. Qed.

(** LEAF (string): lexing [gprint (EStr s) ++ rest = print_string_lit s ++ rest] yields [TStr s] then [rest].
    The opening dquote selects the string branch; [scan_quote_esc_string] recovers the escaped body + [rest];
    [esc_string_roundtrip_opt] VALIDATES+decodes the body back to [Some s] (the escaped body is well-formed by
    construction, so the option decoder never rejects it).  The closing dquote self-terminates, so [clean_start
    rest] is NOT needed (it is kept only for a signature uniform with the other leaf lemmas). *)
Lemma lex_gprint_str : forall s rest fuel tr,
  clean_start rest = true ->
  lex_aux (S (String.length rest)) rest = Some tr ->
  S (String.length (print_string_lit s) + String.length rest) <= fuel ->
  lex_aux fuel (print_string_lit s ++ rest) = Some (TStr s :: tr).
Proof.
  intros s rest fuel tr _ Hrest Hfuel.
  destruct fuel as [ | f ]; [ cbn [String.length print_string_lit] in Hfuel; lia | ].
  unfold print_string_lit.
  replace (((String (ch 34) (esc_string s ++ String (ch 34) "")) ++ rest)%string)
     with (String (ch 34) (esc_string s ++ String (ch 34) rest))
     by (cbn [append]; rewrite str_app_assoc; cbn [append]; reflexivity).
  cbn [lex_aux].
  replace (is_space (ch 34))   with false by reflexivity.
  replace (is_idstart (ch 34)) with false by reflexivity.
  replace (is_dec_char (ch 34)) with false by reflexivity.
  replace (Ascii.eqb (ch 34) (ch 45)) with false by reflexivity.
  replace (Ascii.eqb (ch 34) (ch 34)) with true by reflexivity.
  cbn [andb].
  rewrite scan_quote_esc_string. cbv beta iota. rewrite esc_string_roundtrip_opt. cbv beta iota.
  assert (Hp : 1 <= String.length (print_string_lit s))
    by (unfold print_string_lit; cbn [String.length]; lia).
  assert (Hle : S (String.length rest) <= f) by lia.
  rewrite (lex_aux_mono _ _ _ _ Hrest Hle). reflexivity.
Qed.

(** SELECTOR-DOT SEAM: '.' (ch 46) is a single delimiter char — never id/digit/space, [lex_op] maps it
    to [TDot] — so it lexes to [TDot] then [X] (like the paren seams). *)
Lemma lex_dot_app : forall X fuel tX,
  lex_aux (S (String.length X)) X = Some tX -> S (S (String.length X)) <= fuel ->
  lex_aux fuel (String (ch 46) X) = Some (TDot :: tX).
Proof.
  intros X fuel tX HX Hfuel. destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ].
  cbn. rewrite (lex_aux_mono _ _ _ _ HX) by (cbn in Hfuel; lia). reflexivity.
Qed.

(** INDEX-BRACKET SEAMS: '[' (ch 91) → TLB and ']' (ch 93) → TRB are single delimiter chars (like parens). *)
Lemma lex_lbrack_app : forall X fuel tX,
  lex_aux (S (String.length X)) X = Some tX -> S (S (String.length X)) <= fuel ->
  lex_aux fuel (String (ch 91) X) = Some (TLB :: tX).
Proof.
  intros X fuel tX HX Hfuel. destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ].
  cbn. rewrite (lex_aux_mono _ _ _ _ HX) by (cbn in Hfuel; lia). reflexivity.
Qed.
Lemma lex_rbrack_app : forall X fuel tX,
  lex_aux (S (String.length X)) X = Some tX -> S (S (String.length X)) <= fuel ->
  lex_aux fuel (String (ch 93) X) = Some (TRB :: tX).
Proof.
  intros X fuel tX HX Hfuel. destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ].
  cbn. rewrite (lex_aux_mono _ _ _ _ HX) by (cbn in Hfuel; lia). reflexivity.
Qed.
(** COMPOSITE-BRACE SEAMS: '{' (ch 123) → TLC and '}' (ch 125) → TRC are single delimiter chars (like the
    index brackets); used by the slice-composite-literal [[]T{..}] round-trip. *)
Lemma lex_lbrace_app : forall X fuel tX,
  lex_aux (S (String.length X)) X = Some tX -> S (S (String.length X)) <= fuel ->
  lex_aux fuel (String (ch 123) X) = Some (TLC :: tX).
Proof.
  intros X fuel tX HX Hfuel. destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ].
  cbn. rewrite (lex_aux_mono _ _ _ _ HX) by (cbn in Hfuel; lia). reflexivity.
Qed.
Lemma lex_rbrace_app : forall X fuel tX,
  lex_aux (S (String.length X)) X = Some tX -> S (S (String.length X)) <= fuel ->
  lex_aux fuel (String (ch 125) X) = Some (TRC :: tX).
Proof.
  intros X fuel tX HX Hfuel. destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ].
  cbn. rewrite (lex_aux_mono _ _ _ _ HX) by (cbn in Hfuel; lia). reflexivity.
Qed.
(** SLICE-COLON SEAM: ':' (ch 58) → TColon, a single delimiter char (like the brackets). *)
Lemma lex_colon_app : forall X fuel tX,
  lex_aux (S (String.length X)) X = Some tX -> S (S (String.length X)) <= fuel ->
  lex_aux fuel (String (ch 58) X) = Some (TColon :: tX).
Proof.
  intros X fuel tX HX Hfuel. destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ].
  cbn. rewrite (lex_aux_mono _ _ _ _ HX) by (cbn in Hfuel; lia). reflexivity.
Qed.
(** CALL-COMMA SEAM: ',' (ch 44) → TComma, a single delimiter char. *)
Lemma lex_comma_app : forall X fuel tX,
  lex_aux (S (String.length X)) X = Some tX -> S (S (String.length X)) <= fuel ->
  lex_aux fuel (String (ch 44) X) = Some (TComma :: tX).
Proof.
  intros X fuel tX HX Hfuel. destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ].
  cbn. rewrite (lex_aux_mono _ _ _ _ HX) by (cbn in Hfuel; lia). reflexivity.
Qed.
(** POINTER SEAM: '*' (ch 42) → TStar (single-char op, like the brackets). *)
Lemma lex_star_app : forall X fuel tX,
  lex_aux (S (String.length X)) X = Some tX -> S (S (String.length X)) <= fuel ->
  lex_aux fuel (String (ch 42) X) = Some (TStar :: tX).
Proof.
  intros X fuel tX HX Hfuel. destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ].
  cbn. rewrite (lex_aux_mono _ _ _ _ HX) by (cbn in Hfuel; lia). reflexivity.
Qed.
(** WHITESPACE SKIP: a leading space is consumed (no token), then the rest lexes. *)
Lemma lex_space_app : forall Z fuel tZ,
  lex_aux (S (String.length Z)) Z = Some tZ -> S (S (String.length Z)) <= fuel ->
  lex_aux fuel (String (ch 32) Z) = Some tZ.
Proof.
  intros Z fuel tZ HZ Hfuel. destruct fuel as [ | fuel ]; [ cbn in Hfuel; lia | ].
  cbn [lex_aux]. replace (is_space (ch 32)) with true by reflexivity.
  rewrite (lex_aux_mono _ _ _ _ HZ) by (cbn [String.length] in Hfuel; lia). reflexivity.
Qed.
(** KEYWORD SEAM: an identifier RUN [kw] (here [chan]/[map]) lexing to its keyword token, then the rest.
    Mirrors [lex_gprint_id] but with an arbitrary [lex_ident kw] classification. *)
Lemma lex_kw_app : forall c0 kw0 tok Y fuel tY,
  is_idstart c0 = true -> all_idc (String c0 kw0) = true ->
  lex_ident (String c0 kw0) = Some tok ->
  clean_start Y = true -> lex_aux (S (String.length Y)) Y = Some tY ->
  S (S (String.length Y)) <= fuel ->   (* the id-run scan is ONE [lex_aux] step regardless of [kw] length *)
  lex_aux fuel ((String c0 kw0 ++ Y)%string) = Some (tok :: tY).
Proof.
  intros c0 kw0 tok Y fuel tY Hidstart Hallidc Hkw Hclean HY Hfuel.
  destruct fuel as [ | f ]; [ cbn [String.length] in Hfuel; lia | ].
  cbn [lex_aux String.append].
  rewrite (is_idstart_not_space _ Hidstart), Hidstart.
  replace (scan_id (String c0 (kw0 ++ Y))) with (String c0 kw0, Y)
    by (symmetry; apply (scan_id_app (String c0 kw0) Y Hallidc Hclean)).
  rewrite Hkw.
  rewrite (lex_aux_mono _ _ _ _ HY) by (cbn [String.length] in Hfuel; lia). reflexivity.
Qed.

(** OPERAND SEAM for a selector: [gparen e0] (the bare-or-parenthesised operand) lexes to [gtparen e0]
    then [X], using the per-[e0] round-trip [IHe0] (bare cases directly; paren cases via the '('/')' seams). *)
(** THE TYPE LEX ROUND-TRIP: [lex (print_ty t)] yields [gttokens_ty t] — connecting the string type printer
    [print_ty] to the token layer (rest-threaded, like [lex_gprint_app]).  Scalars/named via [lex_gprint_id];
    [*]/[[]] via the bracket seams; [chan ]/[map[] via [lex_kw_app] (+ [lex_space_app] for chan's space). *)
Lemma gttokens_ty_lex : forall t rest fuel tr,
  clean_start rest = true ->
  lex_aux (S (String.length rest)) rest = Some tr ->
  S (String.length (print_ty t) + String.length rest) <= fuel ->
  lex_aux fuel (print_ty t ++ rest)%string = Some (gttokens_ty t ++ tr)%list.
Proof.
  induction t as [ | | | | | | | | | | | | | | u IHt | u IHt | u IHt | t1 IHt1 t2 IHt2 | n ];
    intros rest fuel tr Hclean Hrest HF.
  1-14: cbn [print_ty gttokens_ty app];
        match goal with |- _ = Some (TId ?i :: _) => apply (lex_gprint_id i) end;
        [ exact Hclean | exact Hrest | cbn [print_ty proj1_sig mkIdent String.length] in HF |- *; lia ].
  - (* GTPtr u: "*" ++ print_ty u *)
    cbn [print_ty gttokens_ty].
    assert (Hu : lex_aux (S (String.length (print_ty u ++ rest))) (print_ty u ++ rest) = Some (gttokens_ty u ++ tr)%list)
      by (apply IHt; [ exact Hclean | exact Hrest | rewrite length_app; lia ]).
    rewrite str_app_assoc.
    change ("*" ++ (print_ty u ++ rest))%string with (String (ch 42) (print_ty u ++ rest)).
    rewrite (lex_star_app _ _ _ Hu)
      by (cbn [print_ty] in HF; repeat rewrite length_app in HF; repeat rewrite length_app; cbn [String.length] in HF |- *; lia).
    cbn [app]; reflexivity.
  - (* GTSlice u: "[]" ++ print_ty u *)
    cbn [print_ty gttokens_ty].
    assert (Hu : lex_aux (S (String.length (print_ty u ++ rest))) (print_ty u ++ rest) = Some (gttokens_ty u ++ tr)%list)
      by (apply IHt; [ exact Hclean | exact Hrest | rewrite length_app; lia ]).
    assert (Hrb : lex_aux (S (String.length (String (ch 93) (print_ty u ++ rest)))) (String (ch 93) (print_ty u ++ rest))
                = Some (TRB :: (gttokens_ty u ++ tr))%list)
      by (apply lex_rbrack_app; [ exact Hu | cbn [String.length]; lia ]).
    assert (Hlb : lex_aux (S (String.length (String (ch 91) (String (ch 93) (print_ty u ++ rest))))) (String (ch 91) (String (ch 93) (print_ty u ++ rest)))
                = Some (TLB :: TRB :: (gttokens_ty u ++ tr))%list)
      by (apply lex_lbrack_app; [ exact Hrb | cbn [String.length]; lia ]).
    rewrite str_app_assoc.
    change ("[]" ++ (print_ty u ++ rest))%string with (String (ch 91) (String (ch 93) (print_ty u ++ rest))).
    rewrite (lex_aux_mono _ _ _ _ Hlb)
      by (cbn [print_ty] in HF; cbn [String.length] in HF |- *; repeat rewrite length_app in HF; repeat rewrite length_app; cbn [String.length] in HF |- *; lia).
    cbn [app]; reflexivity.
  - (* GTChan u: "chan " ++ print_ty u *)
    cbn [print_ty gttokens_ty].
    assert (Hsp : lex_aux (S (String.length (String (ch 32) (print_ty u ++ rest)))) (String (ch 32) (print_ty u ++ rest))
                = Some (gttokens_ty u ++ tr)%list)
      by (apply lex_space_app; [ apply IHt; [ exact Hclean | exact Hrest | rewrite length_app; lia ] | cbn [String.length]; rewrite length_app; lia ]).
    rewrite str_app_assoc.
    change ("chan " ++ (print_ty u ++ rest))%string
      with ((String (ch 99) "han") ++ (String (ch 32) (print_ty u ++ rest)))%string.
    rewrite (lex_kw_app (ch 99) "han" TChan (String (ch 32) (print_ty u ++ rest)) fuel (gttokens_ty u ++ tr)
               ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) Hsp
               ltac:(cbn [print_ty] in HF; cbn [String.length] in HF |- *; repeat rewrite length_app in HF; repeat rewrite length_app; cbn [String.length] in HF |- *; lia)).
    cbn [app]; reflexivity.
  - (* GTMap k v: "map[" ++ print_ty k ++ "]" ++ print_ty v *)
    cbn [print_ty gttokens_ty].
    assert (Hv : lex_aux (S (String.length (print_ty t2 ++ rest))) (print_ty t2 ++ rest) = Some (gttokens_ty t2 ++ tr)%list)
      by (apply IHt2; [ exact Hclean | exact Hrest | rewrite length_app; lia ]).
    assert (Hrbv : lex_aux (S (String.length (String (ch 93) (print_ty t2 ++ rest)))) (String (ch 93) (print_ty t2 ++ rest))
                 = Some (TRB :: (gttokens_ty t2 ++ tr))%list)
      by (apply lex_rbrack_app; [ exact Hv | cbn [String.length]; lia ]).
    assert (Hk : lex_aux (S (String.length (print_ty t1 ++ String (ch 93) (print_ty t2 ++ rest)))) (print_ty t1 ++ String (ch 93) (print_ty t2 ++ rest))
               = Some (gttokens_ty t1 ++ (TRB :: (gttokens_ty t2 ++ tr)))%list)
      by (apply IHt1; [ reflexivity | exact Hrbv | rewrite length_app; cbn [String.length]; rewrite length_app; lia ]).
    assert (Hlb : lex_aux (S (String.length (String (ch 91) (print_ty t1 ++ String (ch 93) (print_ty t2 ++ rest))))) (String (ch 91) (print_ty t1 ++ String (ch 93) (print_ty t2 ++ rest)))
                = Some (TLB :: (gttokens_ty t1 ++ (TRB :: (gttokens_ty t2 ++ tr))))%list)
      by (apply lex_lbrack_app; [ exact Hk | cbn [String.length]; rewrite length_app; cbn [String.length]; rewrite length_app; lia ]).
    rewrite !str_app_assoc.
    change ("map[" ++ (print_ty t1 ++ ("]" ++ (print_ty t2 ++ rest))))%string
      with ((String (ch 109) "ap") ++ (String (ch 91) (print_ty t1 ++ String (ch 93) (print_ty t2 ++ rest))))%string.
    rewrite (lex_kw_app (ch 109) "ap" TMap (String (ch 91) (print_ty t1 ++ String (ch 93) (print_ty t2 ++ rest))) fuel
               (TLB :: (gttokens_ty t1 ++ (TRB :: (gttokens_ty t2 ++ tr))))
               ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) Hlb
               ltac:(cbn [print_ty] in HF;
                     cbn [String.length] in HF |- *; repeat rewrite length_app in HF; repeat rewrite length_app;
                     cbn [String.length] in HF |- *; repeat rewrite length_app in HF; repeat rewrite length_app;
                     cbn [String.length] in HF |- *; repeat rewrite length_app in HF; repeat rewrite length_app;
                     cbn [String.length] in HF |- *; lia)).
    cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
  - (* GTNamed n: the nominal name (a go_ident) *)
    cbn [print_ty gttokens_ty app].
    match goal with |- _ = Some (TId ?i :: _) => apply (lex_gprint_id i) end;
      [ exact Hclean | exact Hrest | cbn [print_ty tyname_to_ident mkIdent proj1_sig] in HF |- *; lia ].
Qed.

(** GENERIC "[(]operand[)]" lexer seam: for ANY operand [e0] (given its lex IH), the parenthesised wrap
    [(gprint 0 e0)] lexes to [TLP … TRP].  Factored so [lex_gparen]'s two LOOSE cases ([EUn]/[EBn], the only
    operands [op_needs_paren] wraps) share ONE proof instead of a copy-pasted block each. *)
Lemma lex_paren_wrap : forall e0 X fuel tX,
  (forall ctx rest fuel tr, clean_start rest = true ->
     lex_aux (S (String.length rest)) rest = Some tr ->
     S (String.length (gprint ctx e0) + String.length rest) <= fuel ->
     lex_aux fuel (gprint ctx e0 ++ rest) = Some ((gtokens ctx e0 ++ tr)%list)) ->
  lex_aux (S (String.length X)) X = Some tX ->
  S (String.length ("(" ++ gprint 0 e0 ++ ")") + String.length X) <= fuel ->
  lex_aux fuel (("(" ++ gprint 0 e0 ++ ")") ++ X) = Some ((TLP :: (gtokens 0 e0 ++ TRP :: nil)) ++ tX)%list.
Proof.
  intros e0 X fuel tX IHe0 HX Hfuel.
  assert (Hrp : lex_aux (S (String.length (String (ch 41) X))) (String (ch 41) X) = Some (TRP :: tX))
    by (apply lex_rparen_app; [ exact HX | cbn [String.length]; lia ]).
  assert (Hin : lex_aux (S (String.length (gprint 0 e0 ++ String (ch 41) X)))
                        (gprint 0 e0 ++ String (ch 41) X)
              = Some (gtokens 0 e0 ++ TRP :: tX)%list)
    by (apply IHe0; [ reflexivity | exact Hrp | rewrite length_app; lia ]).
  rewrite !str_app_assoc.
  change ("(" ++ (gprint 0 e0 ++ (")" ++ X)))%string
    with (String (ch 40) (gprint 0 e0 ++ String (ch 41) X)).
  rewrite (lex_lparen_app _ _ _ Hin)
    by (cbn [String.length] in Hfuel |- *; repeat rewrite length_app in Hfuel;
        repeat rewrite length_app; cbn [String.length] in Hfuel |- *; lia).
  cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
Qed.

Lemma lex_gparen : forall e0 X fuel tX,
  (forall ctx rest fuel tr, clean_start rest = true ->
     lex_aux (S (String.length rest)) rest = Some tr ->
     S (String.length (gprint ctx e0) + String.length rest) <= fuel ->
     lex_aux fuel (gprint ctx e0 ++ rest) = Some ((gtokens ctx e0 ++ tr)%list)) ->
  clean_start X = true ->
  lex_aux (S (String.length X)) X = Some tX ->
  S (String.length (gparen e0) + String.length X) <= fuel ->
  lex_aux fuel (gparen e0 ++ X) = Some ((gtparen e0 ++ tX)%list).
Proof.
  intros e0 X fuel tX IHe0 HXc HX Hfuel.
  destruct e0 as [ i0 | z0 | u0 eu | b0 lb rb | es fs | ei ii | esl elo ehi | ecf ecargs | eaf eaT | ecc ece | eslt esles | ekt evt ekvs | sv ]; cbn [gparen gtparen op_needs_paren] in Hfuel |- *.
  1,2,5,6,7,8,9,10,11,12,13: apply IHe0; [ exact HXc | exact HX | exact Hfuel ].
  (* the two LOOSE operands [EUn]/[EBn] — both parenthesised, one shared seam *)
  all: apply lex_paren_wrap; [ exact IHe0 | exact HX | exact Hfuel ].
Qed.

(** ---- THE LEXER ROUND-TRIP ---- [lex (gprint ctx e ++ rest) = gtokens ctx e ++ (lex rest)] for clean
    [rest] and enough fuel; by induction on [e].  Leaves via the leaf lemmas; [EUn]/[EBn] thread the seams
    around the IHs, every boundary clean (a space / a ')' / [rest]).  String scope is open, so the token
    appends are written [%list]. *)
Lemma lex_gprint_app : forall e ctx rest fuel tr,
  clean_start rest = true ->
  lex_aux (S (String.length rest)) rest = Some tr ->
  S (String.length (gprint ctx e) + String.length rest) <= fuel ->
  lex_aux fuel (gprint ctx e ++ rest) = Some ((gtokens ctx e ++ tr)%list).
Proof.
  induction e as [ i | z | o e IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 i IHi | e0 IHe0 lo IHlo hi IHhi | e0 IHe0 args IHargs | e0 IHe0 T | c0 ec0 IHec0 | slt sles IHsles | mkt mvt mkvs IHmkvs | sv ]
    using GExpr_ind';
    intros ctx rest fuel tr Hclean Hrest Hfuel.
  - cbn [gprint gtokens app] in *. apply lex_gprint_id; assumption.
  - cbn [gprint gtokens app] in *. apply lex_gprint_int; assumption.
  - (* EUn: body is [<op>( gprint 0 e )] (operand always parenthesised) *)
    assert (Hbody : lex_aux (S (String.length (gprint 0 e ++ String (ch 41) rest)))
                            (gprint 0 e ++ String (ch 41) rest)
                  = Some ((gtokens 0 e ++ TRP :: tr)%list)).
    { apply IHe; [ reflexivity
                 | apply lex_rparen_app; [ exact Hrest | cbn [String.length]; lia ]
                 | rewrite length_app; cbn [String.length]; lia ]. }
    destruct o; cbn [gprint gtokens] in Hfuel |- *.
    1-4: rewrite !str_app_assoc;
         change (")" ++ rest)%string with (String (ch 41) rest);
         change ("(" ++ (gprint 0 e ++ String (ch 41) rest))%string
           with (String (ch 40) (gprint 0 e ++ String (ch 41) rest));
         erewrite lex_unop_lp_app;
           [ cbn [app]; rewrite <- app_assoc; reflexivity
           | discriminate
           | exact Hbody
           | repeat rewrite length_app in Hfuel; repeat rewrite length_app;
             cbn [String.length unop_text] in Hfuel |- *; lia ].
    (* UNeg: body is [-( gprint 0 e )] *)
    rewrite !str_app_assoc.
    change (")" ++ rest)%string with (String (ch 41) rest).
    change ("-(" ++ (gprint 0 e ++ String (ch 41) rest))%string
      with (String (ch 45) (String (ch 40) (gprint 0 e ++ String (ch 41) rest))).
    rewrite (lex_minuslp_app _ _ _ Hbody)
      by (repeat rewrite length_app in Hfuel; repeat rewrite length_app;
          cbn [String.length] in Hfuel |- *; lia).
    cbn [app]; rewrite <- app_assoc; reflexivity.
  - (* EBn: inner = gprint p l ++ binop_text o ++ gprint (S p) r *)
    cbn [gprint gtokens] in Hfuel |- *.
    set (p := binop_prec o) in *.
    assert (Hinner : forall X tX f, clean_start X = true ->
              lex_aux (S (String.length X)) X = Some tX ->
              S (String.length (gprint p l ++ binop_text o ++ gprint (S p) r) + String.length X) <= f ->
              lex_aux f (gprint p l ++ binop_text o ++ gprint (S p) r ++ X)
                = Some (((gtokens p l ++ op_token o :: gtokens (S p) r) ++ tX)%list)).
    { intros X tX f HXc HX Hf.
      assert (Hr : lex_aux (S (String.length (gprint (S p) r ++ X))) (gprint (S p) r ++ X)
                 = Some ((gtokens (S p) r ++ tX)%list))
        by (apply IHr; [ exact HXc | exact HX | repeat rewrite length_app; repeat rewrite length_app in Hf; lia ]).
      assert (Hb : lex_aux (S (String.length (binop_text o ++ gprint (S p) r ++ X)))
                           (binop_text o ++ gprint (S p) r ++ X)
                 = Some ((op_token o :: (gtokens (S p) r ++ tX))%list))
        by (apply lex_binop_app; [ exact Hr | repeat rewrite length_app; repeat rewrite length_app in Hf; lia ]).
      rewrite <- app_assoc. cbn [app].
      apply IHl; [ apply clean_start_binop | exact Hb | repeat rewrite length_app; repeat rewrite length_app in Hf; lia ]. }
    destruct (Nat.ltb p ctx); cbn [gprint gtokens] in Hfuel |- *.
    + (* wrapped: "(" ++ inner ++ ")" *)
      assert (Hrp : lex_aux (S (String.length (String (ch 41) rest))) (String (ch 41) rest) = Some (TRP :: tr))
        by (apply lex_rparen_app; [ exact Hrest | cbn [String.length]; lia ]).
      assert (Hin : lex_aux (S (String.length (gprint p l ++ binop_text o ++ gprint (S p) r ++ String (ch 41) rest)))
                            (gprint p l ++ binop_text o ++ gprint (S p) r ++ String (ch 41) rest)
                  = Some (((gtokens p l ++ op_token o :: gtokens (S p) r) ++ TRP :: tr)%list))
        by (apply Hinner; [ reflexivity | exact Hrp | repeat rewrite length_app; cbn [String.length]; lia ]).
      rewrite !str_app_assoc.
      change ("(" ++ (gprint p l ++ (binop_text o ++ (gprint (S p) r ++ (")" ++ rest)))))%string
        with (String (ch 40) (gprint p l ++ binop_text o ++ gprint (S p) r ++ String (ch 41) rest)).
      rewrite (lex_lparen_app _ _ _ Hin)
        by (repeat rewrite length_app in Hfuel; repeat rewrite length_app;
            cbn [String.length] in Hfuel |- *; lia).
      cbn [app]. rewrite <- !app_assoc. cbn [app]. reflexivity.
    + (* unwrapped: inner *)
      rewrite !str_app_assoc.
      rewrite (Hinner rest tr fuel Hclean Hrest
                ltac:(repeat rewrite length_app in Hfuel; repeat rewrite length_app;
                      cbn [String.length] in Hfuel |- *; lia)).
      reflexivity.
  - (* ESel e0 f: [gparen e0] ++ "." ++ field — operand seam ([lex_gparen]) then the '.'+field seam *)
    rewrite gprint_ESel, gtokens_ESel.
    assert (Hfield : lex_aux (S (String.length (proj1_sig f ++ rest))) (proj1_sig f ++ rest) = Some (TId f :: tr))
      by (apply lex_gprint_id; [ exact Hclean | exact Hrest | rewrite length_app; lia ]).
    assert (Hdot : lex_aux (S (String.length (String (ch 46) (proj1_sig f ++ rest))))
                           (String (ch 46) (proj1_sig f ++ rest)) = Some (TDot :: TId f :: tr))
      by (apply lex_dot_app; [ exact Hfield | cbn [String.length]; lia ]).
    rewrite !str_app_assoc.
    change ("." ++ (proj1_sig f ++ rest))%string with (String (ch 46) (proj1_sig f ++ rest)).
    rewrite (lex_gparen e0 (String (ch 46) (proj1_sig f ++ rest)) fuel (TDot :: TId f :: tr)
               IHe0 eq_refl Hdot
               ltac:(rewrite gprint_ESel in Hfuel; cbn [String.length] in Hfuel |- *;
                     repeat rewrite length_app in Hfuel; repeat rewrite length_app;
                     cbn [String.length] in Hfuel |- *; lia)).
    cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
  - (* EIndex e0 i: [gparen e0] ++ "[" ++ index ++ "]" — operand seam then '['+index+']' seam *)
    rewrite gprint_EIndex, gtokens_EIndex.
    assert (Hrb : lex_aux (S (String.length (String (ch 93) rest))) (String (ch 93) rest) = Some (TRB :: tr))
      by (apply lex_rbrack_app; [ exact Hrest | cbn [String.length]; lia ]).
    assert (Hidx : lex_aux (S (String.length (gprint 0 i ++ String (ch 93) rest)))
                           (gprint 0 i ++ String (ch 93) rest) = Some (gtokens 0 i ++ TRB :: tr)%list)
      by (apply IHi; [ reflexivity | exact Hrb | rewrite length_app; cbn [String.length]; lia ]).
    assert (Hlb : lex_aux (S (String.length (String (ch 91) (gprint 0 i ++ String (ch 93) rest))))
                          (String (ch 91) (gprint 0 i ++ String (ch 93) rest))
                = Some (TLB :: (gtokens 0 i ++ TRB :: tr))%list)
      by (apply lex_lbrack_app; [ exact Hidx | cbn [String.length]; lia ]).
    rewrite !str_app_assoc.
    change ("[" ++ (gprint 0 i ++ ("]" ++ rest)))%string
      with (String (ch 91) (gprint 0 i ++ String (ch 93) rest)).
    rewrite (lex_gparen e0 (String (ch 91) (gprint 0 i ++ String (ch 93) rest)) fuel
               (TLB :: (gtokens 0 i ++ TRB :: tr)) IHe0 eq_refl Hlb
               ltac:(rewrite gprint_EIndex in Hfuel; cbn [String.length] in Hfuel |- *;
                     repeat rewrite length_app in Hfuel; repeat rewrite length_app;
                     cbn [String.length] in Hfuel |- *; lia)).
    cbn [app]; rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
  - (* ESlice e0 lo hi: [gparen e0] ++ "[" ++ lo ++ ":" ++ hi ++ "]" — operand seam then '['+lo+':'+hi+']' *)
    rewrite gprint_ESlice, gtokens_ESlice.
    assert (Hrb : lex_aux (S (String.length (String (ch 93) rest))) (String (ch 93) rest) = Some (TRB :: tr))
      by (apply lex_rbrack_app; [ exact Hrest | cbn [String.length]; lia ]).
    assert (Hhi : lex_aux (S (String.length (gprint 0 hi ++ String (ch 93) rest)))
                          (gprint 0 hi ++ String (ch 93) rest) = Some (gtokens 0 hi ++ TRB :: tr)%list)
      by (apply IHhi; [ reflexivity | exact Hrb | rewrite length_app; cbn [String.length]; lia ]).
    assert (Hcolon : lex_aux (S (String.length (String (ch 58) (gprint 0 hi ++ String (ch 93) rest))))
                             (String (ch 58) (gprint 0 hi ++ String (ch 93) rest))
                   = Some (TColon :: (gtokens 0 hi ++ TRB :: tr))%list)
      by (apply lex_colon_app; [ exact Hhi | cbn [String.length]; rewrite length_app; cbn [String.length]; lia ]).
    assert (Hlo : lex_aux (S (String.length (gprint 0 lo ++ String (ch 58) (gprint 0 hi ++ String (ch 93) rest))))
                          (gprint 0 lo ++ String (ch 58) (gprint 0 hi ++ String (ch 93) rest))
                = Some (gtokens 0 lo ++ (TColon :: (gtokens 0 hi ++ TRB :: tr)))%list)
      by (apply IHlo; [ reflexivity | exact Hcolon | rewrite length_app; cbn [String.length]; rewrite length_app; cbn [String.length]; lia ]).
    assert (Hlb : lex_aux (S (String.length (String (ch 91) (gprint 0 lo ++ String (ch 58) (gprint 0 hi ++ String (ch 93) rest)))))
                          (String (ch 91) (gprint 0 lo ++ String (ch 58) (gprint 0 hi ++ String (ch 93) rest)))
                = Some (TLB :: (gtokens 0 lo ++ (TColon :: (gtokens 0 hi ++ TRB :: tr))))%list)
      by (apply lex_lbrack_app; [ exact Hlo | cbn [String.length]; lia ]).
    rewrite !str_app_assoc.
    change ("[" ++ (gprint 0 lo ++ (":" ++ (gprint 0 hi ++ ("]" ++ rest)))))%string
      with (String (ch 91) (gprint 0 lo ++ String (ch 58) (gprint 0 hi ++ String (ch 93) rest))).
    rewrite (lex_gparen e0 (String (ch 91) (gprint 0 lo ++ String (ch 58) (gprint 0 hi ++ String (ch 93) rest))) fuel
               (TLB :: (gtokens 0 lo ++ (TColon :: (gtokens 0 hi ++ TRB :: tr)))) IHe0 eq_refl Hlb
               ltac:(rewrite gprint_ESlice in Hfuel;
                     cbn [String.length] in Hfuel |- *; repeat rewrite length_app in Hfuel; repeat rewrite length_app;
                     cbn [String.length] in Hfuel |- *; repeat rewrite length_app in Hfuel; repeat rewrite length_app;
                     cbn [String.length] in Hfuel |- *; repeat rewrite length_app in Hfuel; repeat rewrite length_app;
                     cbn [String.length] in Hfuel |- *; lia)).
    cbn [app]; rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; cbn [app];
      rewrite <- !app_assoc; cbn [app]; reflexivity.
  - (* ECall e0 args: [gparen e0] ++ "(" ++ gprint_args args ++ ")" — operand seam then '('+args+')' *)
    rewrite gprint_ECall, gtokens_ECall.
    (* the comma-prefixed arg-tail lexes, by induction on the list using the per-arg [Forall] IH. *)
    assert (Htl : forall l Y tY F,
              List.Forall (fun a => forall ctx0 rest0 fuel0 tr0, clean_start rest0 = true ->
                  lex_aux (S (String.length rest0)) rest0 = Some tr0 ->
                  S (String.length (gprint ctx0 a) + String.length rest0) <= fuel0 ->
                  lex_aux fuel0 (gprint ctx0 a ++ rest0) = Some (gtokens ctx0 a ++ tr0)%list) l ->
              clean_start Y = true -> lex_aux (S (String.length Y)) Y = Some tY ->
              S (String.length (gprint_args_tl l) + String.length Y) <= F ->
              lex_aux F (gprint_args_tl l ++ Y) = Some (gtokens_args_tl l ++ tY)%list).
    { induction l as [ | b m IHm ]; intros Y tY F Hfa HYc HY HF.
      - cbn [gprint_args_tl gtokens_args_tl Datatypes.app] in *. apply (lex_aux_mono _ _ _ _ HY).
        cbn [gprint_args_tl String.length] in HF. lia.
      - cbn [gprint_args_tl gtokens_args_tl].
        assert (Hcs : clean_start (gprint_args_tl m ++ Y) = true)
          by (destruct m as [ | b' m' ]; [ cbn [gprint_args_tl Datatypes.app]; exact HYc | reflexivity ]).
        assert (Hm : lex_aux (S (String.length (gprint_args_tl m ++ Y))) (gprint_args_tl m ++ Y)
                   = Some (gtokens_args_tl m ++ tY)%list)
          by (apply IHm; [ exact (List.Forall_inv_tail Hfa) | exact HYc | exact HY | rewrite length_app; lia ]).
        assert (Hb : lex_aux (S (String.length (gprint 0 b ++ gprint_args_tl m ++ Y)))
                             (gprint 0 b ++ gprint_args_tl m ++ Y)
                   = Some (gtokens 0 b ++ (gtokens_args_tl m ++ tY))%list)
          by (apply (List.Forall_inv Hfa); [ exact Hcs | exact Hm | rewrite !length_app; lia ]).
        rewrite !str_app_assoc.
        change ("," ++ (gprint 0 b ++ (gprint_args_tl m ++ Y)))%string
          with (String (ch 44) (gprint 0 b ++ gprint_args_tl m ++ Y)).
        rewrite (lex_comma_app _ _ _ Hb)
          by (cbn [gprint_args_tl] in HF; rewrite !length_app in HF |- *; cbn [String.length] in HF |- *; lia).
        cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity. }
    assert (Hrp : lex_aux (S (String.length (String (ch 41) rest))) (String (ch 41) rest) = Some (TRP :: tr))
      by (apply lex_rparen_app; [ exact Hrest | cbn [String.length]; lia ]).
    assert (Hargs : lex_aux (S (String.length (gprint_args args ++ String (ch 41) rest)))
                            (gprint_args args ++ String (ch 41) rest)
                  = Some (gtokens_args args ++ TRP :: tr)%list).
    { destruct args as [ | a r ].
      - cbn [gprint_args gtokens_args String.append Datatypes.app]. exact Hrp.
      - cbn [gprint_args gtokens_args].
        assert (Hcs : clean_start (gprint_args_tl r ++ String (ch 41) rest) = true)
          by (destruct r as [ | b' r' ]; [ cbn [gprint_args_tl Datatypes.app]; reflexivity | reflexivity ]).
        assert (Htlr : lex_aux (S (String.length (gprint_args_tl r ++ String (ch 41) rest)))
                               (gprint_args_tl r ++ String (ch 41) rest)
                     = Some (gtokens_args_tl r ++ TRP :: tr)%list)
          by (apply (Htl r (String (ch 41) rest) (TRP :: tr));
              [ exact (List.Forall_inv_tail IHargs) | reflexivity | exact Hrp
              | rewrite length_app; cbn [String.length]; lia ]).
        rewrite str_app_assoc, <- app_assoc.
        apply (List.Forall_inv IHargs); [ exact Hcs | exact Htlr | rewrite !length_app; cbn [String.length]; lia ]. }
    assert (Hlp : lex_aux (S (String.length (String (ch 40) (gprint_args args ++ String (ch 41) rest))))
                          (String (ch 40) (gprint_args args ++ String (ch 41) rest))
                = Some (TLP :: (gtokens_args args ++ TRP :: tr))%list)
      by (apply lex_lparen_app; [ exact Hargs | cbn [String.length]; lia ]).
    rewrite !str_app_assoc.
    change ("(" ++ (gprint_args args ++ (")" ++ rest)))%string
      with (String (ch 40) (gprint_args args ++ String (ch 41) rest)).
    rewrite (lex_gparen e0 (String (ch 40) (gprint_args args ++ String (ch 41) rest)) fuel
               (TLP :: (gtokens_args args ++ TRP :: tr)) IHe0 eq_refl Hlp
               ltac:(rewrite gprint_ECall in Hfuel; cbn [String.length] in Hfuel |- *;
                     repeat rewrite length_app in Hfuel; repeat rewrite length_app;
                     cbn [String.length] in Hfuel |- *; lia)).
    cbn [app]; rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
  - (* EAssert e0 T: [gparen e0] ++ ".(" ++ print_ty T ++ ")" — operand seam then '.'+'('+type+')' *)
    rewrite gprint_EAssert, gtokens_EAssert.
    assert (Hrp : lex_aux (S (String.length (String (ch 41) rest))) (String (ch 41) rest) = Some (TRP :: tr))
      by (apply lex_rparen_app; [ exact Hrest | cbn [String.length]; lia ]).
    assert (Hty : lex_aux (S (String.length (print_ty T ++ String (ch 41) rest))) (print_ty T ++ String (ch 41) rest)
                = Some (gttokens_ty T ++ TRP :: tr)%list)
      by (apply gttokens_ty_lex; [ reflexivity | exact Hrp | rewrite length_app; cbn [String.length]; lia ]).
    assert (Hlp : lex_aux (S (String.length (String (ch 40) (print_ty T ++ String (ch 41) rest)))) (String (ch 40) (print_ty T ++ String (ch 41) rest))
                = Some (TLP :: (gttokens_ty T ++ TRP :: tr))%list)
      by (apply lex_lparen_app; [ exact Hty | cbn [String.length]; rewrite length_app; cbn [String.length]; lia ]).
    assert (Hdot : lex_aux (S (String.length (String (ch 46) (String (ch 40) (print_ty T ++ String (ch 41) rest))))) (String (ch 46) (String (ch 40) (print_ty T ++ String (ch 41) rest)))
                 = Some (TDot :: TLP :: (gttokens_ty T ++ TRP :: tr))%list)
      by (apply lex_dot_app; [ exact Hlp | cbn [String.length]; lia ]).
    rewrite !str_app_assoc.
    change (".(" ++ (print_ty T ++ (")" ++ rest)))%string
      with (String (ch 46) (String (ch 40) (print_ty T ++ String (ch 41) rest))).
    rewrite (lex_gparen e0 (String (ch 46) (String (ch 40) (print_ty T ++ String (ch 41) rest))) fuel
               (TDot :: TLP :: (gttokens_ty T ++ TRP :: tr)) IHe0 eq_refl Hdot
               ltac:(rewrite gprint_EAssert in Hfuel; cbn [String.length] in Hfuel |- *;
                     repeat rewrite length_app in Hfuel; repeat rewrite length_app;
                     cbn [String.length] in Hfuel |- *; lia)).
    cbn [app]; rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
  - (* EConv c0 ec0: print_ty(convty_ty c0) ++ "(" ++ gprint 0 ec0 ++ ")" — TYPE prefix then '(' operand ')'.
       Mirrors EAssert's [gttokens_ty_lex] type handling but with the type at the FRONT (outermost seam). *)
    rewrite gprint_EConv, gtokens_EConv.
    assert (Hrp : lex_aux (S (String.length (String (ch 41) rest))) (String (ch 41) rest) = Some (TRP :: tr))
      by (apply lex_rparen_app; [ exact Hrest | cbn [String.length]; lia ]).
    assert (Hbody : lex_aux (S (String.length (gprint 0 ec0 ++ String (ch 41) rest)))
                            (gprint 0 ec0 ++ String (ch 41) rest)
                  = Some (gtokens 0 ec0 ++ TRP :: tr)%list)
      by (apply IHec0; [ reflexivity | exact Hrp | rewrite length_app; cbn [String.length]; lia ]).
    assert (Hlp : lex_aux (S (String.length (String (ch 40) (gprint 0 ec0 ++ String (ch 41) rest))))
                          (String (ch 40) (gprint 0 ec0 ++ String (ch 41) rest))
                = Some (TLP :: (gtokens 0 ec0 ++ TRP :: tr))%list)
      by (apply lex_lparen_app; [ exact Hbody | cbn [String.length]; rewrite length_app; cbn [String.length]; lia ]).
    rewrite !str_app_assoc.
    change ("(" ++ (gprint 0 ec0 ++ (")" ++ rest)))%string
      with (String (ch 40) (gprint 0 ec0 ++ String (ch 41) rest)).
    rewrite (gttokens_ty_lex (convty_ty c0) (String (ch 40) (gprint 0 ec0 ++ String (ch 41) rest)) fuel
               (TLP :: (gtokens 0 ec0 ++ TRP :: tr)) ltac:(reflexivity) Hlp
               ltac:(rewrite gprint_EConv in Hfuel; cbn [String.length] in Hfuel |- *;
                     repeat rewrite length_app in Hfuel; repeat rewrite length_app;
                     cbn [String.length] in Hfuel |- *; lia)).
    cbn [app]; rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
  - (* ESliceLit slt sles: "[]" ++ print_ty slt ++ "{" ++ gprint_args sles ++ "}" — the type prefix [[]T] IS
       [print_ty (GTSlice slt)] (so [gttokens_ty_lex] handles the '['']'+type), then '{' element-list '}'.  The
       element list lexes by induction on [sles] exactly like ECall's args (the shared [Htl] helper), but closes
       with '}' (TRC) instead of ')' (TRP). *)
    rewrite gprint_ESliceLit, gtokens_ESliceLit.
    assert (Htl : forall l Y tY F,
              List.Forall (fun a => forall ctx0 rest0 fuel0 tr0, clean_start rest0 = true ->
                  lex_aux (S (String.length rest0)) rest0 = Some tr0 ->
                  S (String.length (gprint ctx0 a) + String.length rest0) <= fuel0 ->
                  lex_aux fuel0 (gprint ctx0 a ++ rest0) = Some (gtokens ctx0 a ++ tr0)%list) l ->
              clean_start Y = true -> lex_aux (S (String.length Y)) Y = Some tY ->
              S (String.length (gprint_args_tl l) + String.length Y) <= F ->
              lex_aux F (gprint_args_tl l ++ Y) = Some (gtokens_args_tl l ++ tY)%list).
    { induction l as [ | b m IHm ]; intros Y tY F Hfa HYc HY HF.
      - cbn [gprint_args_tl gtokens_args_tl Datatypes.app] in *. apply (lex_aux_mono _ _ _ _ HY).
        cbn [gprint_args_tl String.length] in HF. lia.
      - cbn [gprint_args_tl gtokens_args_tl].
        assert (Hcs : clean_start (gprint_args_tl m ++ Y) = true)
          by (destruct m as [ | b' m' ]; [ cbn [gprint_args_tl Datatypes.app]; exact HYc | reflexivity ]).
        assert (Hm : lex_aux (S (String.length (gprint_args_tl m ++ Y))) (gprint_args_tl m ++ Y)
                   = Some (gtokens_args_tl m ++ tY)%list)
          by (apply IHm; [ exact (List.Forall_inv_tail Hfa) | exact HYc | exact HY | rewrite length_app; lia ]).
        assert (Hb : lex_aux (S (String.length (gprint 0 b ++ gprint_args_tl m ++ Y)))
                             (gprint 0 b ++ gprint_args_tl m ++ Y)
                   = Some (gtokens 0 b ++ (gtokens_args_tl m ++ tY))%list)
          by (apply (List.Forall_inv Hfa); [ exact Hcs | exact Hm | rewrite !length_app; lia ]).
        rewrite !str_app_assoc.
        change ("," ++ (gprint 0 b ++ (gprint_args_tl m ++ Y)))%string
          with (String (ch 44) (gprint 0 b ++ gprint_args_tl m ++ Y)).
        rewrite (lex_comma_app _ _ _ Hb)
          by (cbn [gprint_args_tl] in HF; rewrite !length_app in HF |- *; cbn [String.length] in HF |- *; lia).
        cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity. }
    assert (Hrc : lex_aux (S (String.length (String (ch 125) rest))) (String (ch 125) rest) = Some (TRC :: tr))
      by (apply lex_rbrace_app; [ exact Hrest | cbn [String.length]; lia ]).
    assert (Helems : lex_aux (S (String.length (gprint_args sles ++ String (ch 125) rest)))
                            (gprint_args sles ++ String (ch 125) rest)
                  = Some (gtokens_args sles ++ TRC :: tr)%list).
    { destruct sles as [ | a r ].
      - cbn [gprint_args gtokens_args String.append Datatypes.app]. exact Hrc.
      - cbn [gprint_args gtokens_args].
        assert (Hcs : clean_start (gprint_args_tl r ++ String (ch 125) rest) = true)
          by (destruct r as [ | b' r' ]; [ cbn [gprint_args_tl Datatypes.app]; reflexivity | reflexivity ]).
        assert (Htlr : lex_aux (S (String.length (gprint_args_tl r ++ String (ch 125) rest)))
                               (gprint_args_tl r ++ String (ch 125) rest)
                     = Some (gtokens_args_tl r ++ TRC :: tr)%list)
          by (apply (Htl r (String (ch 125) rest) (TRC :: tr));
              [ exact (List.Forall_inv_tail IHsles) | reflexivity | exact Hrc
              | rewrite length_app; cbn [String.length]; lia ]).
        rewrite str_app_assoc, <- app_assoc.
        apply (List.Forall_inv IHsles); [ exact Hcs | exact Htlr | rewrite !length_app; cbn [String.length]; lia ]. }
    assert (Hlc : lex_aux (S (String.length (String (ch 123) (gprint_args sles ++ String (ch 125) rest))))
                          (String (ch 123) (gprint_args sles ++ String (ch 125) rest))
                = Some (TLC :: (gtokens_args sles ++ TRC :: tr))%list)
      by (apply lex_lbrace_app; [ exact Helems | cbn [String.length]; lia ]).
    rewrite !str_app_assoc.
    change ("[]" ++ (print_ty slt ++ ("{" ++ (gprint_args sles ++ ("}" ++ rest)))))%string
      with (print_ty (GTSlice slt) ++ String (ch 123) (gprint_args sles ++ String (ch 125) rest))%string.
    rewrite (gttokens_ty_lex (GTSlice slt) (String (ch 123) (gprint_args sles ++ String (ch 125) rest)) fuel
               (TLC :: (gtokens_args sles ++ TRC :: tr)) ltac:(reflexivity) Hlc
               ltac:(rewrite gprint_ESliceLit in Hfuel; cbn [String.length print_ty] in Hfuel |- *;
                     repeat rewrite length_app in Hfuel; repeat rewrite length_app;
                     cbn [String.length] in Hfuel |- *; lia)).
    cbn [gttokens_ty app]; rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
  - (* EMapLit mkt mvt mkvs: print_ty(GTMap mkt mvt) ++ "{" ++ gprint_pairs mkvs ++ "}" — the type prefix is
       [print_ty (GTMap mkt mvt)] (handled by [gttokens_ty_lex]), then '{' the KEYED pair-list '}'.  Each pair
       is [k: v] with SPACE seams ([lex_colon_app]+[lex_space_app]) and ", " between pairs ([lex_comma_app]+
       [lex_space_app]); the lexer SKIPS the printed spaces so the token list carries none. *)
    rewrite gprint_EMapLit, gtokens_EMapLit.
    assert (Htl : forall l Y tY F,
              List.Forall (fun p => (forall ctx0 rest0 fuel0 tr0, clean_start rest0 = true ->
                  lex_aux (S (String.length rest0)) rest0 = Some tr0 ->
                  S (String.length (gprint ctx0 (fst p)) + String.length rest0) <= fuel0 ->
                  lex_aux fuel0 (gprint ctx0 (fst p) ++ rest0) = Some (gtokens ctx0 (fst p) ++ tr0)%list)
                /\ (forall ctx0 rest0 fuel0 tr0, clean_start rest0 = true ->
                  lex_aux (S (String.length rest0)) rest0 = Some tr0 ->
                  S (String.length (gprint ctx0 (snd p)) + String.length rest0) <= fuel0 ->
                  lex_aux fuel0 (gprint ctx0 (snd p) ++ rest0) = Some (gtokens ctx0 (snd p) ++ tr0)%list)) l ->
              clean_start Y = true -> lex_aux (S (String.length Y)) Y = Some tY ->
              S (String.length (gprint_pairs_tl l) + String.length Y) <= F ->
              lex_aux F (gprint_pairs_tl l ++ Y) = Some (gtokens_pairs_tl l ++ tY)%list).
    { induction l as [ | [k v] m IHm ]; intros Y tY F Hfa HYc HY HF.
      - cbn [gprint_pairs_tl gtokens_pairs_tl Datatypes.app] in *. apply (lex_aux_mono _ _ _ _ HY).
        cbn [gprint_pairs_tl String.length] in HF. lia.
      - cbn [gprint_pairs_tl gtokens_pairs_tl].
        destruct (List.Forall_inv Hfa) as [ Hlexk Hlexv ]. cbn [fst snd] in Hlexk, Hlexv.
        assert (Hcs : clean_start (gprint_pairs_tl m ++ Y) = true)
          by (destruct m as [ | [k' v'] m' ]; [ cbn [gprint_pairs_tl Datatypes.app]; exact HYc | reflexivity ]).
        assert (Hm : lex_aux (S (String.length (gprint_pairs_tl m ++ Y))) (gprint_pairs_tl m ++ Y)
                   = Some (gtokens_pairs_tl m ++ tY)%list)
          by (apply IHm; [ exact (List.Forall_inv_tail Hfa) | exact HYc | exact HY | rewrite length_app; lia ]).
        assert (Hv : lex_aux (S (String.length (gprint 0 v ++ gprint_pairs_tl m ++ Y))) (gprint 0 v ++ gprint_pairs_tl m ++ Y)
                   = Some (gtokens 0 v ++ (gtokens_pairs_tl m ++ tY))%list)
          by (apply Hlexv; [ exact Hcs | exact Hm | rewrite !length_app; lia ]).
        assert (Hspv : lex_aux (S (String.length (String (ch 32) (gprint 0 v ++ gprint_pairs_tl m ++ Y)))) (String (ch 32) (gprint 0 v ++ gprint_pairs_tl m ++ Y))
                     = Some (gtokens 0 v ++ (gtokens_pairs_tl m ++ tY))%list)
          by (apply lex_space_app; [ exact Hv | cbn [String.length]; lia ]).
        assert (Hcolon : lex_aux (S (String.length (String (ch 58) (String (ch 32) (gprint 0 v ++ gprint_pairs_tl m ++ Y))))) (String (ch 58) (String (ch 32) (gprint 0 v ++ gprint_pairs_tl m ++ Y)))
                       = Some (TColon :: (gtokens 0 v ++ (gtokens_pairs_tl m ++ tY)))%list)
          by (apply lex_colon_app; [ exact Hspv | cbn [String.length]; lia ]).
        assert (Hk : lex_aux (S (String.length (gprint 0 k ++ String (ch 58) (String (ch 32) (gprint 0 v ++ gprint_pairs_tl m ++ Y)))))
                             (gprint 0 k ++ String (ch 58) (String (ch 32) (gprint 0 v ++ gprint_pairs_tl m ++ Y)))
                   = Some (gtokens 0 k ++ (TColon :: (gtokens 0 v ++ (gtokens_pairs_tl m ++ tY))))%list)
          by (apply Hlexk; [ reflexivity | exact Hcolon | rewrite !length_app; cbn [String.length]; lia ]).
        assert (Hspk : lex_aux (S (String.length (String (ch 32) (gprint 0 k ++ String (ch 58) (String (ch 32) (gprint 0 v ++ gprint_pairs_tl m ++ Y))))))
                               (String (ch 32) (gprint 0 k ++ String (ch 58) (String (ch 32) (gprint 0 v ++ gprint_pairs_tl m ++ Y))))
                     = Some (gtokens 0 k ++ (TColon :: (gtokens 0 v ++ (gtokens_pairs_tl m ++ tY))))%list)
          by (apply lex_space_app; [ exact Hk | cbn [String.length]; lia ]).
        rewrite !str_app_assoc.
        change (", " ++ (gprint 0 k ++ (": " ++ (gprint 0 v ++ (gprint_pairs_tl m ++ Y)))))%string
          with (String (ch 44) (String (ch 32) (gprint 0 k ++ String (ch 58) (String (ch 32) (gprint 0 v ++ gprint_pairs_tl m ++ Y))))).
        rewrite (lex_comma_app _ _ _ Hspk)
          by (cbn [gprint_pairs_tl] in HF; cbn [String.length] in HF |- *;
              repeat rewrite length_app in HF; repeat rewrite length_app;
              cbn [String.length] in HF |- *;
              repeat rewrite length_app in HF; repeat rewrite length_app; lia).
        cbn [app]; rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; reflexivity. }
    assert (Hrc : lex_aux (S (String.length (String (ch 125) rest))) (String (ch 125) rest) = Some (TRC :: tr))
      by (apply lex_rbrace_app; [ exact Hrest | cbn [String.length]; lia ]).
    assert (Hpairs : lex_aux (S (String.length (gprint_pairs mkvs ++ String (ch 125) rest)))
                            (gprint_pairs mkvs ++ String (ch 125) rest)
                  = Some (gtokens_pairs mkvs ++ TRC :: tr)%list).
    { destruct mkvs as [ | [k v] r ].
      - cbn [gprint_pairs gtokens_pairs String.append Datatypes.app]. exact Hrc.
      - cbn [gprint_pairs gtokens_pairs].
        destruct (List.Forall_inv IHmkvs) as [ Hlexk Hlexv ]. cbn [fst snd] in Hlexk, Hlexv.
        assert (Hcs : clean_start (gprint_pairs_tl r ++ String (ch 125) rest) = true)
          by (destruct r as [ | [k' v'] r' ]; [ cbn [gprint_pairs_tl Datatypes.app]; reflexivity | reflexivity ]).
        assert (Htlr : lex_aux (S (String.length (gprint_pairs_tl r ++ String (ch 125) rest)))
                               (gprint_pairs_tl r ++ String (ch 125) rest)
                     = Some (gtokens_pairs_tl r ++ TRC :: tr)%list)
          by (apply (Htl r (String (ch 125) rest) (TRC :: tr));
              [ exact (List.Forall_inv_tail IHmkvs) | reflexivity | exact Hrc
              | rewrite length_app; cbn [String.length]; lia ]).
        assert (Hv : lex_aux (S (String.length (gprint 0 v ++ gprint_pairs_tl r ++ String (ch 125) rest))) (gprint 0 v ++ gprint_pairs_tl r ++ String (ch 125) rest)
                   = Some (gtokens 0 v ++ (gtokens_pairs_tl r ++ TRC :: tr))%list)
          by (apply Hlexv; [ exact Hcs | exact Htlr | rewrite !length_app; cbn [String.length]; lia ]).
        assert (Hspv : lex_aux (S (String.length (String (ch 32) (gprint 0 v ++ gprint_pairs_tl r ++ String (ch 125) rest)))) (String (ch 32) (gprint 0 v ++ gprint_pairs_tl r ++ String (ch 125) rest))
                     = Some (gtokens 0 v ++ (gtokens_pairs_tl r ++ TRC :: tr))%list)
          by (apply lex_space_app; [ exact Hv | cbn [String.length]; lia ]).
        assert (Hcolon : lex_aux (S (String.length (String (ch 58) (String (ch 32) (gprint 0 v ++ gprint_pairs_tl r ++ String (ch 125) rest))))) (String (ch 58) (String (ch 32) (gprint 0 v ++ gprint_pairs_tl r ++ String (ch 125) rest)))
                       = Some (TColon :: (gtokens 0 v ++ (gtokens_pairs_tl r ++ TRC :: tr)))%list)
          by (apply lex_colon_app; [ exact Hspv | cbn [String.length]; lia ]).
        rewrite !str_app_assoc.
        change (": " ++ (gprint 0 v ++ (gprint_pairs_tl r ++ String (ch 125) rest)))%string
          with (String (ch 58) (String (ch 32) (gprint 0 v ++ gprint_pairs_tl r ++ String (ch 125) rest))).
        rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc.
        apply Hlexk; [ reflexivity | exact Hcolon | rewrite !length_app; cbn [String.length]; lia ]. }
    assert (Hlc : lex_aux (S (String.length (String (ch 123) (gprint_pairs mkvs ++ String (ch 125) rest))))
                          (String (ch 123) (gprint_pairs mkvs ++ String (ch 125) rest))
                = Some (TLC :: (gtokens_pairs mkvs ++ TRC :: tr))%list)
      by (apply lex_lbrace_app; [ exact Hpairs | cbn [String.length]; lia ]).
    rewrite !str_app_assoc.
    change (print_ty (GTMap mkt mvt) ++ ("{" ++ (gprint_pairs mkvs ++ ("}" ++ rest))))%string
      with (print_ty (GTMap mkt mvt) ++ String (ch 123) (gprint_pairs mkvs ++ String (ch 125) rest))%string.
    rewrite (gttokens_ty_lex (GTMap mkt mvt) (String (ch 123) (gprint_pairs mkvs ++ String (ch 125) rest)) fuel
               (TLC :: (gtokens_pairs mkvs ++ TRC :: tr)) ltac:(reflexivity) Hlc
               ltac:(rewrite gprint_EMapLit in Hfuel; cbn [String.length] in Hfuel |- *;
                     repeat rewrite length_app in Hfuel; repeat rewrite length_app;
                     cbn [String.length] in Hfuel |- *; lia)).
    rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
  - (* EStr sv: the string-literal leaf — [print_string_lit sv] lexes to [TStr sv] (mirrors EId/EInt) *)
    cbn [gprint gtokens app] in *. apply lex_gprint_str; assumption.
Qed.

(** THE HEADLINE (lexer half): [lex (gprint ctx e) = Some (gtokens ctx e)] — the printed AST lexes to its
    canonical token list, for EVERY expression. *)
Theorem gtokens_lex : forall e ctx, lex (gprint ctx e) = Some (gtokens ctx e).
Proof.
  intros e ctx. unfold lex.
  assert (Hb : S (String.length (gprint ctx e) + String.length "") <= S (String.length (gprint ctx e)))
    by (cbn [String.length]; lia).
  pose proof (lex_gprint_app e ctx "" (S (String.length (gprint ctx e))) nil eq_refl eq_refl Hb) as H.
  rewrite str_app_nil_r in H. rewrite app_nil_r in H. exact H.
Qed.

(** ==================================================================================================
    ---- THE PARSER ROUND-TRIP (M3c) ----  [parse_expr] inverts [gtokens]: the canonical token list of
    [e] (printed at any context [ctx >= k]) parses back to [e], leaving any clean tail [rest] untouched.
    Proved by the classic PRECEDENCE-CLIMBING decomposition — peel [e]'s left spine into a [base] primary
    and a list of [(op, right)] pairs ([lspine]); [parse_primary] reads the base, [parse_climb] folds the
    spine ([parse_climb_pairs]).  Composed with [gtokens_lex] this gives the end-to-end
    [parse_str (gprint 0 e) = Some (e, [])].  (The clean-AST analog of the deleted string round-trip.)
    ================================================================================================== *)

(** node count — the parse fuel budget ([3*esize e] partitions exactly across the spine; see [lspine_fuel3]). *)
Fixpoint esize (e : GExpr) : nat :=
  match e with
  | EId _ => 1 | EInt _ => 1 | EStr _ => 1
  | EUn _ e => S (S (S (esize e)))   (* +3: 2 operand-paren tokens + 1 for the parse_primary postfix layer *)
  | EBn _ l r => S (esize l + esize r)
  | ESel e _ => S (S (esize e))      (* +2: the TDot + field tokens *)
  | EIndex e i => S (S (esize e + esize i))   (* +2: the TLB + TRB brackets (around the index child) *)
  | ESlice e lo hi => S (S (S (esize e + esize lo + esize hi)))  (* +3: TLB + TColon + TRB (also covers the two-child parse-fuel budget) *)
  | ECall e args => S (esize e + (fix esa (l : list GExpr) : nat :=
                                    match l with nil => 0 | a :: r => S (esize a + esa r) end) args)
      (* args contribute [sum (esize a) + length args] — one unit per arg covers its printed comma, keeping
         esize <= token length while [3*esize] still covers the MAX-based parse_args fuel (see ECall plan). *)
  | EAssert e T => S (S (esize e + tsize T))   (* +2: the TDot + TLP/TRP around the type (the GoTy child) *)
  | EConv c e => S (S (esize e + tsize (convty_ty c)))   (* +2: the TLP/TRP around the operand; type via tsize *)
  | ESliceLit t es => S (S (tsize t + (fix esa (l : list GExpr) : nat :=
                                         match l with nil => 0 | a :: r => S (esize a + esa r) end) es))
      (* +2: the '['']' bracket pair before the type ([{]/[}] covered by the per-element +1, as ECall's commas).
         Element sum + length mirrors ECall's args; [esize_ESliceLit] re-folds onto [esa]. *)
  | EMapLit kt vt kvs => S (S (tsize kt + tsize vt + (fix mpa (l : list (GExpr * GExpr)) : nat :=
                                                        match l with nil => 0 | (k, v) :: r => S (esize k + esize v + mpa r) end) kvs))
      (* +2: the map[K]V prefix's two bracket/keyword tokens beyond [tsize kt + tsize vt] ([{]/[}]/colons covered
         by the per-pair +1).  Pair sum + length; [esize_EMapLit] re-folds onto [mpa]. *)
  end.
Lemma esize_pos : forall e, 1 <= esize e.
Proof. intro e; destruct e; cbn [esize]; lia. Qed.
(** standalone arg-size sum (mirrors the local [fix] in [esize]'s ECall case); [esize_ECall] re-folds. *)
Fixpoint esa (l : list GExpr) : nat := match l with nil => 0 | a :: r => S (esize a + esa r) end.
Lemma esa_eq : forall l,
  (fix esa0 (l0 : list GExpr) : nat := match l0 with nil => 0 | a :: r => S (esize a + esa0 r) end) l = esa l.
Proof. induction l as [ | a r IH ]; [ reflexivity | cbn [esa]; rewrite <- IH; reflexivity ]. Qed.
Lemma esize_ECall : forall e0 args, esize (ECall e0 args) = S (esize e0 + esa args).
Proof.
  intros e0 args.
  change (esize (ECall e0 args))
    with (S (esize e0 + (fix esa0 (l0 : list GExpr) : nat :=
                           match l0 with nil => 0 | a :: r => S (esize a + esa0 r) end) args)).
  rewrite esa_eq. reflexivity.
Qed.
Lemma esize_ESliceLit : forall t es, esize (ESliceLit t es) = S (S (tsize t + esa es)).
Proof.
  intros t es.
  change (esize (ESliceLit t es))
    with (S (S (tsize t + (fix esa0 (l0 : list GExpr) : nat :=
                             match l0 with nil => 0 | a :: r => S (esize a + esa0 r) end) es))).
  rewrite esa_eq. reflexivity.
Qed.
(** standalone pair-size sum (mirrors the local [fix] in [esize]'s EMapLit case); [esize_EMapLit] re-folds. *)
Fixpoint mpa (l : list (GExpr * GExpr)) : nat := match l with nil => 0 | (k, v) :: r => S (esize k + esize v + mpa r) end.
Lemma mpa_eq : forall l,
  (fix mpa0 (l0 : list (GExpr * GExpr)) : nat := match l0 with nil => 0 | (k, v) :: r => S (esize k + esize v + mpa0 r) end) l = mpa l.
Proof. induction l as [ | [k v] r IH ]; [ reflexivity | cbn [mpa]; rewrite <- IH; reflexivity ]. Qed.
Lemma esize_EMapLit : forall kt vt kvs, esize (EMapLit kt vt kvs) = S (S (tsize kt + tsize vt + mpa kvs)).
Proof.
  intros kt vt kvs.
  change (esize (EMapLit kt vt kvs))
    with (S (S (tsize kt + tsize vt + (fix mpa0 (l0 : list (GExpr * GExpr)) : nat :=
                                         match l0 with nil => 0 | (k, v) :: r => S (esize k + esize v + mpa0 r) end) kvs))).
  rewrite mpa_eq. reflexivity.
Qed.

(** the operand-wrap [gtparen] only ADDS tokens, so it never shrinks below the operand's node count —
    factored out of the five identical postfix [assert]s below (one [unfold gtparen]/[destruct]/[lia] each). *)
Lemma esize_le_gtparen : forall e0,
  (forall ctx, esize e0 <= List.length (gtokens ctx e0)) ->
  esize e0 <= List.length (gtparen e0).
Proof.
  intros e0 IH. unfold gtparen; destruct e0;
    cbn [List.length op_needs_paren]; rewrite ?List.length_app; cbn [List.length]; pose proof (IH 0); lia.
Qed.

(** A printed expression is at least as many tokens as it has nodes — so [parse]'s [3*length+3] fuel
    always covers the [3*esize+2] budget. *)
Lemma length_gtokens_ge_esize : forall e ctx, esize e <= List.length (gtokens ctx e).
Proof.
  induction e as [ i | z | o e0 IH | o l IHl r IHr | es IHs fs | eb IHb ix IHx | esl IHsl slo IHlo shi IHhi | ec IHec ecargs IHargs | ea IHea T | cv ecv IHcv | slt sles IHsles | mkt mvt mkvs IHmkvs | sv ]
    using GExpr_ind'; intro ctx.
  - cbn; lia.
  - cbn; lia.
  - cbn [esize gtokens List.length]. destruct o; cbn [List.length]; rewrite !List.length_app;
      pose proof (IH 0); cbn [List.length]; lia.
  - cbn [esize gtokens List.length]. pose proof (IHl (binop_prec o)); pose proof (IHr (S (binop_prec o))).
    destruct (Nat.ltb (binop_prec o) ctx); cbn [List.length]; rewrite !List.length_app; cbn [List.length]; lia.
  - (* ESel es fs *) rewrite gtokens_ESel, List.length_app. cbn [esize List.length].
    assert (Hb : esize es <= List.length (gtparen es)) by (apply esize_le_gtparen; exact IHs).
    lia.
  - (* EIndex eb ix *) rewrite gtokens_EIndex, List.length_app. cbn [esize List.length].
    rewrite List.length_app. cbn [List.length].
    assert (Hb : esize eb <= List.length (gtparen eb)) by (apply esize_le_gtparen; exact IHb).
    pose proof (IHx 0) as Hx. lia.
  - (* ESlice esl slo shi *) rewrite gtokens_ESlice, List.length_app. cbn [esize List.length].
    rewrite List.length_app. cbn [List.length]. rewrite List.length_app. cbn [List.length].
    assert (Hb : esize esl <= List.length (gtparen esl)) by (apply esize_le_gtparen; exact IHsl).
    pose proof (IHlo 0) as Hlo'. pose proof (IHhi 0) as Hhi'. lia.
  - (* ECall ec ecargs *) rewrite esize_ECall, (gtokens_ECall ctx ec ecargs), List.length_app.
    cbn [List.length]. rewrite List.length_app. cbn [List.length].
    assert (Hb : esize ec <= List.length (gtparen ec)) by (apply esize_le_gtparen; exact IHec).
    assert (Hat : forall l, List.Forall (fun a => forall ctx0, esize a <= List.length (gtokens ctx0 a)) l ->
                  esa l <= List.length (gtokens_args_tl l)).
    { induction l as [ | b m IHm ]; intro Hfa; [ cbn [esa gtokens_args_tl]; lia | ].
      cbn [esa gtokens_args_tl List.length]. rewrite List.length_app.
      pose proof (List.Forall_inv Hfa 0) as Hbb. pose proof (IHm (List.Forall_inv_tail Hfa)) as Hmm. lia. }
    assert (Hae : esa ecargs <= List.length (gtokens_args ecargs) + 1).
    { destruct ecargs as [ | a r ]; [ cbn [esa gtokens_args]; lia | ].
      cbn [esa gtokens_args]. rewrite List.length_app.
      pose proof (List.Forall_inv IHargs 0) as Hbb. pose proof (Hat r (List.Forall_inv_tail IHargs)) as Hmm. lia. }
    lia.
  - (* EAssert ea T *) rewrite gtokens_EAssert, List.length_app. cbn [esize List.length].
    rewrite List.length_app. cbn [List.length].
    assert (Hb : esize ea <= List.length (gtparen ea)) by (apply esize_le_gtparen; exact IHea).
    pose proof (tsize_le_len T) as Ht. lia.
  - (* EConv cv ecv *) rewrite gtokens_EConv, List.length_app. cbn [esize List.length].
    rewrite List.length_app. cbn [List.length].
    pose proof (tsize_le_len (convty_ty cv)) as Ht. pose proof (IHcv 0) as He. lia.
  - (* ESliceLit slt sles — mirror ECall's element-list bound; the type prefix via [tsize_le_len] *)
    rewrite esize_ESliceLit, (gtokens_ESliceLit ctx slt sles).
    cbn [List.length]. rewrite List.length_app. cbn [List.length]. rewrite List.length_app. cbn [List.length].
    pose proof (tsize_le_len slt) as Ht.
    assert (Hat : forall l, List.Forall (fun a => forall ctx0, esize a <= List.length (gtokens ctx0 a)) l ->
                  esa l <= List.length (gtokens_args_tl l)).
    { induction l as [ | b m IHm ]; intro Hfa; [ cbn [esa gtokens_args_tl]; lia | ].
      cbn [esa gtokens_args_tl List.length]. rewrite List.length_app.
      pose proof (List.Forall_inv Hfa 0) as Hbb. pose proof (IHm (List.Forall_inv_tail Hfa)) as Hmm. lia. }
    assert (Hae : esa sles <= List.length (gtokens_args sles) + 1).
    { destruct sles as [ | a r ]; [ cbn [esa gtokens_args]; lia | ].
      cbn [esa gtokens_args]. rewrite List.length_app.
      pose proof (List.Forall_inv IHsles 0) as Hbb. pose proof (Hat r (List.Forall_inv_tail IHsles)) as Hmm. lia. }
    lia.
  - (* EMapLit mkt mvt mkvs — the map[K]V prefix via [tsize_le_len]; the KEYED pair list bounded like ECall's args *)
    rewrite esize_EMapLit, (gtokens_EMapLit ctx mkt mvt mkvs).
    rewrite List.length_app. cbn [List.length]. rewrite List.length_app. cbn [List.length].
    pose proof (tsize_le_len (GTMap mkt mvt)) as Ht. cbn [tsize] in Ht.
    assert (Hmt : forall l, List.Forall (fun p => (forall ctx0, esize (fst p) <= List.length (gtokens ctx0 (fst p)))
                                               /\ (forall ctx0, esize (snd p) <= List.length (gtokens ctx0 (snd p)))) l ->
                  mpa l <= List.length (gtokens_pairs_tl l)).
    { induction l as [ | [k v] m IHm ]; intro Hfa; [ cbn [mpa gtokens_pairs_tl]; lia | ].
      cbn [mpa gtokens_pairs_tl List.length]. rewrite !List.length_app. cbn [List.length]. rewrite !List.length_app.
      destruct (List.Forall_inv Hfa) as [ Hbk Hbv ]. cbn [fst snd] in Hbk, Hbv.
      pose proof (Hbk 0). pose proof (Hbv 0). pose proof (IHm (List.Forall_inv_tail Hfa)) as Hmm. lia. }
    assert (Hme : mpa mkvs <= List.length (gtokens_pairs mkvs) + 1).
    { destruct mkvs as [ | [k v] r ]; [ cbn [mpa gtokens_pairs]; lia | ].
      cbn [mpa gtokens_pairs]. rewrite !List.length_app. cbn [List.length]. rewrite !List.length_app.
      destruct (List.Forall_inv IHmkvs) as [ Hbk Hbv ]. cbn [fst snd] in Hbk, Hbv.
      pose proof (Hbk 0). pose proof (Hbv 0). pose proof (Hmt r (List.Forall_inv_tail IHmkvs)) as Hmm. lia. }
    lia.
  - (* EStr sv — a leaf: [gtokens] is [TStr sv :: nil], length 1 = esize *) cbn; lia.
Qed.

(** [tail_ok k rest] — a tail at which [parse_climb k] STOPS: empty, led by a NON-infix token, or led by
    an infix operator binding LOOSER than [k] (precedence [< k]).  (The token analog of the old string
    [tail_ok]; discrete tokens make it a one-line match — no [good_seam] char analysis.) *)
(** a postfix starter — the [parse_postfix] loop consumes a [TDot]-led [.field]; a clean tail must not. *)
Definition is_postfix_start (t : Token) : bool := match t with TDot => true | TLB => true | TLP => true | _ => false end.

Definition tail_ok (k : nat) (rest : list Token) : Prop :=
  match rest with
  | nil => True
  | t :: _ => is_postfix_start t = false /\ match infix_op t with Some o => binop_prec o < k | None => True end
  end.

Lemma tail_ok_mono : forall k k' rest, tail_ok k rest -> k <= k' -> tail_ok k' rest.
Proof.
  intros k k' rest H Hle. destruct rest as [ | t rs ]; [ exact I | ].
  cbn [tail_ok] in *. destruct H as [ Hp Hi ]. split; [ exact Hp | ].
  destruct (infix_op t); [ lia | exact I ].
Qed.
Lemma tail_ok_pclean : forall k rest, tail_ok k rest ->
  match rest with nil => True | t :: _ => is_postfix_start t = false end.
Proof. intros k rest H. destruct rest as [ | t rs ]; [ exact I | exact (proj1 H) ]. Qed.

(** fuel-unfold lemmas (one [S] exposes the head match of each mutually-recursive parser). *)
Lemma parse_expr_S : forall f k toks, parse_expr (S f) k toks =
  match parse_primary f toks with Some (l, r) => parse_climb f k l r | None => None end.
Proof. reflexivity. Qed.
Lemma parse_primary_S : forall f toks, parse_primary (S f) toks =
  match parse_atom f toks with Some (a, r) => parse_postfix f a r | None => None end.
Proof. reflexivity. Qed.
Lemma parse_atom_S : forall f toks, parse_atom (S f) toks =
  match toks with
  | TLP :: rest => match parse_expr f 0 rest with Some (e, TRP :: r) => Some (e, r) | _ => None end
  | TBang  :: rest => match parse_atom f rest with Some (e, r) => Some (EUn UNot e, r)   | None => None end
  | TCaret :: rest => match parse_atom f rest with Some (e, r) => Some (EUn UXor e, r)   | None => None end
  | TStar  :: rest => match parse_atom f rest with Some (e, r) => Some (EUn UDeref e, r) | None => None end
  | TAmp   :: rest => match parse_atom f rest with Some (e, r) => Some (EUn UAddr e, r)  | None => None end
  | TMinus :: TLP :: rest => match parse_expr f 0 rest with Some (e, TRP :: r) => Some (EUn UNeg e, r) | _ => None end
  | TLB :: TRB :: _ =>
      match parse_gty f toks with
      | Some (GTSlice u, TLP :: r1) => match parse_expr f 0 r1 with Some (e, TRP :: r2) => Some (EConv (CTSlice u) e, r2) | _ => None end
      | Some (GTSlice u, TLC :: r1) => match parse_elems f r1 with Some (es, r2) => Some (ESliceLit u es, r2) | None => None end
      | _ => None end
  | TChan :: _ =>
      match parse_gty f toks with
      | Some (GTChan u, TLP :: r1) => match parse_expr f 0 r1 with Some (e, TRP :: r2) => Some (EConv (CTChan u) e, r2) | _ => None end
      | _ => None end
  | TMap :: _ =>
      match parse_gty f toks with
      | Some (GTMap k v, TLP :: r1) => match parse_expr f 0 r1 with Some (e, TRP :: r2) => Some (EConv (CTMap k v) e, r2) | _ => None end
      | Some (GTMap k v, TLC :: r1) => match parse_map_elems f r1 with Some (kvs, r2) => Some (EMapLit k v kvs, r2) | None => None end
      | _ => None end
  | TId i :: rest  => Some (EId i, rest)
  | TInt z :: rest => Some (EInt z, rest)
  | TStr s :: rest => Some (EStr s, rest)
  | _ => None
  end.
Proof. reflexivity. Qed.
Lemma parse_postfix_S : forall f a toks, parse_postfix (S f) a toks =
  match toks with
  | TDot :: TLP :: rest =>
      match parse_gty f rest with Some (T, TRP :: r) => parse_postfix f (EAssert a T) r | _ => None end
  | TDot :: TId field :: rest => parse_postfix f (ESel a field) rest
  | TLB :: rest =>
      match parse_expr f 0 rest with
      | Some (lo, TColon :: r1) =>
          match parse_expr f 0 r1 with Some (hi, TRB :: r2) => parse_postfix f (ESlice a lo hi) r2 | _ => None end
      | Some (i, TRB :: r) => parse_postfix f (EIndex a i) r
      | _ => None
      end
  | TLP :: rest => match parse_args f rest with Some (args, r) => parse_postfix f (ECall a args) r | None => None end
  | _ => Some (a, toks)
  end.
Proof. reflexivity. Qed.
Lemma parse_climb_S : forall f k l toks, parse_climb (S f) k l toks =
  match toks with
  | t :: rest =>
      match infix_op t with
      | Some o => if Nat.leb k (binop_prec o)
                  then match parse_expr f (S (binop_prec o)) rest with
                       | Some (r, r2) => parse_climb f k (EBn o l r) r2
                       | None => None end
                  else Some (l, toks)
      | None => Some (l, toks)
      end
  | nil => Some (l, toks)
  end.
Proof. reflexivity. Qed.
Lemma parse_args_S : forall f toks, parse_args (S f) toks =
  match toks with
  | TRP :: r => Some (nil, r)
  | _ => match parse_expr f 0 toks with
         | Some (a, r0) => match parse_args_tl f r0 with Some (args, r1) => Some (a :: args, r1) | None => None end
         | None => None
         end
  end.
Proof. reflexivity. Qed.
Lemma parse_args_tl_S : forall f toks, parse_args_tl (S f) toks =
  match toks with
  | TRP :: r => Some (nil, r)
  | TComma :: r => match parse_expr f 0 r with
                   | Some (a, r0) => match parse_args_tl f r0 with Some (args, r1) => Some (a :: args, r1) | None => None end
                   | None => None
                   end
  | _ => None
  end.
Proof. reflexivity. Qed.
(** [parse_args] on a NON-empty (not ')'-led) token stream takes the parse-an-expr branch.  This sidesteps
    the opaque-head reduction: the arg tokens begin with [gtokens]'s first token, never [TRP]. *)
Definition starts_TRP (toks : list Token) : bool := match toks with TRP :: _ => true | _ => false end.
Lemma parse_args_cons : forall F toks, starts_TRP toks = false ->
  parse_args (S F) toks = match parse_expr F 0 toks with
    | Some (a, r0) => match parse_args_tl F r0 with Some (args, r1) => Some (a :: args, r1) | None => None end
    | None => None
    end.
Proof. intros F toks H. rewrite parse_args_S. destruct toks as [ | t r ]; [ reflexivity | destruct t; try reflexivity; discriminate H ]. Qed.
(** [parse_elems] / [parse_elems_tl] fuel-unfold + cons lemmas — VERBATIM the [parse_args] ones with terminator
    [TRP] replaced by [TRC]. *)
Lemma parse_elems_S : forall f toks, parse_elems (S f) toks =
  match toks with
  | TRC :: r => Some (nil, r)
  | _ => match parse_expr f 0 toks with
         | Some (a, r0) => match parse_elems_tl f r0 with Some (es, r1) => Some (a :: es, r1) | None => None end
         | None => None
         end
  end.
Proof. reflexivity. Qed.
Lemma parse_elems_tl_S : forall f toks, parse_elems_tl (S f) toks =
  match toks with
  | TRC :: r => Some (nil, r)
  | TComma :: r => match parse_expr f 0 r with
                   | Some (a, r0) => match parse_elems_tl f r0 with Some (es, r1) => Some (a :: es, r1) | None => None end
                   | None => None
                   end
  | _ => None
  end.
Proof. reflexivity. Qed.
Definition starts_TRC (toks : list Token) : bool := match toks with TRC :: _ => true | _ => false end.
Lemma parse_elems_cons : forall F toks, starts_TRC toks = false ->
  parse_elems (S F) toks = match parse_expr F 0 toks with
    | Some (a, r0) => match parse_elems_tl F r0 with Some (es, r1) => Some (a :: es, r1) | None => None end
    | None => None
    end.
Proof. intros F toks H. rewrite parse_elems_S. destruct toks as [ | t r ]; [ reflexivity | destruct t; try reflexivity; discriminate H ]. Qed.
(** [parse_map_elems] / [parse_map_elems_tl] fuel-unfold + cons lemmas — like the [parse_elems] ones, but each
    element parses a KEY, expects [TColon], then a VALUE. *)
Lemma parse_map_elems_S : forall f toks, parse_map_elems (S f) toks =
  match toks with
  | TRC :: r => Some (nil, r)
  | _ => match parse_expr f 0 toks with
         | Some (k, TColon :: r0) =>
             match parse_expr f 0 r0 with
             | Some (v, r1) => match parse_map_elems_tl f r1 with Some (kvs, r2) => Some ((k, v) :: kvs, r2) | None => None end
             | None => None
             end
         | _ => None
         end
  end.
Proof. reflexivity. Qed.
Lemma parse_map_elems_tl_S : forall f toks, parse_map_elems_tl (S f) toks =
  match toks with
  | TRC :: r => Some (nil, r)
  | TComma :: r =>
      match parse_expr f 0 r with
      | Some (k, TColon :: r0) =>
          match parse_expr f 0 r0 with
          | Some (v, r1) => match parse_map_elems_tl f r1 with Some (kvs, r2) => Some ((k, v) :: kvs, r2) | None => None end
          | None => None
          end
      | _ => None
      end
  | _ => None
  end.
Proof. reflexivity. Qed.
Lemma parse_map_elems_cons : forall F toks, starts_TRC toks = false ->
  parse_map_elems (S F) toks = match parse_expr F 0 toks with
    | Some (k, TColon :: r0) =>
        match parse_expr F 0 r0 with
        | Some (v, r1) => match parse_map_elems_tl F r1 with Some (kvs, r2) => Some ((k, v) :: kvs, r2) | None => None end
        | None => None
        end
    | _ => None
    end.
Proof. intros F toks H. rewrite parse_map_elems_S. destruct toks as [ | t r ]; [ reflexivity | destruct t; try reflexivity; discriminate H ]. Qed.

(** [parse_climb] stops cleanly at a [tail_ok] tail, returning the accumulated left operand untouched. *)
Lemma tail_ok_climb_stop : forall k rest F l, tail_ok k rest -> parse_climb (S F) k l rest = Some (l, rest).
Proof.
  intros k rest F l H. rewrite parse_climb_S.
  destruct rest as [ | t rs ]; [ reflexivity | ].
  cbn [tail_ok] in H. destruct H as [ _ Hi ]. destruct (infix_op t) eqn:E; [ | reflexivity ].
  rewrite (proj2 (Nat.leb_gt _ _) Hi). reflexivity.
Qed.

(** [parse_postfix] stops (the loop consumes nothing) at a tail whose head is not a postfix starter. *)
Lemma parse_postfix_stop : forall F a r,
  (match r with nil => True | t :: _ => is_postfix_start t = false end) ->
  parse_postfix (S F) a r = Some (a, r).
Proof.
  intros F a r H. rewrite parse_postfix_S. destruct r as [ | t rest ]; [ reflexivity | ].
  destruct t; cbn [is_postfix_start] in H; solve [ reflexivity | discriminate H ].
Qed.

(** The per-tree round-trip property, carried as a hypothesis for sub-operands inside the spine fold.
    Budget [3*esize e + 2 < F]: the [+2] is the slack a wrapped (parenthesised) [e] needs. *)
Definition Pexpr (e : GExpr) : Prop :=
  forall k ctx rest F, k <= ctx -> tail_ok k rest -> 3 * esize e + 3 < F ->
    parse_expr F k (gtokens ctx e ++ rest)%list = Some (e, rest).

(** A LEFT-LEANING spine: a [base] operand and a list of [(operator, right-operand)] pairs printed in
    sequence.  [fold_pairs] rebuilds the (left-associative) tree, [gtok_pairs] the token surface. *)
Fixpoint gtok_pairs (ps : list (BinOp * GExpr)) : list Token :=
  match ps with
  | nil => nil
  | (o, r) :: ps' => op_token o :: (gtokens (S (binop_prec o)) r ++ gtok_pairs ps')%list
  end.
Fixpoint fold_pairs (base : GExpr) (ps : list (BinOp * GExpr)) : GExpr :=
  match ps with nil => base | (o, r) :: ps' => fold_pairs (EBn o base r) ps' end.
Fixpoint pairs_fuel (ps : list (BinOp * GExpr)) : nat :=
  match ps with nil => 2 | (_, r) :: ps' => S (3 * esize r + 2 + pairs_fuel ps') end.
(** Climb-readiness: every operator binds at precedence [>= k], consecutive operators are NON-increasing
    (left-associativity — so each right operand parse stops before the next operator), and every right
    operand round-trips ([Pexpr]). *)
Fixpoint spine_ok (k : nat) (ps : list (BinOp * GExpr)) : Prop :=
  match ps with
  | nil => True
  | (o, r) :: ps' => k <= binop_prec o /\ Pexpr r
      /\ (match ps' with nil => True | (o2, _) :: _ => binop_prec o2 <= binop_prec o end)
      /\ spine_ok k ps'
  end.

Lemma pairs_fuel_pos : forall ps, 2 <= pairs_fuel ps.
Proof. intro ps. destruct ps as [ | [o r] ps' ]; cbn [pairs_fuel]; lia. Qed.

Lemma gtok_pairs_app : forall a b, gtok_pairs (a ++ b)%list = (gtok_pairs a ++ gtok_pairs b)%list.
Proof.
  induction a as [ | [o r] a IH ]; intro b; cbn [gtok_pairs app]; [ reflexivity | ].
  rewrite IH, app_assoc. reflexivity.
Qed.
Lemma fold_pairs_app : forall a b base, fold_pairs base (a ++ b)%list = fold_pairs (fold_pairs base a) b.
Proof.
  induction a as [ | [o r] a IH ]; intros b base; cbn [fold_pairs app]; [ reflexivity | apply IH ].
Qed.

Lemma gtok_pairs_snoc_pclean : forall ps0 o r rest,
  match (gtok_pairs (ps0 ++ (o, r) :: nil)%list ++ rest)%list with nil => True | t :: _ => is_postfix_start t = false end.
Proof.
  intros ps0 o r rest. destruct ps0 as [ | [o1 r1] ps0' ]; cbn [gtok_pairs app];
    [ destruct o; reflexivity | destruct o1; reflexivity ].
Qed.

(** SPINE FOLD — [parse_climb] consumes a printed left-leaning spine EXACTLY, left-folding it back to
    [fold_pairs base ps] and stopping at the [tail_ok] tail.  Induction on the pair list; each step recovers
    one operator ([infix_op_token]), parses the right operand ([Pexpr]), folds, and recurses. *)
Lemma parse_climb_pairs : forall ps k base rest F,
  spine_ok k ps -> tail_ok k rest -> pairs_fuel ps <= F ->
  parse_climb F k base (gtok_pairs ps ++ rest)%list = Some (fold_pairs base ps, rest).
Proof.
  induction ps as [ | [o r] ps' IH ]; intros k base rest F Hsp Htl HF.
  - cbn [gtok_pairs fold_pairs app] in *. destruct F as [ | f ]; [ cbn [pairs_fuel] in HF; lia | ].
    apply tail_ok_climb_stop; exact Htl.
  - cbn [pairs_fuel] in HF. destruct F as [ | f ]; [ lia | ].
    destruct Hsp as [ Hk [ Hpr [ Hnext Hsp' ] ] ].
    cbn [gtok_pairs fold_pairs]. rewrite parse_climb_S.
    cbn [app]. rewrite infix_op_token.
    rewrite (proj2 (Nat.leb_le _ _) Hk).
    assert (Htl2 : tail_ok (S (binop_prec o)) (gtok_pairs ps' ++ rest)%list).
    { destruct ps' as [ | [o2 r2] ps'' ].
      - cbn [gtok_pairs app]. apply (tail_ok_mono k); [ exact Htl | lia ].
      - cbn [gtok_pairs app]. cbn [tail_ok]. rewrite infix_op_token. split; [ destruct o2; reflexivity | lia ]. }
    pose proof (pairs_fuel_pos ps') as Hpos. pose proof (esize_pos r) as Her.
    rewrite <- app_assoc.
    rewrite (Hpr (S (binop_prec o)) (S (binop_prec o)) (gtok_pairs ps' ++ rest)%list f
                 (le_n _) Htl2 ltac:(lia)).
    apply IH; [ exact Hsp' | exact Htl | lia ].
Qed.

Lemma ltb_false_of_leb : forall fl p, Nat.leb fl p = true -> Nat.ltb p fl = false.
Proof.
  intros fl p H. apply Nat.leb_le in H. apply Nat.ltb_ge. exact H.
Qed.

(** ---- LEFT-SPINE DECOMPOSITION ---- [lspine fl e] peels [e]'s left children while they print UNWRAPPED
    at the running floor (operator precedence [>= floor]), yielding the leftmost PRIMARY [base], the floor
    [bfl], and the spine of [(operator, right-operand)] pairs.  [gtokens fl e = gtokens bfl base ++
    gtok_pairs ps] and [fold_pairs base ps = e]: print- and structure-faithful. *)
Fixpoint lspine (fl : nat) (e : GExpr) : nat * GExpr * list (BinOp * GExpr) :=
  match e with
  | EId i  => (fl, EId i, nil)
  | EInt z => (fl, EInt z, nil)
  | EStr s => (fl, EStr s, nil)
  | EUn o e => (fl, EUn o e, nil)
  | ESel e0 f => (fl, ESel e0 f, nil)   (* a selector is a PRIMARY base — no binary left-spine *)
  | EIndex e0 i => (fl, EIndex e0 i, nil)   (* an index is also a PRIMARY base *)
  | ESlice e0 lo hi => (fl, ESlice e0 lo hi, nil)   (* a slice is also a PRIMARY base *)
  | ECall e0 args => (fl, ECall e0 args, nil)   (* a call is also a PRIMARY base *)
  | EAssert e0 T => (fl, EAssert e0 T, nil)   (* a type assertion is also a PRIMARY base *)
  | EConv c e0 => (fl, EConv c e0, nil)   (* a type-form conversion is also a PRIMARY base *)
  | ESliceLit t es => (fl, ESliceLit t es, nil)   (* a slice composite literal is also a PRIMARY base *)
  | EMapLit kt vt kvs => (fl, EMapLit kt vt kvs, nil)   (* a map composite literal is also a PRIMARY base *)
  | EBn o l r =>
      if Nat.leb fl (binop_prec o)
      then let '(bfl, base, ps) := lspine (binop_prec o) l in (bfl, base, (ps ++ (o, r) :: nil)%list)
      else (fl, EBn o l r, nil)
  end.

Lemma lspine_print : forall e fl bfl base ps,
  lspine fl e = (bfl, base, ps) -> gtokens fl e = (gtokens bfl base ++ gtok_pairs ps)%list.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | es IHs fs | eb IHb ix IHx | esl IHsl slo IHlo shi IHhi | ec IHec ecargs | ea IHea T | ecv ece IHec | eslt esles | ekt evt ekvs | sv ]; intros fl bfl base ps H.
  - cbn in H. inversion H; subst. cbn [gtok_pairs]. rewrite app_nil_r. reflexivity.
  - cbn in H. inversion H; subst. cbn [gtok_pairs]. rewrite app_nil_r. reflexivity.
  - cbn in H. inversion H; subst. cbn [gtok_pairs]. rewrite app_nil_r. reflexivity.
  - cbn [lspine] in H. destruct (Nat.leb fl (binop_prec o)) eqn:Eleb.
    + destruct (lspine (binop_prec o) l) as [ [ bfl0 base0 ] ps0 ] eqn:El.
      inversion H; subst. clear H.
      cbn [gtokens]. rewrite (ltb_false_of_leb _ _ Eleb), (IHl _ _ _ _ El), gtok_pairs_app.
      cbn [gtok_pairs]. rewrite app_nil_r, <- !app_assoc. cbn [app]. reflexivity.
    + inversion H; subst. cbn [gtok_pairs]. rewrite app_nil_r. reflexivity.
  - cbn in H. inversion H; subst. cbn [gtok_pairs]. rewrite app_nil_r. reflexivity.
  - cbn in H. inversion H; subst. cbn [gtok_pairs]. rewrite app_nil_r. reflexivity.
  - cbn in H. inversion H; subst. cbn [gtok_pairs]. rewrite app_nil_r. reflexivity.
  - cbn in H. inversion H; subst. cbn [gtok_pairs]. rewrite app_nil_r. reflexivity.
  - cbn in H. inversion H; subst. cbn [gtok_pairs]. rewrite app_nil_r. reflexivity.
  - cbn in H. inversion H; subst. cbn [gtok_pairs]. rewrite app_nil_r. reflexivity.
  - cbn in H. inversion H; subst. cbn [gtok_pairs]. rewrite app_nil_r. reflexivity.
  - cbn in H. inversion H; subst. cbn [gtok_pairs]. rewrite app_nil_r. reflexivity.
  - (* EStr sv *) cbn in H. inversion H; subst. cbn [gtok_pairs]. rewrite app_nil_r. reflexivity.
Qed.

Lemma lspine_fold : forall e fl bfl base ps,
  lspine fl e = (bfl, base, ps) -> fold_pairs base ps = e.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | es IHs fs | eb IHb ix IHx | esl IHsl slo IHlo shi IHhi | ec IHec ecargs | ea IHea T | ecv ece IHec | eslt esles | ekt evt ekvs | sv ]; intros fl bfl base ps H.
  - cbn in H. inversion H; subst. reflexivity.
  - cbn in H. inversion H; subst. reflexivity.
  - cbn in H. inversion H; subst. reflexivity.
  - cbn [lspine] in H. destruct (Nat.leb fl (binop_prec o)) eqn:Eleb.
    + destruct (lspine (binop_prec o) l) as [ [ bfl0 base0 ] ps0 ] eqn:El.
      inversion H; subst. clear H.
      rewrite fold_pairs_app. cbn [fold_pairs]. rewrite (IHl _ _ _ _ El). reflexivity.
    + inversion H; subst. reflexivity.
  - cbn in H. inversion H; subst. reflexivity.
  - cbn in H. inversion H; subst. reflexivity.
  - cbn in H. inversion H; subst. reflexivity.
  - cbn in H. inversion H; subst. reflexivity.
  - cbn in H. inversion H; subst. reflexivity.
  - cbn in H. inversion H; subst. reflexivity.
  - cbn in H. inversion H; subst. reflexivity.
  - cbn in H. inversion H; subst. reflexivity.
  - (* EStr sv *) cbn in H. inversion H; subst. reflexivity.
Qed.

(** [spine_ok] tolerates a LOWER climb level, and accepts an operator appended at the spine end when the
    existing spine already binds at [>= prec o]. *)
Lemma spine_ok_weaken : forall ps k k', spine_ok k ps -> k' <= k -> spine_ok k' ps.
Proof.
  induction ps as [ | [o r] ps' IH ]; intros k k' H Hle; cbn [spine_ok] in *; [ exact I | ].
  destruct H as [ Hk [ Hpr [ Hnext Hsp' ] ] ].
  split; [ lia | split; [ exact Hpr | split; [ exact Hnext | apply (IH k); assumption ] ] ].
Qed.
Lemma spine_ok_snoc : forall ps o r, spine_ok (binop_prec o) ps -> Pexpr r ->
  spine_ok (binop_prec o) (ps ++ (o, r) :: nil)%list.
Proof.
  induction ps as [ | [o1 r1] ps' IH ]; intros o r Hsp Hpr.
  - cbn [spine_ok app]. split; [ lia | split; [ exact Hpr | split; exact I ] ].
  - cbn [app spine_ok] in *. destruct Hsp as [ Hk1 [ Hpr1 [ Hnext1 Hsp1 ] ] ].
    split; [ exact Hk1 | split; [ exact Hpr1 | split ] ].
    + destruct ps' as [ | [o2 r2] ps'' ]; cbn [app]; [ exact Hk1 | exact Hnext1 ].
    + apply IH; [ exact Hsp1 | exact Hpr ].
Qed.

(** [spine_ok] of the decomposed spine: each operand [Pexpr] via the size-IH; non-increasing precedences
    via [spine_ok_snoc]. *)
Lemma lspine_spine_ok : forall e fl bfl base ps,
  (forall e', esize e' < esize e -> Pexpr e') ->
  lspine fl e = (bfl, base, ps) -> spine_ok fl ps.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | es IHs fs | eb IHb ix IHx | esl IHsl slo IHlo shi IHhi | ec IHec ecargs | ea IHea T | ecv ece IHec | eslt esles | ekt evt ekvs | sv ]; intros fl bfl base ps Hsih H.
  - cbn in H. inversion H; subst. exact I.
  - cbn in H. inversion H; subst. exact I.
  - cbn in H. inversion H; subst. exact I.
  - cbn [lspine] in H. destruct (Nat.leb fl (binop_prec o)) eqn:Eleb.
    + destruct (lspine (binop_prec o) l) as [ [ bfl0 base0 ] ps0 ] eqn:El.
      inversion H; subst.
      apply (spine_ok_weaken _ (binop_prec o)); [ | apply Nat.leb_le; exact Eleb ].
      apply spine_ok_snoc.
      * eapply IHl; [ | exact El ].
        intros e' He'. apply Hsih. cbn [esize]. lia.
      * apply Hsih. cbn [esize]. lia.
    + inversion H; subst. exact I.
  - cbn in H. inversion H; subst. exact I.
  - cbn in H. inversion H; subst. exact I.
  - cbn in H. inversion H; subst. exact I.
  - cbn in H. inversion H; subst. exact I.
  - cbn in H. inversion H; subst. exact I.
  - cbn in H. inversion H; subst. exact I.
  - cbn in H. inversion H; subst. exact I.
  - cbn in H. inversion H; subst. exact I.
  - (* EStr sv *) cbn in H. inversion H; subst. exact I.
Qed.

(** The base is a PRIMARY: a literal/unary leaf, or an [EBn] wrapped because [bfl] exceeds its operator
    precedence (so it prints parenthesised). *)
Lemma lspine_base : forall e fl bfl base ps,
  lspine fl e = (bfl, base, ps) ->
  match base with EBn o' _ _ => binop_prec o' < bfl | _ => True end.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | es IHs fs | eb IHb ix IHx | esl IHsl slo IHlo shi IHhi | ec IHec ecargs | ea IHea T | ecv ece IHec | eslt esles | ekt evt ekvs | sv ]; intros fl bfl base ps H.
  - cbn in H. inversion H; subst. exact I.
  - cbn in H. inversion H; subst. exact I.
  - cbn in H. inversion H; subst. exact I.
  - cbn [lspine] in H. destruct (Nat.leb fl (binop_prec o)) eqn:Eleb.
    + destruct (lspine (binop_prec o) l) as [ [ bfl0 base0 ] ps0 ] eqn:El.
      inversion H; subst. apply (IHl _ _ _ _ El).
    + inversion H; subst. apply Nat.leb_gt in Eleb. exact Eleb.
  - cbn in H. inversion H; subst. exact I.
  - cbn in H. inversion H; subst. exact I.
  - cbn in H. inversion H; subst. exact I.
  - cbn in H. inversion H; subst. exact I.
  - cbn in H. inversion H; subst. exact I.
  - cbn in H. inversion H; subst. exact I.
  - cbn in H. inversion H; subst. exact I.
  - cbn in H. inversion H; subst. exact I.
  - (* EStr sv *) cbn in H. inversion H; subst. exact I.
Qed.

Lemma lspine_base_le : forall e fl bfl base ps, lspine fl e = (bfl, base, ps) -> esize base <= esize e.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | es IHs fs | eb IHb ix IHx | esl IHsl slo IHlo shi IHhi | ec IHec ecargs | ea IHea T | ecv ece IHec | eslt esles | ekt evt ekvs | sv ]; intros fl bfl base ps H.
  - cbn in H. inversion H; subst. cbn [esize]. lia.
  - cbn in H. inversion H; subst. cbn [esize]. lia.
  - cbn in H. inversion H; subst. cbn [esize]. lia.
  - cbn [lspine] in H. destruct (Nat.leb fl (binop_prec o)) eqn:Eleb.
    + destruct (lspine (binop_prec o) l) as [ [ bfl0 base0 ] ps0 ] eqn:El.
      inversion H; subst. pose proof (IHl _ _ _ _ El). cbn [esize]. lia.
    + inversion H; subst. cbn [esize]. lia.
  - cbn in H. inversion H; subst. cbn [esize]. lia.
  - cbn in H. inversion H; subst. cbn [esize]. lia.
  - cbn in H. inversion H; subst. cbn [esize]. lia.
  - cbn in H. inversion H; subst. cbn [esize]. lia.
  - cbn in H. inversion H; subst. cbn [esize]. lia.
  - cbn in H. inversion H; subst. cbn [esize]. lia.
  - cbn in H. inversion H; subst. cbn [esize]. lia.
  - cbn in H. inversion H; subst. cbn [esize]. lia.
  - (* EStr sv *) cbn in H. inversion H; subst. cbn [esize]. lia.
Qed.

Lemma pairs_fuel_snoc : forall ps o r, pairs_fuel (ps ++ (o, r) :: nil)%list = pairs_fuel ps + (3 * esize r + 3).
Proof.
  induction ps as [ | [o1 r1] ps' IH ]; intros o r; cbn [app pairs_fuel]; [ lia | rewrite IH; lia ].
Qed.

(** Base size and spine fuel partition exactly [S (3*esize e)] — so [3*esize e] budget covers both. *)
Lemma lspine_fuel3 : forall e fl bfl base ps,
  lspine fl e = (bfl, base, ps) -> 3 * esize base + pairs_fuel ps = S (S (3 * esize e)).
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | es IHs fs | eb IHb ix IHx | esl IHsl slo IHlo shi IHhi | ec IHec ecargs | ea IHea T | ecv ece IHec | eslt esles | ekt evt ekvs | sv ]; intros fl bfl base ps H.
  - cbn in H. inversion H; subst. cbn [esize pairs_fuel]. lia.
  - cbn in H. inversion H; subst. cbn [esize pairs_fuel]. lia.
  - cbn in H. inversion H; subst. cbn [esize pairs_fuel]. lia.
  - cbn [lspine] in H. destruct (Nat.leb fl (binop_prec o)) eqn:Eleb.
    + destruct (lspine (binop_prec o) l) as [ [ bfl0 base0 ] ps0 ] eqn:El.
      inversion H; subst. clear H. rewrite pairs_fuel_snoc.
      pose proof (IHl _ _ _ _ El) as IH. cbn [esize]. lia.
    + inversion H; subst. cbn [esize pairs_fuel]. lia.
  - cbn in H. inversion H; subst. cbn [esize pairs_fuel]. lia.
  - cbn in H. inversion H; subst. cbn [esize pairs_fuel]. lia.
  - cbn in H. inversion H; subst. cbn [esize pairs_fuel]. lia.
  - cbn in H. inversion H; subst. cbn [esize pairs_fuel]. lia.
  - cbn in H. inversion H; subst. cbn [esize pairs_fuel]. lia.
  - cbn in H. inversion H; subst. cbn [esize pairs_fuel]. lia.
  - cbn in H. inversion H; subst. cbn [esize pairs_fuel]. lia.
  - cbn in H. inversion H; subst. cbn [esize pairs_fuel]. lia.
  - (* EStr sv *) cbn in H. inversion H; subst. cbn [esize pairs_fuel]. lia.
Qed.

(** [parse_primary] reads a unary node: each prints [op] then its PARENTHESISED operand (always wrapped,
    so the seam is a single ['('] — no maximal-munch hazard).  The four bare ops dispatch on their token;
    [UNeg] on the two-token [TMinus :: TLP] prefix.  Operand via [Pexpr] (the outer strong IH). *)
(** a PRIMARY is its atom when the postfix loop consumes nothing (or folds a chain via [parse_postfix_pairs]). *)
Lemma parse_primary_of_atom : forall f toks a r,
  parse_atom (S f) toks = Some (a, r) ->
  (match r with nil => True | t :: _ => is_postfix_start t = false end) ->
  parse_primary (S (S f)) toks = Some (a, r).
Proof. intros f toks a r H Hr. rewrite parse_primary_S, H. apply parse_postfix_stop; exact Hr. Qed.

(** [parse_atom] reads a unary node: each prints [op] then its PARENTHESISED operand (always wrapped, so
    the seam is a single ['('] — no maximal-munch hazard).  Operand via [Pexpr] (the outer strong IH). *)
Lemma parse_atom_unary : forall o e0 ctx TAIL F,
  Pexpr e0 -> 3 * esize e0 + 5 < F ->
  parse_atom F (gtokens ctx (EUn o e0) ++ TAIL)%list = Some (EUn o e0, TAIL).
Proof.
  intros o e0 ctx TAIL F HP HF. pose proof (esize_pos e0) as Hpos.
  assert (Hpar : forall G, 3 * esize e0 + 3 < G ->
            parse_atom (S G) (TLP :: (gtokens 0 e0 ++ TRP :: TAIL))%list = Some (e0, TAIL)).
  { intros G HG. rewrite parse_atom_S.
    rewrite (HP 0 0 (TRP :: TAIL) G (le_n 0) (conj eq_refl I) ltac:(lia)). reflexivity. }
  destruct o; cbn [gtokens prefix_token]; cbn [app]; rewrite <- app_assoc; cbn [app].
  - destruct F as [ | f1 ]; [ lia | ]. rewrite parse_atom_S.
    destruct f1 as [ | f2 ]; [ lia | ]. rewrite (Hpar f2 ltac:(lia)). reflexivity.
  - destruct F as [ | f1 ]; [ lia | ]. rewrite parse_atom_S.
    destruct f1 as [ | f2 ]; [ lia | ]. rewrite (Hpar f2 ltac:(lia)). reflexivity.
  - destruct F as [ | f1 ]; [ lia | ]. rewrite parse_atom_S.
    destruct f1 as [ | f2 ]; [ lia | ]. rewrite (Hpar f2 ltac:(lia)). reflexivity.
  - destruct F as [ | f1 ]; [ lia | ]. rewrite parse_atom_S.
    destruct f1 as [ | f2 ]; [ lia | ]. rewrite (Hpar f2 ltac:(lia)). reflexivity.
  - destruct F as [ | f1 ]; [ lia | ]. rewrite parse_atom_S.
    rewrite (HP 0 0 (TRP :: TAIL) f1 (le_n 0) (conj eq_refl I) ltac:(lia)). reflexivity.
Qed.
Lemma parse_primary_unary : forall o e0 ctx TAIL F,
  Pexpr e0 -> (match TAIL with nil => True | t :: _ => is_postfix_start t = false end) ->
  3 * esize e0 + 6 < F ->
  parse_primary F (gtokens ctx (EUn o e0) ++ TAIL)%list = Some (EUn o e0, TAIL).
Proof.
  intros o e0 ctx TAIL F HP Hcl HF. destruct F as [ | F' ]; [ lia | ]. destruct F' as [ | f ]; [ lia | ].
  apply parse_primary_of_atom; [ apply parse_atom_unary; [ exact HP | lia ] | exact Hcl ].
Qed.

(** A binop printed at a context that exceeds its precedence is PARENTHESISED: its tokens are
    [TLP :: (its-unwrapped-tokens ++ TRP)]. *)
Lemma gtokens_wrapped : forall o l r ctx, Nat.ltb (binop_prec o) ctx = true ->
  gtokens ctx (EBn o l r) = (TLP :: (gtokens (binop_prec o) (EBn o l r) ++ TRP :: nil))%list.
Proof.
  intros o l r ctx Hw. cbn [gtokens]. rewrite Hw.
  assert (Hp : Nat.ltb (binop_prec o) (binop_prec o) = false) by (apply Nat.ltb_ge; lia).
  rewrite Hp. reflexivity.
Qed.

(** ---- POSTFIX SPINE ---- peel a postfix chain (selector/index) to its innermost (non-postfix) base + the
    op list ([POp]); [parse_postfix] folds the ops ([parse_postfix_pairs]), [parse_atom] reads the base. *)
Inductive POp := PSel : Ident -> POp | PIdx : GExpr -> POp | PSlice : GExpr -> GExpr -> POp | PCall : list GExpr -> POp | PAssert : GoTy -> POp.
Fixpoint pspine (e : GExpr) : GExpr * list POp :=
  match e with
  | ESel e0 f => let (b, ops) := pspine e0 in (b, (ops ++ PSel f :: nil)%list)
  | EIndex e0 i => let (b, ops) := pspine e0 in (b, (ops ++ PIdx i :: nil)%list)
  | ESlice e0 lo hi => let (b, ops) := pspine e0 in (b, (ops ++ PSlice lo hi :: nil)%list)
  | ECall e0 args => let (b, ops) := pspine e0 in (b, (ops ++ PCall args :: nil)%list)
  | EAssert e0 T => let (b, ops) := pspine e0 in (b, (ops ++ PAssert T :: nil)%list)
  | _ => (e, nil)
  end.
Fixpoint gtokens_pops (ops : list POp) : list Token :=
  match ops with
  | nil => nil
  | PSel f :: ops' => TDot :: TId f :: gtokens_pops ops'
  | PIdx i :: ops' => TLB :: (gtokens 0 i ++ TRB :: gtokens_pops ops')
  | PSlice lo hi :: ops' => TLB :: (gtokens 0 lo ++ TColon :: (gtokens 0 hi ++ TRB :: gtokens_pops ops'))
  | PCall args :: ops' => TLP :: (gtokens_args args ++ TRP :: gtokens_pops ops')
  | PAssert T :: ops' => TDot :: TLP :: (gttokens_ty T ++ TRP :: gtokens_pops ops')
  end.
Fixpoint fold_pops (b : GExpr) (ops : list POp) : GExpr :=
  match ops with
  | nil => b
  | PSel f :: ops' => fold_pops (ESel b f) ops'
  | PIdx i :: ops' => fold_pops (EIndex b i) ops'
  | PSlice lo hi :: ops' => fold_pops (ESlice b lo hi) ops'
  | PCall args :: ops' => fold_pops (ECall b args) ops'
  | PAssert T :: ops' => fold_pops (EAssert b T) ops'
  end.

Lemma gtokens_pops_app : forall a b, gtokens_pops (a ++ b)%list = (gtokens_pops a ++ gtokens_pops b)%list.
Proof.
  induction a as [ | op a IH ]; intro b; [ reflexivity | ].
  destruct op as [ f | i | lo hi | args | T ]; cbn [gtokens_pops app]; rewrite IH.
  - reflexivity.
  - rewrite <- app_assoc; reflexivity.
  - rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
  - rewrite <- !app_assoc; cbn [app]; reflexivity.
  - rewrite <- !app_assoc; cbn [app]; reflexivity.
Qed.
Lemma fold_pops_app : forall a b base, fold_pops base (a ++ b)%list = fold_pops (fold_pops base a) b.
Proof.
  induction a as [ | op a IH ]; intros b base; [ reflexivity | ].
  destruct op as [ f | i | lo hi | args | T ]; cbn [fold_pops app]; apply IH.
Qed.

Lemma pspine_fold : forall e, fold_pops (fst (pspine e)) (snd (pspine e)) = e.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T | c0 ece0 IHc0 | eslt esles | ekt evt ekvs | sv ]; cbn [pspine]; try reflexivity;
    destruct (pspine e0) as [ b ops ] eqn:Ep; cbn [fst snd] in *;
    rewrite fold_pops_app; cbn [fold_pops]; rewrite IHe0; reflexivity.
Qed.
Lemma pspine_base_kind : forall e,
  match fst (pspine e) with ESel _ _ => False | EIndex _ _ => False | ESlice _ _ _ => False | ECall _ _ => False | EAssert _ _ => False | _ => True end.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T | c0 ece0 IHc0 | eslt esles | ekt evt ekvs | sv ]; cbn [pspine]; try exact I;
    destruct (pspine e0) as [ b ops ] eqn:Ep; cbn [fst] in *; exact IHe0.
Qed.
Lemma pspine_esize : forall e, esize (fst (pspine e)) <= esize e.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T | c0 ece0 IHc0 | eslt esles | ekt evt ekvs | sv ];
    try (cbn; lia);
    cbn [pspine]; destruct (pspine e0) as [ b ops ] eqn:Ep; cbn [fst esize] in *; lia.
Qed.
(** a chain (selector/index top) has a STRICTLY smaller base. *)
Lemma pspine_esize_lt : forall e0 f, esize (fst (pspine (ESel e0 f))) < esize (ESel e0 f).
Proof.
  intros e0 f. pose proof (pspine_esize e0). cbn [pspine esize].
  destruct (pspine e0) as [ b ops ]. cbn [fst] in *. lia.
Qed.
Lemma pspine_esize_lt_idx : forall e0 i, esize (fst (pspine (EIndex e0 i))) < esize (EIndex e0 i).
Proof.
  intros e0 i. pose proof (pspine_esize e0). cbn [pspine esize].
  destruct (pspine e0) as [ b ops ]. cbn [fst] in *. lia.
Qed.
Lemma pspine_esize_lt_slice : forall e0 lo hi, esize (fst (pspine (ESlice e0 lo hi))) < esize (ESlice e0 lo hi).
Proof.
  intros e0 lo hi. pose proof (pspine_esize e0). cbn [pspine esize].
  destruct (pspine e0) as [ b ops ]. cbn [fst] in *. lia.
Qed.
Lemma pspine_esize_lt_call : forall e0 args, esize (fst (pspine (ECall e0 args))) < esize (ECall e0 args).
Proof.
  intros e0 args. pose proof (pspine_esize e0). rewrite esize_ECall. cbn [pspine].
  destruct (pspine e0) as [ b ops ]. cbn [fst] in *. lia.
Qed.
Lemma pspine_esize_lt_assert : forall e0 T, esize (fst (pspine (EAssert e0 T))) < esize (EAssert e0 T).
Proof.
  intros e0 T. pose proof (pspine_esize e0). cbn [pspine esize].
  destruct (pspine e0) as [ b ops ]. cbn [fst] in *. lia.
Qed.

(** the chain's tokens = [gtparen] of the innermost base ++ the op tokens (holds for ALL e). *)
Lemma gtparen_pspine : forall e, gtparen e = (gtparen (fst (pspine e)) ++ gtokens_pops (snd (pspine e)))%list.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T | c0 ece0 IHc0 | eslt esles | ekt evt ekvs | sv ]; cbn [pspine];
    try (cbn [fst snd gtokens_pops]; rewrite app_nil_r; reflexivity).
  - destruct (pspine e0) as [ b ops ] eqn:Ep. cbn [fst snd] in *.
    change (gtparen (ESel e0 f)) with (gtparen e0 ++ TDot :: TId f :: nil)%list.
    rewrite IHe0, gtokens_pops_app. cbn [gtokens_pops]. rewrite <- app_assoc. reflexivity.
  - destruct (pspine e0) as [ b ops ] eqn:Ep. cbn [fst snd] in *.
    change (gtparen (EIndex e0 ix)) with (gtparen e0 ++ TLB :: (gtokens 0 ix ++ TRB :: nil))%list.
    rewrite IHe0, gtokens_pops_app. cbn [gtokens_pops]. rewrite <- app_assoc. reflexivity.
  - destruct (pspine e0) as [ b ops ] eqn:Ep. cbn [fst snd] in *.
    change (gtparen (ESlice e0 slo shi))
      with (gtparen e0 ++ TLB :: (gtokens 0 slo ++ TColon :: (gtokens 0 shi ++ TRB :: nil)))%list.
    rewrite IHe0, gtokens_pops_app. cbn [gtokens_pops]. rewrite <- !app_assoc. reflexivity.
  - destruct (pspine e0) as [ b ops ] eqn:Ep. cbn [fst snd] in *.
    change (gtparen (ECall e0 ecargs)) with (gtokens 0 (ECall e0 ecargs)).
    rewrite gtokens_ECall, IHe0, gtokens_pops_app. cbn [gtokens_pops]. rewrite <- !app_assoc. reflexivity.
  - destruct (pspine e0) as [ b ops ] eqn:Ep. cbn [fst snd] in *.
    change (gtparen (EAssert e0 T)) with (gtokens 0 (EAssert e0 T)).
    rewrite gtokens_EAssert, IHe0, gtokens_pops_app. cbn [gtokens_pops]. rewrite <- !app_assoc. reflexivity.
Qed.

(** [parse_args] consumes fuel MAX-wise (each arg parses at a fresh fuel, NOT a running sum), so the arg-list
    fuel is a [Nat.max] recurrence — this is what keeps it within the [3*esize] budget (a sum measure would
    exceed it; see the ECall plan).  [af_le] bounds it by [3*esa + 2]. *)
Fixpoint af (args : list GExpr) : nat :=
  match args with nil => 1 | a :: r => S (Nat.max (3 * esize a + 4) (af r)) end.
Lemma af_le : forall args, af args <= 3 * esa args + 2.
Proof.
  induction args as [ | a r IH ]; [ cbn [af esa]; lia | ].
  cbn [af esa]. pose proof (Nat.le_max_l (3 * esize a + 4) (af r)).
  pose proof (Nat.le_max_r (3 * esize a + 4) (af r)). lia.
Qed.
(** [parse_map_elems] consumes fuel MAX-wise too: each pair parses its KEY and VALUE at a fresh fuel, so the
    pair-list fuel is the [Nat.max] over BOTH children of each pair (and the tail).  [mf_le] bounds it by
    [3*mpa + 2], staying within the [3*esize] budget. *)
Fixpoint mf (kvs : list (GExpr * GExpr)) : nat :=
  match kvs with nil => 1 | (k, v) :: r => S (Nat.max (3 * esize k + 4) (Nat.max (3 * esize v + 4) (mf r))) end.
Lemma mf_le : forall kvs, mf kvs <= 3 * mpa kvs + 2.
Proof.
  induction kvs as [ | [k v] r IH ]; [ cbn [mf mpa]; lia | ].
  cbn [mf mpa]. pose proof (Nat.le_max_l (3 * esize k + 4) (Nat.max (3 * esize v + 4) (mf r))).
  pose proof (Nat.le_max_r (3 * esize k + 4) (Nat.max (3 * esize v + 4) (mf r))).
  pose proof (Nat.le_max_l (3 * esize v + 4) (mf r)).
  pose proof (Nat.le_max_r (3 * esize v + 4) (mf r)). lia.
Qed.

(** the [parse_postfix] fuel an op run needs: 1 per selector, [3*esize i + 3] per index child, two such for a
    slice's two bounds, [af args] for a call's argument list. *)
Fixpoint pops_fuel (ops : list POp) : nat :=
  match ops with
  | nil => 1
  | PSel _ :: ops' => S (pops_fuel ops')
  | PIdx i :: ops' => S (3 * esize i + 3 + pops_fuel ops')
  | PSlice lo hi :: ops' => S (3 * esize lo + 3 + 3 * esize hi + 3 + pops_fuel ops')
  | PCall args :: ops' => S (af args + pops_fuel ops')
  | PAssert T :: ops' => S (tsize T + pops_fuel ops')
  end.
Lemma pops_fuel_pos : forall ops, 1 <= pops_fuel ops.
Proof. destruct ops as [ | op ops' ]; [ cbn; lia | destruct op; cbn [pops_fuel]; lia ]. Qed.
Lemma pops_fuel_snoc_sel : forall ops f, pops_fuel (ops ++ PSel f :: nil)%list = S (pops_fuel ops).
Proof. induction ops as [ | op ops IH ]; intro f; [ reflexivity | destruct op; cbn [pops_fuel app]; rewrite IH; lia ]. Qed.
Lemma pops_fuel_snoc_idx : forall ops i, pops_fuel (ops ++ PIdx i :: nil)%list = pops_fuel ops + (3 * esize i + 4).
Proof. induction ops as [ | op ops IH ]; intro i; [ cbn [pops_fuel app]; lia | destruct op; cbn [pops_fuel app]; rewrite IH; lia ]. Qed.
Lemma pops_fuel_snoc_slice : forall ops lo hi,
  pops_fuel (ops ++ PSlice lo hi :: nil)%list = pops_fuel ops + (3 * esize lo + 3 * esize hi + 7).
Proof. induction ops as [ | op ops IH ]; intros lo hi; [ cbn [pops_fuel app]; lia | destruct op; cbn [pops_fuel app]; rewrite IH; lia ]. Qed.
Lemma pops_fuel_snoc_call : forall ops args, pops_fuel (ops ++ PCall args :: nil)%list = pops_fuel ops + (af args + 1).
Proof. induction ops as [ | op ops IH ]; intro args; [ cbn [pops_fuel app]; lia | destruct op; cbn [pops_fuel app]; rewrite IH; lia ]. Qed.
Lemma pops_fuel_snoc_assert : forall ops T, pops_fuel (ops ++ PAssert T :: nil)%list = pops_fuel ops + (tsize T + 1).
Proof. induction ops as [ | op ops IH ]; intro T; [ cbn [pops_fuel app]; lia | destruct op; cbn [pops_fuel app]; rewrite IH; lia ]. Qed.
Lemma pspine_pops_fuel : forall e, pops_fuel (snd (pspine e)) <= 3 * esize e.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T | c0 ece0 IHc0 | eslt esles | ekt evt ekvs | sv ];
    try (cbn; lia).
  - cbn [pspine]. destruct (pspine e0) as [ b ops ] eqn:Ep. cbn [snd esize] in *. rewrite pops_fuel_snoc_sel. lia.
  - cbn [pspine]. destruct (pspine e0) as [ b ops ] eqn:Ep. cbn [snd esize] in *. rewrite pops_fuel_snoc_idx. lia.
  - cbn [pspine]. destruct (pspine e0) as [ b ops ] eqn:Ep. cbn [snd esize] in *. rewrite pops_fuel_snoc_slice. lia.
  - cbn [pspine]. destruct (pspine e0) as [ b ops ] eqn:Ep. rewrite esize_ECall. cbn [snd] in *.
    rewrite pops_fuel_snoc_call. pose proof (af_le ecargs). lia.
  - cbn [pspine]. destruct (pspine e0) as [ b ops ] eqn:Ep. cbn [snd esize] in *. rewrite pops_fuel_snoc_assert. lia.
Qed.
Lemma pspine_snd_sel : forall e0 f, snd (pspine (ESel e0 f)) = (snd (pspine e0) ++ PSel f :: nil)%list.
Proof. intros e0 f. cbn [pspine]. destruct (pspine e0). reflexivity. Qed.
Lemma pspine_snd_idx : forall e0 i, snd (pspine (EIndex e0 i)) = (snd (pspine e0) ++ PIdx i :: nil)%list.
Proof. intros e0 i. cbn [pspine]. destruct (pspine e0). reflexivity. Qed.
Lemma pspine_snd_slice : forall e0 lo hi, snd (pspine (ESlice e0 lo hi)) = (snd (pspine e0) ++ PSlice lo hi :: nil)%list.
Proof. intros e0 lo hi. cbn [pspine]. destruct (pspine e0). reflexivity. Qed.
Lemma pspine_snd_call : forall e0 args, snd (pspine (ECall e0 args)) = (snd (pspine e0) ++ PCall args :: nil)%list.
Proof. intros e0 args. cbn [pspine]. destruct (pspine e0). reflexivity. Qed.
Lemma pspine_snd_assert : forall e0 T, snd (pspine (EAssert e0 T)) = (snd (pspine e0) ++ PAssert T :: nil)%list.
Proof. intros e0 T. cbn [pspine]. destruct (pspine e0). reflexivity. Qed.
Lemma pspine_pidx_esize : forall e i, List.In (PIdx i) (snd (pspine e)) -> esize i < esize e.
Proof.
  induction e as [ i0 | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T | c0 ece0 IHc0 | eslt esles | ekt evt ekvs | sv ]; intros i Hin;
    try (cbn in Hin; contradiction).
  - rewrite pspine_snd_sel in Hin. cbn [esize].
    apply List.in_app_or in Hin. destruct Hin as [ Hin | Hin ].
    + pose proof (IHe0 i Hin). lia.
    + destruct Hin as [ H | H ]; [ discriminate H | contradiction ].
  - rewrite pspine_snd_idx in Hin. cbn [esize].
    apply List.in_app_or in Hin. destruct Hin as [ Hin | Hin ].
    + pose proof (IHe0 i Hin). lia.
    + destruct Hin as [ H | H ]; [ injection H as ->; lia | contradiction ].
  - rewrite pspine_snd_slice in Hin. cbn [esize].
    apply List.in_app_or in Hin. destruct Hin as [ Hin | Hin ].
    + pose proof (IHe0 i Hin). lia.
    + destruct Hin as [ H | H ]; [ discriminate H | contradiction ].
  - rewrite pspine_snd_call in Hin. rewrite esize_ECall.
    apply List.in_app_or in Hin. destruct Hin as [ Hin | Hin ].
    + pose proof (IHe0 i Hin). lia.
    + destruct Hin as [ H | H ]; [ discriminate H | contradiction ].
  - rewrite pspine_snd_assert in Hin. cbn [esize].
    apply List.in_app_or in Hin. destruct Hin as [ Hin | Hin ].
    + pose proof (IHe0 i Hin). lia.
    + destruct Hin as [ H | H ]; [ discriminate H | contradiction ].
Qed.
Lemma pspine_pslice_esize : forall e lo hi,
  List.In (PSlice lo hi) (snd (pspine e)) -> esize lo < esize e /\ esize hi < esize e.
Proof.
  induction e as [ i0 | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T | c0 ece0 IHc0 | eslt esles | ekt evt ekvs | sv ]; intros lo hi Hin;
    try (cbn in Hin; contradiction).
  - rewrite pspine_snd_sel in Hin. cbn [esize].
    apply List.in_app_or in Hin. destruct Hin as [ Hin | Hin ].
    + pose proof (IHe0 lo hi Hin) as [ ? ? ]. split; lia.
    + destruct Hin as [ H | H ]; [ discriminate H | contradiction ].
  - rewrite pspine_snd_idx in Hin. cbn [esize].
    apply List.in_app_or in Hin. destruct Hin as [ Hin | Hin ].
    + pose proof (IHe0 lo hi Hin) as [ ? ? ]. split; lia.
    + destruct Hin as [ H | H ]; [ discriminate H | contradiction ].
  - rewrite pspine_snd_slice in Hin. cbn [esize].
    apply List.in_app_or in Hin. destruct Hin as [ Hin | Hin ].
    + pose proof (IHe0 lo hi Hin) as [ ? ? ]. split; lia.
    + destruct Hin as [ H | H ]; [ injection H as -> ->; split; lia | contradiction ].
  - rewrite pspine_snd_call in Hin. rewrite esize_ECall.
    apply List.in_app_or in Hin. destruct Hin as [ Hin | Hin ].
    + pose proof (IHe0 lo hi Hin) as [ ? ? ]. split; lia.
    + destruct Hin as [ H | H ]; [ discriminate H | contradiction ].
  - rewrite pspine_snd_assert in Hin. cbn [esize].
    apply List.in_app_or in Hin. destruct Hin as [ Hin | Hin ].
    + pose proof (IHe0 lo hi Hin) as [ ? ? ]. split; lia.
    + destruct Hin as [ H | H ]; [ discriminate H | contradiction ].
Qed.
(** each element of an arg list is strictly smaller than the list's [esa] sum. *)
Lemma esa_in : forall l a, List.In a l -> esize a < esa l.
Proof.
  induction l as [ | b r IH ]; intros a Hin; [ contradiction | ].
  destruct Hin as [ -> | Hin ]; cbn [esa]; [ lia | pose proof (IH a Hin); lia ].
Qed.
(** each pair of a map literal's element list is strictly smaller (both key and value) than the list's [mpa] sum. *)
Lemma mpa_in : forall l p, List.In p l -> esize (fst p) + esize (snd p) < mpa l.
Proof.
  induction l as [ | [k v] r IH ]; intros p Hin; [ contradiction | ].
  cbn [mpa]. destruct Hin as [ <- | Hin ]; [ cbn [fst snd]; lia | pose proof (IH p Hin); lia ].
Qed.
(** the arguments of a [PCall] in the spine are all strictly smaller than the chain (for their [Pexpr]). *)
Lemma pspine_pcall_esize : forall e args,
  List.In (PCall args) (snd (pspine e)) -> List.Forall (fun a => esize a < esize e) args.
Proof.
  induction e as [ i0 | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T | c0 ece0 IHc0 | eslt esles | ekt evt ekvs | sv ]; intros args Hin;
    try (cbn in Hin; contradiction).
  - rewrite pspine_snd_sel in Hin. apply List.in_app_or in Hin. destruct Hin as [ Hin | Hin ].
    + eapply List.Forall_impl; [ | exact (IHe0 args Hin) ]. intros a Ha. cbn [esize] in Ha |- *; lia.
    + destruct Hin as [ H | H ]; [ discriminate H | contradiction ].
  - rewrite pspine_snd_idx in Hin. apply List.in_app_or in Hin. destruct Hin as [ Hin | Hin ].
    + eapply List.Forall_impl; [ | exact (IHe0 args Hin) ]. intros a Ha. cbn [esize] in Ha |- *; lia.
    + destruct Hin as [ H | H ]; [ discriminate H | contradiction ].
  - rewrite pspine_snd_slice in Hin. apply List.in_app_or in Hin. destruct Hin as [ Hin | Hin ].
    + eapply List.Forall_impl; [ | exact (IHe0 args Hin) ]. intros a Ha. cbn [esize] in Ha |- *; lia.
    + destruct Hin as [ H | H ]; [ discriminate H | contradiction ].
  - rewrite pspine_snd_call in Hin. apply List.in_app_or in Hin. destruct Hin as [ Hin | Hin ].
    + eapply List.Forall_impl; [ | exact (IHe0 args Hin) ]. intros a Ha. cbn beta in Ha; rewrite esize_ECall; lia.
    + destruct Hin as [ H | H ]; [ injection H as -> | contradiction ].
      apply List.Forall_forall. intros a Ha. rewrite esize_ECall. pose proof (esa_in args a Ha). lia.
  - rewrite pspine_snd_assert in Hin. apply List.in_app_or in Hin. destruct Hin as [ Hin | Hin ].
    + eapply List.Forall_impl; [ | exact (IHe0 args Hin) ]. intros a Ha. cbn [esize] in Ha |- *; lia.
    + destruct Hin as [ H | H ]; [ discriminate H | contradiction ].
Qed.

(** [gtokens]'s first token is never [TRP] (it is a closer) — so an arg stream is [TRP]-led iff empty. *)
Lemma gtokens_hd_TRP_false : forall e ctx Z, starts_TRP (gtokens ctx e ++ Z)%list = false.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T | c0 ece0 IHc0 | eslt esles | ekt evt ekvs | sv ]; intros ctx Z.
  - reflexivity.
  - reflexivity.
  - cbn [gtokens]. destruct o; reflexivity.
  - cbn [gtokens]. destruct (Nat.ltb (binop_prec o) ctx); [ reflexivity | ]. rewrite <- app_assoc. apply IHl.
  - rewrite gtokens_ESel, <- app_assoc. unfold gtparen; destruct e0; (apply IHe0 || reflexivity).
  - rewrite gtokens_EIndex, <- app_assoc. unfold gtparen; destruct e0; (apply IHe0 || reflexivity).
  - rewrite gtokens_ESlice, <- app_assoc. unfold gtparen; destruct e0; (apply IHe0 || reflexivity).
  - rewrite gtokens_ECall, <- app_assoc. unfold gtparen; destruct e0; (apply IHe0 || reflexivity).
  - rewrite gtokens_EAssert, <- app_assoc. unfold gtparen; destruct e0; (apply IHe0 || reflexivity).
  - rewrite gtokens_EConv, <- app_assoc. destruct c0 as [ u | u | k v ]; reflexivity.
  - rewrite gtokens_ESliceLit. reflexivity.
  - rewrite gtokens_EMapLit. cbn [gttokens_ty app]. reflexivity.
  - (* EStr sv *) reflexivity.
Qed.
(** the [TRC] analogue — [gtokens] never starts with the composite-literal closer either (used by
    [parse_elems_roundtrip], exactly as [gtokens_hd_TRP_false] serves [parse_args_roundtrip]). *)
Lemma gtokens_hd_TRC_false : forall e ctx Z, starts_TRC (gtokens ctx e ++ Z)%list = false.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T | c0 ece0 IHc0 | eslt esles | ekt evt ekvs | sv ]; intros ctx Z.
  - reflexivity.
  - reflexivity.
  - cbn [gtokens]. destruct o; reflexivity.
  - cbn [gtokens]. destruct (Nat.ltb (binop_prec o) ctx); [ reflexivity | ]. rewrite <- app_assoc. apply IHl.
  - rewrite gtokens_ESel, <- app_assoc. unfold gtparen; destruct e0; (apply IHe0 || reflexivity).
  - rewrite gtokens_EIndex, <- app_assoc. unfold gtparen; destruct e0; (apply IHe0 || reflexivity).
  - rewrite gtokens_ESlice, <- app_assoc. unfold gtparen; destruct e0; (apply IHe0 || reflexivity).
  - rewrite gtokens_ECall, <- app_assoc. unfold gtparen; destruct e0; (apply IHe0 || reflexivity).
  - rewrite gtokens_EAssert, <- app_assoc. unfold gtparen; destruct e0; (apply IHe0 || reflexivity).
  - rewrite gtokens_EConv, <- app_assoc. destruct c0 as [ u | u | k v ]; reflexivity.
  - rewrite gtokens_ESliceLit. reflexivity.
  - rewrite gtokens_EMapLit. cbn [gttokens_ty app]. reflexivity.
  - (* EStr sv *) reflexivity.
Qed.

(** the argument list parses back: [parse_args]/[parse_args_tl] invert [gtokens_args]/[gtokens_args_tl] up to
    and including the ')'.  Each arg round-trips via its [Pexpr] (from the [Forall]); the MAX-based [af] fuel
    suffices because each arg parses at a fresh fuel (not a running sum). *)
Lemma parse_args_tl_roundtrip : forall args rest F,
  List.Forall Pexpr args -> af args <= F ->
  parse_args_tl F (gtokens_args_tl args ++ TRP :: rest)%list = Some (args, rest).
Proof.
  induction args as [ | a r IH ]; intros rest F Hfa HF.
  - cbn [gtokens_args_tl app]. destruct F as [ | F' ]; [ cbn [af] in HF; lia | ]. rewrite parse_args_tl_S. reflexivity.
  - cbn [gtokens_args_tl]. destruct F as [ | F' ]; [ cbn [af] in HF; lia | ].
    cbn [app]. rewrite parse_args_tl_S. rewrite <- app_assoc.
    assert (Htlok : tail_ok 0 (gtokens_args_tl r ++ TRP :: rest)%list)
      by (destruct r as [ | b r' ]; cbn [gtokens_args_tl Datatypes.app tail_ok is_postfix_start infix_op]; split; (reflexivity || exact I)).
    rewrite (List.Forall_inv Hfa 0 0 (gtokens_args_tl r ++ TRP :: rest)%list F' (le_n 0) Htlok
               ltac:(cbn [af] in HF; pose proof (Nat.le_max_l (3 * esize a + 4) (af r)); lia)).
    cbv beta iota.
    rewrite (IH rest F' (List.Forall_inv_tail Hfa)
               ltac:(cbn [af] in HF; pose proof (Nat.le_max_r (3 * esize a + 4) (af r)); lia)).
    reflexivity.
Qed.
Lemma parse_args_roundtrip : forall args rest F,
  List.Forall Pexpr args -> af args <= F ->
  parse_args F (gtokens_args args ++ TRP :: rest)%list = Some (args, rest).
Proof.
  intros args rest F Hfa HF. destruct args as [ | a r ].
  - cbn [gtokens_args app]. destruct F as [ | F' ]; [ cbn [af] in HF; lia | ]. rewrite parse_args_S. reflexivity.
  - destruct F as [ | F' ]; [ cbn [af] in HF; lia | ].
    cbn [gtokens_args]. rewrite <- app_assoc.
    rewrite (parse_args_cons F' (gtokens 0 a ++ gtokens_args_tl r ++ TRP :: rest)%list
               ltac:(apply gtokens_hd_TRP_false)).
    assert (Htlok : tail_ok 0 (gtokens_args_tl r ++ TRP :: rest)%list)
      by (destruct r as [ | b r' ]; cbn [gtokens_args_tl Datatypes.app tail_ok is_postfix_start infix_op]; split; (reflexivity || exact I)).
    rewrite (List.Forall_inv Hfa 0 0 (gtokens_args_tl r ++ TRP :: rest)%list F' (le_n 0) Htlok
               ltac:(cbn [af] in HF; pose proof (Nat.le_max_l (3 * esize a + 4) (af r)); lia)).
    cbv beta iota.
    rewrite (parse_args_tl_roundtrip r rest F' (List.Forall_inv_tail Hfa)
               ltac:(cbn [af] in HF; pose proof (Nat.le_max_r (3 * esize a + 4) (af r)); lia)).
    reflexivity.
Qed.
(** the ELEMENT list parses back: [parse_elems]/[parse_elems_tl] invert [gtokens_args]/[gtokens_args_tl] up to
    and including the '}'.  VERBATIM the [parse_args] round-trips with terminator [TRP]→[TRC] (elements reuse
    the same comma machinery + [af] fuel; only the closer token differs). *)
Lemma parse_elems_tl_roundtrip : forall es rest F,
  List.Forall Pexpr es -> af es <= F ->
  parse_elems_tl F (gtokens_args_tl es ++ TRC :: rest)%list = Some (es, rest).
Proof.
  induction es as [ | a r IH ]; intros rest F Hfa HF.
  - cbn [gtokens_args_tl app]. destruct F as [ | F' ]; [ cbn [af] in HF; lia | ]. rewrite parse_elems_tl_S. reflexivity.
  - cbn [gtokens_args_tl]. destruct F as [ | F' ]; [ cbn [af] in HF; lia | ].
    cbn [app]. rewrite parse_elems_tl_S. rewrite <- app_assoc.
    assert (Htlok : tail_ok 0 (gtokens_args_tl r ++ TRC :: rest)%list)
      by (destruct r as [ | b r' ]; cbn [gtokens_args_tl Datatypes.app tail_ok is_postfix_start infix_op]; split; (reflexivity || exact I)).
    rewrite (List.Forall_inv Hfa 0 0 (gtokens_args_tl r ++ TRC :: rest)%list F' (le_n 0) Htlok
               ltac:(cbn [af] in HF; pose proof (Nat.le_max_l (3 * esize a + 4) (af r)); lia)).
    cbv beta iota.
    rewrite (IH rest F' (List.Forall_inv_tail Hfa)
               ltac:(cbn [af] in HF; pose proof (Nat.le_max_r (3 * esize a + 4) (af r)); lia)).
    reflexivity.
Qed.
Lemma parse_elems_roundtrip : forall es rest F,
  List.Forall Pexpr es -> af es <= F ->
  parse_elems F (gtokens_args es ++ TRC :: rest)%list = Some (es, rest).
Proof.
  intros es rest F Hfa HF. destruct es as [ | a r ].
  - cbn [gtokens_args app]. destruct F as [ | F' ]; [ cbn [af] in HF; lia | ]. rewrite parse_elems_S. reflexivity.
  - destruct F as [ | F' ]; [ cbn [af] in HF; lia | ].
    cbn [gtokens_args]. rewrite <- app_assoc.
    rewrite (parse_elems_cons F' (gtokens 0 a ++ gtokens_args_tl r ++ TRC :: rest)%list
               ltac:(apply gtokens_hd_TRC_false)).
    assert (Htlok : tail_ok 0 (gtokens_args_tl r ++ TRC :: rest)%list)
      by (destruct r as [ | b r' ]; cbn [gtokens_args_tl Datatypes.app tail_ok is_postfix_start infix_op]; split; (reflexivity || exact I)).
    rewrite (List.Forall_inv Hfa 0 0 (gtokens_args_tl r ++ TRC :: rest)%list F' (le_n 0) Htlok
               ltac:(cbn [af] in HF; pose proof (Nat.le_max_l (3 * esize a + 4) (af r)); lia)).
    cbv beta iota.
    rewrite (parse_elems_tl_roundtrip r rest F' (List.Forall_inv_tail Hfa)
               ltac:(cbn [af] in HF; pose proof (Nat.le_max_r (3 * esize a + 4) (af r)); lia)).
    reflexivity.
Qed.
(** the KEYED pair list parses back: [parse_map_elems]/[parse_map_elems_tl] invert [gtokens_pairs]/[gtokens_pairs_tl]
    up to and including the '}'.  Each pair's KEY parses (stopping at the [TColon]) then its VALUE (stopping at the
    pair separator / closer), both via their [Pexpr] (from the [Forall]); the MAX-based [mf] fuel covers both. *)
Lemma parse_map_elems_tl_roundtrip : forall kvs rest F,
  List.Forall (fun p => Pexpr (fst p) /\ Pexpr (snd p)) kvs -> mf kvs <= F ->
  parse_map_elems_tl F (gtokens_pairs_tl kvs ++ TRC :: rest)%list = Some (kvs, rest).
Proof.
  induction kvs as [ | [k v] r IH ]; intros rest F Hfa HF.
  - cbn [gtokens_pairs_tl app]. destruct F as [ | F' ]; [ cbn [mf] in HF; lia | ]. rewrite parse_map_elems_tl_S. reflexivity.
  - destruct F as [ | F' ]; [ cbn [mf] in HF; lia | ].
    destruct (List.Forall_inv Hfa) as [ Hpk Hpv ]. cbn [fst snd] in Hpk, Hpv.
    cbn [gtokens_pairs_tl app parse_map_elems_tl].
    rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc.
    assert (Htlk : tail_ok 0 (TColon :: (gtokens 0 v ++ (gtokens_pairs_tl r ++ TRC :: rest)))%list)
      by (cbn [tail_ok is_postfix_start infix_op]; split; (reflexivity || exact I)).
    rewrite (Hpk 0 0 (TColon :: (gtokens 0 v ++ (gtokens_pairs_tl r ++ TRC :: rest)))%list F' (le_n 0) Htlk
               ltac:(cbn [mf] in HF; pose proof (Nat.le_max_l (3 * esize k + 4) (Nat.max (3 * esize v + 4) (mf r))); lia)).
    cbv beta iota.
    assert (Htlv : tail_ok 0 (gtokens_pairs_tl r ++ TRC :: rest)%list)
      by (destruct r as [ | [k' v'] r' ]; cbn [gtokens_pairs_tl Datatypes.app tail_ok is_postfix_start infix_op]; split; (reflexivity || exact I)).
    rewrite (Hpv 0 0 (gtokens_pairs_tl r ++ TRC :: rest)%list F' (le_n 0) Htlv
               ltac:(cbn [mf] in HF; pose proof (Nat.le_max_r (3 * esize k + 4) (Nat.max (3 * esize v + 4) (mf r)));
                     pose proof (Nat.le_max_l (3 * esize v + 4) (mf r)); lia)).
    cbv beta iota.
    rewrite (IH rest F' (List.Forall_inv_tail Hfa)
               ltac:(cbn [mf] in HF; pose proof (Nat.le_max_r (3 * esize k + 4) (Nat.max (3 * esize v + 4) (mf r)));
                     pose proof (Nat.le_max_r (3 * esize v + 4) (mf r)); lia)).
    reflexivity.
Qed.
Lemma parse_map_elems_roundtrip : forall kvs rest F,
  List.Forall (fun p => Pexpr (fst p) /\ Pexpr (snd p)) kvs -> mf kvs <= F ->
  parse_map_elems F (gtokens_pairs kvs ++ TRC :: rest)%list = Some (kvs, rest).
Proof.
  intros kvs rest F Hfa HF. destruct kvs as [ | [k v] r ].
  - cbn [gtokens_pairs app]. destruct F as [ | F' ]; [ cbn [mf] in HF; lia | ]. rewrite parse_map_elems_S. reflexivity.
  - destruct F as [ | F' ]; [ cbn [mf] in HF; lia | ].
    destruct (List.Forall_inv Hfa) as [ Hpk Hpv ]. cbn [fst snd] in Hpk, Hpv.
    cbn [gtokens_pairs]. rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc.
    rewrite (parse_map_elems_cons F' (gtokens 0 k ++ TColon :: (gtokens 0 v ++ (gtokens_pairs_tl r ++ TRC :: rest)))%list
               ltac:(apply gtokens_hd_TRC_false)).
    assert (Htlk : tail_ok 0 (TColon :: (gtokens 0 v ++ (gtokens_pairs_tl r ++ TRC :: rest)))%list)
      by (cbn [tail_ok is_postfix_start infix_op]; split; (reflexivity || exact I)).
    rewrite (Hpk 0 0 (TColon :: (gtokens 0 v ++ (gtokens_pairs_tl r ++ TRC :: rest)))%list F' (le_n 0) Htlk
               ltac:(cbn [mf] in HF; pose proof (Nat.le_max_l (3 * esize k + 4) (Nat.max (3 * esize v + 4) (mf r))); lia)).
    cbv beta iota.
    assert (Htlv : tail_ok 0 (gtokens_pairs_tl r ++ TRC :: rest)%list)
      by (destruct r as [ | [k' v'] r' ]; cbn [gtokens_pairs_tl Datatypes.app tail_ok is_postfix_start infix_op]; split; (reflexivity || exact I)).
    rewrite (Hpv 0 0 (gtokens_pairs_tl r ++ TRC :: rest)%list F' (le_n 0) Htlv
               ltac:(cbn [mf] in HF; pose proof (Nat.le_max_r (3 * esize k + 4) (Nat.max (3 * esize v + 4) (mf r)));
                     pose proof (Nat.le_max_l (3 * esize v + 4) (mf r)); lia)).
    cbv beta iota.
    rewrite (parse_map_elems_tl_roundtrip r rest F' (List.Forall_inv_tail Hfa)
               ltac:(cbn [mf] in HF; pose proof (Nat.le_max_r (3 * esize k + 4) (Nat.max (3 * esize v + 4) (mf r)));
                     pose proof (Nat.le_max_r (3 * esize v + 4) (mf r)); lia)).
    reflexivity.
Qed.

(** THE TYPE-PARSER ROUND-TRIP: [parse_gty] inverts [gttokens_ty] (leaving any clean tail [rest]). *)
Lemma parse_gty_roundtrip : forall t rest F, tsize t <= F -> parse_gty F (gttokens_ty t ++ rest)%list = Some (t, rest).
Proof.
  induction t as [ | | | | | | | | | | | | | | u IHt | u IHt | u IHt | t1 IHt1 t2 IHt2 | n ];
    intros rest F HF; destruct F as [ | f ]; try (cbn [tsize] in HF; lia).
  1-14: cbn [gttokens_ty app]; rewrite parse_gty_S; reflexivity.
  - (* GTPtr u *) cbn [gttokens_ty app]. rewrite parse_gty_S. rewrite (IHt rest f ltac:(cbn [tsize] in HF; lia)). reflexivity.
  - (* GTSlice u *) cbn [gttokens_ty app]. rewrite parse_gty_S. rewrite (IHt rest f ltac:(cbn [tsize] in HF; lia)). reflexivity.
  - (* GTChan u *) cbn [gttokens_ty app]. rewrite parse_gty_S. rewrite (IHt rest f ltac:(cbn [tsize] in HF; lia)). reflexivity.
  - (* GTMap k v *) cbn [gttokens_ty]. rewrite parse_gty_S. cbn [app]. rewrite <- app_assoc. cbn [app].
    rewrite (IHt1 (TRB :: gttokens_ty t2 ++ rest)%list f ltac:(cbn [tsize] in HF; lia)).
    rewrite (IHt2 rest f ltac:(cbn [tsize] in HF; lia)). reflexivity.
  - (* GTNamed n *) cbn [gttokens_ty app]. rewrite parse_gty_S.
    assert (Hkw : is_type_keyword (proj1_sig n) = false).
    { pose proof (proj2_sig n) as Hn. unfold nominal_type_ident in Hn.
      apply andb_prop in Hn. destruct Hn as [ _ Hnk ]. apply negb_true_iff in Hnk. exact Hnk. }
    destruct (kw_false_classify _ Hkw) as [ Hcl _ ].
    cbn [tyname_to_ident mkIdent proj1_sig]. rewrite Hcl.
    destruct (bool_dec (nominal_type_ident (proj1_sig n)) true) as [ H | H ]; [ | exfalso; apply H; exact (proj2_sig n) ].
    destruct n as [ s Hs ]. cbn [proj1_sig] in *.
    assert (E : H = Hs) by apply (Eqdep_dec.UIP_dec bool_dec). rewrite E. reflexivity.
Qed.

(** [parse_postfix] folds a printed op run, left-associating into [ESel]/[EIndex]/[ESlice]/[ECall]; index/
    slice/call children parse via their [Pexpr]; stops at a postfix-clean tail. *)
Lemma parse_postfix_pairs : forall ops b rest F,
  (forall i, List.In (PIdx i) ops -> Pexpr i) ->
  (forall lo hi, List.In (PSlice lo hi) ops -> Pexpr lo /\ Pexpr hi) ->
  (forall args, List.In (PCall args) ops -> List.Forall Pexpr args) ->
  (match rest with nil => True | t :: _ => is_postfix_start t = false end) ->
  pops_fuel ops <= F ->
  parse_postfix F b (gtokens_pops ops ++ rest)%list = Some (fold_pops b ops, rest).
Proof.
  induction ops as [ | op ops IH ]; intros b rest F Hpe Hps Hpc Hcl HF.
  - cbn [gtokens_pops app fold_pops]. destruct F as [ | F' ]; [ cbn [pops_fuel] in HF; lia | ].
    apply parse_postfix_stop; exact Hcl.
  - destruct op as [ f | i | lo hi | args | T ]; cbn [gtokens_pops fold_pops].
    + (* PSel f *) destruct F as [ | F' ]; [ cbn [pops_fuel] in HF; lia | ].
      cbn [app]. rewrite parse_postfix_S.
      apply IH; [ intros j Hj; apply Hpe; right; exact Hj
                | intros lo hi Hj; apply Hps; right; exact Hj
                | intros args Hj; apply Hpc; right; exact Hj | exact Hcl | cbn [pops_fuel] in HF; lia ].
    + (* PIdx i *) destruct F as [ | F' ]; [ cbn [pops_fuel] in HF; lia | ].
      cbn [app]. rewrite parse_postfix_S. rewrite <- app_assoc. cbn [app].
      rewrite (Hpe i (or_introl eq_refl) 0 0 (TRB :: gtokens_pops ops ++ rest)%list F'
                 (le_n 0) (conj eq_refl I) ltac:(pose proof (pops_fuel_pos ops); cbn [pops_fuel] in HF; lia)).
      apply IH; [ intros j Hj; apply Hpe; right; exact Hj
                | intros lo hi Hj; apply Hps; right; exact Hj
                | intros args Hj; apply Hpc; right; exact Hj | exact Hcl | cbn [pops_fuel] in HF; lia ].
    + (* PSlice lo hi *) destruct F as [ | F' ]; [ cbn [pops_fuel] in HF; lia | ].
      destruct (Hps lo hi (or_introl eq_refl)) as [ Hplo Hphi ].
      cbn [app]. rewrite parse_postfix_S.
      rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; cbn [app].
      rewrite (Hplo 0 0 (TColon :: (gtokens 0 hi ++ TRB :: (gtokens_pops ops ++ rest)))%list F'
                 (le_n 0) (conj eq_refl I) ltac:(pose proof (pops_fuel_pos ops); cbn [pops_fuel] in HF; lia)).
      cbv beta iota.
      rewrite (Hphi 0 0 (TRB :: (gtokens_pops ops ++ rest))%list F'
                 (le_n 0) (conj eq_refl I) ltac:(pose proof (pops_fuel_pos ops); cbn [pops_fuel] in HF; lia)).
      apply IH; [ intros j Hj; apply Hpe; right; exact Hj
                | intros lo' hi' Hj; apply Hps; right; exact Hj
                | intros args Hj; apply Hpc; right; exact Hj | exact Hcl | cbn [pops_fuel] in HF; lia ].
    + (* PCall args *) destruct F as [ | F' ]; [ cbn [pops_fuel] in HF; lia | ].
      cbn [app]. rewrite parse_postfix_S. rewrite <- app_assoc. cbn [app].
      rewrite (parse_args_roundtrip args (gtokens_pops ops ++ rest)%list F'
                 (Hpc args (or_introl eq_refl)) ltac:(cbn [pops_fuel] in HF; lia)).
      apply IH; [ intros j Hj; apply Hpe; right; exact Hj
                | intros lo hi Hj; apply Hps; right; exact Hj
                | intros args' Hj; apply Hpc; right; exact Hj | exact Hcl | cbn [pops_fuel] in HF; lia ].
    + (* PAssert T *) destruct F as [ | F' ]; [ cbn [pops_fuel] in HF; lia | ].
      cbn [app]. rewrite parse_postfix_S. rewrite <- app_assoc. cbn [app].
      rewrite (parse_gty_roundtrip T (TRP :: gtokens_pops ops ++ rest)%list F' ltac:(cbn [pops_fuel] in HF; lia)).
      cbv beta iota.
      apply IH; [ intros j Hj; apply Hpe; right; exact Hj
                | intros lo hi Hj; apply Hps; right; exact Hj
                | intros args Hj; apply Hpc; right; exact Hj | exact Hcl | cbn [pops_fuel] in HF; lia ].
Qed.

(** [parse_atom] reads a type-form CONVERSION operand [EConv c e0] ([]T(x) / chan T(x) / map[K]V(x)).  At
    ATOM position a type lead ([]/chan/map) is unambiguous (no preceding operand to index), so [parse_atom]
    dispatches on it, [parse_gty] consumes [convty_ty c] ([parse_gty_roundtrip]), then the parenthesised
    operand round-trips via its [Pexpr e0].  The analogue of [parse_atom_unary] for the type-prefixed primary;
    [op_needs_paren (EConv …) = false] (a conversion is a Go PrimaryExpr — never self-parenthesised).  Both
    [parse_gty_roundtrip] and the goal are [cbn]'d identically so the head-token dispatch lines up syntactically. *)
Lemma parse_atom_conv : forall c e0 ctx TAIL F,
  Pexpr e0 -> 3 * esize e0 + tsize (convty_ty c) + 4 < F ->
  parse_atom F (gtokens ctx (EConv c e0) ++ TAIL)%list = Some (EConv c e0, TAIL).
Proof.
  intros c e0 ctx TAIL F HP HF. rewrite gtokens_EConv.
  destruct F as [ | f ]; [ lia | ].
  (* normalise the operand tail to [gtokens 0 e0 ++ TRP :: TAIL] (push [app_assoc] past the stuck
     [gtokens 0 e0] — needs the alternating dance, as the [PSlice] case does). *)
  rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; cbn [app].
  destruct c as [ u | u | k v ].
  - (* CTSlice u — []u(e0) *)
    pose proof (parse_gty_roundtrip (GTSlice u) (TLP :: (gtokens 0 e0 ++ TRP :: TAIL)) f
                  ltac:(cbn [tsize convty_ty] in HF |- *; lia)) as Hg.
    rewrite parse_atom_S. cbn [convty_ty gttokens_ty app] in Hg |- *.
    rewrite Hg. cbv beta iota.
    rewrite (HP 0 0 (TRP :: TAIL) f (le_n 0) (conj eq_refl I)
               ltac:(cbn [tsize convty_ty] in HF |- *; lia)). reflexivity.
  - (* CTChan u — chan u(e0) *)
    pose proof (parse_gty_roundtrip (GTChan u) (TLP :: (gtokens 0 e0 ++ TRP :: TAIL)) f
                  ltac:(cbn [tsize convty_ty] in HF |- *; lia)) as Hg.
    rewrite parse_atom_S. cbn [convty_ty gttokens_ty app] in Hg |- *.
    rewrite Hg. cbv beta iota.
    rewrite (HP 0 0 (TRP :: TAIL) f (le_n 0) (conj eq_refl I)
               ltac:(cbn [tsize convty_ty] in HF |- *; lia)). reflexivity.
  - (* CTMap k v — map[k]v(e0) *)
    pose proof (parse_gty_roundtrip (GTMap k v) (TLP :: (gtokens 0 e0 ++ TRP :: TAIL)) f
                  ltac:(cbn [tsize convty_ty] in HF |- *; lia)) as Hg.
    rewrite parse_atom_S. cbn [convty_ty gttokens_ty app] in Hg |- *.
    rewrite Hg. cbv beta iota.
    rewrite (HP 0 0 (TRP :: TAIL) f (le_n 0) (conj eq_refl I)
               ltac:(cbn [tsize convty_ty] in HF |- *; lia)). reflexivity.
Qed.

(** [parse_atom] reads a slice composite literal [ESliceLit t es] ([[]T{e1,..,en}]).  At ATOM position the
    [[]T] lead is a type ([parse_gty] consumes [GTSlice t]); the NEXT token '{' (TLC) — vs the conversion's
    '(' (TLP) — selects the literal, then [parse_elems] consumes the brace-delimited element list
    ([parse_elems_roundtrip]).  Each element round-trips via its [Pexpr] (from the [Forall]).  The type-led
    analogue of [parse_atom_conv]; [op_needs_paren (ESliceLit …) = false] (a Go PrimaryExpr). *)
Lemma parse_atom_slicelit : forall t es ctx TAIL F,
  List.Forall Pexpr es -> tsize t + 3 * esa es + 4 < F ->
  parse_atom F (gtokens ctx (ESliceLit t es) ++ TAIL)%list = Some (ESliceLit t es, TAIL).
Proof.
  intros t es ctx TAIL F Hfa HF. rewrite gtokens_ESliceLit.
  destruct F as [ | f ]; [ lia | ].
  (* normalise the input to [TLB :: TRB :: gttokens_ty t ++ TLC :: (gtokens_args es ++ TRC :: TAIL)] — push the
     stuck [gttokens_ty t]/[gtokens_args es] appends right (alternating, as the EConv case does, +1 round for
     the leading '['']' conses). *)
  cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; cbn [app].
  pose proof (parse_gty_roundtrip (GTSlice t) (TLC :: (gtokens_args es ++ TRC :: TAIL)) f
                ltac:(cbn [tsize]; lia)) as Hg.
  rewrite parse_atom_S. cbn [gttokens_ty app] in Hg |- *.
  rewrite Hg. cbv beta iota.
  rewrite (parse_elems_roundtrip es TAIL f Hfa ltac:(pose proof (af_le es); lia)).
  reflexivity.
Qed.

(** [parse_atom] reads a map composite literal [EMapLit kt vt kvs] ([map[K]V{k1: v1,..,kn: vn}]).  At ATOM
    position the [map[K]V] lead is a type ([parse_gty] consumes [GTMap kt vt]); the NEXT token '{' (TLC) — vs the
    conversion's '(' (TLP) — selects the literal, then [parse_map_elems] consumes the brace-delimited KEYED pair
    list ([parse_map_elems_roundtrip]).  Each key/value round-trips via its [Pexpr].  Type-led analogue of
    [parse_atom_slicelit]; [op_needs_paren (EMapLit …) = false]. *)
Lemma parse_atom_maplit : forall kt vt kvs ctx TAIL F,
  List.Forall (fun p => Pexpr (fst p) /\ Pexpr (snd p)) kvs -> tsize kt + tsize vt + 3 * mpa kvs + 4 < F ->
  parse_atom F (gtokens ctx (EMapLit kt vt kvs) ++ TAIL)%list = Some (EMapLit kt vt kvs, TAIL).
Proof.
  intros kt vt kvs ctx TAIL F Hfa HF. rewrite gtokens_EMapLit.
  destruct F as [ | f ]; [ lia | ].
  (* normalise the [++ TAIL] into the type's clean tail, keeping [gttokens_ty (GTMap kt vt)] folded as the head *)
  rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; cbn [app].
  pose proof (parse_gty_roundtrip (GTMap kt vt) (TLC :: (gtokens_pairs kvs ++ TRC :: TAIL)) f
                ltac:(cbn [tsize]; lia)) as Hg.
  rewrite parse_atom_S. cbn [gttokens_ty app] in Hg |- *.
  rewrite Hg. cbv beta iota.
  rewrite (parse_map_elems_roundtrip kvs TAIL f Hfa ltac:(pose proof (mf_le kvs); lia)).
  reflexivity.
Qed.

(** [parse_atom] reads a [gparen]-printed operand (a non-postfix base: literal/unary/paren-binop/conversion). *)
Lemma parse_atom_gparen : forall b TAIL F,
  match b with ESel _ _ => False | EIndex _ _ => False | ESlice _ _ _ => False | ECall _ _ => False | EAssert _ _ => False | _ => True end ->
  (forall e', esize e' < esize b -> Pexpr e') ->   (* size-IH — the conversion operand needs its own [Pexpr] *)
  Pexpr b -> 3 * esize b + 4 < F ->
  parse_atom F (gtparen b ++ TAIL)%list = Some (b, TAIL).
Proof.
  intros b TAIL F Hkind Hsih HP HF.
  destruct b as [ i | z | o e0 | o' l' r' | es fs | es ix | es slo shi | es eargs | es eaT | ecc ece | eslt esles | ekt evt ekvs | sv ];
    [ | | | | exfalso; exact Hkind | exfalso; exact Hkind | exfalso; exact Hkind | exfalso; exact Hkind | exfalso; exact Hkind | | | | ].
  - destruct F as [ | f ]; [ cbn [esize] in HF; lia | ]. cbn [gtparen gtokens app]. rewrite parse_atom_S. reflexivity.
  - destruct F as [ | f ]; [ cbn [esize] in HF; lia | ]. cbn [gtparen gtokens app]. rewrite parse_atom_S. reflexivity.
  - cbn [gtparen op_needs_paren]. destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
    cbn [app]. rewrite <- app_assoc. cbn [app]. rewrite parse_atom_S.
    rewrite (HP 0 0 (TRP :: TAIL) f (le_n 0) (conj eq_refl I) ltac:(cbn [esize] in HF |- *; lia)). reflexivity.
  - cbn [gtparen op_needs_paren]. destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
    cbn [app]. rewrite <- app_assoc. cbn [app]. rewrite parse_atom_S.
    rewrite (HP 0 0 (TRP :: TAIL) f (le_n 0) (conj eq_refl I) ltac:(cbn [esize] in HF |- *; lia)). reflexivity.
  - (* EConv ecc ece — [op_needs_paren = false], so [gtparen] is just [gtokens 0]; read via [parse_atom_conv]. *)
    cbn [gtparen op_needs_paren].
    apply parse_atom_conv; [ apply Hsih; cbn [esize]; lia | cbn [esize] in HF |- *; lia ].
  - (* ESliceLit eslt esles — [op_needs_paren = false]; read via [parse_atom_slicelit], elements' [Pexpr] from the size-IH *)
    cbn [gtparen op_needs_paren].
    apply parse_atom_slicelit;
      [ apply List.Forall_forall; intros a Ha; apply Hsih; rewrite esize_ESliceLit; pose proof (esa_in esles a Ha); lia
      | rewrite esize_ESliceLit in HF; lia ].
  - (* EMapLit ekt evt ekvs — [op_needs_paren = false]; read via [parse_atom_maplit], pairs' [Pexpr] from the size-IH *)
    cbn [gtparen op_needs_paren].
    apply parse_atom_maplit;
      [ apply List.Forall_forall; intros p Hp; split;
          (apply Hsih; rewrite esize_EMapLit; pose proof (mpa_in ekvs p Hp); lia)
      | rewrite esize_EMapLit in HF; lia ].
  - (* EStr sv — a leaf atom (like EId/EInt) *)
    destruct F as [ | f ]; [ cbn [esize] in HF; lia | ]. cbn [gtparen gtokens app]. rewrite parse_atom_S. reflexivity.
Qed.

(** [parse_atom] reads a standalone (non-selector) base [gtokens bfl base] — literal/unary direct, a
    wrapped binop via the paren rule. *)
Lemma parse_atom_base : forall base bfl TAIL F,
  (forall e', esize e' < esize base -> Pexpr e') ->
  Pexpr base ->
  match base with ESel _ _ => False | EIndex _ _ => False | ESlice _ _ _ => False | ECall _ _ => False | EAssert _ _ => False | EBn o' _ _ => binop_prec o' < bfl | _ => True end ->
  3 * esize base + 4 < F ->
  parse_atom F (gtokens bfl base ++ TAIL)%list = Some (base, TAIL).
Proof.
  intros base bfl TAIL F Hsih HPbase Hprim HF.
  destruct base as [ i | z | o e0 | o' l' r' | es fs | es ix | es slo shi | es eargs | es eaT | ecc ece | eslt esles | ekt evt ekvs | sv ];
    [ | | | | exfalso; exact Hprim | exfalso; exact Hprim | exfalso; exact Hprim | exfalso; exact Hprim | exfalso; exact Hprim | | | | ].
  - destruct F as [ | f ]; [ cbn [esize] in HF; lia | ]. cbn [gtokens app]. rewrite parse_atom_S. reflexivity.
  - destruct F as [ | f ]; [ cbn [esize] in HF; lia | ]. cbn [gtokens app]. rewrite parse_atom_S. reflexivity.
  - apply parse_atom_unary; [ apply Hsih; cbn [esize]; lia | cbn [esize] in HF; lia ].
  - assert (Hw : Nat.ltb (binop_prec o') bfl = true) by (apply Nat.ltb_lt; exact Hprim).
    rewrite (gtokens_wrapped o' l' r' bfl Hw).
    destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
    cbn [app]. rewrite <- app_assoc. cbn [app]. rewrite parse_atom_S.
    rewrite (HPbase 0 (binop_prec o') (TRP :: TAIL) f (Nat.le_0_l _) (conj eq_refl I)
               ltac:(cbn [esize] in HF |- *; lia)).
    reflexivity.
  - (* EConv ecc ece — read via [parse_atom_conv]; the operand [Pexpr] comes from the size-IH. *)
    apply parse_atom_conv; [ apply Hsih; cbn [esize]; lia | cbn [esize] in HF |- *; lia ].
  - (* ESliceLit eslt esles — read via [parse_atom_slicelit]; elements' [Pexpr] from the size-IH *)
    apply parse_atom_slicelit;
      [ apply List.Forall_forall; intros a Ha; apply Hsih; rewrite esize_ESliceLit; pose proof (esa_in esles a Ha); lia
      | rewrite esize_ESliceLit in HF; lia ].
  - (* EMapLit ekt evt ekvs — read via [parse_atom_maplit]; pairs' [Pexpr] from the size-IH *)
    apply parse_atom_maplit;
      [ apply List.Forall_forall; intros p Hp; split;
          (apply Hsih; rewrite esize_EMapLit; pose proof (mpa_in ekvs p Hp); lia)
      | rewrite esize_EMapLit in HF; lia ].
  - (* EStr sv — a leaf atom (like EId/EInt) *)
    destruct F as [ | f ]; [ cbn [esize] in HF; lia | ]. cbn [gtokens app]. rewrite parse_atom_S. reflexivity.
Qed.

(** a [GExpr] that is a postfix CHAIN (selector/index top) — the forms [parse_primary] decodes via the spine. *)
Definition is_chain (e : GExpr) : Prop :=
  match e with ESel _ _ => True | EIndex _ _ => True | ESlice _ _ _ => True | ECall _ _ => True | EAssert _ _ => True | _ => False end.
Lemma gtokens_chain_gtparen : forall ctx e, is_chain e -> gtokens ctx e = gtparen e.
Proof. intros ctx e H. destruct e; try contradiction; reflexivity. Qed.
Lemma pspine_esize_lt_chain : forall e, is_chain e -> esize (fst (pspine e)) < esize e.
Proof. intros e H. destruct e; try contradiction; [ apply pspine_esize_lt | apply pspine_esize_lt_idx | apply pspine_esize_lt_slice | apply pspine_esize_lt_call | apply pspine_esize_lt_assert ]. Qed.

(** [parse_primary] reads a postfix chain: [parse_atom] reads the innermost base ([parse_atom_gparen]),
    [parse_postfix] folds the selector/index ops ([parse_postfix_pairs]; index children round-trip via their
    [Pexpr], supplied from the size-IH).  Needs only the size-IH (NOT [Pexpr] of the whole chain — which
    would be circular when the chain IS the expression being decided). *)
Lemma parse_primary_chain : forall e ctx TAIL F,
  is_chain e ->
  (forall e', esize e' < esize e -> Pexpr e') ->
  (match TAIL with nil => True | t :: _ => is_postfix_start t = false end) ->
  3 * esize e + 2 < F ->
  parse_primary F (gtokens ctx e ++ TAIL)%list = Some (e, TAIL).
Proof.
  intros e ctx TAIL F Hch Hsih Hcl HF.
  destruct F as [ | F1 ]; [ lia | ].
  destruct (pspine e) as [ base' ops ] eqn:Eps.
  pose proof (pspine_base_kind e) as Hbk. rewrite Eps in Hbk. cbn [fst] in Hbk.
  pose proof (pspine_fold e) as Hfo. rewrite Eps in Hfo. cbn [fst snd] in Hfo.
  pose proof (pspine_pops_fuel e) as Hpf. rewrite Eps in Hpf. cbn [snd] in Hpf.
  pose proof (pspine_esize_lt_chain e Hch) as Hlt. rewrite Eps in Hlt. cbn [fst] in Hlt.
  pose proof (pspine_pidx_esize e) as Hpx. rewrite Eps in Hpx. cbn [snd] in Hpx.
  pose proof (pspine_pslice_esize e) as Hpsx. rewrite Eps in Hpsx. cbn [snd] in Hpsx.
  pose proof (pspine_pcall_esize e) as Hpcx. rewrite Eps in Hpcx. cbn [snd] in Hpcx.
  rewrite (gtokens_chain_gtparen ctx e Hch), (gtparen_pspine e), Eps. cbn [fst snd].
  rewrite <- app_assoc.
  rewrite parse_primary_S.
  rewrite (parse_atom_gparen base' (gtokens_pops ops ++ TAIL)%list F1 Hbk
             ltac:(intros e' He'; apply Hsih; lia)
             ltac:(apply Hsih; exact Hlt) ltac:(lia)).
  rewrite (parse_postfix_pairs ops base' TAIL F1
             ltac:(intros i Hi; apply Hsih; apply Hpx; exact Hi)
             ltac:(intros lo hi Hi; destruct (Hpsx lo hi Hi) as [ Hl Hh ]; split; [ apply Hsih; exact Hl | apply Hsih; exact Hh ])
             ltac:(intros args Hi; eapply List.Forall_impl; [ intros a Ha; apply Hsih; exact Ha | exact (Hpcx args Hi) ])
             Hcl ltac:(lia)).
  rewrite Hfo. reflexivity.
Qed.

(** [parse_primary] reads the decomposed [base] EXACTLY: a non-selector base via [parse_atom_base] then an
    empty postfix loop; a selector chain via [parse_primary_sel]. *)
Lemma parse_primary_base : forall base bfl TAIL F,
  (forall e', esize e' < esize base -> Pexpr e') ->
  Pexpr base ->
  match base with EBn o' _ _ => binop_prec o' < bfl | _ => True end ->
  (match TAIL with nil => True | t :: _ => is_postfix_start t = false end) ->
  3 * esize base + 5 < F ->
  parse_primary F (gtokens bfl base ++ TAIL)%list = Some (base, TAIL).
Proof.
  intros base bfl TAIL F Hsih HPbase Hprim Hcl HF.
  destruct base as [ i | z | o e0 | o' l' r' | es fs | es ix | es slo shi | es eargs | es eaT | ecc ece | eslt esles | ekt evt ekvs | sv ].
  (* ESel / EIndex / ESlice / ECall / EAssert chain — via the postfix spine ([parse_primary_chain]) *)
  5-9: apply parse_primary_chain; [ exact I | exact Hsih | exact Hcl | lia ].
  (* EId / EInt / EUn / EBn / EConv / ESliceLit / EMapLit — a non-chain base via [parse_atom_base] then an empty postfix loop *)
  all: destruct F as [ | F' ]; [ cbn [esize] in HF; lia | ]; destruct F' as [ | f ]; [ cbn [esize] in HF; lia | ];
       apply parse_primary_of_atom; [ apply parse_atom_base; [ exact Hsih | exact HPbase | exact Hprim | cbn [esize] in HF |- *; lia ] | exact Hcl ].
Qed.

(** [parse_primary] reads a type-form conversion [EConv c e0] (analogue of [parse_primary_unary]). *)
Lemma parse_primary_conv : forall c e0 ctx TAIL F,
  Pexpr e0 -> (match TAIL with nil => True | t :: _ => is_postfix_start t = false end) ->
  3 * esize e0 + tsize (convty_ty c) + 5 < F ->
  parse_primary F (gtokens ctx (EConv c e0) ++ TAIL)%list = Some (EConv c e0, TAIL).
Proof.
  intros c e0 ctx TAIL F HP Hcl HF. destruct F as [ | F' ]; [ lia | ]. destruct F' as [ | f ]; [ lia | ].
  apply parse_primary_of_atom; [ apply parse_atom_conv; [ exact HP | lia ] | exact Hcl ].
Qed.
(** [parse_primary] reads a slice composite literal [ESliceLit t es] (analogue of [parse_primary_conv]). *)
Lemma parse_primary_slicelit : forall t es ctx TAIL F,
  List.Forall Pexpr es -> (match TAIL with nil => True | t0 :: _ => is_postfix_start t0 = false end) ->
  tsize t + 3 * esa es + 5 < F ->
  parse_primary F (gtokens ctx (ESliceLit t es) ++ TAIL)%list = Some (ESliceLit t es, TAIL).
Proof.
  intros t es ctx TAIL F Hfa Hcl HF. destruct F as [ | F' ]; [ lia | ]. destruct F' as [ | f ]; [ lia | ].
  apply parse_primary_of_atom; [ apply parse_atom_slicelit; [ exact Hfa | lia ] | exact Hcl ].
Qed.
(** [parse_primary] reads a map composite literal [EMapLit kt vt kvs] (analogue of [parse_primary_slicelit]). *)
Lemma parse_primary_maplit : forall kt vt kvs ctx TAIL F,
  List.Forall (fun p => Pexpr (fst p) /\ Pexpr (snd p)) kvs ->
  (match TAIL with nil => True | t0 :: _ => is_postfix_start t0 = false end) ->
  tsize kt + tsize vt + 3 * mpa kvs + 5 < F ->
  parse_primary F (gtokens ctx (EMapLit kt vt kvs) ++ TAIL)%list = Some (EMapLit kt vt kvs, TAIL).
Proof.
  intros kt vt kvs ctx TAIL F Hfa Hcl HF. destruct F as [ | F' ]; [ lia | ]. destruct F' as [ | f ]; [ lia | ].
  apply parse_primary_of_atom; [ apply parse_atom_maplit; [ exact Hfa | lia ] | exact Hcl ].
Qed.

(** ---- THE EXPRESSION ROUND-TRIP ---- every [e] satisfies [Pexpr] (strong induction on [esize]).  An
    UNWRAPPED [e] (at a context [<=] its top precedence) parses via the left-spine decomposition
    ([parse_primary_base] reads the base, [parse_climb_pairs] folds the spine); a WRAPPED binop parses via
    the paren rule, recursing on its own unwrapped form. *)
Lemma all_Pexpr : forall n e, esize e <= n -> Pexpr e.
Proof.
  induction n as [ | n IH ]; intros e Hsz.
  - pose proof (esize_pos e); lia.
  - assert (Hunwr : forall k ctx rest F, k <= ctx -> tail_ok k rest -> 3 * esize e < F ->
              match e with EBn o _ _ => ctx <= binop_prec o | ESel _ _ => False | EIndex _ _ => False | ESlice _ _ _ => False | ECall _ _ => False | EAssert _ _ => False | _ => True end ->
              parse_expr F k (gtokens ctx e ++ rest)%list = Some (e, rest)).
    { intros k ctx rest F Hk Htl HF Hctx. destruct e as [ i | z | o e0 | o l r | es fs | es ix | es slo shi | es eargs | es eaT | ec0 ece0 | slt sles | mkt mvt mkvs | sv ].
      - (* EId *) destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
        destruct f as [ | g ]; [ cbn [esize] in HF; lia | ]. destruct g as [ | g' ]; [ cbn [esize] in HF; lia | ].
        cbn [gtokens app]. rewrite parse_expr_S.
        rewrite (parse_primary_of_atom g' (TId i :: rest) (EId i) rest
                   ltac:(rewrite parse_atom_S; reflexivity) (tail_ok_pclean _ _ Htl)).
        apply tail_ok_climb_stop; exact Htl.
      - (* EInt *) destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
        destruct f as [ | g ]; [ cbn [esize] in HF; lia | ]. destruct g as [ | g' ]; [ cbn [esize] in HF; lia | ].
        cbn [gtokens app]. rewrite parse_expr_S.
        rewrite (parse_primary_of_atom g' (TInt z :: rest) (EInt z) rest
                   ltac:(rewrite parse_atom_S; reflexivity) (tail_ok_pclean _ _ Htl)).
        apply tail_ok_climb_stop; exact Htl.
      - (* EUn *) destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
        destruct f as [ | g ]; [ cbn [esize] in HF; lia | ].
        rewrite parse_expr_S.
        rewrite (parse_primary_unary o e0 ctx rest (S g)
                   ltac:(apply IH; cbn [esize] in Hsz; lia) (tail_ok_pclean _ _ Htl) ltac:(cbn [esize] in HF; lia)).
        apply tail_ok_climb_stop; exact Htl.
      - (* EBn unwrapped: Hctx : ctx <= binop_prec o *)
        cbn [esize] in Hsz, HF.
        assert (Hleb : Nat.leb ctx (binop_prec o) = true) by (apply Nat.leb_le; exact Hctx).
        destruct (lspine (binop_prec o) l) as [ [ bfl base ] ps0 ] eqn:El.
        assert (Els : lspine ctx (EBn o l r) = (bfl, base, (ps0 ++ (o, r) :: nil)%list))
          by (cbn [lspine]; rewrite Hleb, El; reflexivity).
        pose proof (lspine_fold _ _ _ _ _ Els) as Hfold.
        pose proof (lspine_base _ _ _ _ _ Els) as Hprim.
        pose proof (lspine_fuel3 _ _ _ _ _ Els) as Hf3. cbn [esize] in Hf3.
        pose proof (lspine_base_le _ _ _ _ _ El) as Hble.
        pose proof (pairs_fuel_snoc ps0 o r) as Hpfs.
        pose proof (pairs_fuel_pos ps0) as Hpp0. pose proof (esize_pos r) as Her.
        pose proof (esize_pos base) as Heb.
        assert (HPbase : Pexpr base) by (apply (IH base); lia).
        assert (Hspine : spine_ok k (ps0 ++ (o, r) :: nil)%list).
        { apply (spine_ok_weaken _ ctx); [ | exact Hk ].
          eapply lspine_spine_ok; [ | exact Els ].
          intros e' He'. apply (IH e'). cbn [esize] in He'. lia. }
        rewrite (lspine_print _ _ _ _ _ Els), <- app_assoc.
        destruct F as [ | f ]; [ lia | ].
        rewrite parse_expr_S.
        rewrite (parse_primary_base base bfl (gtok_pairs (ps0 ++ (o, r) :: nil) ++ rest)%list f
                   ltac:(intros e' He'; apply (IH e'); lia) HPbase Hprim
                   (gtok_pairs_snoc_pclean ps0 o r rest) ltac:(lia)).
        change (parse_climb f k base (gtok_pairs (ps0 ++ (o, r) :: nil) ++ rest)%list = Some (EBn o l r, rest)).
        rewrite (parse_climb_pairs (ps0 ++ (o, r) :: nil) k base rest f Hspine Htl ltac:(lia)).
        rewrite Hfold. reflexivity.
      - (* ESel — Hctx : False (postfix chains handled directly in the outer case) *) destruct Hctx.
      - (* EIndex — Hctx : False (postfix chains handled directly in the outer case) *) destruct Hctx.
      - (* ESlice — Hctx : False (postfix chains handled directly in the outer case) *) destruct Hctx.
      - (* ECall — Hctx : False (postfix chains handled directly in the outer case) *) destruct Hctx.
      - (* EAssert — Hctx : False (postfix chains handled directly in the outer case) *) destruct Hctx.
      - (* EConv ec0 ece0 — a primary (never wrapped); read via [parse_primary_conv] *)
        destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
        destruct f as [ | g ]; [ cbn [esize] in HF; lia | ].
        rewrite parse_expr_S.
        rewrite (parse_primary_conv ec0 ece0 ctx rest (S g)
                   ltac:(apply IH; cbn [esize] in Hsz; lia) (tail_ok_pclean _ _ Htl)
                   ltac:(cbn [esize] in HF; lia)).
        apply tail_ok_climb_stop; exact Htl.
      - (* ESliceLit slt sles — a primary (never wrapped); read via [parse_primary_slicelit] *)
        destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
        destruct f as [ | g ]; [ cbn [esize] in HF; lia | ].
        rewrite parse_expr_S.
        rewrite (parse_primary_slicelit slt sles ctx rest (S g)
                   ltac:(apply List.Forall_forall; intros a Ha; apply IH; rewrite esize_ESliceLit in Hsz; pose proof (esa_in sles a Ha); lia)
                   (tail_ok_pclean _ _ Htl)
                   ltac:(rewrite esize_ESliceLit in HF; lia)).
        apply tail_ok_climb_stop; exact Htl.
      - (* EMapLit mkt mvt mkvs — a primary (never wrapped); read via [parse_primary_maplit] *)
        destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
        destruct f as [ | g ]; [ cbn [esize] in HF; lia | ].
        rewrite parse_expr_S.
        rewrite (parse_primary_maplit mkt mvt mkvs ctx rest (S g)
                   ltac:(apply List.Forall_forall; intros p Hp; split;
                           (apply IH; rewrite esize_EMapLit in Hsz; pose proof (mpa_in mkvs p Hp); lia))
                   (tail_ok_pclean _ _ Htl)
                   ltac:(rewrite esize_EMapLit in HF; lia)).
        apply tail_ok_climb_stop; exact Htl.
      - (* EStr sv — a leaf atom (like EId/EInt) *)
        destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
        destruct f as [ | g ]; [ cbn [esize] in HF; lia | ]. destruct g as [ | g' ]; [ cbn [esize] in HF; lia | ].
        cbn [gtokens app]. rewrite parse_expr_S.
        rewrite (parse_primary_of_atom g' (TStr sv :: rest) (EStr sv) rest
                   ltac:(rewrite parse_atom_S; reflexivity) (tail_ok_pclean _ _ Htl)).
        apply tail_ok_climb_stop; exact Htl. }
    unfold Pexpr. intros k ctx rest F Hk Htl HF.
    destruct e as [ i | z | o e0 | o l r | es fs | es ix | es slo shi | es eargs | es eaT | ecc ece | eslt esles | ekt evt ekvs | sv ].
    + apply Hunwr; [ exact Hk | exact Htl | cbn [esize] in HF |- *; lia | exact I ].
    + apply Hunwr; [ exact Hk | exact Htl | cbn [esize] in HF |- *; lia | exact I ].
    + apply Hunwr; [ exact Hk | exact Htl | cbn [esize] in HF |- *; lia | exact I ].
    + destruct (Nat.ltb (binop_prec o) ctx) eqn:Ewrap.
      * (* wrapped *)
        rewrite (gtokens_wrapped o l r ctx Ewrap).
        destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
        destruct f as [ | g ]; [ cbn [esize] in HF; lia | ].
        destruct g as [ | g' ]; [ cbn [esize] in HF; lia | ].
        cbn [app]. rewrite <- app_assoc. cbn [app].
        rewrite parse_expr_S.
        rewrite (parse_primary_of_atom g'
                   (TLP :: (gtokens (binop_prec o) (EBn o l r) ++ TRP :: rest))%list (EBn o l r) rest
                   ltac:(rewrite parse_atom_S;
                         rewrite (Hunwr 0 (binop_prec o) (TRP :: rest) g' (Nat.le_0_l _) (conj eq_refl I)
                                   ltac:(cbn [esize] in HF |- *; lia) (le_n _));
                         reflexivity)
                   (tail_ok_pclean _ _ Htl)).
        apply tail_ok_climb_stop; exact Htl.
      * (* unwrapped *)
        apply Hunwr; [ exact Hk | exact Htl | cbn [esize] in HF |- *; lia
                     | apply Nat.ltb_ge in Ewrap; exact Ewrap ].
    + (* ESel es fs — a primary (never wrapped), via the postfix spine *)
      destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
      destruct f as [ | g ]; [ cbn [esize] in HF; lia | ].
      rewrite parse_expr_S.
      rewrite (parse_primary_chain (ESel es fs) ctx rest (S g) I
                 ltac:(intros e' He'; apply (IH e'); cbn [esize] in Hsz, He'; lia)
                 (tail_ok_pclean _ _ Htl) ltac:(cbn [esize] in HF |- *; lia)).
      apply tail_ok_climb_stop; exact Htl.
    + (* EIndex es ix — a primary (never wrapped), via the postfix spine *)
      destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
      destruct f as [ | g ]; [ cbn [esize] in HF; lia | ].
      rewrite parse_expr_S.
      rewrite (parse_primary_chain (EIndex es ix) ctx rest (S g) I
                 ltac:(intros e' He'; apply (IH e'); cbn [esize] in Hsz, He'; lia)
                 (tail_ok_pclean _ _ Htl) ltac:(cbn [esize] in HF |- *; lia)).
      apply tail_ok_climb_stop; exact Htl.
    + (* ESlice es slo shi — a primary (never wrapped), via the postfix spine *)
      destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
      destruct f as [ | g ]; [ cbn [esize] in HF; lia | ].
      rewrite parse_expr_S.
      rewrite (parse_primary_chain (ESlice es slo shi) ctx rest (S g) I
                 ltac:(intros e' He'; apply (IH e'); cbn [esize] in Hsz, He'; lia)
                 (tail_ok_pclean _ _ Htl) ltac:(cbn [esize] in HF |- *; lia)).
      apply tail_ok_climb_stop; exact Htl.
    + (* ECall es eargs — a primary (never wrapped), via the postfix spine *)
      destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
      destruct f as [ | g ]; [ cbn [esize] in HF; lia | ].
      rewrite parse_expr_S.
      rewrite (parse_primary_chain (ECall es eargs) ctx rest (S g) I
                 ltac:(intros e' He'; apply (IH e'); cbn [esize] in Hsz, He'; lia)
                 (tail_ok_pclean _ _ Htl) ltac:(cbn [esize] in HF |- *; lia)).
      apply tail_ok_climb_stop; exact Htl.
    + (* EAssert es eaT — a primary (never wrapped), via the postfix spine *)
      destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
      destruct f as [ | g ]; [ cbn [esize] in HF; lia | ].
      rewrite parse_expr_S.
      rewrite (parse_primary_chain (EAssert es eaT) ctx rest (S g) I
                 ltac:(intros e' He'; apply (IH e'); cbn [esize] in Hsz, He'; lia)
                 (tail_ok_pclean _ _ Htl) ltac:(cbn [esize] in HF |- *; lia)).
      apply tail_ok_climb_stop; exact Htl.
    + (* EConv ecc ece — a primary (never wrapped); the unwrapped path ([op_needs_paren = false]) *)
      apply Hunwr; [ exact Hk | exact Htl | cbn [esize] in HF |- *; lia | exact I ].
    + (* ESliceLit eslt esles — a primary (never wrapped); the unwrapped path ([op_needs_paren = false]) *)
      apply Hunwr; [ exact Hk | exact Htl | cbn [esize] in HF |- *; lia | exact I ].
    + (* EMapLit ekt evt ekvs — a primary (never wrapped); the unwrapped path ([op_needs_paren = false]) *)
      apply Hunwr; [ exact Hk | exact Htl | cbn [esize] in HF |- *; lia | exact I ].
    + (* EStr sv — a leaf atom (never wrapped) *)
      apply Hunwr; [ exact Hk | exact Htl | cbn [esize] in HF |- *; lia | exact I ].
Qed.

(** THE HEADLINE (parser half): [parse] inverts [gtokens] — the canonical token list parses back to [e]. *)
Theorem gtokens_parse : forall e, parse (gtokens 0 e) = Some (e, nil).
Proof.
  intro e. unfold parse.
  pose proof (length_gtokens_ge_esize e 0) as Hlen.
  pose proof (all_Pexpr (esize e) e (le_n _) 0 0 nil (3 * List.length (gtokens 0 e) + 4)
                (le_n 0) I ltac:(lia)) as HP.
  rewrite app_nil_r in HP. exact HP.
Qed.

(** ★ THE END-TO-END EXPRESSION ROUND-TRIP — printing then parsing (lex + parse) recovers the AST EXACTLY.
    Composes [gtokens_lex] (printer→tokens) with [gtokens_parse] (tokens→AST).  HONEST SCOPE: printer/parser
    SELF-CONSISTENCY for the clean Rocq grammar — NOT yet a theorem about Go's own parser (gap #10). *)
Theorem parse_print_roundtrip : forall e, parse_str (gprint 0 e) = Some (e, nil).
Proof.
  intro e. unfold parse_str. rewrite (gtokens_lex e 0). apply gtokens_parse.
Qed.

(** FAITHFULNESS COROLLARY — the printer is INJECTIVE: distinct ASTs never print alike. *)
Corollary gprint_inj : forall e1 e2, gprint 0 e1 = gprint 0 e2 -> e1 = e2.
Proof.
  intros e1 e2 He.
  pose proof (parse_print_roundtrip e1) as R1. pose proof (parse_print_roundtrip e2) as R2.
  unfold parse_str in R1, R2. rewrite He in R1. rewrite R1 in R2. injection R2 as Ht. exact Ht.
Qed.

(** ==================================================================================================
    ---- M5: TOKEN-LEVEL TYPE LAYER ----  a Go type as a TOKEN list ([gttokens_ty], mirroring [print_ty]'s
    surface) + a recursive-descent token parser ([parse_gty]) + the round-trip [parse_gty_roundtrip].  The
    gateway for type-form conversions / composite literals / type assertions.  Scalars and the [chan]/[map]
    heads lex as [TId] (the lexer keys only [func]/[return]); [*]→[TStar], [[]]→[TLB;TRB], map's brackets →
    [TLB]/[TRB].  Self-contained: additive over [GoTy], no [GExpr] dependency.  [GoTy] has no list child, so
    ordinary induction suffices and a SUM-based [tsize] fuel works (a map's two children parse at the same
    fuel, sum >= max).  ================================================================================== *)


(** composed: the printed type lexes to its token list. *)
Lemma lex_print_ty : forall t, lex (print_ty t) = Some (gttokens_ty t).
Proof.
  intro t. unfold lex.
  pose proof (gttokens_ty_lex t "" (S (String.length (print_ty t))) nil eq_refl ltac:(reflexivity)
                ltac:(cbn [String.length]; lia)) as H.
  rewrite str_app_nil_r in H. rewrite app_nil_r in H. exact H.
Qed.
(** lex round-trip by example. *)
Example lt_slice : lex (print_ty (GTSlice GTInt)) = Some (gttokens_ty (GTSlice GTInt)).  (* []int *)
Proof. apply lex_print_ty. Qed.
Example lt_chan : lex (print_ty (GTChan GTInt)) = Some (gttokens_ty (GTChan GTInt)).  (* chan int *)
Proof. apply lex_print_ty. Qed.
Example lt_map : lex (print_ty (GTMap GTInt (GTSlice GTString))) = Some (gttokens_ty (GTMap GTInt (GTSlice GTString))).  (* map[int][]string *)
Proof. apply lex_print_ty. Qed.

(** ★THE END-TO-END TYPE ROUND-TRIP: the printed type [print_ty t] lexes and parses back to [t]. *)
Theorem parse_gty_print_ty : forall t,
  match lex (print_ty t) with Some toks => parse_gty (S (List.length toks)) toks | None => None end = Some (t, nil).
Proof.
  intro t. rewrite lex_print_ty.
  rewrite <- (app_nil_r (gttokens_ty t)). apply parse_gty_roundtrip.
  pose proof (tsize_le_len t). rewrite app_nil_r. lia.
Qed.

(** type round-trip by example: [parse_gty (gttokens_ty t) = Some (t, [])]. *)
Example tyr_int   : parse_gty 4 (gttokens_ty GTInt) = Some (GTInt, nil). Proof. vm_compute; reflexivity. Qed.
Example tyr_slice : parse_gty 4 (gttokens_ty (GTSlice GTInt)) = Some (GTSlice GTInt, nil).  (* []int *)
Proof. vm_compute; reflexivity. Qed.
Example tyr_ptr   : parse_gty 4 (gttokens_ty (GTPtr (GTNamed (mkTyName "Foo" eq_refl))))
                  = Some (GTPtr (GTNamed (mkTyName "Foo" eq_refl)), nil).  (* *Foo *)
Proof. vm_compute; reflexivity. Qed.
Example tyr_chan  : parse_gty 4 (gttokens_ty (GTChan GTInt)) = Some (GTChan GTInt, nil).  (* chan int *)
Proof. vm_compute; reflexivity. Qed.
Example tyr_map   : parse_gty 6 (gttokens_ty (GTMap GTInt GTString)) = Some (GTMap GTInt GTString, nil).  (* map[int]string *)
Proof. vm_compute; reflexivity. Qed.
Example tyr_slice2 : parse_gty 6 (gttokens_ty (GTSlice (GTSlice GTInt64))) = Some (GTSlice (GTSlice GTInt64), nil).  (* [][]int64 *)
Proof. vm_compute; reflexivity. Qed.
Example tyr_mapslice : parse_gty 8 (gttokens_ty (GTMap GTString (GTSlice GTInt))) = Some (GTMap GTString (GTSlice GTInt), nil).  (* map[string][]int *)
Proof. vm_compute; reflexivity. Qed.

(** ---- M7 GROUNDWORK: the CONVERSION type-form layer ----  A type-form conversion [convform(x)] (e.g.
    [[]byte(s)], [chan int(c)], [map[string]int(m)]) needs a conversion target that is SYNTACTICALLY
    unambiguous at expression-atom position — its printed form must NOT begin with an identifier, or [T(x)]
    would be the call [ECall (EId T) [x]] instead.  [ConvTy] is exactly that subset of [GoTy]: the three
    bracket/keyword-led composite heads ([ []T / chan T / map[K]V ]).  A dedicated 3-constructor inductive
    (NOT a [{T | conv_ok T}] subset) makes the restriction STRUCTURAL — illegal states unrepresentable, ZERO
    proof obligations — and [convty_ty] embeds it into [GoTy] so the M5 type printer/lexer/parser are reused
    VERBATIM.  This is the M5-analog groundwork for the upcoming [EConv] expression form, exactly as
    [parse_gty] preceded the [EAssert] type assertion (M6).  (Pointer [*T] is excluded: a bare [*T(x)] is
    ambiguous with a deref and would need parentheses around the pointer type; primitives and named types are
    identifier-led, so they ARE the call form [ECall (EId T) [x]] already.) *)
Definition conv_print  (c : ConvTy) : string     := print_ty (convty_ty c).
Definition conv_tokens (c : ConvTy) : list Token := gttokens_ty (convty_ty c).
Definition conv_size   (c : ConvTy) : nat        := tsize (convty_ty c).

(** the printed conversion-type lexes to its token list (inherited from [lex_print_ty]). *)
Lemma conv_print_lex : forall c, lex (conv_print c) = Some (conv_tokens c).
Proof. intro c. apply lex_print_ty. Qed.

(** [parse_convty] = [parse_gty] keeping ONLY the three conversion heads; anything else (a primitive, a
    pointer, or a named type — all identifier/[*]-led, i.e. NOT a syntactic conversion form) is rejected. *)
Definition parse_convty (fuel : nat) (toks : list Token) : option (ConvTy * list Token) :=
  match parse_gty fuel toks with
  | Some (GTSlice u, r) => Some (CTSlice u, r)
  | Some (GTChan u, r)  => Some (CTChan u, r)
  | Some (GTMap k v, r) => Some (CTMap k v, r)
  | _ => None
  end.

(** round-trip: a conversion-type's tokens parse back to it (reusing [parse_gty_roundtrip]). *)
Lemma parse_convty_roundtrip : forall c rest F,
  conv_size c <= F -> parse_convty F (conv_tokens c ++ rest)%list = Some (c, rest).
Proof.
  intros c rest F HF. unfold parse_convty, conv_tokens, conv_size in *.
  destruct c as [ u | u | k v ]; cbn [convty_ty] in HF |- *;
    rewrite (parse_gty_roundtrip _ rest F HF); reflexivity.
Qed.

(** ★END-TO-END: the printed conversion-type lexes and parses back to itself. *)
Theorem parse_conv_print : forall c,
  match lex (conv_print c) with Some toks => parse_convty (S (List.length toks)) toks | None => None end = Some (c, nil).
Proof.
  intro c. rewrite conv_print_lex.
  rewrite <- (app_nil_r (conv_tokens c)). apply parse_convty_roundtrip.
  unfold conv_size, conv_tokens. pose proof (tsize_le_len (convty_ty c)). rewrite app_nil_r. lia.
Qed.

Example convr_slice : parse_convty 4 (conv_tokens (CTSlice GTU8)) = Some (CTSlice GTU8, nil).  (* []uint8(x) *)
Proof. vm_compute; reflexivity. Qed.
Example convr_chan  : parse_convty 4 (conv_tokens (CTChan GTInt)) = Some (CTChan GTInt, nil).  (* chan int(x) *)
Proof. vm_compute; reflexivity. Qed.
Example convr_map   : parse_convty 6 (conv_tokens (CTMap GTString GTInt)) = Some (CTMap GTString GTInt, nil).  (* map[string]int(x) *)
Proof. vm_compute; reflexivity. Qed.
Example convr_mapslice : parse_convty 8 (conv_tokens (CTMap GTString (GTSlice GTInt))) = Some (CTMap GTString (GTSlice GTInt), nil).
Proof. vm_compute; reflexivity. Qed.


(** FAITHFULNESS — the type printer is INJECTIVE, derived from the SINGLE (token-level) type round-trip
    [parse_gty_print_ty]: distinct [GoTy]s print to distinct strings (no [int64]/[bool],
    [*int64]/[[]int64], [map[int]int]/[map[int8]int], or two distinct named types ever conflated; a keyword-
    prefixed name [int8x] never confused with the keyword [int8]; a keyword [int] never a nominal name).  The
    old string-level prefix parser [parse_ty]/[parse_print_ty] is GONE — its only consumer was this corollary,
    and [GoPrint]'s token parser proves the same round-trip, so keeping both was a duplicate authority. *)
Theorem print_ty_inj : forall t1 t2, print_ty t1 = print_ty t2 -> t1 = t2.
Proof.
  intros t1 t2 H.
  pose proof (parse_gty_print_ty t1) as Q1.
  pose proof (parse_gty_print_ty t2) as Q2.
  rewrite <- H in Q2. rewrite Q1 in Q2. congruence.
Qed.

(** ---- PROGRAM PRINTER ---- prints a [GoAst.Program] to Go source: `package <pkg>` then `func main()` whose
    body is the program's [GoStmt] list, ONE tab-indented statement per line (gofmt's layout).  An expression
    statement reuses the machine-checked [gprint]; the package name is a validated [Ident] (no raw text).  An
    EMPTY body prints the same `func main() {\n}` as the pre-Phase-3 stub (so the empty-program bytes are
    unchanged).  GoEmit's blessed [emit_supported] is exactly [print_program], gated by a [SupportedProgram]
    certificate. *)
Definition go_nl : string := String (Ascii.ascii_of_nat 10) EmptyString.
Definition go_tab : string := String (Ascii.ascii_of_nat 9) EmptyString.
Definition print_stmt (s : GoStmt) : string :=
  match s with
  | GsExprStmt e    => gprint 0 e
  | GsReturn        => "return"
  | GsReturnVal e   => ("return " ++ gprint 0 e)%string
  | GsBlankAssign e => ("_ = " ++ gprint 0 e)%string
  end.
Fixpoint print_stmts (ss : list GoStmt) : string :=
  match ss with
  | nil => ""
  | s :: rest => (go_tab ++ print_stmt s ++ go_nl ++ print_stmts rest)%string
  end.
Definition print_program (p : Program) : string :=
  ("package " ++ proj1_sig (prog_pkg p) ++ go_nl ++ go_nl ++
   "func main() {" ++ go_nl ++ print_stmts (prog_body p) ++ "}" ++ go_nl)%string.

(** No [gprint] output is the bare keyword "return": it would have to parse back to that expression
    ([parse_print_roundtrip]), but "return" LEXES to the [TReturn] keyword token, which is not a valid
    expression, so the parser rejects it ([parse_str "return" = None]) — and the round-trip would then equate
    [None] with [Some _].  This is what keeps [GsReturn] disjoint from [GsExprStmt] at the printer level (no
    ad-hoc "gprint contains no …" string surgery). *)
Lemma gprint_neq_return : forall e, gprint 0 e <> "return"%string.
Proof.
  intros e H. pose proof (parse_print_roundtrip e) as R. rewrite H in R. vm_compute in R. discriminate R.
Qed.

(** append-cancel: a common prefix is injective (used by [print_stmt_inj] and [print_program_inj]). *)
Lemma sapp_inv_head : forall p a b, (p ++ a)%string = (p ++ b)%string -> a = b.
Proof.
  induction p as [ | c p IH ]; intros a b H; cbn [append] in H; [ exact H | ].
  injection H as H. exact (IH _ _ H).
Qed.

(** The expression parser REJECTS a leading [TReturn] (the reserved keyword token is not a valid atom), so
    [parse] of any [TReturn]-led list is [None].  (Fuel [3*len+4 >= 3] suffices to reach the [parse_atom]
    rejection.) *)
Lemma parse_expr_TReturn_None : forall f rest, parse_expr (S (S (S f))) 0 (TReturn :: rest) = None.
Proof. intros f rest. rewrite parse_expr_S, parse_primary_S, parse_atom_S. reflexivity. Qed.
Lemma parse_TReturn_None : forall rest, parse (TReturn :: rest) = None.
Proof.
  intros rest. unfold parse.
  assert (Hf : 3 * List.length (TReturn :: rest) + 4 = S (S (S (3 * List.length rest + 4))))
    by (cbn [List.length]; lia).
  rewrite Hf. apply parse_expr_TReturn_None.
Qed.

(** A printed [return e] (the [GsReturnVal] text "return " ++ gprint 0 e) does NOT parse back: it LEXES to a
    leading [TReturn] ([lex_return_app] over [gtokens_lex]), which [parse] rejects.  So no [gprint] output can
    equal "return " ++ gprint 0 e (it would make the round-trip [Some] equal this [None]) — the [GsExprStmt] /
    [GsReturnVal] disjointness, the [GsReturnVal] analogue of [gprint_neq_return]. *)
Lemma parse_str_return_gprint : forall e, parse_str ("return " ++ gprint 0 e)%string = None.
Proof.
  intro e. unfold parse_str, lex.
  pose proof (gtokens_lex e 0) as HL. unfold lex in HL.
  rewrite (lex_return_app (gprint 0 e) (S (String.length ("return " ++ gprint 0 e)%string))
             (gtokens 0 e) HL ltac:(lia)).
  apply parse_TReturn_None.
Qed.
Lemma gprint_neq_return_val : forall e1 e2, gprint 0 e2 <> ("return " ++ gprint 0 e1)%string.
Proof.
  intros e1 e2 H. pose proof (parse_print_roundtrip e2) as R. rewrite H in R.
  rewrite parse_str_return_gprint in R. discriminate R.
Qed.

(** A printed [_ = e] (the [GsBlankAssign] text "_ = " ++ X) does NOT parse back: a LONE '=' fails to lex
    ([lex_op] yields [None] unless the next char is '=', GoPrint.v:692), so [lex ("_ = " ++ X) = None] and
    thus [parse_str ("_ = " ++ X) = None] outright (cleaner than the [TReturn] case, which lexes then the
    PARSER rejects).  Hence no [gprint] output equals "_ = " ++ gprint 0 e — the [GsExprStmt] / [GsBlankAssign]
    disjointness.  (The whole reject is decided by the fixed "_ = " prefix, so [vm_compute] closes it for any
    tail [X].) *)
Lemma parse_str_blank_None : forall X, parse_str ("_ = " ++ X)%string = None.
Proof. intro X. vm_compute. reflexivity. Qed.
Lemma gprint_neq_blank : forall e1 e2, gprint 0 e2 <> ("_ = " ++ gprint 0 e1)%string.
Proof.
  intros e1 e2 H. pose proof (parse_print_roundtrip e2) as R. rewrite H in R.
  rewrite parse_str_blank_None in R. discriminate R.
Qed.

(** Statement-printer INJECTIVITY — the honest statement-level analogue of [gprint_inj]: distinct statements
    print to distinct text.  A 4-constructor (16-case) proof: expression statements lift from [gprint_inj];
    the [GsExprStmt] cross cases close by [gprint_neq_return] / [gprint_neq_return_val] / [gprint_neq_blank];
    the keyword/prefix-vs-keyword/prefix cases by string [discriminate] (distinct leading bytes) or
    [sapp_inv_head] (a shared "return " / "_ = " prefix is injective).  (The list-level / whole-[print_program]
    lift — via a "gprint emits no newline" delimiter argument — is proved just below as [print_program_inj].) *)
Lemma print_stmt_inj : forall s1 s2, print_stmt s1 = print_stmt s2 -> s1 = s2.
Proof.
  intros [e1| |r1|b1] [e2| |r2|b2] H; simpl in H.
  (* s1 = GsExprStmt e1 *)
  - f_equal. exact (gprint_inj e1 e2 H).
  - exfalso. exact (gprint_neq_return e1 H).
  - exfalso. exact (gprint_neq_return_val r2 e1 H).
  - exfalso. exact (gprint_neq_blank b2 e1 H).
  (* s1 = GsReturn *)
  - exfalso. symmetry in H. exact (gprint_neq_return e2 H).
  - reflexivity.
  - exfalso. cbn in H. discriminate H.
  - exfalso. cbn in H. discriminate H.
  (* s1 = GsReturnVal r1 *)
  - exfalso. symmetry in H. exact (gprint_neq_return_val r1 e2 H).
  - exfalso. symmetry in H. cbn in H. discriminate H.
  - f_equal. apply (sapp_inv_head "return ") in H. exact (gprint_inj r1 r2 H).
  - exfalso. cbn in H. discriminate H.
  (* s1 = GsBlankAssign b1 *)
  - exfalso. symmetry in H. exact (gprint_neq_blank b1 e2 H).
  - exfalso. symmetry in H. cbn in H. discriminate H.
  - exfalso. symmetry in H. cbn in H. discriminate H.
  - f_equal. apply (sapp_inv_head "_ = ") in H. exact (gprint_inj b1 b2 H).
Qed.

(** ============================================================================
    PROGRAM-PRINTER INJECTIVITY — [print_program] is INJECTIVE: distinct programs emit distinct Go source
    (the program-level analogue of [gprint_inj]).  The crux: every expression the body prints is
    NEWLINE-FREE ([no_nl_gprint]), so the body's '\n'-delimited statement lines (and the package name's
    terminating '\n') are recoverable — the SAME delimiter-split technique [split_p] uses for the float-hex
    'p'.  SCOPE (kept narrow on purpose): this is print INJECTIVITY only — NOT a parse round-trip and NOT a
    proof that the emitted text is accepted by a Go grammar.  Statement re-parsing (ASI/semicolons) and Go
    syntax acceptance are separate, deferred. *)
Definition nlc : ascii := ascii_of_nat 10.
Definition is_nl (c : ascii) : bool := Ascii.eqb c nlc.
Fixpoint no_nl (s : string) : Prop :=
  match s with EmptyString => True | String c s' => is_nl c = false /\ no_nl s' end.
Ltac no_nl_lit := cbn [no_nl]; repeat split; (exact I || (vm_compute; reflexivity)).
Lemma no_nl_app : forall a b, no_nl a -> no_nl b -> no_nl (a ++ b).
Proof.
  induction a as [ | c a IH ]; intros b Ha Hb; [ exact Hb | ].
  cbn [no_nl append] in *. destruct Ha as [Hc Ha]. split; [ exact Hc | apply IH; assumption ].
Qed.
Lemma go_nl_app : forall r, (go_nl ++ r)%string = String nlc r.
Proof. intro r. unfold go_nl, nlc. reflexivity. Qed.
Lemma scons_app : forall c s t, (String c s ++ t)%string = String c (s ++ t).
Proof. reflexivity. Qed.

(** leaf printers are newline-free. *)
Lemma is_nl_idc : forall c, is_idc c = true -> is_nl c = false.
Proof. intros c H. unfold is_nl, nlc. apply Bool.not_true_iff_false. intro Hc.
  apply Ascii.eqb_eq in Hc. subst c. vm_compute in H. discriminate H. Qed.
Lemma no_nl_all_idc : forall s, all_idc s = true -> no_nl s.
Proof.
  induction s as [ | c s IH ]; intro H; [ exact I | ].
  cbn [all_idc] in H. apply andb_prop in H. destruct H as [Hc Hs].
  cbn [no_nl]. split; [ apply is_nl_idc; exact Hc | apply IH; exact Hs ].
Qed.
Lemma no_nl_ident : forall i : Ident, no_nl (proj1_sig i).
Proof.
  intros [s H]. simpl. unfold go_ident in H. destruct s as [ | c s' ]; [ discriminate H | ].
  apply andb_prop in H. destruct H as [H _]. apply andb_prop in H. destruct H as [_ Hall].
  apply no_nl_all_idc. exact Hall.
Qed.
Lemma no_nl_tyname : forall n : TyName, no_nl (proj1_sig n).
Proof.
  intros [s H]. simpl. unfold nominal_type_ident in H. apply andb_prop in H. destruct H as [Hgo _].
  exact (no_nl_ident (exist _ s Hgo)).
Qed.
Lemma no_nl_print_ty : forall t, no_nl (print_ty t).
Proof.
  induction t; cbn [print_ty]; try no_nl_lit.
  - apply no_nl_app; [ no_nl_lit | exact IHt ].
  - apply no_nl_app; [ no_nl_lit | exact IHt ].
  - apply no_nl_app; [ no_nl_lit | exact IHt ].
  - apply no_nl_app; [ no_nl_lit | apply no_nl_app; [ exact IHt1 | apply no_nl_app; [ no_nl_lit | exact IHt2 ] ] ].
  - apply no_nl_tyname.
Qed.
Lemma is_nl_dec_digit : forall n, (n < 10)%nat -> is_nl (dec_digit n) = false.
Proof.
  intros n Hn. unfold is_nl, nlc, dec_digit. apply Bool.not_true_iff_false. intro H.
  apply Ascii.eqb_eq in H. apply (f_equal nat_of_ascii) in H.
  rewrite !Ascii.nat_ascii_embedding in H by lia. lia.
Qed.
Lemma no_nl_z_digits : forall fuel z acc, no_nl acc -> no_nl (z_digits fuel z acc).
Proof.
  induction fuel as [ | f IH ]; intros z acc Hacc; [ exact Hacc | ].
  cbn [z_digits].
  assert (Hk : (Z.to_nat (z mod 10) < 10)%nat)
    by (pose proof (Z.mod_pos_bound z 10 ltac:(lia)) as Hb; lia).
  destruct (Z.eqb (z / 10) 0).
  - cbn [no_nl]. split; [ apply is_nl_dec_digit; exact Hk | exact Hacc ].
  - apply IH. cbn [no_nl]. split; [ apply is_nl_dec_digit; exact Hk | exact Hacc ].
Qed.
Lemma no_nl_print_Z : forall z, no_nl (print_Z z).
Proof.
  intro z. unfold print_Z. destruct (z =? 0)%Z; [ no_nl_lit | ].
  destruct (z <? 0)%Z.
  - apply no_nl_app; [ no_nl_lit | apply no_nl_z_digits; exact I ].
  - apply no_nl_z_digits; exact I.
Qed.
Lemma no_nl_binop_text : forall o, no_nl (binop_text o).
Proof. intro o; destruct o; no_nl_lit. Qed.
Lemma no_nl_unop_text : forall o, no_nl (unop_text o).
Proof. intro o; destruct o; no_nl_lit. Qed.

(** the printer's expression output is newline-free, for ANY context ([ctx] only adds parens). *)
Lemma no_nl_gparen : forall e0, no_nl (gprint 0 e0) -> no_nl (gparen e0).
Proof.
  intros e0 H. unfold gparen. destruct (op_needs_paren e0).
  - apply no_nl_app; [ no_nl_lit | apply no_nl_app; [ exact H | no_nl_lit ] ].
  - exact H.
Qed.
Lemma gprint_EUn_pre : forall ctx o e0,
  gprint ctx (EUn o e0) = (unop_text o ++ "(" ++ gprint 0 e0 ++ ")")%string.
Proof. intros ctx o e0. destruct o; reflexivity. Qed.
Lemma gprint_EBn_eq : forall ctx o l r,
  gprint ctx (EBn o l r) =
    (if Nat.ltb (binop_prec o) ctx
     then ("(" ++ (gprint (binop_prec o) l ++ binop_text o ++ gprint (S (binop_prec o)) r) ++ ")")%string
     else (gprint (binop_prec o) l ++ binop_text o ++ gprint (S (binop_prec o)) r))%string.
Proof. reflexivity. Qed.
Lemma no_nl_gprint_args_tl : forall args,
  Forall (fun a => no_nl (gprint 0 a)) args -> no_nl (gprint_args_tl args).
Proof.
  induction args as [ | b m IH ]; intro HF; [ exact I | ]. cbn [gprint_args_tl].
  apply no_nl_app; [ no_nl_lit
    | apply no_nl_app; [ exact (Forall_inv HF) | apply IH; exact (Forall_inv_tail HF) ] ].
Qed.
Lemma no_nl_gprint_args : forall args,
  Forall (fun a => no_nl (gprint 0 a)) args -> no_nl (gprint_args args).
Proof.
  intros [ | a r ] HF; [ exact I | ]. cbn [gprint_args].
  apply no_nl_app; [ exact (Forall_inv HF) | apply no_nl_gprint_args_tl; exact (Forall_inv_tail HF) ].
Qed.
Lemma no_nl_gprint_pairs_tl : forall kvs,
  Forall (fun p => no_nl (gprint 0 (fst p)) /\ no_nl (gprint 0 (snd p))) kvs -> no_nl (gprint_pairs_tl kvs).
Proof.
  induction kvs as [ | [k v] m IH ]; intro HF; [ exact I | ]. cbn [gprint_pairs_tl].
  destruct (Forall_inv HF) as [ Hk Hv ]. cbn [fst snd] in Hk, Hv.
  apply no_nl_app; [ no_nl_lit
    | apply no_nl_app; [ exact Hk | apply no_nl_app; [ no_nl_lit | apply no_nl_app; [ exact Hv | apply IH; exact (Forall_inv_tail HF) ] ] ] ].
Qed.
Lemma no_nl_gprint_pairs : forall kvs,
  Forall (fun p => no_nl (gprint 0 (fst p)) /\ no_nl (gprint 0 (snd p))) kvs -> no_nl (gprint_pairs kvs).
Proof.
  intros [ | [k v] r ] HF; [ exact I | ]. cbn [gprint_pairs].
  destruct (Forall_inv HF) as [ Hk Hv ]. cbn [fst snd] in Hk, Hv.
  apply no_nl_app; [ exact Hk | apply no_nl_app; [ no_nl_lit | apply no_nl_app; [ exact Hv | apply no_nl_gprint_pairs_tl; exact (Forall_inv_tail HF) ] ] ].
Qed.
(** ---- [print_string_lit] emits NO newline ---- the escaping maps byte 10 (NL) to the two bytes [\n], so the
    literal's bytes (opening dquote, escaped body, closing dquote) are all newline-free; hence [no_nl] holds for
    [EStr]'s printing (needed so the program-printer's '\n'-delimited statement lines stay recoverable). *)
Lemma is_nl_ch_ne : forall b, b < 256 -> b <> 10 -> is_nl (ch b) = false.
Proof.
  intros b Hb Hne. unfold is_nl, nlc, ch.
  destruct (Ascii.eqb (ascii_of_nat b) (ascii_of_nat 10)) eqn:E; [ | reflexivity ].
  exfalso. apply Ascii.eqb_eq in E. apply (f_equal nat_of_ascii) in E.
  rewrite !Ascii.nat_ascii_embedding in E by lia. lia.
Qed.
Lemma is_nl_hexdig : forall k, k < 16 -> is_nl (hexdig k) = false.
Proof.
  intros k Hk. unfold hexdig. destruct (Nat.ltb k 10) eqn:E.
  - apply Nat.ltb_lt in E. apply (is_nl_ch_ne (48 + k)); lia.
  - apply Nat.ltb_ge in E. apply (is_nl_ch_ne (87 + k)); lia.
Qed.
Lemma no_nl_esc_byte : forall c X, no_nl X -> no_nl (esc_byte (nat_of_ascii c) X).
Proof.
  intros c X HX. assert (Hc : nat_of_ascii c < 256) by apply nat_of_ascii_lt_256.
  unfold esc_byte.
  destruct (Nat.eqb (nat_of_ascii c) 34) eqn:E34.
  { cbn [no_nl]; split; [ vm_compute; reflexivity | split; [ vm_compute; reflexivity | exact HX ] ]. }
  destruct (Nat.eqb (nat_of_ascii c) 92) eqn:E92.
  { cbn [no_nl]; split; [ vm_compute; reflexivity | split; [ vm_compute; reflexivity | exact HX ] ]. }
  destruct (Nat.eqb (nat_of_ascii c) 10) eqn:E10.
  { cbn [no_nl]; split; [ vm_compute; reflexivity | split; [ vm_compute; reflexivity | exact HX ] ]. }
  destruct (Nat.eqb (nat_of_ascii c) 9) eqn:E9.
  { cbn [no_nl]; split; [ vm_compute; reflexivity | split; [ vm_compute; reflexivity | exact HX ] ]. }
  destruct (Nat.eqb (nat_of_ascii c) 13) eqn:E13.
  { cbn [no_nl]; split; [ vm_compute; reflexivity | split; [ vm_compute; reflexivity | exact HX ] ]. }
  destruct (andb (Nat.leb 32 (nat_of_ascii c)) (Nat.ltb (nat_of_ascii c) 127)) eqn:Eprint.
  { (* printable byte: it is itself, and it is not NL (it is not 10, by E10) *)
    cbn [no_nl]; split; [ apply is_nl_ch_ne; [ exact Hc | apply Nat.eqb_neq; exact E10 ] | exact HX ]. }
  { (* hex escape \xHL: backslash, 'x', two hex nibbles — none is NL *)
    assert (Hd1 : Nat.div (nat_of_ascii c) 16 < 16) by (apply Nat.Div0.div_lt_upper_bound; lia).
    assert (Hd2 : Nat.modulo (nat_of_ascii c) 16 < 16) by (apply Nat.mod_upper_bound; lia).
    cbn [no_nl]; split; [ vm_compute; reflexivity
      | split; [ vm_compute; reflexivity
        | split; [ apply is_nl_hexdig; exact Hd1
          | split; [ apply is_nl_hexdig; exact Hd2 | exact HX ] ] ] ]. }
Qed.
Lemma no_nl_esc_string : forall s, no_nl (esc_string s).
Proof.
  induction s as [ | c rest IH ]; [ exact I | ].
  cbn [esc_string]. apply no_nl_esc_byte. exact IH.
Qed.
Lemma no_nl_print_string_lit : forall s, no_nl (print_string_lit s).
Proof.
  intro s. unfold print_string_lit. cbn [no_nl]. split; [ vm_compute; reflexivity | ].
  apply no_nl_app; [ apply no_nl_esc_string | cbn [no_nl]; split; [ vm_compute; reflexivity | exact I ] ].
Qed.

Lemma no_nl_gprint : forall e ctx, no_nl (gprint ctx e).
Proof.
  intro e.
  induction e as [ i | z | o e0 IHe0 | o l IHl r IHr | e0 IHe0 f | e0 IHe0 i IHi
                 | e0 IHe0 lo IHlo hi IHhi | e0 IHe0 args IHargs | e0 IHe0 T | ec0 ece0 IHec0 | slt sles IHsles | mkt mvt mkvs IHmkvs | sv ]
    using GExpr_ind'; intro ctx.
  - cbn [gprint]. apply no_nl_ident.
  - cbn [gprint]. apply no_nl_print_Z.
  - rewrite gprint_EUn_pre.
    apply no_nl_app; [ apply no_nl_unop_text
      | apply no_nl_app; [ no_nl_lit | apply no_nl_app; [ apply IHe0 | no_nl_lit ] ] ].
  - rewrite gprint_EBn_eq.
    assert (Hin : no_nl (gprint (binop_prec o) l ++ binop_text o ++ gprint (S (binop_prec o)) r))
      by (apply no_nl_app; [ apply IHl | apply no_nl_app; [ apply no_nl_binop_text | apply IHr ] ]).
    destruct (Nat.ltb (binop_prec o) ctx);
      [ apply no_nl_app; [ no_nl_lit | apply no_nl_app; [ exact Hin | no_nl_lit ] ] | exact Hin ].
  - rewrite gprint_ESel.
    apply no_nl_app; [ apply no_nl_gparen; apply IHe0 | apply no_nl_app; [ no_nl_lit | apply no_nl_ident ] ].
  - rewrite gprint_EIndex.
    apply no_nl_app; [ apply no_nl_gparen; apply IHe0
                     | apply no_nl_app; [ no_nl_lit | apply no_nl_app; [ apply IHi | no_nl_lit ] ] ].
  - rewrite gprint_ESlice.
    apply no_nl_app; [ apply no_nl_gparen; apply IHe0 | ].
    apply no_nl_app; [ no_nl_lit
      | apply no_nl_app; [ apply IHlo | apply no_nl_app; [ no_nl_lit | apply no_nl_app; [ apply IHhi | no_nl_lit ] ] ] ].
  - rewrite gprint_ECall.
    assert (Hargs0 : Forall (fun a => no_nl (gprint 0 a)) args)
      by (eapply Forall_impl; [ | exact IHargs ]; intros a Ha; apply Ha).
    apply no_nl_app; [ apply no_nl_gparen; apply IHe0
      | apply no_nl_app; [ no_nl_lit | apply no_nl_app; [ apply no_nl_gprint_args; exact Hargs0 | no_nl_lit ] ] ].
  - rewrite gprint_EAssert.
    apply no_nl_app; [ apply no_nl_gparen; apply IHe0
      | apply no_nl_app; [ no_nl_lit | apply no_nl_app; [ apply no_nl_print_ty | no_nl_lit ] ] ].
  - rewrite gprint_EConv.
    apply no_nl_app; [ apply no_nl_print_ty
      | apply no_nl_app; [ no_nl_lit | apply no_nl_app; [ apply IHec0 | no_nl_lit ] ] ].
  - rewrite gprint_ESliceLit.
    assert (Hes0 : Forall (fun a => no_nl (gprint 0 a)) sles)
      by (eapply Forall_impl; [ | exact IHsles ]; intros a Ha; apply Ha).
    apply no_nl_app; [ no_nl_lit
      | apply no_nl_app; [ apply no_nl_print_ty
        | apply no_nl_app; [ no_nl_lit | apply no_nl_app; [ apply no_nl_gprint_args; exact Hes0 | no_nl_lit ] ] ] ].
  - rewrite gprint_EMapLit.
    assert (Hkvs0 : Forall (fun p => no_nl (gprint 0 (fst p)) /\ no_nl (gprint 0 (snd p))) mkvs)
      by (eapply Forall_impl; [ | exact IHmkvs ]; intros p Hp; destruct Hp as [ Hp1 Hp2 ]; split; [ apply Hp1 | apply Hp2 ]).
    apply no_nl_app; [ apply no_nl_print_ty
      | apply no_nl_app; [ no_nl_lit | apply no_nl_app; [ apply no_nl_gprint_pairs; exact Hkvs0 | no_nl_lit ] ] ].
  - (* EStr sv — the string-literal printer is newline-free *)
    cbn [gprint]. apply no_nl_print_string_lit.
Qed.
Lemma no_nl_print_stmt : forall s, no_nl (print_stmt s).
Proof.
  intros [e| |r|b]; cbn [print_stmt].
  - apply no_nl_gprint.
  - no_nl_lit.
  - apply no_nl_app; [ no_nl_lit | apply no_nl_gprint ].
  - apply no_nl_app; [ no_nl_lit | apply no_nl_gprint ].
Qed.

(** delimiter-split + append-cancel infrastructure (mirrors [split_p_app]).  [sapp_inv_head] is hoisted
    earlier (it is also used by [print_stmt_inj]). *)
Lemma split_nl : forall a1 a2 t1 t2, no_nl a1 -> no_nl a2 ->
  (a1 ++ String nlc t1)%string = (a2 ++ String nlc t2)%string -> a1 = a2 /\ t1 = t2.
Proof.
  induction a1 as [ | c1 a1 IH ]; intros a2 t1 t2 H1 H2 H.
  - destruct a2 as [ | c2 a2 ]; cbn [append] in H.
    + injection H as Ht. split; [ reflexivity | exact Ht ].
    + injection H as Hc Ht. cbn [no_nl] in H2. destruct H2 as [Hc2 _].
      exfalso. unfold is_nl in Hc2. rewrite <- Hc, Ascii.eqb_refl in Hc2. discriminate Hc2.
  - destruct a2 as [ | c2 a2 ]; cbn [append] in H.
    + injection H as Hc Ht. cbn [no_nl] in H1. destruct H1 as [Hc1 _].
      exfalso. unfold is_nl in Hc1. rewrite Hc, Ascii.eqb_refl in Hc1. discriminate Hc1.
    + injection H as Hc Ht. cbn [no_nl] in H1, H2. destruct H1 as [_ H1]. destruct H2 as [_ H2].
      destruct (IH a2 t1 t2 H1 H2 Ht) as [Ha Ht']. subst. split; reflexivity.
Qed.
Lemma ident_eq : forall i j : Ident, proj1_sig i = proj1_sig j -> i = j.
Proof.
  intros [s p] [t q] H. simpl in H. subst t.
  assert (E : p = q) by apply (UIP_dec Bool.bool_dec). rewrite E. reflexivity.
Qed.

(** statement-LIST injectivity: the body's tab-led, newline-terminated lines are recoverable as long as the
    suffix [R] (here the closing brace) does not itself start with a tab. *)
Definition tabc : ascii := ascii_of_nat 9.
Definition is_tab (c : ascii) : bool := Ascii.eqb c tabc.
Definition hd_not_tab (s : string) : Prop :=
  match s with EmptyString => True | String c _ => is_tab c = false end.
Lemma print_stmts_cons : forall s l,
  print_stmts (s :: l) = String tabc (print_stmt s ++ String nlc (print_stmts l)).
Proof. intros s l. cbn [print_stmts]. unfold go_tab, go_nl, tabc, nlc. reflexivity. Qed.
Lemma print_stmts_inj_suffix : forall l1 l2 R1 R2,
  hd_not_tab R1 -> hd_not_tab R2 ->
  (print_stmts l1 ++ R1)%string = (print_stmts l2 ++ R2)%string -> l1 = l2 /\ R1 = R2.
Proof.
  induction l1 as [ | s1 l1 IH ]; intros l2 R1 R2 HR1 HR2 H.
  - destruct l2 as [ | s2 l2 ].
    + cbn [print_stmts append] in H. split; [ reflexivity | exact H ].
    + change (print_stmts []) with ""%string in H. cbn [append] in H. rewrite print_stmts_cons in H.
      exfalso. rewrite H in HR1. vm_compute in HR1. discriminate HR1.
  - destruct l2 as [ | s2 l2 ].
    + change (print_stmts []) with ""%string in H. cbn [append] in H. rewrite print_stmts_cons in H.
      exfalso. rewrite <- H in HR2. vm_compute in HR2. discriminate HR2.
    + rewrite !print_stmts_cons, !scons_app in H. injection H as H.
      rewrite !sapp_assoc, !scons_app in H.
      destruct (split_nl _ _ _ _ (no_nl_print_stmt s1) (no_nl_print_stmt s2) H) as [Hs Hbody].
      apply print_stmt_inj in Hs.
      destruct (IH l2 R1 R2 HR1 HR2 Hbody) as [Hl HR]. subst. split; reflexivity.
Qed.
Lemma print_program_inj : forall p1 p2, print_program p1 = print_program p2 -> p1 = p2.
Proof.
  intros [pk1 b1] [pk2 b2] H. unfold print_program in H. cbn [prog_pkg prog_body] in H.
  apply (sapp_inv_head "package ") in H. rewrite !go_nl_app in H.
  destruct (split_nl _ _ _ _ (no_nl_ident pk1) (no_nl_ident pk2) H) as [Hpk Hrest].
  apply ident_eq in Hpk. injection Hrest as Hrest.
  destruct (print_stmts_inj_suffix b1 b2 ("}" ++ go_nl) ("}" ++ go_nl)
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hrest) as [Hb _].
  subst. reflexivity.
Qed.

(** GATE — GoAst.v + GoPrint.v are part of the trust base: the EXTRACTED printer is governed by these
    theorems, so they MUST be axiom-free.  The build (Dockerfile prover stage) compiles GoAst.v + GoPrint.v
    standalone (`rocq c -Q . Fido`) and FAILS
    if any of these rests on an unproved assumption (a non-empty Axioms section in its Print Assumptions).
    Keep this list in sync with the headline results below. *)
Print Assumptions print_ty_inj.
Print Assumptions esc_string_roundtrip_opt.
Print Assumptions unescape_opt_image.
Print Assumptions print_parse_Z.
Print Assumptions print_parse_hex.
Print Assumptions print_parse_float_hex.
Print Assumptions gtokens_lex.
Print Assumptions gtokens_parse.
Print Assumptions parse_print_roundtrip.
Print Assumptions gprint_inj.
Print Assumptions parse_gty_roundtrip.
Print Assumptions gttokens_ty_lex.
Print Assumptions lex_print_ty.
Print Assumptions parse_convty_roundtrip.
Print Assumptions parse_conv_print.
Print Assumptions parse_gty_print_ty.
Print Assumptions print_stmt_inj.
Print Assumptions print_program_inj.

(** Extract the Rocq printers to the OCaml the plugin calls. *)
Require Import Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "printer.ml" print_ty print_Z print_string_lit print_hex print_float_hex print_sep nominal_type_ident go_ident binop_prec binop_text gprint.
