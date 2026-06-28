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

(* SYNTAX lives in GoAst.v; this file (the old Module Front, now flattened) is GoPrint: printers + lexer + parser + round-trips. *)
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
    precedence.  Consumed by [Module Front]'s [gprint] (the verified frontend below), which parenthesises a
    sub-expression exactly when its [binop_prec] is looser than the context.  (The plugin's trusted OCaml
    [pp_prec] renders the same binary-operator tree as strings; [Front] is being built to replace it.) *)

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
    plugin never emits it.)  [unop_text] gives the surface text; consumed by [Module Front]'s [gprint].
    [UNeg] (unary [-]) prints PARENTHESISED — [-(x)] — because a bare [-x] would collide with the [-5]
    negative literal, and [Front]'s parser dispatches the unambiguous two-char prefix [-(] to it (the other
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
  | TId  : Ident -> Token | TInt : Z -> Token
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

(** ---- THE GRAMMAR (EBNF) ---- the exact language Module Front lexes, parses, and prints.  The AST below,
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
               | "(" Expr ")"                     -- explicit grouping: re-parsed, NOT an AST node (gprint
                                                     re-derives the parens from precedence)
               | ( "!" | "^" | "*" | "&" ) Atom  -> EUn      prefix not / xor / deref / addr (bind to an Atom)
               | "-" "(" Expr ")" .              -> EUn UNeg  parenthesised, so it never collides with a -literal
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

    NOT yet in the grammar (the next growth steps, M7+): type-form conversions [ []T(x) / map[K]V(x) / chan T(x) ],
    composite literals, and func-literals.  A NAMED conversion [T(x)] is currently the call [ECall (EId T) [x]]
    -- byte-identical, and the call/conversion distinction needs a type environment the parser does not have. *)


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
  | EId _ | EInt _ | ESel _ _ | EIndex _ _ | ESlice _ _ _ | ECall _ _ | EAssert _ _ => false
  end.

(** ---- THE PRINTER ---- precedence-correct (reuses [binop_prec]/[binop_text]/[unop_text]); a binop wraps
    in parens exactly when its precedence [< ctx].  Mirrors the legacy [print_expr] over the clean AST. *)
Fixpoint gprint (ctx : nat) (e : GExpr) {struct e} : string :=
  match e with
  | EId i  => proj1_sig i
  | EInt z => print_Z z
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
  end.

(** the comma-joined argument list: head then a comma-prefixed tail (no trailing comma — gofmt-clean).
    Standalone (mirrors the local [fix] in [gprint]'s ECall case); [gprint_ECall] re-folds onto it. *)
Fixpoint gprint_args_tl (args : list GExpr) : string :=
  match args with nil => "" | b :: m => ("," ++ gprint 0 b ++ gprint_args_tl m)%string end.
Definition gprint_args (args : list GExpr) : string :=
  match args with nil => "" | a :: r => (gprint 0 a ++ gprint_args_tl r)%string end.

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
    | TId i :: rest  => Some (EId i, rest)
    | TInt z :: rest => Some (EInt z, rest)
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
  end.
(** standalone arg-token list (mirrors the local [fix] in [gtokens]'s ECall case); [gtokens_ECall] bridges. *)
Fixpoint gtokens_args_tl (args : list GExpr) : list Token :=
  match args with nil => nil | b :: m => (TComma :: (gtokens 0 b ++ gtokens_args_tl m))%list end.
Definition gtokens_args (args : list GExpr) : list Token :=
  match args with nil => nil | a :: r => (gtokens 0 a ++ gtokens_args_tl r)%list end.

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

(** Digit-shape facts for the integer leaf (proved from scratch for Module Front). *)
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
  destruct e0 as [ i0 | z0 | u0 eu | b0 lb rb | es fs | ei ii | esl elo ehi | ecf ecargs | eaf eaT ]; cbn [gparen gtparen op_needs_paren] in Hfuel |- *.
  1,2,5,6,7,8,9: apply IHe0; [ exact HXc | exact HX | exact Hfuel ].
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
  induction e as [ i | z | o e IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 i IHi | e0 IHe0 lo IHlo hi IHhi | e0 IHe0 args IHargs | e0 IHe0 T ]
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
  | EId _ => 1 | EInt _ => 1
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
  induction e as [ i | z | o e0 IH | o l IHl r IHr | es IHs fs | eb IHb ix IHx | esl IHsl slo IHlo shi IHhi | ec IHec ecargs IHargs | ea IHea T ]
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
  | TId i :: rest  => Some (EId i, rest)
  | TInt z :: rest => Some (EInt z, rest)
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
  | EUn o e => (fl, EUn o e, nil)
  | ESel e0 f => (fl, ESel e0 f, nil)   (* a selector is a PRIMARY base — no binary left-spine *)
  | EIndex e0 i => (fl, EIndex e0 i, nil)   (* an index is also a PRIMARY base *)
  | ESlice e0 lo hi => (fl, ESlice e0 lo hi, nil)   (* a slice is also a PRIMARY base *)
  | ECall e0 args => (fl, ECall e0 args, nil)   (* a call is also a PRIMARY base *)
  | EAssert e0 T => (fl, EAssert e0 T, nil)   (* a type assertion is also a PRIMARY base *)
  | EBn o l r =>
      if Nat.leb fl (binop_prec o)
      then let '(bfl, base, ps) := lspine (binop_prec o) l in (bfl, base, (ps ++ (o, r) :: nil)%list)
      else (fl, EBn o l r, nil)
  end.

Lemma lspine_print : forall e fl bfl base ps,
  lspine fl e = (bfl, base, ps) -> gtokens fl e = (gtokens bfl base ++ gtok_pairs ps)%list.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | es IHs fs | eb IHb ix IHx | esl IHsl slo IHlo shi IHhi | ec IHec ecargs | ea IHea T ]; intros fl bfl base ps H.
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
Qed.

Lemma lspine_fold : forall e fl bfl base ps,
  lspine fl e = (bfl, base, ps) -> fold_pairs base ps = e.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | es IHs fs | eb IHb ix IHx | esl IHsl slo IHlo shi IHhi | ec IHec ecargs | ea IHea T ]; intros fl bfl base ps H.
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
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | es IHs fs | eb IHb ix IHx | esl IHsl slo IHlo shi IHhi | ec IHec ecargs | ea IHea T ]; intros fl bfl base ps Hsih H.
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
Qed.

(** The base is a PRIMARY: a literal/unary leaf, or an [EBn] wrapped because [bfl] exceeds its operator
    precedence (so it prints parenthesised). *)
Lemma lspine_base : forall e fl bfl base ps,
  lspine fl e = (bfl, base, ps) ->
  match base with EBn o' _ _ => binop_prec o' < bfl | _ => True end.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | es IHs fs | eb IHb ix IHx | esl IHsl slo IHlo shi IHhi | ec IHec ecargs | ea IHea T ]; intros fl bfl base ps H.
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
Qed.

Lemma lspine_base_le : forall e fl bfl base ps, lspine fl e = (bfl, base, ps) -> esize base <= esize e.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | es IHs fs | eb IHb ix IHx | esl IHsl slo IHlo shi IHhi | ec IHec ecargs | ea IHea T ]; intros fl bfl base ps H.
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
Qed.

Lemma pairs_fuel_snoc : forall ps o r, pairs_fuel (ps ++ (o, r) :: nil)%list = pairs_fuel ps + (3 * esize r + 3).
Proof.
  induction ps as [ | [o1 r1] ps' IH ]; intros o r; cbn [app pairs_fuel]; [ lia | rewrite IH; lia ].
Qed.

(** Base size and spine fuel partition exactly [S (3*esize e)] — so [3*esize e] budget covers both. *)
Lemma lspine_fuel3 : forall e fl bfl base ps,
  lspine fl e = (bfl, base, ps) -> 3 * esize base + pairs_fuel ps = S (S (3 * esize e)).
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | es IHs fs | eb IHb ix IHx | esl IHsl slo IHlo shi IHhi | ec IHec ecargs | ea IHea T ]; intros fl bfl base ps H.
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
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T ]; cbn [pspine]; try reflexivity;
    destruct (pspine e0) as [ b ops ] eqn:Ep; cbn [fst snd] in *;
    rewrite fold_pops_app; cbn [fold_pops]; rewrite IHe0; reflexivity.
Qed.
Lemma pspine_base_kind : forall e,
  match fst (pspine e) with ESel _ _ => False | EIndex _ _ => False | ESlice _ _ _ => False | ECall _ _ => False | EAssert _ _ => False | _ => True end.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T ]; cbn [pspine]; try exact I;
    destruct (pspine e0) as [ b ops ] eqn:Ep; cbn [fst] in *; exact IHe0.
Qed.
Lemma pspine_esize : forall e, esize (fst (pspine e)) <= esize e.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T ];
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
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T ]; cbn [pspine];
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
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T ];
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
  induction e as [ i0 | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T ]; intros i Hin;
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
  induction e as [ i0 | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T ]; intros lo hi Hin;
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
(** the arguments of a [PCall] in the spine are all strictly smaller than the chain (for their [Pexpr]). *)
Lemma pspine_pcall_esize : forall e args,
  List.In (PCall args) (snd (pspine e)) -> List.Forall (fun a => esize a < esize e) args.
Proof.
  induction e as [ i0 | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T ]; intros args Hin;
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
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T ]; intros ctx Z.
  - reflexivity.
  - reflexivity.
  - cbn [gtokens]. destruct o; reflexivity.
  - cbn [gtokens]. destruct (Nat.ltb (binop_prec o) ctx); [ reflexivity | ]. rewrite <- app_assoc. apply IHl.
  - rewrite gtokens_ESel, <- app_assoc. unfold gtparen; destruct e0; (apply IHe0 || reflexivity).
  - rewrite gtokens_EIndex, <- app_assoc. unfold gtparen; destruct e0; (apply IHe0 || reflexivity).
  - rewrite gtokens_ESlice, <- app_assoc. unfold gtparen; destruct e0; (apply IHe0 || reflexivity).
  - rewrite gtokens_ECall, <- app_assoc. unfold gtparen; destruct e0; (apply IHe0 || reflexivity).
  - rewrite gtokens_EAssert, <- app_assoc. unfold gtparen; destruct e0; (apply IHe0 || reflexivity).
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

(** [parse_atom] reads a [gparen]-printed operand (a non-postfix base: literal/unary/paren-binop). *)
Lemma parse_atom_gparen : forall b TAIL F,
  match b with ESel _ _ => False | EIndex _ _ => False | ESlice _ _ _ => False | ECall _ _ => False | EAssert _ _ => False | _ => True end ->
  Pexpr b -> 3 * esize b + 4 < F ->
  parse_atom F (gtparen b ++ TAIL)%list = Some (b, TAIL).
Proof.
  intros b TAIL F Hkind HP HF.
  destruct b as [ i | z | o e0 | o' l' r' | es fs | es ix | es slo shi | es eargs | es eaT ];
    [ | | | | exfalso; exact Hkind | exfalso; exact Hkind | exfalso; exact Hkind | exfalso; exact Hkind | exfalso; exact Hkind ].
  - destruct F as [ | f ]; [ cbn [esize] in HF; lia | ]. cbn [gtparen gtokens app]. rewrite parse_atom_S. reflexivity.
  - destruct F as [ | f ]; [ cbn [esize] in HF; lia | ]. cbn [gtparen gtokens app]. rewrite parse_atom_S. reflexivity.
  - cbn [gtparen op_needs_paren]. destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
    cbn [app]. rewrite <- app_assoc. cbn [app]. rewrite parse_atom_S.
    rewrite (HP 0 0 (TRP :: TAIL) f (le_n 0) (conj eq_refl I) ltac:(cbn [esize] in HF |- *; lia)). reflexivity.
  - cbn [gtparen op_needs_paren]. destruct F as [ | f ]; [ cbn [esize] in HF; lia | ].
    cbn [app]. rewrite <- app_assoc. cbn [app]. rewrite parse_atom_S.
    rewrite (HP 0 0 (TRP :: TAIL) f (le_n 0) (conj eq_refl I) ltac:(cbn [esize] in HF |- *; lia)). reflexivity.
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
  destruct base as [ i | z | o e0 | o' l' r' | es fs | es ix | es slo shi | es eargs | es eaT ];
    [ | | | | exfalso; exact Hprim | exfalso; exact Hprim | exfalso; exact Hprim | exfalso; exact Hprim | exfalso; exact Hprim ].
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
  destruct base as [ i | z | o e0 | o' l' r' | es fs | es ix | es slo shi | es eargs | es eaT ].
  1-4: destruct F as [ | F' ]; [ cbn [esize] in HF; lia | ]; destruct F' as [ | f ]; [ cbn [esize] in HF; lia | ];
       apply parse_primary_of_atom; [ apply parse_atom_base; [ exact Hsih | exact HPbase | exact Hprim | cbn [esize] in HF |- *; lia ] | exact Hcl ].
  (* ESel / EIndex / ESlice / ECall / EAssert chain — via the postfix spine ([parse_primary_chain]) *)
  all: apply parse_primary_chain; [ exact I | exact Hsih | exact Hcl | lia ].
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
    { intros k ctx rest F Hk Htl HF Hctx. destruct e as [ i | z | o e0 | o l r | es fs | es ix | es slo shi | es eargs | es eaT ].
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
      - (* EAssert — Hctx : False (postfix chains handled directly in the outer case) *) destruct Hctx. }
    unfold Pexpr. intros k ctx rest F Hk Htl HF.
    destruct e as [ i | z | o e0 | o l r | es fs | es ix | es slo shi | es eargs | es eaT ].
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
    and [Front]'s token parser proves the same round-trip, so keeping both was a duplicate authority. *)
Theorem print_ty_inj : forall t1 t2, print_ty t1 = print_ty t2 -> t1 = t2.
Proof.
  intros t1 t2 H.
  pose proof (parse_gty_print_ty t1) as Q1.
  pose proof (parse_gty_print_ty t2) as Q2.
  rewrite <- H in Q2. rewrite Q1 in Q2. congruence.
Qed.

(** GATE — goprint.v is part of the trust base: the EXTRACTED printer is governed by these theorems, so
    they MUST be axiom-free.  The build (Dockerfile prover stage) compiles goprint.v standalone and FAILS
    if any of these rests on an unproved assumption (a non-empty Axioms section in its Print Assumptions).
    Keep this list in sync with the headline results below. *)
Print Assumptions print_ty_inj.
Print Assumptions esc_string_roundtrip.
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

(** Extract the Rocq printers to the OCaml the plugin calls. *)
Require Import Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "printer.ml" print_ty print_Z print_string_lit print_hex print_float_hex print_sep nominal_type_ident go_ident binop_prec binop_text gprint.
