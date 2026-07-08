(** ============================================================================
    GoPrint — the Go PRINTER, LEXER/PARSER, and round-trip / injectivity proofs.

    [GoAst] owns the SYNTAX ([GExpr]/[GoTy]/operators).  This file owns everything that turns that syntax
    into text and reasons about it: the printers ([print_ty], the literal printers, [gprint] for
    expressions, [print_stmt]/[print_program]), a [lex] + recursive-descent/precedence [parse] (used ONLY
    by the proofs), and the round-trip + injectivity THEOREMS.  [Extraction "printer.ml"] emits the OCaml
    the plugin calls, so the plugin runs the SAME printer Rocq reasons about.

    LIVE WIRING: the extracted [gprint] is called by the plugin for a SMALL expression class today (the exact
    live-bridged list is single-sourced in PROGRESS.md, not re-enumerated here); every other expression shape
    is still printed by the trusted OCaml [pp_expr] in [plugin/go.ml].  So this file does NOT make the live Go
    "verified" — and even for the bridged class only the PRINTING is verified, NOT the trusted MiniML->[GExpr]
    CONSTRUCTION in [plugin/go.ml] that chooses the AST.

    WHAT IS PROVEN: EXPRESSIONS have a full printer/parser round-trip ([parse_print_roundtrip]) plus
    injectivity ([gprint_inj]); the TYPE sub-language likewise ([print_ty_inj], [parse_gty_roundtrip]).
    Statements and whole programs currently have print-INJECTIVITY only ([print_stmt_inj] /
    [print_program_inj]) — there is no statement PARSER yet, so no statement round-trip.

    ⚠️ HONEST SCOPE — these are ROCQ-GRAMMAR self-consistency results, and the executable parser is
    DERIVED TOOLING (CLAUDE.md "Syntax authority"): the intended authority is the relational/canonical
    grammar layer.  That layer now EXISTS for TYPES and EXPRESSIONS — [CanonTy]/[CanonExpr] relations,
    [gprint_expr_canonical] (the printer inhabits the grammar), [lex_gprint_expr] (lexical faithfulness),
    and [canon_ty_unique] (type-level token uniqueness, proved PARSER-FREE via [gttokens_ty_inj]).  Still
    OPEN: expression-level uniqueness [canon_expr_unique], and the statement/program canonical layers
    ([CanonStmt]/[CanonProgram] + their canonicity/uniqueness/lex).  Until those land, [print_stmt_inj] /
    [print_program_inj] remain STRING-injectivity and [gprint_inj] is still parser-round-trip-based — so
    the parser has NOT yet been demoted below the grammar at the expression-uniqueness/statement layers.
    Nothing here is Go-compiler acceptance.  There is NO theorem that Go's compiler reads the
    emitted text as the same AST (that Go-subset RECOGNITION theorem — emitted grammar ⊆ Go grammar — is
    UNPROVEN, a SEPARATE Go-syntax recognition gap; Go's toolchain is TRUSTED, ARCHITECTURE §2a item 3 —
    NOT the plugin's source→term gap #10), and the plugin → emitted-bytes path also has a trusted [gofmt]
    post-step (see the Makefile).
    This file proves NO behavioral safety. *)

From Stdlib Require Import String List Ascii ZArith Lia Bool Eqdep_dec Floats.SpecFloat.
Import ListNotations.
Open Scope string_scope.

(* SYNTAX lives in GoAst.v; this file is the printers + lexer + parser + round-trips. *)
From Fido Require Import GoAst.
From Fido Require Export digits.   (* the ONE decimal authority: dec_digit/pos_digits/render_digits/print_Z (Export: downstream keeps GoPrint.print_Z) *)


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



(** [scan_id] consumes the maximal run of identifier characters — stopping exactly at the boundaries
    [print_ty] places after a type ("]", a space, end-of-string); [classify] (the keyword→[GoTy] map, in
    GoAst with the other char/ident predicates) maps a complete token to its scalar type ([None] for a
    nominal name).  Token-FIRST parsing (scan, then classify) gives maximal munch: "int8x" scans whole and
    classifies as nominal, never as [int8] + "x". *)
Fixpoint scan_id (s : string) : string * string :=
  match s with
  | EmptyString => (EmptyString, EmptyString)
  | String c s' => if is_idc c then let (tok, rest) := scan_id s' in (String c tok, rest)
                   else (EmptyString, s)
  end.


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
  unfold classify, special_ident.
  rewrite Hi64, Hi32, Hi16, Hi8, Hint, Hu64, Hu32, Hu16, Hu8, Hu, Hbool, Hstr, Hf64, Hf32.
  (* the table's non-type rows (nil/len/cap/println/print/panic) all classify to [None], whichever
     way their tests go — case-split them and every branch is definitional *)
  destruct (String.eqb s "nil"), (String.eqb s "len"), (String.eqb s "cap"),
           (String.eqb s "println"), (String.eqb s "print"), (String.eqb s "panic");
    (split; [ reflexivity | split; [ exact Hchan | exact Hmap ] ]).
Qed.



(** ---- INTEGER LITERALS ---- the decimal rendering of a [Z] value.  Magnitude is carried by [Z], so
    this is faithful for the FULL int64 AND uint64 ranges (unsigned [2^63,2^64) values are just large
    [Zpos] — no special-casing). *)
(** ---- INTEGER FAITHFULNESS (round-trip) ---- a decimal PARSER recovers the [Z] from [print_Z]'s
    output, so the emitted integer literal denotes EXACTLY the source value. *)
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

(** KEY LEMMA — parsing a rendered digit list from accumulator [a] consumes the digits
    MSB-first into the running fold, then continues with the suffix. *)
Lemma parseZ_pos_render : forall ds a s, Forall (fun d => (d < 10)%nat) ds ->
  parseZ_pos a (render_digits dec_digit ds s)
  = parseZ_pos (a * 10 ^ Z.of_nat (List.length ds) + dlist_val 10 ds)%Z s.
Proof.
  induction ds as [| d tl IH]; intros a s Hall.
  - cbn [render_digits fold_left List.length dlist_val]. f_equal. cbn. lia.
  - inversion Hall; subst.
    change (render_digits dec_digit (d :: tl) s)
      with (render_digits dec_digit tl (String (dec_digit d) s)).
    rewrite (IH a (String (dec_digit d) s)) by assumption.
    cbn [parseZ_pos]. rewrite dval_dec_digit by assumption.
    f_equal. cbn [List.length dlist_val].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

(** The first character a non-empty all-digit render emits is a decimal digit (so, for a
    POSITIVE [z], it is never the leading "-" — [parse_Z] takes the unsigned branch). *)
Lemma render_digits_head : forall ds s, ds <> nil -> Forall (fun d => (d < 10)%nat) ds ->
  exists k r, (k < 10)%nat /\ render_digits dec_digit ds s = String (dec_digit k) r.
Proof.
  induction ds as [| d tl IH]; intros s Hne Hall; [ contradiction | ].
  inversion Hall; subst. destruct tl as [| d2 tl'].
  - exists d, s. split; [ assumption | reflexivity ].
  - change (render_digits dec_digit (d :: d2 :: tl') s)
      with (render_digits dec_digit (d2 :: tl') (String (dec_digit d) s)).
    apply IH; [ discriminate | assumption ].
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

(** [parseZ_pos 0] of a rendered positive recovers it exactly. *)
Lemma parseZ_pos_print_Z_pos : forall p, parseZ_pos 0 (print_Z_pos p) = Zpos p.
Proof.
  intro p. unfold print_Z_pos.
  rewrite parseZ_pos_render by (apply pos_digits_bound; lia).
  rewrite pos_digits_val by lia. cbn [parseZ_pos]. lia.
Qed.

(** FAITHFULNESS, UNCONDITIONAL: the round-trip holds for EVERY [z]. *)
Theorem print_parse_Z : forall z, parse_Z (print_Z z) = z.
Proof.
  intro z. destruct z as [| p | p]; cbn [print_Z].
  - reflexivity.
  - unfold print_Z_pos.
    destruct (render_digits_head (pos_digits 10 p) "" (pos_digits_nonnil 10 p)
                (pos_digits_bound 10 p ltac:(lia))) as [k [r [Hk Hr]]].
    unfold print_Z_pos in *.
    rewrite Hr, (parse_Z_nonminus _ _ (dec_digit_ne_minus k Hk)), <- Hr.
    apply parseZ_pos_print_Z_pos.
  - change (("-" ++ print_Z_pos p)%string) with (String (ascii_of_nat 45) (print_Z_pos p)).
    rewrite parse_Z_neg, parseZ_pos_print_Z_pos. reflexivity.
Qed.

(** ---- STRING LITERALS ---- escape a Go double-quoted string literal: wrap in dquotes, escape
    dquote/backslash/newline/tab/CR, pass printable ASCII through, and emit a hex escape (backslash-x,
    lowercase, 2 digits) for everything else.  ASCII codes: 34 dquote, 92 backslash, 10 newline, 9 tab,
    13 CR, 110 n, 116 t, 114 r, 120 x. *)
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


(** ---- STRING-LITERAL FAITHFULNESS (round-trip) ---- the escaping is LOSSLESS: the VALIDATING decoder
    [unescape_opt] recovers the exact original bytes from [esc_string] (as [Some s]), so [print_string_lit]
    denotes precisely its argument.  [unescape_opt] is also FAIL-CLOSED: [None] on any malformed escape, so
    the lexer rejects ill-formed string syntax instead of normalizing it (see the [lex_bad_*] examples). *)
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
    [unescape_opt] REJECTS a [\x] whose two chars are not both [is_hex] (a non-hex or upper-case [\x] is
    outside the printer image and must fail to lex).  [unhex] above inverts every byte this accepts. *)
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
    (34 dquote / 92 backslash / 10 nl / 9 tab / 13 cr) and NOT printable [32,126] — exactly the set
    [esc_byte]'s final branch covers.  The decoder's [\x] arm requires it, so a [\xHH] is accepted ONLY
    when [esc_byte] would actually have EMITTED it (a hex escape of printable 'A' or of the dquote is
    REJECTED — [esc_string] prints those raw / named, never as hex). *)
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

(** The VALIDATING decoder: reverse [esc_byte], FAIL-CLOSED.  Accepts EXACTLY the PRINTER IMAGE — the byte
    set [esc_string] can emit — and nothing else (accepted == emitted, PROVEN by [unescape_opt_image] below);
    [None] on every other spelling, so the lexer REJECTS non-printer-image string syntax at tokenization
    instead of normalizing it.  Accepted: the five named escapes (escaped dquote, escaped backslash,
    [\n] [\t] [\r]), a [\xHH] whose two digits are both [is_hex] (LOWER-CASE) AND whose decoded byte
    [hex_escaped_byte]s (so [esc_byte] really takes its hex fallback), and a RAW body byte in [32,126]
    minus {34,92}.  Rejected: truncated or unknown escapes, a [\x] whose two chars are not both lower-case
    hex, a [\xHH] of a named-escape/printable byte, and any raw byte [esc_byte] would have escaped.
    Structural on sub-terms of [s]; the ONE decode authority. *)
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

(** ★ THE STRING-LITERAL ROUND-TRIP — the VALIDATING decoder recovers EXACTLY what [esc_string] emits, so
    [print_string_lit] denotes precisely its argument and the lexer's [TStr] is faithful
    (emitted ⊆ accepted). *)
Theorem esc_string_roundtrip_opt : forall s, unescape_opt (esc_string s) = Some s.
Proof.
  induction s as [ | c rest IH ]; [ reflexivity | ].
  cbn [esc_string]. rewrite unescape_opt_esc_byte, IH. reflexivity.
Qed.

(** ★ THE STRING-LITERAL REVERSE-IMAGE THEOREM — every body the decoder ACCEPTS is EXACTLY the canonical
    [esc_string] escaping of its decode; with [esc_string_roundtrip_opt] (emitted ⊆ accepted) this is a
    two-way exactness: [unescape_opt body = Some s  ↔  body = esc_string s].  Helper lemmas first, then
    the theorem by strong induction on the body length. *)
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
    (via [esc_string_roundtrip_opt]), so there is exactly ONE un-escaper.
    Structural on [s] (each recursive call is on a sub-term, like [unescape_opt]). *)
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

(** ---- HEX LITERALS ---- [0x]-prefixed lowercase hex.  LIVE in the plugin: [print_hex] renders the
    fixed-width mask / sign-bit constants and the [spec_float] hex-literal mantissa, and the [EHex] GExpr
    LEAF lets the fixed-width arithmetic bridge build the WHOLE masked / sign-extended expression for the
    verified [gprint].  STILL on the trusted [fw_wrap]: the fixed-width CONVERSIONS [uint8(x)], shifts,
    div/mod, and standalone fw ops. *)
Definition print_hex_body (n : N) : string :=
  match n with
  | N0 => "0"
  | Npos p => render_digits hexdig (pos_digits 16 p) ""
  end.
Definition print_hex (n : N) : string := ("0x" ++ print_hex_body n)%string.

(** ---- HEX FAITHFULNESS (round-trip) ---- [print_hex]'s DOMAIN is [N]: Go hex literals are
    unsigned ([-0xff] is unary minus over [0xff]), so a negative input is UNREPRESENTABLE at the
    type — the round-trip is unconditional over the whole domain. *)
Fixpoint parseHex_pos (acc : Z) (s : string) : Z :=
  match s with EmptyString => acc | String c s' => parseHex_pos (acc * 16 + Z.of_nat (unhex c))%Z s' end.
Definition parse_hex (s : string) : Z :=
  match s with String _ (String _ rest) => parseHex_pos 0 rest | _ => 0%Z end.

Lemma parse_hex_0x : forall X, parse_hex ("0x" ++ X)%string = parseHex_pos 0 X.
Proof. intro X. reflexivity. Qed.

Lemma parseHex_pos_render : forall ds a s, Forall (fun d => (d < 16)%nat) ds ->
  parseHex_pos a (render_digits hexdig ds s)
  = parseHex_pos (a * 16 ^ Z.of_nat (List.length ds) + dlist_val 16 ds)%Z s.
Proof.
  induction ds as [| d tl IH]; intros a s Hall.
  - cbn [render_digits fold_left List.length dlist_val]. f_equal. cbn. lia.
  - inversion Hall; subst.
    change (render_digits hexdig (d :: tl) s)
      with (render_digits hexdig tl (String (hexdig d) s)).
    rewrite (IH a (String (hexdig d) s)) by assumption.
    cbn [parseHex_pos]. rewrite unhex_hexdig by assumption.
    f_equal. cbn [List.length dlist_val].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

(** UNCONDITIONAL over the whole domain. *)
Theorem print_parse_hex : forall n, parse_hex (print_hex n) = Z.of_N n.
Proof.
  intro n. unfold print_hex. rewrite parse_hex_0x.
  destruct n as [| p]; [ reflexivity | ].
  cbn [print_hex_body].
  rewrite parseHex_pos_render by (apply pos_digits_bound; lia).
  rewrite pos_digits_val by lia. cbn [parseHex_pos]. lia.
Qed.

(** ---- FLOAT-HEX LITERAL ---- the IEEE [spec_float] finite value ±m·2^e emits as Go's hex float
    [±0x<m>p<e>], assembling the verified mantissa/exponent printers ([print_hex] / [print_Z]).
    [sign] = sign, [mant] = mantissa (rendered hex), [exp] = exponent (signed decimal). *)
(** binary64 VALIDITY of a finite (mantissa, exponent) — SpecFloat's own [bounded] (canonical
    mantissa + exponent bound), extracted so the trusted plugin gates a raw [S754_finite]
    literal against the MODEL's canonical-carrier invariant with the VERIFIED checker (one
    authority — no hand-rolled approximation in OCaml). *)
Definition f64_bounded (m : positive) (e : Z) : bool := bounded 53 1024 m e.

Definition print_float_hex (sign : bool) (mant : N) (exp : Z) : string :=
  ((if sign then "-" else "") ++ print_hex mant ++ "p" ++ print_Z exp)%string.


(** FAITHFULNESS — the float literal round-trips: a parser recovers [(sign, mant, exp)] EXACTLY.  The
    "p" delimiter is unambiguous because the mantissa render [print_hex] contains no "p" (hex digits are
    0-9a-f); [split_p] cuts there, then [parse_hex] / [parse_Z] recover the parts. *)
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

Lemma render_hex_no_p : forall ds acc, Forall (fun d => (d < 16)%nat) ds -> no_p acc ->
  no_p (render_digits hexdig ds acc).
Proof.
  induction ds as [| d tl IH]; intros acc Hall Hacc; [ exact Hacc | ].
  inversion Hall; subst.
  change (render_digits hexdig (d :: tl) acc)
    with (render_digits hexdig tl (String (hexdig d) acc)).
  apply IH; [ assumption | cbn [no_p]; split; [ apply is_p_hexdig; assumption | exact Hacc ] ].
Qed.

Lemma no_p_print_hex : forall n, no_p (print_hex n).
Proof.
  intro n. unfold print_hex. apply no_p_app.
  - cbn [no_p]. repeat split; (reflexivity || exact I).
  - destruct n as [| p]; cbn [print_hex_body];
      [ cbn [no_p]; repeat split; (reflexivity || exact I)
      | apply render_hex_no_p; [ apply pos_digits_bound; lia | exact I ] ].
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
(** UNCONDITIONAL — the mantissa's domain [N] makes a negative literal unrepresentable. *)
Theorem print_parse_float_hex : forall sign mant exp,
  parse_float_hex (print_float_hex sign mant exp) = (sign, Z.of_N mant, exp).
Proof.
  intros sign mant exp.
  assert (Hmrt : parse_hex (print_hex mant) = Z.of_N mant) by (apply print_parse_hex).
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

(** ============================================================================
    ---- EXPRESSIONS: OPERATOR PRECEDENCE ---- the printer inserts parentheses ONLY where an operand's
    operator binds LOOSER than its context — get this wrong and [(a+b)*c] misprints as [a+b*c], silently
    changing the program's meaning.  [binop_prec] / [binop_text] DERIVE precedence and surface text from
    the constructor — the single source of truth; [gprint] parenthesises a sub-expression exactly when its
    [binop_prec] is looser than the context. *)
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
(** every char a LOWER-CASE hex digit ([is_hex], 0-9a-f) — the rendered-hex alphabet, for the hex-literal scan. *)
Fixpoint all_hex (s : string) : bool :=
  match s with EmptyString => true | String c s' => andb (is_hex c) (all_hex s') end.
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
  | THex : HexZ -> Token  (* a [0x]-prefixed HEX integer literal token (parses to [EHex]); the value is a NON-NEGATIVE [Z] (in [HexZ]) *)
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
(** scan a maximal run of LOWER-CASE hex digits ([is_hex]) off the head — the body of a [0x]-hex literal. *)
Fixpoint scan_hex (s : string) : string * string :=
  match s with
  | String c s' => if is_hex c then let (d, r) := scan_hex s' in (String c d, r) else (EmptyString, s)
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

(** ---- LENGTH FACTS for the scanners: every rest is a (non-strict) suffix by length —
    with the consumed head char, each lexer step strictly shrinks the input, which is the
    whole termination argument (no step budget). *)
Lemma scan_id_len : forall s tok r, scan_id s = (tok, r) -> String.length r <= String.length s.
Proof.
  induction s as [| c s' IH]; intros tok r H; cbn [scan_id] in H.
  - injection H as <- <-. cbn. lia.
  - destruct (is_idc c); [ | injection H as <- <-; cbn; lia ].
    destruct (scan_id s') as [d r'] eqn:E. injection H as <- <-.
    cbn. pose proof (IH d r' eq_refl). lia.
Qed.
Lemma scan_digits_len : forall s num r, scan_digits s = (num, r) -> String.length r <= String.length s.
Proof.
  induction s as [| c s' IH]; intros num r H; cbn [scan_digits] in H.
  - injection H as <- <-. cbn. lia.
  - destruct (is_dec_char c); [ | injection H as <- <-; cbn; lia ].
    destruct (scan_digits s') as [d r'] eqn:E. injection H as <- <-.
    cbn. pose proof (IH d r' eq_refl). lia.
Qed.
Lemma scan_hex_len : forall s d r, scan_hex s = (d, r) -> String.length r <= String.length s.
Proof.
  induction s as [| c s' IH]; intros d r H; cbn [scan_hex] in H.
  - injection H as <- <-. cbn. lia.
  - destruct (is_hex c); [ | injection H as <- <-; cbn; lia ].
    destruct (scan_hex s') as [d' r'] eqn:E. injection H as <- <-.
    cbn. pose proof (IH d' r' eq_refl). lia.
Qed.
Lemma scan_quote_len : forall s b r, scan_quote s = Some (b, r) -> String.length r <= String.length s.
Proof.
  (* the escape case skips TWO characters, so induct on a length bound (a proof-side
     measure over the finite input — not an evaluator budget) *)
  assert (aux : forall n s b r, String.length s <= n ->
                scan_quote s = Some (b, r) -> String.length r <= String.length s).
  { induction n as [| n IH]; intros s b r Hle H.
    - destruct s; [ discriminate H | cbn in Hle; lia ].
    - destruct s as [| c1 s']; [ discriminate H | ]. cbn [scan_quote] in H.
      destruct (Nat.eqb (nat_of_ascii c1) 34); [ injection H as <- <-; cbn; lia | ].
      destruct (Nat.eqb (nat_of_ascii c1) 92).
      + destruct s' as [| c2 rest2]; [ discriminate H | ].
        destruct (scan_quote rest2) as [[body r']|] eqn:E; [ | discriminate H ].
        injection H as <- <-.
        cbn in Hle |- *. pose proof (IH rest2 body r' ltac:(lia) E). lia.
      + destruct (scan_quote s') as [[body r']|] eqn:E; [ | discriminate H ].
        injection H as <- <-. cbn in Hle |- *. pose proof (IH s' body r' ltac:(lia) E). lia. }
  intros s b r H. exact (aux (String.length s) s b r (le_n _) H).
Qed.
Lemma lex_op_len : forall c s' t r, lex_op c s' = Some (t, r) -> String.length r <= String.length s'.
Proof.
  intros c s' t r H. unfold lex_op in H.
  destruct s' as [| d s''];
    repeat match type of H with
    | context [Ascii.eqb ?a ?b] => destruct (Ascii.eqb a b)
    end;
    try discriminate H; inversion H; subst; cbn; lia.
Qed.

(** The per-arm DECREASE facts — each recursive call's [Acc_inv] obligation, discharged from
    the scanner length lemmas plus the consumed head character (stated on the CONCRETE
    [String c s'] shape the match branch provides — no equation plumbing). *)
Lemma is_idstart_is_idc : forall c, is_idstart c = true -> is_idc c = true.
Proof.
  intros c H. unfold is_idstart in H. unfold is_idc.
  apply Bool.orb_prop in H. destruct H as [H | H].
  - apply Bool.orb_prop in H. destruct H as [H | H]; rewrite H;
      rewrite ?Bool.orb_true_r, ?Bool.orb_true_l; reflexivity.
  - rewrite H. rewrite ?Bool.orb_true_r. reflexivity.
Qed.
Lemma lex_step_tail : forall c s', String.length s' < String.length (String c s').
Proof. intros. cbn. lia. Qed.
Lemma lex_step_id : forall c s' tok rest, is_idc c = true ->
  scan_id (String c s') = (tok, rest) -> String.length rest < String.length (String c s').
Proof.
  intros c s' tok rest Hc Hscan. cbn [scan_id] in Hscan. rewrite Hc in Hscan.
  destruct (scan_id s') as [d r] eqn:E2. injection Hscan as <- <-.
  pose proof (scan_id_len s' d r E2). cbn. lia.
Qed.
Lemma lex_step_digits : forall c s' num rest, is_dec_char c = true ->
  scan_digits (String c s') = (num, rest) -> String.length rest < String.length (String c s').
Proof.
  intros c s' num rest Hc Hscan. cbn [scan_digits] in Hscan. rewrite Hc in Hscan.
  destruct (scan_digits s') as [d r] eqn:E2. injection Hscan as <- <-.
  pose proof (scan_digits_len s' d r E2). cbn. lia.
Qed.
Lemma lex_step_negdigits : forall c s' num rest,
  scan_digits s' = (num, rest) -> String.length rest < String.length (String c s').
Proof. intros c s' num rest Hscan. pose proof (scan_digits_len s' num rest Hscan). cbn. lia. Qed.
Lemma lex_step_hex : forall c c1 s2 hd rest,
  scan_hex s2 = (hd, rest) -> String.length rest < String.length (String c (String c1 s2)).
Proof. intros c c1 s2 hd rest Hscan. pose proof (scan_hex_len s2 hd rest Hscan). cbn. lia. Qed.
Lemma lex_step_quote : forall c s' body rest,
  scan_quote s' = Some (body, rest) -> String.length rest < String.length (String c s').
Proof. intros c s' body rest Hscan. pose proof (scan_quote_len s' body rest Hscan). cbn. lia. Qed.
Lemma lex_step_op : forall c s' t rest,
  lex_op c s' = Some (t, rest) -> String.length rest < String.length (String c s').
Proof. intros c s' t rest Hop. pose proof (lex_op_len c s' t rest Hop). cbn. lia. Qed.

Definition cert {A : Type} (x : A) : { y : A | x = y } := exist _ x eq_refl.
(** THE LEXER.  Skip whitespace; an [is_idstart] head is an identifier/keyword; a digit (or [-]+digit, the
    negative-literal form — binary [-] is always SPACED in the printer) is an integer; a dquote is a string
    literal; otherwise an operator/delimiter.  Structural recursion on the [Acc lt] certificate of the input
    length (every token consumes >= 1 char): totality IS the well-founded order — no step budget anywhere.
    A digit head is a DECIMAL int UNLESS it is the [0x] prefix of a HEX literal (checked first; sound
    because [print_Z] never emits "0x").  "0x" with NO hex digit and a malformed string escape
    ([unescape_opt = None]) FAIL the whole lex — fail-closed, never a guessed token. *)
Fixpoint lex_acc (s : string) (a : Acc lt (String.length s)) {struct a} : option (list Token) :=
  match s return Acc lt (String.length s) -> option (list Token) with
  | EmptyString => fun _ => Some nil
  | String c s' => fun a =>
      if is_space c then
        lex_acc s' (Acc_inv a (lex_step_tail c s'))
      else match Bool.bool_dec (is_idstart c) true with
      | left Hid =>
          match cert (scan_id (String c s')) with
          | exist _ (tok, rest) Hscan =>
              match lex_ident tok with
              | Some t =>
                  match lex_acc rest (Acc_inv a (lex_step_id c s' tok rest
                                                   (is_idstart_is_idc c Hid) Hscan)) with
                  | Some l => Some (t :: l) | None => None end
              | None => None end
          end
      | right _ =>
      match Bool.bool_dec (is_dec_char c) true with
      | left Hdec =>
          match s' return Acc lt (String.length (String c s')) -> option (list Token) with
          | String c1 s2 => fun a =>
              if andb (Ascii.eqb c (ch 48)) (Ascii.eqb c1 (ch 120)) then
                match cert (scan_hex s2) with
                | exist _ (hd, rest) Hscan =>
                    match hd with
                    | EmptyString => None
                    | String _ _ =>
                        match bool_dec ((0 <=? parseHex_pos 0 hd)%Z) true with
                        | left H =>
                            match lex_acc rest (Acc_inv a (lex_step_hex c c1 s2 hd rest Hscan)) with
                            | Some l => Some (THex (exist _ (parseHex_pos 0 hd) H) :: l) | None => None end
                        | right _ => None
                        end
                    end
                end
              else
                match cert (scan_digits (String c (String c1 s2))) with
                | exist _ (num, rest) Hscan =>
                    match lex_acc rest (Acc_inv a (lex_step_digits c (String c1 s2) num rest Hdec Hscan)) with
                    | Some l => Some (TInt (parse_Z num) :: l) | None => None end
                end
          | EmptyString => fun a =>
              match cert (scan_digits (String c EmptyString)) with
              | exist _ (num, rest) Hscan =>
                  match lex_acc rest (Acc_inv a (lex_step_digits c EmptyString num rest Hdec Hscan)) with
                  | Some l => Some (TInt (parse_Z num) :: l) | None => None end
              end
          end a
      | right _ =>
      if andb (Ascii.eqb c (ch 45)) (match s' with String d _ => is_dec_char d | _ => false end) then
        match cert (scan_digits s') with
        | exist _ (num, rest) Hscan =>
            match lex_acc rest (Acc_inv a (lex_step_negdigits c s' num rest Hscan)) with
            | Some l => Some (TInt (parse_Z (String c num)) :: l) | None => None end
        end
      else if Ascii.eqb c (ch 34) then
        match cert (scan_quote s') with
        | exist _ (Some (body, rest)) Hscan =>
            match unescape_opt body with
            | Some sdec =>
                match lex_acc rest (Acc_inv a (lex_step_quote c s' body rest Hscan)) with
                | Some l => Some (TStr sdec :: l) | None => None end
            | None => None
            end
        | exist _ None _ => None
        end
      else
        match cert (lex_op c s') with
        | exist _ (Some (t, rest)) Hop =>
            match lex_acc rest (Acc_inv a (lex_step_op c s' t rest Hop)) with
            | Some l => Some (t :: l) | None => None end
        | exist _ None _ => None
        end
      end end
  end a.
Definition lex (s : string) : option (list Token) := lex_acc s (lt_wf (String.length s)).

(** [lex_acc] is PROOF-IRRELEVANT in its termination certificate: any two [Acc] proofs give the same
    result (strong induction on the input length; every branch steps both sides in lockstep and the
    recursive certificates fall to the IH).  This is what lets the one-step unfold equations below be
    stated over [lex] ITSELF — no auxiliary evaluator and no step budget of any kind. *)
Lemma lex_acc_pi : forall n s, String.length s < n ->
  forall a1 a2 : Acc lt (String.length s), lex_acc s a1 = lex_acc s a2.
Proof.
  induction n as [| n IH]; intros s Hn a1 a2; [ lia | ].
  destruct a1 as [h1]. destruct a2 as [h2].
  destruct s as [| c s']; [ reflexivity | ].
  cbn [lex_acc Acc_inv].
  destruct (is_space c) eqn:Hsp.
  { apply IH. cbn in Hn |- *. lia. }
  destruct (Bool.bool_dec (is_idstart c) true) as [Hid | Hnid].
  { destruct (cert (scan_id (String c s'))) as [[tok rest] Hscan].
    destruct (lex_ident tok) as [t|]; [ | reflexivity ].
    pose proof (lex_step_id c s' tok rest (is_idstart_is_idc c Hid) Hscan) as Hlt.
    erewrite (IH rest); [ reflexivity | cbn in Hn, Hlt |- *; lia ]. }
  destruct (Bool.bool_dec (is_dec_char c) true) as [Hdec | Hndec].
  { destruct s' as [| c1 s2]; cbn [Acc_inv].
    { destruct (cert (scan_digits (String c EmptyString))) as [[num rest] Hscan].
      pose proof (lex_step_digits c EmptyString num rest Hdec Hscan) as Hlt.
      erewrite (IH rest); [ reflexivity | cbn in Hn, Hlt |- *; lia ]. }
    destruct (andb (Ascii.eqb c (ch 48)) (Ascii.eqb c1 (ch 120))) eqn:Hpre.
    { destruct (cert (scan_hex s2)) as [[hd rest] Hscan].
      destruct hd as [| h hd']; [ reflexivity | ].
      destruct (bool_dec ((0 <=? parseHex_pos 0 (String h hd'))%Z) true); [ | reflexivity ].
      pose proof (lex_step_hex c c1 s2 (String h hd') rest Hscan) as Hlt.
      erewrite (IH rest); [ reflexivity | cbn in Hn, Hlt |- *; lia ]. }
    { destruct (cert (scan_digits (String c (String c1 s2)))) as [[num rest] Hscan].
      pose proof (lex_step_digits c (String c1 s2) num rest Hdec Hscan) as Hlt.
      erewrite (IH rest); [ reflexivity | cbn in Hn, Hlt |- *; lia ]. } }
  destruct (andb (Ascii.eqb c (ch 45)) (match s' with String d _ => is_dec_char d | _ => false end)) eqn:Hneg.
  { destruct (cert (scan_digits s')) as [[num rest] Hscan].
    pose proof (lex_step_negdigits c s' num rest Hscan) as Hlt.
    erewrite (IH rest); [ reflexivity | cbn in Hn, Hlt |- *; lia ]. }
  destruct (Ascii.eqb c (ch 34)) eqn:Hq.
  { destruct (cert (scan_quote s')) as [[[body rest]|] Hscan]; [ | reflexivity ].
    destruct (unescape_opt body); [ | reflexivity ].
    pose proof (lex_step_quote c s' body rest Hscan) as Hlt.
    erewrite (IH rest); [ reflexivity | cbn in Hn, Hlt |- *; lia ]. }
  destruct (cert (lex_op c s')) as [[[t rest]|] Hop]; [ | reflexivity ].
  pose proof (lex_step_op c s' t rest Hop) as Hlt.
  erewrite (IH rest); [ reflexivity | cbn in Hn, Hlt |- *; lia ].
Qed.

(** [lex] at an [Acc_intro] certificate whose sub-certificates are [lt_wf] — the shape that makes ONE
    step of [lex_acc] reduce and every recursive certificate come back as [lt_wf], i.e. as [lex]. *)
Lemma lex_unfold_pi : forall s,
  lex s = lex_acc s (Acc_intro (String.length s) (fun y _ => lt_wf y)).
Proof.
  intro s. unfold lex. apply (lex_acc_pi (S (String.length s)) s (Nat.lt_succ_diag_r _)).
Qed.
Lemma lex_empty : lex ""%string = Some nil.
Proof. rewrite lex_unfold_pi. reflexivity. Qed.

(** decimal-head classification facts (needed by the decimal unfold equation just below). *)
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

(** ---- ONE-STEP UNFOLD EQUATIONS for [lex] ---- each lexer branch as an equation over [lex] ITSELF.
    The recursive occurrence on the right is [lex rest]: no auxiliary lexer, no budget premise —
    "step once" is a proved EQUATION between total functions, never an approximation. *)
Lemma lex_eq_space : forall c s', is_space c = true -> lex (String c s') = lex s'.
Proof.
  intros c s' Hsp. rewrite (lex_unfold_pi (String c s')). cbn [lex_acc Acc_inv].
  rewrite Hsp. reflexivity.
Qed.

Lemma lex_eq_id : forall c s' tok rest,
  is_space c = false -> is_idstart c = true ->
  scan_id (String c s') = (tok, rest) ->
  lex (String c s') = match lex_ident tok with
                      | Some t => match lex rest with Some l => Some (t :: l) | None => None end
                      | None => None
                      end.
Proof.
  intros c s' tok rest Hsp Hid Hscan.
  rewrite (lex_unfold_pi (String c s')). cbn [lex_acc Acc_inv]. rewrite Hsp.
  destruct (Bool.bool_dec (is_idstart c) true) as [Hid2 | C]; [ | contradiction ].
  destruct (cert (scan_id (String c s'))) as [[tok0 rest0] Hscan0].
  pose proof (eq_trans (eq_sym Hscan) Hscan0) as He. injection He as <- <-.
  destruct (lex_ident tok) as [t|]; reflexivity.
Qed.

Lemma lex_eq_dec : forall c s',
  is_dec_char c = true ->
  match s' with String c1 _ => Ascii.eqb c1 (ch 120) = false | EmptyString => True end ->
  lex (String c s') =
    (let (num, rest) := scan_digits (String c s') in
     match lex rest with Some l => Some (TInt (parse_Z num) :: l) | None => None end).
Proof.
  intros c s' Hdec Hnotx.
  rewrite (lex_unfold_pi (String c s')). cbn [lex_acc Acc_inv].
  rewrite (is_dec_char_not_space _ Hdec).
  destruct (Bool.bool_dec (is_idstart c) true) as [C | _];
    [ exfalso; rewrite (is_dec_char_not_idstart _ Hdec) in C; discriminate C | ].
  destruct (Bool.bool_dec (is_dec_char c) true) as [Hdec2 | C]; [ | contradiction ].
  destruct s' as [| c1 s2]; cbn [Acc_inv].
  - destruct (cert (scan_digits (String c EmptyString))) as [[num0 rest0] Hscan0].
    rewrite Hscan0. reflexivity.
  - rewrite Hnotx, Bool.andb_false_r.
    destruct (cert (scan_digits (String c (String c1 s2)))) as [[num0 rest0] Hscan0].
    rewrite Hscan0. reflexivity.
Qed.

Lemma lex_eq_neg : forall d D',
  is_dec_char d = true ->
  lex (String (ch 45) (String d D')) =
    (let (num, rest) := scan_digits (String d D') in
     match lex rest with Some l => Some (TInt (parse_Z (String (ch 45) num)) :: l) | None => None end).
Proof.
  intros d D' Hd.
  rewrite (lex_unfold_pi (String (ch 45) (String d D'))). cbn [lex_acc Acc_inv].
  replace (is_space (ch 45)) with false by reflexivity.
  destruct (Bool.bool_dec (is_idstart (ch 45)) true) as [C | _]; [ exfalso; vm_compute in C; discriminate C | ].
  destruct (Bool.bool_dec (is_dec_char (ch 45)) true) as [C | _]; [ exfalso; vm_compute in C; discriminate C | ].
  replace (Ascii.eqb (ch 45) (ch 45)) with true by reflexivity.
  rewrite Hd. cbn [andb].
  destruct (cert (scan_digits (String d D'))) as [[num0 rest0] Hscan0].
  rewrite Hscan0. reflexivity.
Qed.

Lemma lex_eq_hex : forall s2,
  lex (String (ch 48) (String (ch 120) s2)) =
    match scan_hex s2 with
    | (EmptyString, _) => None
    | (String h hd', rest) =>
        match bool_dec ((0 <=? parseHex_pos 0 (String h hd'))%Z) true with
        | left H => match lex rest with
                    | Some l => Some (THex (exist _ (parseHex_pos 0 (String h hd')) H) :: l)
                    | None => None end
        | right _ => None
        end
    end.
Proof.
  intro s2.
  rewrite (lex_unfold_pi (String (ch 48) (String (ch 120) s2))). cbn [lex_acc Acc_inv].
  replace (is_space (ch 48)) with false by reflexivity.
  destruct (Bool.bool_dec (is_idstart (ch 48)) true) as [C | _]; [ exfalso; vm_compute in C; discriminate C | ].
  destruct (Bool.bool_dec (is_dec_char (ch 48)) true) as [Hd | C]; [ | vm_compute in C; exfalso; apply C; reflexivity ].
  replace (andb (Ascii.eqb (ch 48) (ch 48)) (Ascii.eqb (ch 120) (ch 120))) with true by reflexivity.
  destruct (cert (scan_hex s2)) as [[hd0 rest0] Hscan0]. rewrite Hscan0.
  destruct hd0 as [| h hd']; [ reflexivity | ].
  destruct (bool_dec ((0 <=? parseHex_pos 0 (String h hd'))%Z) true) as [H | H]; reflexivity.
Qed.

Lemma lex_eq_quote : forall s',
  lex (String (ch 34) s') =
    match scan_quote s' with
    | Some (body, rest) =>
        match unescape_opt body with
        | Some sdec => match lex rest with Some l => Some (TStr sdec :: l) | None => None end
        | None => None
        end
    | None => None
    end.
Proof.
  intro s'.
  rewrite (lex_unfold_pi (String (ch 34) s')). cbn [lex_acc Acc_inv].
  replace (is_space (ch 34)) with false by reflexivity.
  destruct (Bool.bool_dec (is_idstart (ch 34)) true) as [C | _]; [ exfalso; vm_compute in C; discriminate C | ].
  destruct (Bool.bool_dec (is_dec_char (ch 34)) true) as [C | _]; [ exfalso; vm_compute in C; discriminate C | ].
  replace (Ascii.eqb (ch 34) (ch 45)) with false by reflexivity. cbn [andb].
  replace (Ascii.eqb (ch 34) (ch 34)) with true by reflexivity.
  destruct (cert (scan_quote s')) as [[[body0 rest0]|] Hscan0]; rewrite Hscan0.
  - destruct (unescape_opt body0) as [sdec|]; reflexivity.
  - reflexivity.
Qed.

Lemma lex_eq_op : forall c X t rest,
  is_space c = false -> is_idstart c = false -> is_dec_char c = false ->
  andb (Ascii.eqb c (ch 45)) (match X with String d _ => is_dec_char d | EmptyString => false end) = false ->
  Ascii.eqb c (ch 34) = false ->
  lex_op c X = Some (t, rest) ->
  lex (String c X) = match lex rest with Some l => Some (t :: l) | None => None end.
Proof.
  intros c X t rest Hsp Hid Hdc Hneg H34 Hop.
  rewrite (lex_unfold_pi (String c X)). cbn [lex_acc Acc_inv].
  rewrite Hsp.
  destruct (Bool.bool_dec (is_idstart c) true) as [C | _]; [ exfalso; rewrite Hid in C; discriminate C | ].
  destruct (Bool.bool_dec (is_dec_char c) true) as [C | _]; [ exfalso; rewrite Hdc in C; discriminate C | ].
  rewrite Hneg, H34.
  destruct (cert (lex_op c X)) as [[[t0 rest0]|] Hop0];
    pose proof (eq_trans (eq_sym Hop) Hop0) as He; [ injection He as <- <- | discriminate He ].
  reflexivity.
Qed.

Lemma lex_eq_op_None : forall c X,
  is_space c = false -> is_idstart c = false -> is_dec_char c = false ->
  andb (Ascii.eqb c (ch 45)) (match X with String d _ => is_dec_char d | EmptyString => false end) = false ->
  Ascii.eqb c (ch 34) = false ->
  lex_op c X = None ->
  lex (String c X) = None.
Proof.
  intros c X Hsp Hid Hdc Hneg H34 Hop.
  rewrite (lex_unfold_pi (String c X)). cbn [lex_acc Acc_inv].
  rewrite Hsp.
  destruct (Bool.bool_dec (is_idstart c) true) as [C | _]; [ exfalso; rewrite Hid in C; discriminate C | ].
  destruct (Bool.bool_dec (is_dec_char c) true) as [C | _]; [ exfalso; rewrite Hdc in C; discriminate C | ].
  rewrite Hneg, H34.
  destruct (cert (lex_op c X)) as [[[t0 rest0]|] Hop0];
    pose proof (eq_trans (eq_sym Hop) Hop0) as He; [ discriminate He | reflexivity ].
Qed.

(** ---- TYPE-PARSER DEFINITIONS (before the expression parser so [parse_postfix] can call [parse_gty]
    for type assertions / conversions; the round-trip PROOFS are below, after the seams). ---- *)
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
   [tsize] is a PROOF-LAYER size measure only (type-node count for induction bounds).
   (The output side, [print_ty]/[gttokens_ty], is fully exhaustive.) *)
Fixpoint tsize (t : GoTy) : nat :=
  match t with
  | GTPtr u | GTSlice u | GTChan u => S (tsize u)
  | GTMap k v => S (tsize k + tsize v)
  | _ => 1
  end.
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

(** The type parser is Acc-STRUCTURAL on the token-list length (every arm consumes >= 1 token before
    recursing) — no step budget.  The result carries its own SUFFIX BOUND ([length r <= length input]) so
    the map arm's second recursive call ([V] after [K]) stays inside the termination certificate. *)
Lemma tlt1 : forall n, n < S n.                                    Proof. intros; lia. Qed.
Lemma tlt2 : forall n, n < S (S n).                                Proof. intros; lia. Qed.
Lemma tle1 : forall m n, m <= n -> m <= S n.                       Proof. intros; lia. Qed.
Lemma tle2 : forall m n, m <= n -> m <= S (S n).                   Proof. intros; lia. Qed.
Lemma tlt_map : forall a b, S a <= b -> a < S (S b).               Proof. intros; lia. Qed.
Lemma tle_map : forall a b c, a <= b -> S b <= c -> a <= S (S c).  Proof. intros; lia. Qed.
(* strict analogs — for [skip_gty_acc]'s STRICT result sig (its remainder is always shorter). *)
Lemma slt2 : forall a b, a < b -> a < S (S b).                     Proof. intros; lia. Qed.
Lemma strmap_acc : forall a b, S a < b -> a < S (S b).            Proof. intros; lia. Qed.
Lemma smap : forall a b c, a < b -> S b < c -> a < S (S c).        Proof. intros; lia. Qed.
Lemma ppop    : forall x y, S x <= y -> x < S y.                   Proof. intros; lia. Qed.
Lemma ppop2   : forall x a y, S x <= a -> S a <= y -> x < S y.     Proof. intros; lia. Qed.
Lemma pacc    : forall x a y, x <= a -> a < y -> x < y.            Proof. intros; lia. Qed.
Lemma pskip   : forall x y, S (S x) <= y -> x < y.                 Proof. intros; lia. Qed.
Lemma pfin    : forall x a y, x <= a -> a < y -> x <= y.           Proof. intros; lia. Qed.
Lemma pconv   : forall x a b y, S x <= a -> S a <= b -> b <= y -> x < y.  Proof. intros; lia. Qed.
(** the RANKED parser measure [5 * token-length + rank] (atom 1, primary 2, expr 3, list HEADS 4,
    postfix/climb/list TAILS 0): same-length grammar dispatch descends by RANK, every other call by
    LENGTH.  A well-founded measure certifying descent — never a budget bounding execution. *)
Lemma m_r1 : forall t, 5 * t + 1 < 5 * t + 2.                      Proof. intros; lia. Qed.
Lemma m_r2 : forall t, 5 * t + 2 < 5 * t + 3.                      Proof. intros; lia. Qed.
Lemma m_r3 : forall t, 5 * t + 3 < 5 * t + 4.                      Proof. intros; lia. Qed.
Lemma m_s0 : forall r t rc, r < t -> 5 * r + 0 < 5 * t + rc.       Proof. intros; lia. Qed.
Lemma m_s1 : forall r t rc, r < t -> 5 * r + 1 < 5 * t + rc.       Proof. intros; lia. Qed.
Lemma m_s3 : forall r t rc, r < t -> 5 * r + 3 < 5 * t + rc.       Proof. intros; lia. Qed.
Lemma m_s4 : forall r t rc, r < t -> 5 * r + 4 < 5 * t + rc.       Proof. intros; lia. Qed.

Fixpoint parse_gty_acc (toks : list Token) (a : Acc lt (List.length toks)) {struct a}
  : option (GoTy * { r : list Token | List.length r <= List.length toks }) :=
  match toks return Acc lt (List.length toks) ->
                    option (GoTy * { r : list Token | List.length r <= List.length toks }) with
  | nil => fun _ => None
  | tok :: rest0 => fun a =>
    match tok with
    | TStar =>
        match parse_gty_acc rest0 (Acc_inv a (tlt1 (List.length rest0))) with
        | Some (u, exist _ r Hr) => Some (GTPtr u, exist _ r (tle1 _ _ Hr))
        | None => None
        end
    | TChan =>
        match parse_gty_acc rest0 (Acc_inv a (tlt1 (List.length rest0))) with
        | Some (u, exist _ r Hr) => Some (GTChan u, exist _ r (tle1 _ _ Hr))
        | None => None
        end
    | TLB =>
        match rest0 as r0 return Acc lt (S (List.length r0)) ->
                                 option (GoTy * { r : list Token | List.length r <= S (List.length r0) }) with
        | TRB :: rest => fun a =>
            match parse_gty_acc rest (Acc_inv a (tlt2 (List.length rest))) with
            | Some (u, exist _ r Hr) => Some (GTSlice u, exist _ r (tle2 _ _ Hr))
            | None => None
            end
        | _ => fun _ => None
        end a
    | TMap =>
        match rest0 as r0' return Acc lt (S (List.length r0')) ->
                                  option (GoTy * { r : list Token | List.length r <= S (List.length r0') }) with
        | TLB :: r0 => fun a =>
            match parse_gty_acc r0 (Acc_inv a (tlt2 (List.length r0))) with
            | Some (k, exist _ rK HrK) =>
                match rK as rk return List.length rk <= List.length r0 ->
                                      option (GoTy * { r : list Token | List.length r <= S (S (List.length r0)) }) with
                | TRB :: r1 => fun HrK =>
                    match parse_gty_acc r1 (Acc_inv a (tlt_map _ _ HrK)) with
                    | Some (v, exist _ r2 Hr2) => Some (GTMap k v, exist _ r2 (tle_map _ _ _ Hr2 HrK))
                    | None => None
                    end
                | _ => fun _ => None
                end HrK
            | None => None
            end
        | _ => fun _ => None
        end a
    | TId i =>
        match classify (proj1_sig i) with
        | Some t => Some (t, exist _ rest0 (tle1 _ _ (le_n _)))
        | None => match bool_dec (nominal_type_ident (proj1_sig i)) true with
                  | left H => Some (GTNamed (mkTyName (proj1_sig i) H), exist _ rest0 (tle1 _ _ (le_n _)))
                  | right _ => None
                  end
        end
    | _ => None
    end
  end a.
Definition parse_gty (toks : list Token) : option (GoTy * list Token) :=
  match parse_gty_acc toks (lt_wf (List.length toks)) with
  | Some (t, exist _ r _) => Some (t, r)
  | None => None
  end.

(** certificate proof-irrelevance (the [lex_acc_pi] recipe) + the one-step unfold equations over
    [parse_gty] ITSELF — the reasoning principle that replaces any budget-indexed unfolding. *)
Lemma parse_gty_acc_pi : forall n toks, List.length toks < n ->
  forall a1 a2 : Acc lt (List.length toks), parse_gty_acc toks a1 = parse_gty_acc toks a2.
Proof.
  induction n as [| n IH]; intros toks Hn a1 a2; [ lia | ].
  destruct a1 as [h1]. destruct a2 as [h2].
  destruct toks as [| tok rest0]; [ reflexivity | ].
  cbn [parse_gty_acc Acc_inv].
  destruct tok; try reflexivity.
  - (* TStar *)
    erewrite (IH rest0); [ reflexivity | cbn in Hn |- *; lia ].
  - (* TLB *)
    destruct rest0 as [| tk rest]; [ reflexivity | ]. destruct tk; try reflexivity.
    cbn [Acc_inv].
    erewrite (IH rest); [ reflexivity | cbn in Hn |- *; lia ].
  - (* TChan *)
    erewrite (IH rest0); [ reflexivity | cbn in Hn |- *; lia ].
  - (* TMap *)
    destruct rest0 as [| tk r0]; [ reflexivity | ]. destruct tk; try reflexivity.
    cbn [Acc_inv].
    rewrite (IH r0 ltac:(cbn in Hn |- *; lia)
               (h1 (List.length r0) (tlt2 (List.length r0)))
               (h2 (List.length r0) (tlt2 (List.length r0)))).
    destruct (parse_gty_acc r0 (h2 (List.length r0) (tlt2 (List.length r0))))
      as [[k [rK HrK]]|]; [ | reflexivity ].
    destruct rK as [| tk1 r1]; [ reflexivity | ]. destruct tk1; try reflexivity.
    cbv beta.
    match goal with |- context [parse_gty_acc r1 ?P] =>
      tryif is_var P then fail else generalize P end.
    match goal with |- context [parse_gty_acc r1 ?P] =>
      tryif is_var P then fail else generalize P end.
    intros g2 g1.
    rewrite (IH r1 ltac:(cbn in Hn, HrK |- *; lia) g1 g2).
    reflexivity.
Qed.
Lemma parse_gty_unfold_pi : forall toks,
  parse_gty toks
  = match parse_gty_acc toks (Acc_intro (List.length toks) (fun y _ => lt_wf y)) with
    | Some (t, exist _ r _) => Some (t, r)
    | None => None
    end.
Proof.
  intro toks. unfold parse_gty.
  rewrite (parse_gty_acc_pi (S (List.length toks)) toks (Nat.lt_succ_diag_r _)
             (lt_wf (List.length toks)) (Acc_intro (List.length toks) (fun y _ => lt_wf y))).
  reflexivity.
Qed.

Lemma parse_gty_eq_star : forall rest,
  parse_gty (TStar :: rest) = match parse_gty rest with Some (u, r) => Some (GTPtr u, r) | None => None end.
Proof.
  intro rest. rewrite parse_gty_unfold_pi. cbn [parse_gty_acc Acc_inv]. unfold parse_gty.
  destruct (parse_gty_acc rest (lt_wf (List.length rest))) as [[u [r Hr]]|]; reflexivity.
Qed.
Lemma parse_gty_eq_chan : forall rest,
  parse_gty (TChan :: rest) = match parse_gty rest with Some (u, r) => Some (GTChan u, r) | None => None end.
Proof.
  intro rest. rewrite parse_gty_unfold_pi. cbn [parse_gty_acc Acc_inv]. unfold parse_gty.
  destruct (parse_gty_acc rest (lt_wf (List.length rest))) as [[u [r Hr]]|]; reflexivity.
Qed.
Lemma parse_gty_eq_slice : forall rest,
  parse_gty (TLB :: TRB :: rest) = match parse_gty rest with Some (u, r) => Some (GTSlice u, r) | None => None end.
Proof.
  intro rest. rewrite parse_gty_unfold_pi. cbn [parse_gty_acc Acc_inv]. unfold parse_gty.
  destruct (parse_gty_acc rest (lt_wf (List.length rest))) as [[u [r Hr]]|]; reflexivity.
Qed.
Lemma parse_gty_eq_map : forall r0,
  parse_gty (TMap :: TLB :: r0)
  = match parse_gty r0 with
    | Some (k, TRB :: r1) => match parse_gty r1 with Some (v, r2) => Some (GTMap k v, r2) | None => None end
    | _ => None
    end.
Proof.
  intro r0. rewrite parse_gty_unfold_pi. cbn [parse_gty_acc Acc_inv]. unfold parse_gty.
  destruct (parse_gty_acc r0 (lt_wf (List.length r0))) as [[k [rK HrK]]|]; [ | reflexivity ].
  destruct rK as [| tk1 r1]; [ reflexivity | ]. destruct tk1; try reflexivity.
  cbv beta.
  match goal with |- context [parse_gty_acc r1 ?P] =>
    tryif is_var P then fail else generalize P end.
  match goal with |- context [parse_gty_acc r1 ?P] =>
    tryif is_var P then fail else generalize P end.
  intros g2 g1.
  rewrite (parse_gty_acc_pi (S (List.length r1)) r1 (Nat.lt_succ_diag_r _) g1 g2).
  destruct (parse_gty_acc r1 g2) as [[v [r2 Hr2]]|]; reflexivity.
Qed.
Lemma parse_gty_eq_id : forall i rest,
  parse_gty (TId i :: rest)
  = match classify (proj1_sig i) with
    | Some t => Some (t, rest)
    | None => match bool_dec (nominal_type_ident (proj1_sig i)) true with
              | left H => Some (GTNamed (mkTyName (proj1_sig i) H), rest)
              | right _ => None
              end
    end.
Proof.
  intros i rest. rewrite parse_gty_unfold_pi. cbn [parse_gty_acc Acc_inv].
  destruct (classify (proj1_sig i)); [ reflexivity | ].
  destruct (bool_dec (nominal_type_ident (proj1_sig i)) true); reflexivity.
Qed.

(** ---- STRING-LEXER FAIL-CLOSED REGRESSION ---- a spelling NOT in the printer image (a malformed escape, or a
    raw byte [esc_byte] would have escaped) must be REJECTED at tokenization ([lex = None]), NOT lossily normalized
    into a [TStr] (a fail-open).  Representative case: an UNKNOWN escape "\q" makes [lex] (hence
    [parse_str]) return [None] (the bytes are built explicitly with [ch]: [ch 34] = the dquote, [ch 92] = the backslash). *)
Example lex_bad_escape : lex (String (ch 34) (String (ch 92) (String (ch 113) (String (ch 34) "")))) = None.
Proof. vm_compute; reflexivity. Qed.                              (* "\q"  — 'q' = 113, not an accepted escape *)
(* POSITIVE companion: a WELL-FORMED literal still tokenizes to its single [TStr] (the round-trip side; the
   fully-general statement is [gtokens_lex] at [EStr], proved below for EVERY [s]). *)
Example lex_str_pos : lex (print_string_lit "hi") = Some (TStr "hi" :: nil).
Proof. vm_compute; reflexivity. Qed.
Example lex_str_pos_esc : lex (print_string_lit (String (ch 34) (String (ch 92) (String (ch 10) "x"))))
                        = Some (TStr (String (ch 34) (String (ch 92) (String (ch 10) "x"))) :: nil).
Proof. vm_compute; reflexivity. Qed.

(** ---- THE GRAMMAR (EBNF, prose) ---- the language GoPrint lexes, parses, and prints.  The AST below,
    the printer [gprint], and the recursive-descent parser [parse] are three views of this grammar;
    [parse_print_roundtrip] proves printer and parser agree.  The intended AUTHORITY is a RELATIONAL
    canonical-grammar layer (CanonExpr et al., CLAUDE.md "Syntax authority") — once it lands, this prose
    EBNF and the executable parser are both derived views proved against it.  (Wirth-style:
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
               | hexlit                           -> EHex     hex integer literal [0x...] (lowercase 0-9a-f);
                                                              NON-NEGATIVE (a [HexZ]); disjoint from [int] by the
                                                              "0x" lead, which decimal [int] never produces
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
               | ident .                          -> GTNamed  nominal type
      ident    = idstart { idstart | digit } ,  idstart = "_" | "A".."Z" | "a".."z" .   -- a [go_ident]
      int      = [ "-" ] digit { digit } .       -- decimal; the lexer reads a leading "-"<digit> as one [TInt]
      hexlit   = "0" "x" hex { hex } .           -- lowercase hex int literal (>= 0); [hex] = digit | a..f (as in
                                                    Escape); the lexer's [0x] branch scans it to one [THex]

    NOT yet in the grammar: STRUCT / ARRAY composite literals ([N]T{..} / T{..}) and func-literals.  A
    NAMED conversion [T(x)] is the call [ECall (EId T) [x]] -- byte-identical, and the call/conversion
    distinction needs a type environment the parser does not have. *)


(** A bare prefix operator applied DIRECTLY to another is a LEXICAL hazard: [&][&] prints "&&" (maximal-
    munched to [TLand]), [&][^] prints "&^" ([TAndNot]) — a token MERGE on the LEFT of the seam (the seam
    is two-sided).  So a unary operand that could re-lex or re-parse wrongly is PARENTHESISED — [op(x)].
    (UNeg ALWAYS self-parenthesises as [-(x)], also to avoid the [-5] negative-literal lexing.)

    A LEAF-atom operand ([EId]/[EInt]/[EStr]/[EHex]) prints BARE — the minimal gofmt-canonical [^x]:
    (a) its first char (idstart / digit / '-' / dquote) can never merge with a prefix into a 2-char token
    ([gprint_head_clean] / [lex_unop_app]); (b) a leaf is fully consumed by [parse_atom], leaving nothing
    for the postfix loop to mis-capture.  A POSTFIX operand ([ESel]/[EIndex]/[ESlice]/[ECall]/[EAssert])
    must STILL be parenthesised: the grammar binds a prefix unary to an *Atom*, with the postfix chain
    folded OUTSIDE the unary — a bare [^a.b] would re-parse as [(^a).b], breaking the round-trip.  Type-led
    atoms ([EConv]/[ESliceLit]/[EMapLit]) are parenthesised too (sound to bare; the printer keeps the
    conservative wrap).  The BARE set is exactly the leaf atoms; everything else gets parens. *)

(** [unop_needs_paren e0] — does a PREFIX-UNARY operand [e0] need parentheses?  FALSE only for the four LEAF
    atoms ([EId]/[EInt]/[EStr]/[EHex], printed BARE — the minimal [^x]); TRUE for every other form.  This is a
    SEPARATE source of truth from [op_needs_paren] (the POSTFIX-operand rule): a postfix node ([ESel]/…) is a
    bare-OK postfix operand but a paren-REQUIRED unary operand (the grammar binds unary to an Atom, so bare
    [^a.b] re-associates — see the note above).  EXHAUSTIVE on purpose (no [_] catch-all): the only UNSAFE
    direction is bare-by-default, so a new constructor makes this non-exhaustive and FAILS THE BUILD until its
    unary-operand precedence is declared — fail-loud, never a silent wrong default.  Inspects only the head
    constructor, so it is defined before [gprint]. *)
Definition unop_needs_paren (e0 : GExpr) : bool :=
  match e0 with
  | EId _ | EInt _ | EStr _ | EHex _ => false
  | EUn _ _ | EBn _ _ _ | ESel _ _ | EIndex _ _ | ESlice _ _ _ | ECall _ _ | EAssert _ _ | EConv _ _ | ESliceLit _ _ | EMapLit _ _ _ => true
  end.

(** [unop_paren o e0] — does the printed unary [EUn o e0] wrap its operand?  [UNeg] ALWAYS does ([-(x)], to
    dodge the [-5] literal); the other four wrap iff [unop_needs_paren e0].  The SINGLE rule shared by
    [gprint]/[gtokens]/[esize] for [EUn] (so they stay in lock-step — the round-trip relates them). *)
Definition unop_paren (o : UnaryOp) (e0 : GExpr) : bool :=
  match o with UNeg => true | _ => unop_needs_paren e0 end.

(** [op_needs_paren e0] — does a POSTFIX operand [e0] need parentheses?  TRUE for the LOOSE nodes
    ([EUn]/[EBn], which bind looser than a postfix operator); FALSE for every atom / postfix form.  The
    SINGLE source of truth for postfix-operand parenthesisation ([gprint]/[gparen]/[gtokens]/[gtparen]).
    EXHAUSTIVE on purpose — NO [_] catch-all: the only UNSAFE direction is bare-by-default, so a new
    constructor makes this non-exhaustive and FAILS THE BUILD until its precedence is declared here.
    Inspects only the head constructor, so it is defined before [gprint]. *)
Definition op_needs_paren (e0 : GExpr) : bool :=
  match e0 with
  | EUn _ _ | EBn _ _ _ => true
  | EId _ | EInt _ | EStr _ | EHex _ | ESel _ _ | EIndex _ _ | ESlice _ _ _ | ECall _ _ | EAssert _ _ | EConv _ _ | ESliceLit _ _ | EMapLit _ _ _ => false
  end.

(** ---- THE PRINTER ---- precedence-correct (reuses [binop_prec]/[binop_text]/[unop_text]); a binop wraps
    in parens exactly when its precedence [< ctx]. *)
Fixpoint gprint (ctx : nat) (e : GExpr) {struct e} : string :=
  match e with
  | EId i  => proj1_sig i
  | EInt z => print_Z z
  | EStr s => print_string_lit s   (* STRING literal: the verified escaping printer (its round-trip is [esc_string_roundtrip_opt]) *)
  | EHex zc => print_hex (Z.to_N (proj1_sig zc))   (* HEX literal: the verified [0x]-hex printer over its [N] domain ([HexZ]'s non-negativity makes [Z.to_N] lossless; round-trip [print_parse_hex]) *)
  | EUn o e =>
      (* [unop_text o] then the operand, wrapped iff [unop_paren o e]; a leaf operand prints BARE.
         See [unop_needs_paren]/[unop_paren]. *)
      (unop_text o ++ (if unop_paren o e then ("(" ++ gprint 0 e ++ ")")%string else gprint 0 e))%string
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
         (like [UNeg], unconditionally) — so it never needs the [op_needs_paren] dance. *)
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
(** [gprint]'s EUn case as a rewrite: [op] then the operand, wrapped iff [unop_paren o e0]. *)
Lemma gprint_EUn : forall ctx o e0,
  gprint ctx (EUn o e0) = (unop_text o ++ (if unop_paren o e0 then ("(" ++ gprint 0 e0 ++ ")")%string else gprint 0 e0))%string.
Proof. reflexivity. Qed.
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
    ([parse_atom]); an infix one is a binary op ([infix_op] in [parse_climb]).  [TMinus]+[TLP] is the
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


(** ================================================================================================
    The FUEL-FREE expression parser: the same ELEVEN mutual functions, Acc-structural on the RANKED
    measure [5 * token-length + rank] instead of a fuel budget.  [{struct a}] requires every
    recursive call to carry a strictly smaller certificate: the same-length grammar dispatches
    (expr -> primary -> atom, list-head -> expr) descend by RANK; every other call consumes at
    least one token and descends by LENGTH.  Results carry their suffix bound ([<] for the consuming phases, [<=] for the possibly-empty
    postfix/climb folds) — the bound of each call is the Acc certificate of the next. *)
(** bound-carrying [parse_gty]: the public face throws the suffix bound away; the conversion and
    assertion arms below need it for their NEXT recursive call. *)
Definition parse_gty_b (toks : list Token) := parse_gty_acc toks (lt_wf (List.length toks)).

Fixpoint parse_expr_acc (k : nat) (toks : list Token) (a : Acc lt (5 * List.length toks + 3)) {struct a}
  : option (GExpr * { r : list Token | List.length r < List.length toks }) :=
  match parse_primary_acc toks (Acc_inv a (m_r2 (List.length toks))) with
  | Some (l, exist _ r Hr) =>
      match parse_climb_acc k l r (Acc_inv a (m_s0 _ _ _ Hr)) with
      | Some (e, exist _ r2 Hr2) => Some (e, exist _ r2 (pacc _ _ _ Hr2 Hr))
      | None => None
      end
  | None => None
  end
with parse_primary_acc (toks : list Token) (a : Acc lt (5 * List.length toks + 2)) {struct a}
  : option (GExpr * { r : list Token | List.length r < List.length toks }) :=
  match parse_atom_acc toks (Acc_inv a (m_r1 (List.length toks))) with
  | Some (e, exist _ r Hr) =>
      match parse_postfix_acc e r (Acc_inv a (m_s0 _ _ _ Hr)) with
      | Some (e2, exist _ r2 Hr2) => Some (e2, exist _ r2 (pacc _ _ _ Hr2 Hr))
      | None => None
      end
  | None => None
  end
with parse_atom_acc (toks : list Token) (a : Acc lt (5 * List.length toks + 1)) {struct a}
  : option (GExpr * { r : list Token | List.length r < List.length toks }) :=
  match toks return Acc lt (5 * List.length toks + 1) ->
                    option (GExpr * { r : list Token | List.length r < List.length toks }) with
  | TLP :: rest => fun a =>
      match parse_expr_acc 0 rest (Acc_inv a (m_s3 _ _ _ (tlt1 (List.length rest)))) with
      | Some (e, exist _ r0 Hr0) =>
          match r0 as rr return List.length rr < List.length rest ->
                                option (GExpr * { r : list Token | List.length r < S (List.length rest) }) with
          | TRP :: r2 => fun Hr0 => Some (e, exist _ r2 (ppop _ _ (Nat.lt_le_incl _ _ Hr0)))
          | _ => fun _ => None
          end Hr0
      | None => None
      end
  | TBang :: rest => fun a =>
      match parse_atom_acc rest (Acc_inv a (m_s1 _ _ _ (tlt1 (List.length rest)))) with
      | Some (e, exist _ r Hr) => Some (EUn UNot e, exist _ r (Nat.lt_lt_succ_r _ _ Hr))
      | None => None
      end
  | TCaret :: rest => fun a =>
      match parse_atom_acc rest (Acc_inv a (m_s1 _ _ _ (tlt1 (List.length rest)))) with
      | Some (e, exist _ r Hr) => Some (EUn UXor e, exist _ r (Nat.lt_lt_succ_r _ _ Hr))
      | None => None
      end
  | TStar :: rest => fun a =>
      match parse_atom_acc rest (Acc_inv a (m_s1 _ _ _ (tlt1 (List.length rest)))) with
      | Some (e, exist _ r Hr) => Some (EUn UDeref e, exist _ r (Nat.lt_lt_succ_r _ _ Hr))
      | None => None
      end
  | TAmp :: rest => fun a =>
      match parse_atom_acc rest (Acc_inv a (m_s1 _ _ _ (tlt1 (List.length rest)))) with
      | Some (e, exist _ r Hr) => Some (EUn UAddr e, exist _ r (Nat.lt_lt_succ_r _ _ Hr))
      | None => None
      end
  | TMinus :: TLP :: rest => fun a =>
      match parse_expr_acc 0 rest (Acc_inv a (m_s3 _ _ _ (tlt2 (List.length rest)))) with
      | Some (e, exist _ r0 Hr0) =>
          match r0 as rr return List.length rr < List.length rest ->
                                option (GExpr * { r : list Token | List.length r < S (S (List.length rest)) }) with
          | TRP :: r2 => fun Hr0 => Some (EUn UNeg e, exist _ r2 (tlt_map _ _ (Nat.lt_le_incl _ _ Hr0)))
          | _ => fun _ => None
          end Hr0
      | None => None
      end
  (* type-form CONVERSIONS and composite LITERALS — the type via the bound-carrying [parse_gty_b],
     then '(' -> conversion, '{' -> literal — the same case split as [parse_atom_eq] states. *)
  | TLB :: TRB :: rest0 => fun a =>
      match parse_gty_b (TLB :: TRB :: rest0) with
      | Some (GTSlice u, exist _ r Hr) =>
          match r as rr return List.length rr <= S (S (List.length rest0)) ->
                               option (GExpr * { r' : list Token | List.length r' < S (S (List.length rest0)) }) with
          | TLP :: r1 => fun Hr =>
              match parse_expr_acc 0 r1 (Acc_inv a (m_s3 _ _ _ Hr)) with
              | Some (e, exist _ r2' Hr2') =>
                  match r2' as rr2 return List.length rr2 < List.length r1 ->
                                          option (GExpr * { r' : list Token | List.length r' < S (S (List.length rest0)) }) with
                  | TRP :: r2 => fun Hr2' =>
                      Some (EConv (CTSlice u) e, exist _ r2 (pconv _ _ _ _ (Nat.lt_le_incl _ _ Hr2') Hr (le_n _)))
                  | _ => fun _ => None
                  end Hr2'
              | None => None
              end
          | TLC :: r1 => fun Hr =>
              match parse_elems_acc r1 (Acc_inv a (m_s4 _ _ _ Hr)) with
              | Some (es, exist _ r2 Hr2) =>
                  Some (ESliceLit u es, exist _ r2 (pacc _ _ _ (Nat.lt_le_incl _ _ Hr2) Hr))
              | None => None
              end
          | _ => fun _ => None
          end Hr
      | _ => None
      end
  | TChan :: rest0 => fun a =>
      match parse_gty_b (TChan :: rest0) with
      | Some (GTChan u, exist _ r Hr) =>
          match r as rr return List.length rr <= S (List.length rest0) ->
                               option (GExpr * { r' : list Token | List.length r' < S (List.length rest0) }) with
          | TLP :: r1 => fun Hr =>
              match parse_expr_acc 0 r1 (Acc_inv a (m_s3 _ _ _ Hr)) with
              | Some (e, exist _ r2' Hr2') =>
                  match r2' as rr2 return List.length rr2 < List.length r1 ->
                                          option (GExpr * { r' : list Token | List.length r' < S (List.length rest0) }) with
                  | TRP :: r2 => fun Hr2' =>
                      Some (EConv (CTChan u) e, exist _ r2 (pconv _ _ _ _ (Nat.lt_le_incl _ _ Hr2') Hr (le_n _)))
                  | _ => fun _ => None
                  end Hr2'
              | None => None
              end
          | _ => fun _ => None
          end Hr
      | _ => None
      end
  | TMap :: rest0 => fun a =>
      match parse_gty_b (TMap :: rest0) with
      | Some (GTMap kt vt, exist _ r Hr) =>
          match r as rr return List.length rr <= S (List.length rest0) ->
                               option (GExpr * { r' : list Token | List.length r' < S (List.length rest0) }) with
          | TLP :: r1 => fun Hr =>
              match parse_expr_acc 0 r1 (Acc_inv a (m_s3 _ _ _ Hr)) with
              | Some (e, exist _ r2' Hr2') =>
                  match r2' as rr2 return List.length rr2 < List.length r1 ->
                                          option (GExpr * { r' : list Token | List.length r' < S (List.length rest0) }) with
                  | TRP :: r2 => fun Hr2' =>
                      Some (EConv (CTMap kt vt) e, exist _ r2 (pconv _ _ _ _ (Nat.lt_le_incl _ _ Hr2') Hr (le_n _)))
                  | _ => fun _ => None
                  end Hr2'
              | None => None
              end
          | TLC :: r1 => fun Hr =>
              match parse_map_elems_acc r1 (Acc_inv a (m_s4 _ _ _ Hr)) with
              | Some (kvs, exist _ r2 Hr2) =>
                  Some (EMapLit kt vt kvs, exist _ r2 (pacc _ _ _ (Nat.lt_le_incl _ _ Hr2) Hr))
              | None => None
              end
          | _ => fun _ => None
          end Hr
      | _ => None
      end
  | TId i :: rest => fun _ => Some (EId i, exist _ rest (tlt1 (List.length rest)))
  | TInt z :: rest => fun _ => Some (EInt z, exist _ rest (tlt1 (List.length rest)))
  | TStr s :: rest => fun _ => Some (EStr s, exist _ rest (tlt1 (List.length rest)))
  | THex zc :: rest => fun _ => Some (EHex zc, exist _ rest (tlt1 (List.length rest)))
  | _ => fun _ => None
  end a
with parse_postfix_acc (b : GExpr) (toks : list Token) (a : Acc lt (5 * List.length toks + 0)) {struct a}
  : option (GExpr * { r : list Token | List.length r <= List.length toks }) :=
  match toks return Acc lt (5 * List.length toks + 0) ->
                    option (GExpr * { r : list Token | List.length r <= List.length toks }) with
  | TDot :: TLP :: rest => fun a =>   (* type assertion [.(T)] *)
      match parse_gty_b rest with
      | Some (T, exist _ r0 Hr0) =>
          match r0 as rr return List.length rr <= List.length rest ->
                                option (GExpr * { r : list Token | List.length r <= S (S (List.length rest)) }) with
          | TRP :: r1 => fun Hr0 =>
              match parse_postfix_acc (EAssert b T) r1 (Acc_inv a (m_s0 _ _ _ (tlt_map _ _ Hr0))) with
              | Some (e2, exist _ r2 Hr2) => Some (e2, exist _ r2 (tle_map _ _ _ Hr2 Hr0))
              | None => None
              end
          | _ => fun _ => None
          end Hr0
      | None => None
      end
  | TDot :: TId field :: rest => fun a =>
      match parse_postfix_acc (ESel b field) rest (Acc_inv a (m_s0 _ _ _ (tlt2 (List.length rest)))) with
      | Some (e2, exist _ r2 Hr2) => Some (e2, exist _ r2 (tle2 _ _ Hr2))
      | None => None
      end
  | TLB :: rest => fun a =>
      match parse_expr_acc 0 rest (Acc_inv a (m_s3 _ _ _ (tlt1 (List.length rest)))) with
      | Some (lo, exist _ r0 Hr0) =>
          match r0 as rr return List.length rr < List.length rest ->
                                option (GExpr * { r : list Token | List.length r <= S (List.length rest) }) with
          | TColon :: r1 => fun Hr0 =>
              match parse_expr_acc 0 r1 (Acc_inv a (m_s3 _ _ _ (ppop _ _ (Nat.lt_le_incl _ _ Hr0)))) with
              | Some (hi, exist _ r2' Hr2') =>
                  match r2' as rr2 return List.length rr2 < List.length r1 ->
                                          option (GExpr * { r : list Token | List.length r <= S (List.length rest) }) with
                  | TRB :: r2 => fun Hr2' =>
                      match parse_postfix_acc (ESlice b lo hi) r2
                              (Acc_inv a (m_s0 _ _ _ (ppop2 _ _ _ (Nat.lt_le_incl _ _ Hr2') (Nat.lt_le_incl _ _ Hr0)))) with
                      | Some (e3, exist _ r3 Hr3) =>
                          Some (e3, exist _ r3 (pfin _ _ _ Hr3 (ppop2 _ _ _ (Nat.lt_le_incl _ _ Hr2') (Nat.lt_le_incl _ _ Hr0))))
                      | None => None
                      end
                  | _ => fun _ => None
                  end Hr2'
              | None => None
              end
          | TRB :: r1 => fun Hr0 =>
              match parse_postfix_acc (EIndex b lo) r1 (Acc_inv a (m_s0 _ _ _ (ppop _ _ (Nat.lt_le_incl _ _ Hr0)))) with
              | Some (e2, exist _ r2 Hr2) => Some (e2, exist _ r2 (pfin _ _ _ Hr2 (ppop _ _ (Nat.lt_le_incl _ _ Hr0))))
              | None => None
              end
          | _ => fun _ => None
          end Hr0
      | None => None
      end
  | TLP :: rest => fun a =>
      match parse_args_acc rest (Acc_inv a (m_s4 _ _ _ (tlt1 (List.length rest)))) with
      | Some (args, exist _ r Hr) =>
          match parse_postfix_acc (ECall b args) r (Acc_inv a (m_s0 _ _ _ (Nat.lt_lt_succ_r _ _ Hr))) with
          | Some (e2, exist _ r2 Hr2) => Some (e2, exist _ r2 (pfin _ _ _ Hr2 (Nat.lt_lt_succ_r _ _ Hr)))
          | None => None
          end
      | None => None
      end
  | t => fun _ => Some (b, exist _ t (le_n (List.length t)))
  end a
with parse_args_acc (toks : list Token) (a : Acc lt (5 * List.length toks + 4)) {struct a}
  : option (list GExpr * { r : list Token | List.length r < List.length toks }) :=
  match toks return Acc lt (5 * List.length toks + 4) ->
                    option (list GExpr * { r : list Token | List.length r < List.length toks }) with
  | TRP :: r => fun _ => Some (nil, exist _ r (tlt1 (List.length r)))
  | td => fun a =>
      match parse_expr_acc 0 td (Acc_inv a (m_r3 (List.length td))) with
      | Some (a0, exist _ r0 Hr0) =>
          match parse_args_tl_acc r0 (Acc_inv a (m_s0 _ _ _ Hr0)) with
          | Some (args, exist _ r1 Hr1) => Some (a0 :: args, exist _ r1 (Nat.lt_trans _ _ _ Hr1 Hr0))
          | None => None
          end
      | None => None
      end
  end a
with parse_args_tl_acc (toks : list Token) (a : Acc lt (5 * List.length toks + 0)) {struct a}
  : option (list GExpr * { r : list Token | List.length r < List.length toks }) :=
  match toks return Acc lt (5 * List.length toks + 0) ->
                    option (list GExpr * { r : list Token | List.length r < List.length toks }) with
  | TRP :: r => fun _ => Some (nil, exist _ r (tlt1 (List.length r)))
  | TComma :: r => fun a =>
      match parse_expr_acc 0 r (Acc_inv a (m_s3 _ _ _ (tlt1 (List.length r)))) with
      | Some (a0, exist _ r0 Hr0) =>
          match parse_args_tl_acc r0 (Acc_inv a (m_s0 _ _ _ (Nat.lt_lt_succ_r _ _ Hr0))) with
          | Some (args, exist _ r1 Hr1) =>
              Some (a0 :: args, exist _ r1 (Nat.lt_lt_succ_r _ _ (Nat.lt_trans _ _ _ Hr1 Hr0)))
          | None => None
          end
      | None => None
      end
  | _ => fun _ => None
  end a
with parse_elems_acc (toks : list Token) (a : Acc lt (5 * List.length toks + 4)) {struct a}
  : option (list GExpr * { r : list Token | List.length r < List.length toks }) :=
  match toks return Acc lt (5 * List.length toks + 4) ->
                    option (list GExpr * { r : list Token | List.length r < List.length toks }) with
  | TRC :: r => fun _ => Some (nil, exist _ r (tlt1 (List.length r)))
  | td => fun a =>
      match parse_expr_acc 0 td (Acc_inv a (m_r3 (List.length td))) with
      | Some (a0, exist _ r0 Hr0) =>
          match parse_elems_tl_acc r0 (Acc_inv a (m_s0 _ _ _ Hr0)) with
          | Some (es, exist _ r1 Hr1) => Some (a0 :: es, exist _ r1 (Nat.lt_trans _ _ _ Hr1 Hr0))
          | None => None
          end
      | None => None
      end
  end a
with parse_elems_tl_acc (toks : list Token) (a : Acc lt (5 * List.length toks + 0)) {struct a}
  : option (list GExpr * { r : list Token | List.length r < List.length toks }) :=
  match toks return Acc lt (5 * List.length toks + 0) ->
                    option (list GExpr * { r : list Token | List.length r < List.length toks }) with
  | TRC :: r => fun _ => Some (nil, exist _ r (tlt1 (List.length r)))
  | TComma :: r => fun a =>
      match parse_expr_acc 0 r (Acc_inv a (m_s3 _ _ _ (tlt1 (List.length r)))) with
      | Some (a0, exist _ r0 Hr0) =>
          match parse_elems_tl_acc r0 (Acc_inv a (m_s0 _ _ _ (Nat.lt_lt_succ_r _ _ Hr0))) with
          | Some (es, exist _ r1 Hr1) =>
              Some (a0 :: es, exist _ r1 (Nat.lt_lt_succ_r _ _ (Nat.lt_trans _ _ _ Hr1 Hr0)))
          | None => None
          end
      | None => None
      end
  | _ => fun _ => None
  end a
with parse_map_elems_acc (toks : list Token) (a : Acc lt (5 * List.length toks + 4)) {struct a}
  : option (list (GExpr * GExpr) * { r : list Token | List.length r < List.length toks }) :=
  match toks return Acc lt (5 * List.length toks + 4) ->
                    option (list (GExpr * GExpr) * { r : list Token | List.length r < List.length toks }) with
  | TRC :: r => fun _ => Some (nil, exist _ r (tlt1 (List.length r)))
  | td => fun a =>
      match parse_expr_acc 0 td (Acc_inv a (m_r3 (List.length td))) with
      | Some (ke, exist _ rK HrK) =>
          match rK as rk return List.length rk < List.length td ->
                                option (list (GExpr * GExpr) * { r : list Token | List.length r < List.length td }) with
          | TColon :: r0 => fun HrK =>
              match parse_expr_acc 0 r0 (Acc_inv a (m_s3 _ _ _ (pskip _ _ HrK))) with
              | Some (ve, exist _ rV HrV) =>
                  match parse_map_elems_tl_acc rV (Acc_inv a (m_s0 _ _ _ (Nat.lt_trans _ _ _ HrV (pskip _ _ HrK)))) with
                  | Some (kvs, exist _ r2 Hr2) =>
                      Some ((ke, ve) :: kvs, exist _ r2
                              (Nat.lt_trans _ _ _ Hr2 (Nat.lt_trans _ _ _ HrV (pskip _ _ HrK))))
                  | None => None
                  end
              | None => None
              end
          | _ => fun _ => None
          end HrK
      | None => None
      end
  end a
with parse_map_elems_tl_acc (toks : list Token) (a : Acc lt (5 * List.length toks + 0)) {struct a}
  : option (list (GExpr * GExpr) * { r : list Token | List.length r < List.length toks }) :=
  match toks return Acc lt (5 * List.length toks + 0) ->
                    option (list (GExpr * GExpr) * { r : list Token | List.length r < List.length toks }) with
  | TRC :: r => fun _ => Some (nil, exist _ r (tlt1 (List.length r)))
  | TComma :: r => fun a =>
      match parse_expr_acc 0 r (Acc_inv a (m_s3 _ _ _ (tlt1 (List.length r)))) with
      | Some (ke, exist _ rK HrK) =>
          match rK as rk return List.length rk < List.length r ->
                                option (list (GExpr * GExpr) * { r' : list Token | List.length r' < S (List.length r) }) with
          | TColon :: r0 => fun HrK =>
              match parse_expr_acc 0 r0 (Acc_inv a (m_s3 _ _ _ (Nat.lt_lt_succ_r _ _ (pskip _ _ HrK)))) with
              | Some (ve, exist _ rV HrV) =>
                  match parse_map_elems_tl_acc rV
                          (Acc_inv a (m_s0 _ _ _ (Nat.lt_lt_succ_r _ _ (Nat.lt_trans _ _ _ HrV (pskip _ _ HrK))))) with
                  | Some (kvs, exist _ r2 Hr2) =>
                      Some ((ke, ve) :: kvs, exist _ r2
                              (Nat.lt_lt_succ_r _ _ (Nat.lt_trans _ _ _ Hr2 (Nat.lt_trans _ _ _ HrV (pskip _ _ HrK)))))
                  | None => None
                  end
              | None => None
              end
          | _ => fun _ => None
          end HrK
      | None => None
      end
  | _ => fun _ => None
  end a
with parse_climb_acc (k : nat) (l : GExpr) (toks : list Token) (a : Acc lt (5 * List.length toks + 0)) {struct a}
  : option (GExpr * { r : list Token | List.length r <= List.length toks }) :=
  match toks return Acc lt (5 * List.length toks + 0) ->
                    option (GExpr * { r : list Token | List.length r <= List.length toks }) with
  | t :: rest => fun a =>
      match infix_op t with
      | Some o =>
          if Nat.leb k (binop_prec o)
          then match parse_expr_acc (S (binop_prec o)) rest (Acc_inv a (m_s3 _ _ _ (tlt1 (List.length rest)))) with
               | Some (rgt, exist _ r2 Hr2) =>
                   match parse_climb_acc k (EBn o l rgt) r2 (Acc_inv a (m_s0 _ _ _ (Nat.lt_lt_succ_r _ _ Hr2))) with
                   | Some (e3, exist _ r3 Hr3) =>
                       Some (e3, exist _ r3 (pfin _ _ _ Hr3 (Nat.lt_lt_succ_r _ _ Hr2)))
                   | None => None
                   end
               | None => None
               end
          else Some (l, exist _ (t :: rest) (le_n _))
      | None => Some (l, exist _ (t :: rest) (le_n _))
      end
  | nil => fun _ => Some (l, exist _ nil (le_n 0))
  end a.

(** certificate proof-irrelevance for the whole mutual block (the [lex_acc_pi] recipe): one strong
    induction on the ranked measure, one conjunct per function.  Each call site generalizes BOTH
    sides' elaborated certificates before rewriting with the inductive hypothesis. *)
Local Ltac pi_rw_e IHe :=
  match goal with |- context [parse_expr_acc ?k ?t ?P] => tryif is_var P then fail else generalize P end;
  match goal with |- context [parse_expr_acc ?k ?t ?P] => tryif is_var P then fail else generalize P end;
  let g2 := fresh "g" in let g1 := fresh "g" in intros g2 g1;
  match goal with |- context [parse_expr_acc ?k ?t g1] => rewrite (IHe k t ltac:(cbn in *; lia) g1 g2) end.
Local Ltac pi_rw_p IHp :=
  match goal with |- context [parse_primary_acc ?t ?P] => tryif is_var P then fail else generalize P end;
  match goal with |- context [parse_primary_acc ?t ?P] => tryif is_var P then fail else generalize P end;
  let g2 := fresh "g" in let g1 := fresh "g" in intros g2 g1;
  match goal with |- context [parse_primary_acc ?t g1] => rewrite (IHp t ltac:(cbn in *; lia) g1 g2) end.
Local Ltac pi_rw_a IHa :=
  match goal with |- context [parse_atom_acc ?t ?P] => tryif is_var P then fail else generalize P end;
  match goal with |- context [parse_atom_acc ?t ?P] => tryif is_var P then fail else generalize P end;
  let g2 := fresh "g" in let g1 := fresh "g" in intros g2 g1;
  match goal with |- context [parse_atom_acc ?t g1] => rewrite (IHa t ltac:(cbn in *; lia) g1 g2) end.
Local Ltac pi_rw_pf IHpf :=
  match goal with |- context [parse_postfix_acc ?b ?t ?P] => tryif is_var P then fail else generalize P end;
  match goal with |- context [parse_postfix_acc ?b ?t ?P] => tryif is_var P then fail else generalize P end;
  let g2 := fresh "g" in let g1 := fresh "g" in intros g2 g1;
  match goal with |- context [parse_postfix_acc ?b ?t g1] => rewrite (IHpf b t ltac:(cbn in *; lia) g1 g2) end.
Local Ltac pi_rw_ar IHar :=
  match goal with |- context [parse_args_acc ?t ?P] => tryif is_var P then fail else generalize P end;
  match goal with |- context [parse_args_acc ?t ?P] => tryif is_var P then fail else generalize P end;
  let g2 := fresh "g" in let g1 := fresh "g" in intros g2 g1;
  match goal with |- context [parse_args_acc ?t g1] => rewrite (IHar t ltac:(cbn in *; lia) g1 g2) end.
Local Ltac pi_rw_at IHat :=
  match goal with |- context [parse_args_tl_acc ?t ?P] => tryif is_var P then fail else generalize P end;
  match goal with |- context [parse_args_tl_acc ?t ?P] => tryif is_var P then fail else generalize P end;
  let g2 := fresh "g" in let g1 := fresh "g" in intros g2 g1;
  match goal with |- context [parse_args_tl_acc ?t g1] => rewrite (IHat t ltac:(cbn in *; lia) g1 g2) end.
Local Ltac pi_rw_el IHel :=
  match goal with |- context [parse_elems_acc ?t ?P] => tryif is_var P then fail else generalize P end;
  match goal with |- context [parse_elems_acc ?t ?P] => tryif is_var P then fail else generalize P end;
  let g2 := fresh "g" in let g1 := fresh "g" in intros g2 g1;
  match goal with |- context [parse_elems_acc ?t g1] => rewrite (IHel t ltac:(cbn in *; lia) g1 g2) end.
Local Ltac pi_rw_et IHet :=
  match goal with |- context [parse_elems_tl_acc ?t ?P] => tryif is_var P then fail else generalize P end;
  match goal with |- context [parse_elems_tl_acc ?t ?P] => tryif is_var P then fail else generalize P end;
  let g2 := fresh "g" in let g1 := fresh "g" in intros g2 g1;
  match goal with |- context [parse_elems_tl_acc ?t g1] => rewrite (IHet t ltac:(cbn in *; lia) g1 g2) end.
Local Ltac pi_rw_me IHme :=
  match goal with |- context [parse_map_elems_acc ?t ?P] => tryif is_var P then fail else generalize P end;
  match goal with |- context [parse_map_elems_acc ?t ?P] => tryif is_var P then fail else generalize P end;
  let g2 := fresh "g" in let g1 := fresh "g" in intros g2 g1;
  match goal with |- context [parse_map_elems_acc ?t g1] => rewrite (IHme t ltac:(cbn in *; lia) g1 g2) end.
Local Ltac pi_rw_mt IHmt :=
  match goal with |- context [parse_map_elems_tl_acc ?t ?P] => tryif is_var P then fail else generalize P end;
  match goal with |- context [parse_map_elems_tl_acc ?t ?P] => tryif is_var P then fail else generalize P end;
  let g2 := fresh "g" in let g1 := fresh "g" in intros g2 g1;
  match goal with |- context [parse_map_elems_tl_acc ?t g1] => rewrite (IHmt t ltac:(cbn in *; lia) g1 g2) end.
Local Ltac pi_rw_cl IHcl :=
  match goal with |- context [parse_climb_acc ?k ?l ?t ?P] => tryif is_var P then fail else generalize P end;
  match goal with |- context [parse_climb_acc ?k ?l ?t ?P] => tryif is_var P then fail else generalize P end;
  let g2 := fresh "g" in let g1 := fresh "g" in intros g2 g1;
  match goal with |- context [parse_climb_acc ?k ?l ?t g1] => rewrite (IHcl k l t ltac:(cbn in *; lia) g1 g2) end.
Lemma parse_acc_pi_all : forall n,
  (forall k toks, 5 * List.length toks + 3 < n ->
     forall a1 a2 : Acc lt (5 * List.length toks + 3), parse_expr_acc k toks a1 = parse_expr_acc k toks a2)
  /\ (forall toks, 5 * List.length toks + 2 < n ->
     forall a1 a2 : Acc lt (5 * List.length toks + 2), parse_primary_acc toks a1 = parse_primary_acc toks a2)
  /\ (forall toks, 5 * List.length toks + 1 < n ->
     forall a1 a2 : Acc lt (5 * List.length toks + 1), parse_atom_acc toks a1 = parse_atom_acc toks a2)
  /\ (forall b toks, 5 * List.length toks + 0 < n ->
     forall a1 a2 : Acc lt (5 * List.length toks + 0), parse_postfix_acc b toks a1 = parse_postfix_acc b toks a2)
  /\ (forall toks, 5 * List.length toks + 4 < n ->
     forall a1 a2 : Acc lt (5 * List.length toks + 4), parse_args_acc toks a1 = parse_args_acc toks a2)
  /\ (forall toks, 5 * List.length toks + 0 < n ->
     forall a1 a2 : Acc lt (5 * List.length toks + 0), parse_args_tl_acc toks a1 = parse_args_tl_acc toks a2)
  /\ (forall toks, 5 * List.length toks + 4 < n ->
     forall a1 a2 : Acc lt (5 * List.length toks + 4), parse_elems_acc toks a1 = parse_elems_acc toks a2)
  /\ (forall toks, 5 * List.length toks + 0 < n ->
     forall a1 a2 : Acc lt (5 * List.length toks + 0), parse_elems_tl_acc toks a1 = parse_elems_tl_acc toks a2)
  /\ (forall toks, 5 * List.length toks + 4 < n ->
     forall a1 a2 : Acc lt (5 * List.length toks + 4), parse_map_elems_acc toks a1 = parse_map_elems_acc toks a2)
  /\ (forall toks, 5 * List.length toks + 0 < n ->
     forall a1 a2 : Acc lt (5 * List.length toks + 0), parse_map_elems_tl_acc toks a1 = parse_map_elems_tl_acc toks a2)
  /\ (forall k l toks, 5 * List.length toks + 0 < n ->
     forall a1 a2 : Acc lt (5 * List.length toks + 0), parse_climb_acc k l toks a1 = parse_climb_acc k l toks a2).
Proof.
  induction n as [| n IH]; [ repeat apply conj; intros; lia | ].
  destruct IH as (IHe & IHp & IHa & IHpf & IHar & IHat & IHel & IHet & IHme & IHmt & IHcl).
  repeat apply conj.
  - (* expr *)
    intros k toks Hn [h1] [h2]. cbn [parse_expr_acc Acc_inv].
    pi_rw_p IHp.
    match goal with |- context [parse_primary_acc ?t ?P] =>
      destruct (parse_primary_acc t P) as [[l [r Hr]]|] end; [ | reflexivity ].
    pi_rw_cl IHcl.
    match goal with |- context [parse_climb_acc ?k2 ?l2 ?t ?P] =>
      destruct (parse_climb_acc k2 l2 t P) as [[e [r2 Hr2]]|] end; reflexivity.
  - (* primary *)
    intros toks Hn [h1] [h2]. cbn [parse_primary_acc Acc_inv].
    pi_rw_a IHa.
    match goal with |- context [parse_atom_acc ?t ?P] =>
      destruct (parse_atom_acc t P) as [[e [r Hr]]|] end; [ | reflexivity ].
    pi_rw_pf IHpf.
    match goal with |- context [parse_postfix_acc ?b ?t ?P] =>
      destruct (parse_postfix_acc b t P) as [[e2 [r2 Hr2]]|] end; reflexivity.
  - (* atom *)
    intros toks Hn [h1] [h2].
    destruct toks as [| tok rest]; [ reflexivity | ].
    cbn [parse_atom_acc Acc_inv].
    destruct tok; try reflexivity.
    + (* TMinus *)
      destruct rest as [| t2 rest2]; [ reflexivity | ]. destruct t2; try reflexivity.
      cbn [Acc_inv].
      pi_rw_e IHe.
      match goal with |- context [parse_expr_acc ?k ?t ?P] =>
        destruct (parse_expr_acc k t P) as [[e [r0 Hr0]]|] end; [ | reflexivity ].
      destruct r0 as [| t3 r2]; [ reflexivity | ]. destruct t3; reflexivity.
    + (* TStar *)
      pi_rw_a IHa.
      match goal with |- context [parse_atom_acc ?t ?P] =>
        destruct (parse_atom_acc t P) as [[e [r Hr]]|] end; reflexivity.
    + (* TAmp *)
      pi_rw_a IHa.
      match goal with |- context [parse_atom_acc ?t ?P] =>
        destruct (parse_atom_acc t P) as [[e [r Hr]]|] end; reflexivity.
    + (* TCaret *)
      pi_rw_a IHa.
      match goal with |- context [parse_atom_acc ?t ?P] =>
        destruct (parse_atom_acc t P) as [[e [r Hr]]|] end; reflexivity.
    + (* TBang *)
      pi_rw_a IHa.
      match goal with |- context [parse_atom_acc ?t ?P] =>
        destruct (parse_atom_acc t P) as [[e [r Hr]]|] end; reflexivity.
    + (* TLP *)
      pi_rw_e IHe.
      match goal with |- context [parse_expr_acc ?k ?t ?P] =>
        destruct (parse_expr_acc k t P) as [[e [r0 Hr0]]|] end; [ | reflexivity ].
      destruct r0 as [| t2 r2]; [ reflexivity | ]. destruct t2; reflexivity.
    + (* TLB *)
      destruct rest as [| t2 rest0]; [ reflexivity | ]. destruct t2; try reflexivity.
      cbn [Acc_inv].
      destruct (parse_gty_b (TLB :: TRB :: rest0)) as [[ty [r Hr]]|]; [ | reflexivity ].
      destruct ty; try reflexivity.
      destruct r as [| t3 r1]; [ reflexivity | ]. destruct t3; try reflexivity.
      * (* TLP: conversion *)
        cbv beta.
        pi_rw_e IHe.
        match goal with |- context [parse_expr_acc ?k ?t ?P] =>
          destruct (parse_expr_acc k t P) as [[e [r2x Hr2x]]|] end; [ | reflexivity ].
        destruct r2x as [| t4 r2]; [ reflexivity | ]. destruct t4; reflexivity.
      * (* TLC: slice literal *)
        cbv beta.
        pi_rw_el IHel.
        match goal with |- context [parse_elems_acc ?t ?P] =>
          destruct (parse_elems_acc t P) as [[es [r2 Hr2]]|] end; reflexivity.
    + (* TChan *)
      destruct (parse_gty_b (TChan :: rest)) as [[ty [r Hr]]|]; [ | reflexivity ].
      destruct ty; try reflexivity.
      destruct r as [| t3 r1]; [ reflexivity | ]. destruct t3; try reflexivity.
      cbv beta.
      pi_rw_e IHe.
      match goal with |- context [parse_expr_acc ?k ?t ?P] =>
        destruct (parse_expr_acc k t P) as [[e [r2x Hr2x]]|] end; [ | reflexivity ].
      destruct r2x as [| t4 r2]; [ reflexivity | ]. destruct t4; reflexivity.
    + (* TMap *)
      destruct (parse_gty_b (TMap :: rest)) as [[ty [r Hr]]|]; [ | reflexivity ].
      destruct ty; try reflexivity.
      destruct r as [| t3 r1]; [ reflexivity | ]. destruct t3; try reflexivity.
      * (* TLP: conversion *)
        cbv beta.
        pi_rw_e IHe.
        match goal with |- context [parse_expr_acc ?k ?t ?P] =>
          destruct (parse_expr_acc k t P) as [[e [r2x Hr2x]]|] end; [ | reflexivity ].
        destruct r2x as [| t4 r2]; [ reflexivity | ]. destruct t4; reflexivity.
      * (* TLC: map literal *)
        cbv beta.
        pi_rw_me IHme.
        match goal with |- context [parse_map_elems_acc ?t ?P] =>
          destruct (parse_map_elems_acc t P) as [[kvs [r2 Hr2]]|] end; reflexivity.
  - (* postfix *)
    intros b toks Hn [h1] [h2].
    destruct toks as [| t1 r1]; [ reflexivity | ].
    cbn [parse_postfix_acc Acc_inv].
    destruct t1; try reflexivity.
    + (* TLP: call *)
      pi_rw_ar IHar.
      match goal with |- context [parse_args_acc ?t ?P] =>
        destruct (parse_args_acc t P) as [[args [r Hr]]|] end; [ | reflexivity ].
      pi_rw_pf IHpf.
      match goal with |- context [parse_postfix_acc ?e ?t ?P] =>
        destruct (parse_postfix_acc e t P) as [[e2 [r2 Hr2]]|] end; reflexivity.
    + (* TLB: index / slice *)
      pi_rw_e IHe.
      match goal with |- context [parse_expr_acc ?k ?t ?P] =>
        destruct (parse_expr_acc k t P) as [[lo [r0 Hr0]]|] end; [ | reflexivity ].
      destruct r0 as [| t3 rr]; [ reflexivity | ]. destruct t3; try reflexivity.
      * (* TRB: index *)
        cbv beta.
        pi_rw_pf IHpf.
        match goal with |- context [parse_postfix_acc ?e ?t ?P] =>
          destruct (parse_postfix_acc e t P) as [[e2 [r2 Hr2]]|] end; reflexivity.
      * (* TColon: slice *)
        cbv beta.
        pi_rw_e IHe.
        match goal with |- context [parse_expr_acc ?k ?t ?P] =>
          destruct (parse_expr_acc k t P) as [[hi [r2x Hr2x]]|] end; [ | reflexivity ].
        destruct r2x as [| t4 r2]; [ reflexivity | ]. destruct t4; try reflexivity.
        cbv beta.
        pi_rw_pf IHpf.
        match goal with |- context [parse_postfix_acc ?e ?t ?P] =>
          destruct (parse_postfix_acc e t P) as [[e3 [r3 Hr3]]|] end; reflexivity.
    + (* TDot *)
      destruct r1 as [| t2 rest]; [ reflexivity | ]. destruct t2; try reflexivity.
      * (* TId: selector *)
        cbn [Acc_inv].
        pi_rw_pf IHpf.
        match goal with |- context [parse_postfix_acc ?e ?t ?P] =>
          destruct (parse_postfix_acc e t P) as [[e2 [r2 Hr2]]|] end; reflexivity.
      * (* TLP: type assertion *)
        cbn [Acc_inv].
        destruct (parse_gty_b rest) as [[T [r0 Hr0]]|]; [ | reflexivity ].
        destruct r0 as [| t3 rr]; [ reflexivity | ]. destruct t3; try reflexivity.
        cbv beta.
        pi_rw_pf IHpf.
        match goal with |- context [parse_postfix_acc ?e ?t ?P] =>
          destruct (parse_postfix_acc e t P) as [[e2 [r2 Hr2]]|] end; reflexivity.
  - (* args *)
    intros toks Hn [h1] [h2].
    destruct toks as [| t1 r1]; cbn [parse_args_acc Acc_inv].
    { pi_rw_e IHe.
      match goal with |- context [parse_expr_acc ?k ?t ?P] =>
        destruct (parse_expr_acc k t P) as [[a0 [r0 Hr0]]|] end; [ | reflexivity ].
      pi_rw_at IHat.
      match goal with |- context [parse_args_tl_acc ?t ?P] =>
        destruct (parse_args_tl_acc t P) as [[args [r2 Hr2]]|] end; reflexivity. }
    destruct t1; try reflexivity;
      (pi_rw_e IHe;
       (match goal with |- context [parse_expr_acc ?k ?t ?P] =>
          destruct (parse_expr_acc k t P) as [[a0 [r0 Hr0]]|] end);
       [ pi_rw_at IHat;
         (match goal with |- context [parse_args_tl_acc ?t ?P] =>
            destruct (parse_args_tl_acc t P) as [[args [r2 Hr2]]|] end); reflexivity
       | reflexivity ]).
  - (* args_tl *)
    intros toks Hn [h1] [h2].
    destruct toks as [| t1 r1]; [ reflexivity | ].
    cbn [parse_args_tl_acc Acc_inv].
    destruct t1; try reflexivity.
    pi_rw_e IHe.
    match goal with |- context [parse_expr_acc ?k ?t ?P] =>
      destruct (parse_expr_acc k t P) as [[a0 [r0 Hr0]]|] end; [ | reflexivity ].
    pi_rw_at IHat.
    match goal with |- context [parse_args_tl_acc ?t ?P] =>
      destruct (parse_args_tl_acc t P) as [[args [r2 Hr2]]|] end; reflexivity.
  - (* elems *)
    intros toks Hn [h1] [h2].
    destruct toks as [| t1 r1]; cbn [parse_elems_acc Acc_inv].
    { pi_rw_e IHe.
      match goal with |- context [parse_expr_acc ?k ?t ?P] =>
        destruct (parse_expr_acc k t P) as [[a0 [r0 Hr0]]|] end; [ | reflexivity ].
      pi_rw_et IHet.
      match goal with |- context [parse_elems_tl_acc ?t ?P] =>
        destruct (parse_elems_tl_acc t P) as [[es [r2 Hr2]]|] end; reflexivity. }
    destruct t1; try reflexivity;
      (pi_rw_e IHe;
       (match goal with |- context [parse_expr_acc ?k ?t ?P] =>
          destruct (parse_expr_acc k t P) as [[a0 [r0 Hr0]]|] end);
       [ pi_rw_et IHet;
         (match goal with |- context [parse_elems_tl_acc ?t ?P] =>
            destruct (parse_elems_tl_acc t P) as [[es [r2 Hr2]]|] end); reflexivity
       | reflexivity ]).
  - (* elems_tl *)
    intros toks Hn [h1] [h2].
    destruct toks as [| t1 r1]; [ reflexivity | ].
    cbn [parse_elems_tl_acc Acc_inv].
    destruct t1; try reflexivity.
    pi_rw_e IHe.
    match goal with |- context [parse_expr_acc ?k ?t ?P] =>
      destruct (parse_expr_acc k t P) as [[a0 [r0 Hr0]]|] end; [ | reflexivity ].
    pi_rw_et IHet.
    match goal with |- context [parse_elems_tl_acc ?t ?P] =>
      destruct (parse_elems_tl_acc t P) as [[es [r2 Hr2]]|] end; reflexivity.
  - (* map_elems *)
    intros toks Hn [h1] [h2].
    destruct toks as [| t1 r1]; cbn [parse_map_elems_acc Acc_inv].
    { pi_rw_e IHe.
      match goal with |- context [parse_expr_acc ?k ?t ?P] =>
        destruct (parse_expr_acc k t P) as [[ke [rK HrK]]|] end; [ | reflexivity ].
      destruct rK as [| tk r0]; [ reflexivity | ]. destruct tk; try reflexivity.
      cbv beta.
      pi_rw_e IHe.
      match goal with |- context [parse_expr_acc ?k ?t ?P] =>
        destruct (parse_expr_acc k t P) as [[ve [rV HrV]]|] end; [ | reflexivity ].
      pi_rw_mt IHmt.
      match goal with |- context [parse_map_elems_tl_acc ?t ?P] =>
        destruct (parse_map_elems_tl_acc t P) as [[kvs [r2 Hr2]]|] end; reflexivity. }
    destruct t1; try reflexivity;
      (pi_rw_e IHe;
       (match goal with |- context [parse_expr_acc ?k ?t ?P] =>
          destruct (parse_expr_acc k t P) as [[ke [rK HrK]]|] end);
       [ destruct rK as [| tk r0]; [ reflexivity | ]; destruct tk; try reflexivity;
         (cbv beta;
          pi_rw_e IHe;
          (match goal with |- context [parse_expr_acc ?k ?t ?P] =>
             destruct (parse_expr_acc k t P) as [[ve [rV HrV]]|] end);
          [ pi_rw_mt IHmt;
            (match goal with |- context [parse_map_elems_tl_acc ?t ?P] =>
               destruct (parse_map_elems_tl_acc t P) as [[kvs [r2 Hr2]]|] end); reflexivity
          | reflexivity ])
       | reflexivity ]).
  - (* map_elems_tl *)
    intros toks Hn [h1] [h2].
    destruct toks as [| t1 r1]; [ reflexivity | ].
    cbn [parse_map_elems_tl_acc Acc_inv].
    destruct t1; try reflexivity.
    pi_rw_e IHe.
    match goal with |- context [parse_expr_acc ?k ?t ?P] =>
      destruct (parse_expr_acc k t P) as [[ke [rK HrK]]|] end; [ | reflexivity ].
    destruct rK as [| tk r0]; [ reflexivity | ]. destruct tk; try reflexivity.
    cbv beta.
    pi_rw_e IHe.
    match goal with |- context [parse_expr_acc ?k ?t ?P] =>
      destruct (parse_expr_acc k t P) as [[ve [rV HrV]]|] end; [ | reflexivity ].
    pi_rw_mt IHmt.
    match goal with |- context [parse_map_elems_tl_acc ?t ?P] =>
      destruct (parse_map_elems_tl_acc t P) as [[kvs [r2 Hr2]]|] end; reflexivity.
  - (* climb *)
    intros k l toks Hn [h1] [h2].
    destruct toks as [| t rest]; [ reflexivity | ].
    cbn [parse_climb_acc Acc_inv].
    destruct (infix_op t) as [o|]; [ | reflexivity ].
    destruct (Nat.leb k (binop_prec o)); [ | reflexivity ].
    pi_rw_e IHe.
    match goal with |- context [parse_expr_acc ?k2 ?t2 ?P] =>
      destruct (parse_expr_acc k2 t2 P) as [[rgt [r2 Hr2]]|] end; [ | reflexivity ].
    pi_rw_cl IHcl.
    match goal with |- context [parse_climb_acc ?k2 ?l2 ?t2 ?P] =>
      destruct (parse_climb_acc k2 l2 t2 P) as [[e3 [r3 Hr3]]|] end; reflexivity.
Qed.

(** the PUBLIC parser: each function is its worker's projection at the [lt_wf] certificate.
    [parse] takes the token list alone. *)
Definition parse_expr (k : nat) (toks : list Token) : option (GExpr * list Token) :=
  match parse_expr_acc k toks (lt_wf (5 * List.length toks + 3)) with
  | Some (e, exist _ r _) => Some (e, r) | None => None end.
Definition parse_primary (toks : list Token) : option (GExpr * list Token) :=
  match parse_primary_acc toks (lt_wf (5 * List.length toks + 2)) with
  | Some (e, exist _ r _) => Some (e, r) | None => None end.
Definition parse_atom (toks : list Token) : option (GExpr * list Token) :=
  match parse_atom_acc toks (lt_wf (5 * List.length toks + 1)) with
  | Some (e, exist _ r _) => Some (e, r) | None => None end.
Definition parse_postfix (b : GExpr) (toks : list Token) : option (GExpr * list Token) :=
  match parse_postfix_acc b toks (lt_wf (5 * List.length toks + 0)) with
  | Some (e, exist _ r _) => Some (e, r) | None => None end.
Definition parse_args (toks : list Token) : option (list GExpr * list Token) :=
  match parse_args_acc toks (lt_wf (5 * List.length toks + 4)) with
  | Some (es, exist _ r _) => Some (es, r) | None => None end.
Definition parse_args_tl (toks : list Token) : option (list GExpr * list Token) :=
  match parse_args_tl_acc toks (lt_wf (5 * List.length toks + 0)) with
  | Some (es, exist _ r _) => Some (es, r) | None => None end.
Definition parse_elems (toks : list Token) : option (list GExpr * list Token) :=
  match parse_elems_acc toks (lt_wf (5 * List.length toks + 4)) with
  | Some (es, exist _ r _) => Some (es, r) | None => None end.
Definition parse_elems_tl (toks : list Token) : option (list GExpr * list Token) :=
  match parse_elems_tl_acc toks (lt_wf (5 * List.length toks + 0)) with
  | Some (es, exist _ r _) => Some (es, r) | None => None end.
Definition parse_map_elems (toks : list Token) : option (list (GExpr * GExpr) * list Token) :=
  match parse_map_elems_acc toks (lt_wf (5 * List.length toks + 4)) with
  | Some (kvs, exist _ r _) => Some (kvs, r) | None => None end.
Definition parse_map_elems_tl (toks : list Token) : option (list (GExpr * GExpr) * list Token) :=
  match parse_map_elems_tl_acc toks (lt_wf (5 * List.length toks + 0)) with
  | Some (kvs, exist _ r _) => Some (kvs, r) | None => None end.
Definition parse_climb (k : nat) (l : GExpr) (toks : list Token) : option (GExpr * list Token) :=
  match parse_climb_acc k l toks (lt_wf (5 * List.length toks + 0)) with
  | Some (e, exist _ r _) => Some (e, r) | None => None end.
Definition parse (toks : list Token) : option (GExpr * list Token) := parse_expr 0 toks.

(** one-step unfold equations at the [Acc_intro (fun y _ => lt_wf y)] certificate (the [lex_eq_*]
    recipe): each public function equals its worker's body with every recursive certificate reduced
    back to [lt_wf] — i.e. back to the public functions themselves. *)
Lemma parse_expr_unfold_pi : forall k toks,
  parse_expr k toks
  = match parse_expr_acc k toks (Acc_intro (5 * List.length toks + 3) (fun y _ => lt_wf y)) with
    | Some (e, exist _ r _) => Some (e, r) | None => None end.
Proof.
  intros. unfold parse_expr.
  destruct (parse_acc_pi_all (S (5 * List.length toks + 3))) as (PIe & _).
  rewrite (PIe k toks (Nat.lt_succ_diag_r _) (lt_wf _) (Acc_intro _ (fun y _ => lt_wf y))).
  reflexivity.
Qed.
Lemma parse_primary_unfold_pi : forall toks,
  parse_primary toks
  = match parse_primary_acc toks (Acc_intro (5 * List.length toks + 2) (fun y _ => lt_wf y)) with
    | Some (e, exist _ r _) => Some (e, r) | None => None end.
Proof.
  intros. unfold parse_primary.
  destruct (parse_acc_pi_all (S (5 * List.length toks + 2))) as (_ & PIp & _).
  rewrite (PIp toks (Nat.lt_succ_diag_r _) (lt_wf _) (Acc_intro _ (fun y _ => lt_wf y))).
  reflexivity.
Qed.
Lemma parse_atom_unfold_pi : forall toks,
  parse_atom toks
  = match parse_atom_acc toks (Acc_intro (5 * List.length toks + 1) (fun y _ => lt_wf y)) with
    | Some (e, exist _ r _) => Some (e, r) | None => None end.
Proof.
  intros. unfold parse_atom.
  destruct (parse_acc_pi_all (S (5 * List.length toks + 1))) as (_ & _ & PIa & _).
  rewrite (PIa toks (Nat.lt_succ_diag_r _) (lt_wf _) (Acc_intro _ (fun y _ => lt_wf y))).
  reflexivity.
Qed.
Lemma parse_postfix_unfold_pi : forall b toks,
  parse_postfix b toks
  = match parse_postfix_acc b toks (Acc_intro (5 * List.length toks + 0) (fun y _ => lt_wf y)) with
    | Some (e, exist _ r _) => Some (e, r) | None => None end.
Proof.
  intros. unfold parse_postfix.
  destruct (parse_acc_pi_all (S (5 * List.length toks + 0))) as (_ & _ & _ & PIpf & _).
  rewrite (PIpf b toks (Nat.lt_succ_diag_r _) (lt_wf _) (Acc_intro _ (fun y _ => lt_wf y))).
  reflexivity.
Qed.
Lemma parse_args_unfold_pi : forall toks,
  parse_args toks
  = match parse_args_acc toks (Acc_intro (5 * List.length toks + 4) (fun y _ => lt_wf y)) with
    | Some (es, exist _ r _) => Some (es, r) | None => None end.
Proof.
  intros. unfold parse_args.
  destruct (parse_acc_pi_all (S (5 * List.length toks + 4))) as (_ & _ & _ & _ & PIar & _).
  rewrite (PIar toks (Nat.lt_succ_diag_r _) (lt_wf _) (Acc_intro _ (fun y _ => lt_wf y))).
  reflexivity.
Qed.
Lemma parse_args_tl_unfold_pi : forall toks,
  parse_args_tl toks
  = match parse_args_tl_acc toks (Acc_intro (5 * List.length toks + 0) (fun y _ => lt_wf y)) with
    | Some (es, exist _ r _) => Some (es, r) | None => None end.
Proof.
  intros. unfold parse_args_tl.
  destruct (parse_acc_pi_all (S (5 * List.length toks + 0))) as (_ & _ & _ & _ & _ & PIat & _).
  rewrite (PIat toks (Nat.lt_succ_diag_r _) (lt_wf _) (Acc_intro _ (fun y _ => lt_wf y))).
  reflexivity.
Qed.
Lemma parse_elems_unfold_pi : forall toks,
  parse_elems toks
  = match parse_elems_acc toks (Acc_intro (5 * List.length toks + 4) (fun y _ => lt_wf y)) with
    | Some (es, exist _ r _) => Some (es, r) | None => None end.
Proof.
  intros. unfold parse_elems.
  destruct (parse_acc_pi_all (S (5 * List.length toks + 4))) as (_ & _ & _ & _ & _ & _ & PIel & _).
  rewrite (PIel toks (Nat.lt_succ_diag_r _) (lt_wf _) (Acc_intro _ (fun y _ => lt_wf y))).
  reflexivity.
Qed.
Lemma parse_elems_tl_unfold_pi : forall toks,
  parse_elems_tl toks
  = match parse_elems_tl_acc toks (Acc_intro (5 * List.length toks + 0) (fun y _ => lt_wf y)) with
    | Some (es, exist _ r _) => Some (es, r) | None => None end.
Proof.
  intros. unfold parse_elems_tl.
  destruct (parse_acc_pi_all (S (5 * List.length toks + 0))) as (_ & _ & _ & _ & _ & _ & _ & PIet & _).
  rewrite (PIet toks (Nat.lt_succ_diag_r _) (lt_wf _) (Acc_intro _ (fun y _ => lt_wf y))).
  reflexivity.
Qed.
Lemma parse_map_elems_unfold_pi : forall toks,
  parse_map_elems toks
  = match parse_map_elems_acc toks (Acc_intro (5 * List.length toks + 4) (fun y _ => lt_wf y)) with
    | Some (kvs, exist _ r _) => Some (kvs, r) | None => None end.
Proof.
  intros. unfold parse_map_elems.
  destruct (parse_acc_pi_all (S (5 * List.length toks + 4))) as (_ & _ & _ & _ & _ & _ & _ & _ & PIme & _).
  rewrite (PIme toks (Nat.lt_succ_diag_r _) (lt_wf _) (Acc_intro _ (fun y _ => lt_wf y))).
  reflexivity.
Qed.
Lemma parse_map_elems_tl_unfold_pi : forall toks,
  parse_map_elems_tl toks
  = match parse_map_elems_tl_acc toks (Acc_intro (5 * List.length toks + 0) (fun y _ => lt_wf y)) with
    | Some (kvs, exist _ r _) => Some (kvs, r) | None => None end.
Proof.
  intros. unfold parse_map_elems_tl.
  destruct (parse_acc_pi_all (S (5 * List.length toks + 0))) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PImt & _).
  rewrite (PImt toks (Nat.lt_succ_diag_r _) (lt_wf _) (Acc_intro _ (fun y _ => lt_wf y))).
  reflexivity.
Qed.
Lemma parse_climb_unfold_pi : forall k l toks,
  parse_climb k l toks
  = match parse_climb_acc k l toks (Acc_intro (5 * List.length toks + 0) (fun y _ => lt_wf y)) with
    | Some (e, exist _ r _) => Some (e, r) | None => None end.
Proof.
  intros. unfold parse_climb.
  destruct (parse_acc_pi_all (S (5 * List.length toks + 0))) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PIcl).
  rewrite (PIcl k l toks (Nat.lt_succ_diag_r _) (lt_wf _) (Acc_intro _ (fun y _ => lt_wf y))).
  reflexivity.
Qed.

(** the one-step BODY equations over the public functions: each equation is the parser's
    defining case split, verbatim, with no premise of any kind. *)
Lemma parse_expr_eq : forall k toks,
  parse_expr k toks = match parse_primary toks with Some (l, r) => parse_climb k l r | None => None end.
Proof.
  intros. rewrite parse_expr_unfold_pi. cbn [parse_expr_acc Acc_inv]. cbn [Acc_inv].
  unfold parse_primary. cbv beta iota delta [Datatypes.length].
  match goal with |- context [parse_primary_acc ?tx ?px] => destruct (parse_primary_acc tx px) as [[l [r Hr]]|] end; [ | reflexivity ].
  cbn [Acc_inv]. unfold parse_climb. cbv beta iota delta [Datatypes.length].
  match goal with |- context [parse_climb_acc ?ax ?lx ?tx ?px] => destruct (parse_climb_acc ax lx tx px) as [[e [r2 Hr2]]|] end; reflexivity.
Qed.
Lemma parse_primary_eq : forall toks,
  parse_primary toks = match parse_atom toks with Some (a, r) => parse_postfix a r | None => None end.
Proof.
  intros. rewrite parse_primary_unfold_pi. cbn [parse_primary_acc Acc_inv]. cbn [Acc_inv].
  unfold parse_atom. cbv beta iota delta [Datatypes.length].
  match goal with |- context [parse_atom_acc ?tx ?px] => destruct (parse_atom_acc tx px) as [[e [r Hr]]|] end; [ | reflexivity ].
  cbn [Acc_inv]. unfold parse_postfix. cbv beta iota delta [Datatypes.length].
  match goal with |- context [parse_postfix_acc ?bx ?tx ?px] => destruct (parse_postfix_acc bx tx px) as [[e2 [r2 Hr2]]|] end; reflexivity.
Qed.
Lemma parse_atom_eq : forall toks,
  parse_atom toks =
  match toks with
  | TLP :: rest => match parse_expr 0 rest with Some (e, TRP :: r) => Some (e, r) | _ => None end
  | TBang  :: rest => match parse_atom rest with Some (e, r) => Some (EUn UNot e, r)   | None => None end
  | TCaret :: rest => match parse_atom rest with Some (e, r) => Some (EUn UXor e, r)   | None => None end
  | TStar  :: rest => match parse_atom rest with Some (e, r) => Some (EUn UDeref e, r) | None => None end
  | TAmp   :: rest => match parse_atom rest with Some (e, r) => Some (EUn UAddr e, r)  | None => None end
  | TMinus :: TLP :: rest => match parse_expr 0 rest with Some (e, TRP :: r) => Some (EUn UNeg e, r) | _ => None end
  | TLB :: TRB :: _ =>
      match parse_gty toks with
      | Some (GTSlice u, TLP :: r1) => match parse_expr 0 r1 with Some (e, TRP :: r2) => Some (EConv (CTSlice u) e, r2) | _ => None end
      | Some (GTSlice u, TLC :: r1) => match parse_elems r1 with Some (es, r2) => Some (ESliceLit u es, r2) | None => None end
      | _ => None end
  | TChan :: _ =>
      match parse_gty toks with
      | Some (GTChan u, TLP :: r1) => match parse_expr 0 r1 with Some (e, TRP :: r2) => Some (EConv (CTChan u) e, r2) | _ => None end
      | _ => None end
  | TMap :: _ =>
      match parse_gty toks with
      | Some (GTMap kt vt, TLP :: r1) => match parse_expr 0 r1 with Some (e, TRP :: r2) => Some (EConv (CTMap kt vt) e, r2) | _ => None end
      | Some (GTMap kt vt, TLC :: r1) => match parse_map_elems r1 with Some (kvs, r2) => Some (EMapLit kt vt kvs, r2) | None => None end
      | _ => None end
  | TId i :: rest  => Some (EId i, rest)
  | TInt z :: rest => Some (EInt z, rest)
  | TStr s :: rest => Some (EStr s, rest)
  | THex zc :: rest => Some (EHex zc, rest)
  | _ => None
  end.
Proof.
  intros. rewrite parse_atom_unfold_pi.
  destruct toks as [| tok rest]; [ reflexivity | ].
  cbn [parse_atom_acc Acc_inv].
  destruct tok; try reflexivity.
  - (* TMinus *)
    destruct rest as [| t2 rest2]; [ reflexivity | ]. destruct t2; try reflexivity.
    cbn [Acc_inv]. unfold parse_expr. cbv beta iota delta [Datatypes.length].
    match goal with |- context [parse_expr_acc ?ax ?tx ?px] => destruct (parse_expr_acc ax tx px) as [[e [r0 Hr0]]|] end; [ | reflexivity ].
    destruct r0 as [| t3 r2]; [ reflexivity | ]. destruct t3; reflexivity.
  - (* TStar *)
    cbn [Acc_inv]. unfold parse_atom. cbv beta iota delta [Datatypes.length].
    match goal with |- context [parse_atom_acc ?tx ?px] => destruct (parse_atom_acc tx px) as [[e [r Hr]]|] end; reflexivity.
  - (* TAmp *)
    cbn [Acc_inv]. unfold parse_atom. cbv beta iota delta [Datatypes.length].
    match goal with |- context [parse_atom_acc ?tx ?px] => destruct (parse_atom_acc tx px) as [[e [r Hr]]|] end; reflexivity.
  - (* TCaret *)
    cbn [Acc_inv]. unfold parse_atom. cbv beta iota delta [Datatypes.length].
    match goal with |- context [parse_atom_acc ?tx ?px] => destruct (parse_atom_acc tx px) as [[e [r Hr]]|] end; reflexivity.
  - (* TBang *)
    cbn [Acc_inv]. unfold parse_atom. cbv beta iota delta [Datatypes.length].
    match goal with |- context [parse_atom_acc ?tx ?px] => destruct (parse_atom_acc tx px) as [[e [r Hr]]|] end; reflexivity.
  - (* TLP *)
    cbn [Acc_inv]. unfold parse_expr. cbv beta iota delta [Datatypes.length].
    match goal with |- context [parse_expr_acc ?ax ?tx ?px] => destruct (parse_expr_acc ax tx px) as [[e [r0 Hr0]]|] end; [ | reflexivity ].
    destruct r0 as [| t2 r2]; [ reflexivity | ]. destruct t2; reflexivity.
  - (* TLB *)
    destruct rest as [| t2 rest0]; [ reflexivity | ]. destruct t2; try reflexivity.
    cbn [Acc_inv]. unfold parse_gty, parse_gty_b.
    destruct (parse_gty_acc (TLB :: TRB :: rest0) (lt_wf (List.length (TLB :: TRB :: rest0))))
      as [[ty [r Hr]]|]; [ | reflexivity ].
    destruct ty; try reflexivity.
    destruct r as [| t3 r1]; [ reflexivity | ]. destruct t3; try reflexivity.
    + (* TLP: conversion *)
      cbn [Acc_inv]. unfold parse_expr. cbv beta iota delta [Datatypes.length].
      match goal with |- context [parse_expr_acc ?ax ?tx ?px] => destruct (parse_expr_acc ax tx px) as [[e [r2x Hr2x]]|] end; [ | reflexivity ].
      destruct r2x as [| t4 r2]; [ reflexivity | ]. destruct t4; reflexivity.
    + (* TLC: slice literal *)
      cbn [Acc_inv]. unfold parse_elems. cbv beta iota delta [Datatypes.length].
      match goal with |- context [parse_elems_acc ?tx ?px] => destruct (parse_elems_acc tx px) as [[es [r2 Hr2]]|] end; reflexivity.
  - (* TChan *)
    cbn [Acc_inv]. unfold parse_gty, parse_gty_b.
    destruct (parse_gty_acc (TChan :: rest) (lt_wf (List.length (TChan :: rest)))) as [[ty [r Hr]]|]; [ | reflexivity ].
    destruct ty; try reflexivity.
    destruct r as [| t3 r1]; [ reflexivity | ]. destruct t3; try reflexivity.
    cbn [Acc_inv]. unfold parse_expr. cbv beta iota delta [Datatypes.length].
    match goal with |- context [parse_expr_acc ?ax ?tx ?px] => destruct (parse_expr_acc ax tx px) as [[e [r2x Hr2x]]|] end; [ | reflexivity ].
    destruct r2x as [| t4 r2]; [ reflexivity | ]. destruct t4; reflexivity.
  - (* TMap *)
    cbn [Acc_inv]. unfold parse_gty, parse_gty_b.
    destruct (parse_gty_acc (TMap :: rest) (lt_wf (List.length (TMap :: rest)))) as [[ty [r Hr]]|]; [ | reflexivity ].
    destruct ty; try reflexivity.
    destruct r as [| t3 r1]; [ reflexivity | ]. destruct t3; try reflexivity.
    + (* TLP: conversion *)
      cbn [Acc_inv]. unfold parse_expr. cbv beta iota delta [Datatypes.length].
      match goal with |- context [parse_expr_acc ?ax ?tx ?px] => destruct (parse_expr_acc ax tx px) as [[e [r2x Hr2x]]|] end; [ | reflexivity ].
      destruct r2x as [| t4 r2]; [ reflexivity | ]. destruct t4; reflexivity.
    + (* TLC: map literal *)
      cbn [Acc_inv]. unfold parse_map_elems. cbv beta iota delta [Datatypes.length].
      match goal with |- context [parse_map_elems_acc ?tx ?px] => destruct (parse_map_elems_acc tx px) as [[kvs [r2 Hr2]]|] end; reflexivity.
Qed.
Lemma parse_postfix_eq : forall b toks,
  parse_postfix b toks =
  match toks with
  | TDot :: TLP :: rest =>
      match parse_gty rest with Some (T, TRP :: r) => parse_postfix (EAssert b T) r | _ => None end
  | TDot :: TId field :: rest => parse_postfix (ESel b field) rest
  | TLB :: rest =>
      match parse_expr 0 rest with
      | Some (lo, TColon :: r1) =>
          match parse_expr 0 r1 with Some (hi, TRB :: r2) => parse_postfix (ESlice b lo hi) r2 | _ => None end
      | Some (i, TRB :: r) => parse_postfix (EIndex b i) r
      | _ => None
      end
  | TLP :: rest => match parse_args rest with Some (args, r) => parse_postfix (ECall b args) r | None => None end
  | _ => Some (b, toks)
  end.
Proof.
  intros. rewrite parse_postfix_unfold_pi.
  destruct toks as [| t1 r1]; [ reflexivity | ].
  cbn [parse_postfix_acc Acc_inv].
  destruct t1; try reflexivity.
  - (* TLP: call *)
    cbn [Acc_inv]. unfold parse_args. cbv beta iota delta [Datatypes.length].
    match goal with |- context [parse_args_acc ?tx ?px] => destruct (parse_args_acc tx px) as [[args [r Hr]]|] end; [ | reflexivity ].
    cbn [Acc_inv]. unfold parse_postfix. cbv beta iota delta [Datatypes.length].
    match goal with |- context [parse_postfix_acc ?bx ?tx ?px] => destruct (parse_postfix_acc bx tx px) as [[e2 [r2 Hr2]]|] end; reflexivity.
  - (* TLB: index / slice *)
    cbn [Acc_inv]. unfold parse_expr. cbv beta iota delta [Datatypes.length].
    match goal with |- context [parse_expr_acc ?ax ?tx ?px] => destruct (parse_expr_acc ax tx px) as [[lo [r0 Hr0]]|] end; [ | reflexivity ].
    destruct r0 as [| t3 rr]; [ reflexivity | ]. destruct t3; try reflexivity.
    + (* TRB: index *)
      cbn [Acc_inv]. unfold parse_postfix. cbv beta iota delta [Datatypes.length].
      match goal with |- context [parse_postfix_acc ?bx ?tx ?px] => destruct (parse_postfix_acc bx tx px) as [[e2 [r2 Hr2]]|] end; reflexivity.
    + (* TColon: slice *)
      cbn [Acc_inv]. unfold parse_expr. cbv beta iota delta [Datatypes.length].
      match goal with |- context [parse_expr_acc ?ax ?tx ?px] => destruct (parse_expr_acc ax tx px) as [[hi [r2x Hr2x]]|] end; [ | reflexivity ].
      destruct r2x as [| t4 r2]; [ reflexivity | ]. destruct t4; try reflexivity.
      cbn [Acc_inv]. unfold parse_postfix. cbv beta iota delta [Datatypes.length].
      match goal with |- context [parse_postfix_acc ?bx ?tx ?px] => destruct (parse_postfix_acc bx tx px) as [[e3 [r3 Hr3]]|] end; reflexivity.
  - (* TDot *)
    destruct r1 as [| t2 rest]; [ reflexivity | ]. destruct t2; try reflexivity.
    + (* TId: selector *)
      cbn [Acc_inv]. unfold parse_postfix. cbv beta iota delta [Datatypes.length].
      cbv beta iota delta [Datatypes.length]; match goal with |- context [parse_postfix_acc ?e ?tt ?P] =>
        destruct (parse_postfix_acc e tt P) as [[e2 [r2 Hr2]]|] end; reflexivity.
    + (* TLP: type assertion *)
      cbn [Acc_inv]. unfold parse_gty, parse_gty_b.
      destruct (parse_gty_acc rest (lt_wf (List.length rest))) as [[T [r0 Hr0]]|]; [ | reflexivity ].
      destruct r0 as [| t3 rr]; [ reflexivity | ]. destruct t3; try reflexivity.
      cbn [Acc_inv]. unfold parse_postfix. cbv beta iota delta [Datatypes.length].
      match goal with |- context [parse_postfix_acc ?bx ?tx ?px] => destruct (parse_postfix_acc bx tx px) as [[e2 [r2 Hr2]]|] end; reflexivity.
Qed.
Lemma parse_args_eq : forall toks,
  parse_args toks =
  match toks with
  | TRP :: r => Some (nil, r)
  | _ => match parse_expr 0 toks with
         | Some (a, r0) => match parse_args_tl r0 with Some (args, r1) => Some (a :: args, r1) | None => None end
         | None => None
         end
  end.
Proof.
  intros. rewrite parse_args_unfold_pi.
  destruct toks as [| t1 r1]; cbn [parse_args_acc Acc_inv].
  { cbn [Acc_inv]. unfold parse_expr. cbv beta iota delta [Datatypes.length].
    match goal with |- context [parse_expr_acc ?ax ?tx ?px] => destruct (parse_expr_acc ax tx px) as [[a0 [r0 Hr0]]|] end; [ | reflexivity ].
    cbn [Acc_inv]. unfold parse_args_tl. cbv beta iota delta [Datatypes.length].
    match goal with |- context [parse_args_tl_acc ?tx ?px] => destruct (parse_args_tl_acc tx px) as [[args [rx Hrx]]|] end; reflexivity. }
  destruct t1; try reflexivity;
    (cbn [Acc_inv]; unfold parse_expr;
     (cbv beta iota delta [Datatypes.length]; match goal with |- context [parse_expr_acc 0 ?t ?P] =>
        destruct (parse_expr_acc 0 t P) as [[a0 [r0 Hr0]]|] end);
     [ cbn [Acc_inv]; unfold parse_args_tl;
       (cbv beta iota delta [Datatypes.length]; match goal with |- context [parse_args_tl_acc ?t ?P] =>
          destruct (parse_args_tl_acc t P) as [[args [rx Hrx]]|] end); reflexivity
     | reflexivity ]).
Qed.
Lemma parse_args_tl_eq : forall toks,
  parse_args_tl toks =
  match toks with
  | TRP :: r => Some (nil, r)
  | TComma :: r => match parse_expr 0 r with
                   | Some (a, r0) => match parse_args_tl r0 with Some (args, r1) => Some (a :: args, r1) | None => None end
                   | None => None
                   end
  | _ => None
  end.
Proof.
  intros. rewrite parse_args_tl_unfold_pi.
  destruct toks as [| t1 r1]; [ reflexivity | ].
  cbn [parse_args_tl_acc Acc_inv].
  destruct t1; try reflexivity.
  cbn [Acc_inv]. unfold parse_expr. cbv beta iota delta [Datatypes.length].
  match goal with |- context [parse_expr_acc ?ax ?tx ?px] => destruct (parse_expr_acc ax tx px) as [[a0 [r0 Hr0]]|] end; [ | reflexivity ].
  cbn [Acc_inv]. unfold parse_args_tl. cbv beta iota delta [Datatypes.length].
  match goal with |- context [parse_args_tl_acc ?tx ?px] => destruct (parse_args_tl_acc tx px) as [[args [rx Hrx]]|] end; reflexivity.
Qed.
Lemma parse_elems_eq : forall toks,
  parse_elems toks =
  match toks with
  | TRC :: r => Some (nil, r)
  | _ => match parse_expr 0 toks with
         | Some (a, r0) => match parse_elems_tl r0 with Some (es, r1) => Some (a :: es, r1) | None => None end
         | None => None
         end
  end.
Proof.
  intros. rewrite parse_elems_unfold_pi.
  destruct toks as [| t1 r1]; cbn [parse_elems_acc Acc_inv].
  { cbn [Acc_inv]. unfold parse_expr. cbv beta iota delta [Datatypes.length].
    match goal with |- context [parse_expr_acc ?ax ?tx ?px] => destruct (parse_expr_acc ax tx px) as [[a0 [r0 Hr0]]|] end; [ | reflexivity ].
    cbn [Acc_inv]. unfold parse_elems_tl. cbv beta iota delta [Datatypes.length].
    match goal with |- context [parse_elems_tl_acc ?tx ?px] => destruct (parse_elems_tl_acc tx px) as [[es [rx Hrx]]|] end; reflexivity. }
  destruct t1; try reflexivity;
    (cbn [Acc_inv]; unfold parse_expr;
     (cbv beta iota delta [Datatypes.length]; match goal with |- context [parse_expr_acc 0 ?t ?P] =>
        destruct (parse_expr_acc 0 t P) as [[a0 [r0 Hr0]]|] end);
     [ cbn [Acc_inv]; unfold parse_elems_tl;
       (cbv beta iota delta [Datatypes.length]; match goal with |- context [parse_elems_tl_acc ?t ?P] =>
          destruct (parse_elems_tl_acc t P) as [[es [rx Hrx]]|] end); reflexivity
     | reflexivity ]).
Qed.
Lemma parse_elems_tl_eq : forall toks,
  parse_elems_tl toks =
  match toks with
  | TRC :: r => Some (nil, r)
  | TComma :: r => match parse_expr 0 r with
                   | Some (a, r0) => match parse_elems_tl r0 with Some (es, r1) => Some (a :: es, r1) | None => None end
                   | None => None
                   end
  | _ => None
  end.
Proof.
  intros. rewrite parse_elems_tl_unfold_pi.
  destruct toks as [| t1 r1]; [ reflexivity | ].
  cbn [parse_elems_tl_acc Acc_inv].
  destruct t1; try reflexivity.
  cbn [Acc_inv]. unfold parse_expr. cbv beta iota delta [Datatypes.length].
  match goal with |- context [parse_expr_acc ?ax ?tx ?px] => destruct (parse_expr_acc ax tx px) as [[a0 [r0 Hr0]]|] end; [ | reflexivity ].
  cbn [Acc_inv]. unfold parse_elems_tl. cbv beta iota delta [Datatypes.length].
  match goal with |- context [parse_elems_tl_acc ?tx ?px] => destruct (parse_elems_tl_acc tx px) as [[es [rx Hrx]]|] end; reflexivity.
Qed.
Lemma parse_map_elems_eq : forall toks,
  parse_map_elems toks =
  match toks with
  | TRC :: r => Some (nil, r)
  | _ => match parse_expr 0 toks with
         | Some (k, TColon :: r0) =>
             match parse_expr 0 r0 with
             | Some (v, r1) => match parse_map_elems_tl r1 with Some (kvs, r2) => Some ((k, v) :: kvs, r2) | None => None end
             | None => None
             end
         | _ => None
         end
  end.
Proof.
  intros. rewrite parse_map_elems_unfold_pi.
  destruct toks as [| t1 r1]; cbn [parse_map_elems_acc Acc_inv].
  { cbn [Acc_inv]. unfold parse_expr. cbv beta iota delta [Datatypes.length].
    match goal with |- context [parse_expr_acc ?ax ?tx ?px] => destruct (parse_expr_acc ax tx px) as [[ke [rK HrK]]|] end; [ | reflexivity ].
    destruct rK as [| tk r0]; [ reflexivity | ]. destruct tk; try reflexivity.
    cbn [Acc_inv].
    match goal with |- context [parse_expr_acc ?ax ?tx ?px] => destruct (parse_expr_acc ax tx px) as [[ve [rV HrV]]|] end; [ | reflexivity ].
    cbn [Acc_inv]. unfold parse_map_elems_tl. cbv beta iota delta [Datatypes.length].
    match goal with |- context [parse_map_elems_tl_acc ?tx ?px] => destruct (parse_map_elems_tl_acc tx px) as [[kvs [rx Hrx]]|] end; reflexivity. }
  destruct t1; try reflexivity;
    (cbn [Acc_inv]; unfold parse_expr;
     (cbv beta iota delta [Datatypes.length]; match goal with |- context [parse_expr_acc 0 ?t ?P] =>
        destruct (parse_expr_acc 0 t P) as [[ke [rK HrK]]|] end);
     [ destruct rK as [| tk r0]; [ reflexivity | ]; destruct tk; try reflexivity;
       (cbn [Acc_inv];
        (cbv beta iota delta [Datatypes.length]; match goal with |- context [parse_expr_acc 0 r0 ?P] =>
           destruct (parse_expr_acc 0 r0 P) as [[ve [rV HrV]]|] end);
        [ cbn [Acc_inv]; unfold parse_map_elems_tl;
          (cbv beta iota delta [Datatypes.length]; match goal with |- context [parse_map_elems_tl_acc ?t ?P] =>
             destruct (parse_map_elems_tl_acc t P) as [[kvs [rx Hrx]]|] end); reflexivity
        | reflexivity ])
     | reflexivity ]).
Qed.
Lemma parse_map_elems_tl_eq : forall toks,
  parse_map_elems_tl toks =
  match toks with
  | TRC :: r => Some (nil, r)
  | TComma :: r =>
      match parse_expr 0 r with
      | Some (k, TColon :: r0) =>
          match parse_expr 0 r0 with
          | Some (v, r1) => match parse_map_elems_tl r1 with Some (kvs, r2) => Some ((k, v) :: kvs, r2) | None => None end
          | None => None
          end
      | _ => None
      end
  | _ => None
  end.
Proof.
  intros. rewrite parse_map_elems_tl_unfold_pi.
  destruct toks as [| t1 r1]; [ reflexivity | ].
  cbn [parse_map_elems_tl_acc Acc_inv].
  destruct t1; try reflexivity.
  cbn [Acc_inv]. unfold parse_expr. cbv beta iota delta [Datatypes.length].
  match goal with |- context [parse_expr_acc ?ax ?tx ?px] => destruct (parse_expr_acc ax tx px) as [[ke [rK HrK]]|] end; [ | reflexivity ].
  destruct rK as [| tk r0]; [ reflexivity | ]. destruct tk; try reflexivity.
  cbn [Acc_inv].
  match goal with |- context [parse_expr_acc ?ax ?tx ?px] => destruct (parse_expr_acc ax tx px) as [[ve [rV HrV]]|] end; [ | reflexivity ].
  cbn [Acc_inv]. unfold parse_map_elems_tl. cbv beta iota delta [Datatypes.length].
  match goal with |- context [parse_map_elems_tl_acc ?tx ?px] => destruct (parse_map_elems_tl_acc tx px) as [[kvs [rx Hrx]]|] end; reflexivity.
Qed.
Lemma parse_climb_eq : forall k l toks,
  parse_climb k l toks =
  match toks with
  | t :: rest =>
      match infix_op t with
      | Some o => if Nat.leb k (binop_prec o)
                  then match parse_expr (S (binop_prec o)) rest with
                       | Some (r, r2) => parse_climb k (EBn o l r) r2
                       | None => None end
                  else Some (l, toks)
      | None => Some (l, toks)
      end
  | nil => Some (l, toks)
  end.
Proof.
  intros. rewrite parse_climb_unfold_pi.
  destruct toks as [| t rest]; [ reflexivity | ].
  cbn [parse_climb_acc Acc_inv].
  destruct (infix_op t) as [o|]; [ | reflexivity ].
  destruct (Nat.leb k (binop_prec o)); [ | reflexivity ].
  cbn [Acc_inv]. unfold parse_expr. cbv beta iota delta [Datatypes.length].
  match goal with |- context [parse_expr_acc ?ax ?tx ?px] => destruct (parse_expr_acc ax tx px) as [[rgt [r2 Hr2]]|] end; [ | reflexivity ].
  cbn [Acc_inv]. unfold parse_climb. cbv beta iota delta [Datatypes.length].
  match goal with |- context [parse_climb_acc ?ax ?lx ?tx ?px] => destruct (parse_climb_acc ax lx tx px) as [[e3 [r3 Hr3]]|] end; reflexivity.
Qed.


(** parse a STRING end-to-end: [lex] then [parse].  The frontend's front door. *)
Definition parse_str (s : string) : option (GExpr * list Token) :=
  match lex s with Some toks => parse toks | None => None end.

(** END-TO-END round-trip examples: [parse_str (gprint 0 e) = Some (e, [])] — the printed AST lexes and
    parses back to itself.  (The GENERAL theorem [parse_print_roundtrip] is PROVEN below.) *)
Notation EX a := (EId (exist (fun s : string => go_ident s = true) a eq_refl)) (only parsing).
(* parse_str inherits the fail-closed rejection (lex feeds parse): a malformed escape never reaches the
   parser — [parse_str] returns [None] (cf. the [lex_bad_*] negative examples). *)
Example parse_bad_escape : parse_str (String (ch 34) (String (ch 92) (String (ch 113) (String (ch 34) "")))) = None.
Proof. vm_compute; reflexivity. Qed.
Example rt_prec : parse_str (gprint 0 (EBn BAdd (EX "a") (EBn BMul (EX "b") (EX "c"))))
                = Some (EBn BAdd (EX "a") (EBn BMul (EX "b") (EX "c")), nil).  (* a + b*c — no parens *)
Proof. vm_compute; reflexivity. Qed.
Example rt_wrap : parse_str (gprint 0 (EBn BMul (EBn BAdd (EX "a") (EX "b")) (EX "c")))
                = Some (EBn BMul (EBn BAdd (EX "a") (EX "b")) (EX "c"), nil).  (* (a + b)*c — parens recovered *)
Proof. vm_compute; reflexivity. Qed.
Example rt_hex : parse_str (gprint 0 (EHex (exist _ 255%Z eq_refl)))
              = Some (EHex (exist _ 255%Z eq_refl), nil).  (* 0xff *)
Proof. vm_compute; reflexivity. Qed.
Example rt_hex_mask : parse_str (gprint 0 (EBn BAnd (EX "x") (EHex (exist _ 255%Z eq_refl))))
              = Some (EBn BAnd (EX "x") (EHex (exist _ 255%Z eq_refl)), nil).  (* x & 0xff — the fixed-width mask shape *)
Proof. vm_compute; reflexivity. Qed.
Example rt_call_method : parse_str (gprint 0 (ESel (ECall (ESel (EX "a") (exist _ "b" eq_refl)) (EX "x" :: nil)) (exist _ "c" eq_refl)))
                  = Some (ESel (ECall (ESel (EX "a") (exist _ "b" eq_refl)) (EX "x" :: nil)) (exist _ "c" eq_refl), nil).  (* a.b(x).c *)
Proof. vm_compute; reflexivity. Qed.
Example rt_slicelit2 : parse_str (gprint 0 (ESliceLit GTInt (EX "x" :: EX "y" :: nil)))
                  = Some (ESliceLit GTInt (EX "x" :: EX "y" :: nil), nil).  (* []int{x,y} *)
Proof. vm_compute; reflexivity. Qed.
Example rt_maplit2 : parse_str (gprint 0 (EMapLit GTString GTInt ((EX "a", EInt 1) :: (EX "b", EInt 2) :: nil)))
                  = Some (EMapLit GTString GTInt ((EX "a", EInt 1) :: (EX "b", EInt 2) :: nil), nil).  (* map[string]int{a: 1, b: 2} *)
Proof. vm_compute; reflexivity. Qed.

(** ---- THE CANONICAL TOKEN LIST ---- [gtokens ctx e] is the token list [gprint ctx e] lexes to.  Mirrors
    [gprint]'s structure exactly; [op_token] RIGHT-inverts the parser's SINGLE token→op classifier
    [infix_op] (in [parse_climb]) — prefix ops [prefix_token] have NO classifier, [parse_atom]
    recognizes them inline.  The two token maps OVERLAP on [TMinus]/[TStar]/[TAmp]/[TCaret] (slice 2h),
    so a token alone does NOT fix the op — the parser selects infix-vs-prefix by POSITION.
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
  | EHex zc => THex zc :: nil   (* mirrors [gprint]'s EHex: a hex literal lexes to its single [THex] token *)
  | EUn o e =>    (* MIRRORS [gprint]'s EUn (lock-step): [prefix_token o] then the operand tokens,
                     wrapped in [TLP … TRP] iff [unop_paren o e]. *)
      prefix_token o :: (if unop_paren o e then TLP :: (gtokens 0 e ++ TRP :: nil) else gtokens 0 e)
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

(** ============================================================================
    THE CANONICAL RELATIONAL GRAMMAR (plans/canonical-grammar.md; CLAUDE.md "Syntax
    authority").  [CanonTy]/[CanonExpr] state the canonical token productions as an
    INDUCTIVE RELATION — the grammar the printer is proved against, with parenthesis
    choices split into separate productions (each carrying its boolean premise) so
    inversion discriminates on the leading token.  The relation mirrors [gttokens_ty]/
    [gtokens] EXACTLY: any divergence is a bug in one of them, never a tolerance.
    ============================================================================ *)
Inductive CanonTy : GoTy -> list Token -> Prop :=
  | CTyInt     : CanonTy GTInt     (TId (mkIdent "int" eq_refl) :: nil)
  | CTyInt64   : CanonTy GTInt64   (TId (mkIdent "int64" eq_refl) :: nil)
  | CTyBool    : CanonTy GTBool    (TId (mkIdent "bool" eq_refl) :: nil)
  | CTyString  : CanonTy GTString  (TId (mkIdent "string" eq_refl) :: nil)
  | CTyFloat64 : CanonTy GTFloat64 (TId (mkIdent "float64" eq_refl) :: nil)
  | CTyFloat32 : CanonTy GTFloat32 (TId (mkIdent "float32" eq_refl) :: nil)
  | CTyUint    : CanonTy GTUint    (TId (mkIdent "uint" eq_refl) :: nil)
  | CTyU8      : CanonTy GTU8      (TId (mkIdent "uint8" eq_refl) :: nil)
  | CTyI8      : CanonTy GTI8      (TId (mkIdent "int8" eq_refl) :: nil)
  | CTyU16     : CanonTy GTU16     (TId (mkIdent "uint16" eq_refl) :: nil)
  | CTyI16     : CanonTy GTI16     (TId (mkIdent "int16" eq_refl) :: nil)
  | CTyU32     : CanonTy GTU32     (TId (mkIdent "uint32" eq_refl) :: nil)
  | CTyI32     : CanonTy GTI32     (TId (mkIdent "int32" eq_refl) :: nil)
  | CTyU64     : CanonTy GTU64     (TId (mkIdent "uint64" eq_refl) :: nil)
  | CTyPtr     : forall u ts, CanonTy u ts -> CanonTy (GTPtr u) (TStar :: ts)
  | CTySlice   : forall u ts, CanonTy u ts -> CanonTy (GTSlice u) (TLB :: TRB :: ts)
  | CTyChan    : forall u ts, CanonTy u ts -> CanonTy (GTChan u) (TChan :: ts)
  | CTyMap     : forall k v tk tv, CanonTy k tk -> CanonTy v tv ->
      CanonTy (GTMap k v) (TMap :: TLB :: (tk ++ TRB :: tv))
  | CTyNamed   : forall n, CanonTy (GTNamed n) (TId (tyname_to_ident n) :: nil).

Inductive CanonExpr : nat -> GExpr -> list Token -> Prop :=
  | CanId  : forall ctx i,  CanonExpr ctx (EId i)  (TId i :: nil)
  | CanInt : forall ctx z,  CanonExpr ctx (EInt z) (TInt z :: nil)
  | CanStr : forall ctx s,  CanonExpr ctx (EStr s) (TStr s :: nil)
  | CanHex : forall ctx zc, CanonExpr ctx (EHex zc) (THex zc :: nil)
  | CanUnP : forall ctx o e ts,
      unop_paren o e = true -> CanonExpr 0 e ts ->
      CanonExpr ctx (EUn o e) (prefix_token o :: TLP :: (ts ++ TRP :: nil))
  | CanUnN : forall ctx o e ts,
      unop_paren o e = false -> CanonExpr 0 e ts ->
      CanonExpr ctx (EUn o e) (prefix_token o :: ts)
  | CanBnP : forall ctx o l r tl tr,
      Nat.ltb (binop_prec o) ctx = true ->
      CanonExpr (binop_prec o) l tl -> CanonExpr (S (binop_prec o)) r tr ->
      CanonExpr ctx (EBn o l r) (TLP :: ((tl ++ op_token o :: tr) ++ TRP :: nil))
  | CanBnN : forall ctx o l r tl tr,
      Nat.ltb (binop_prec o) ctx = false ->
      CanonExpr (binop_prec o) l tl -> CanonExpr (S (binop_prec o)) r tr ->
      CanonExpr ctx (EBn o l r) (tl ++ op_token o :: tr)
  | CanSelP : forall ctx e0 f t0,
      op_needs_paren e0 = true -> CanonExpr 0 e0 t0 ->
      CanonExpr ctx (ESel e0 f) ((TLP :: (t0 ++ TRP :: nil)) ++ TDot :: TId f :: nil)
  | CanSelN : forall ctx e0 f t0,
      op_needs_paren e0 = false -> CanonExpr 0 e0 t0 ->
      CanonExpr ctx (ESel e0 f) (t0 ++ TDot :: TId f :: nil)
  | CanIndexP : forall ctx e0 i t0 ti,
      op_needs_paren e0 = true -> CanonExpr 0 e0 t0 -> CanonExpr 0 i ti ->
      CanonExpr ctx (EIndex e0 i) ((TLP :: (t0 ++ TRP :: nil)) ++ TLB :: (ti ++ TRB :: nil))
  | CanIndexN : forall ctx e0 i t0 ti,
      op_needs_paren e0 = false -> CanonExpr 0 e0 t0 -> CanonExpr 0 i ti ->
      CanonExpr ctx (EIndex e0 i) (t0 ++ TLB :: (ti ++ TRB :: nil))
  | CanSliceP : forall ctx e0 lo hi t0 tlo thi,
      op_needs_paren e0 = true ->
      CanonExpr 0 e0 t0 -> CanonExpr 0 lo tlo -> CanonExpr 0 hi thi ->
      CanonExpr ctx (ESlice e0 lo hi)
        ((TLP :: (t0 ++ TRP :: nil)) ++ TLB :: (tlo ++ TColon :: (thi ++ TRB :: nil)))
  | CanSliceN : forall ctx e0 lo hi t0 tlo thi,
      op_needs_paren e0 = false ->
      CanonExpr 0 e0 t0 -> CanonExpr 0 lo tlo -> CanonExpr 0 hi thi ->
      CanonExpr ctx (ESlice e0 lo hi)
        (t0 ++ TLB :: (tlo ++ TColon :: (thi ++ TRB :: nil)))
  | CanCallP : forall ctx e0 args t0 targs,
      op_needs_paren e0 = true -> CanonExpr 0 e0 t0 -> CanonArgs args targs ->
      CanonExpr ctx (ECall e0 args) ((TLP :: (t0 ++ TRP :: nil)) ++ TLP :: (targs ++ TRP :: nil))
  | CanCallN : forall ctx e0 args t0 targs,
      op_needs_paren e0 = false -> CanonExpr 0 e0 t0 -> CanonArgs args targs ->
      CanonExpr ctx (ECall e0 args) (t0 ++ TLP :: (targs ++ TRP :: nil))
  | CanAssertP : forall ctx e0 T t0 tT,
      op_needs_paren e0 = true -> CanonExpr 0 e0 t0 -> CanonTy T tT ->
      CanonExpr ctx (EAssert e0 T) ((TLP :: (t0 ++ TRP :: nil)) ++ TDot :: TLP :: (tT ++ TRP :: nil))
  | CanAssertN : forall ctx e0 T t0 tT,
      op_needs_paren e0 = false -> CanonExpr 0 e0 t0 -> CanonTy T tT ->
      CanonExpr ctx (EAssert e0 T) (t0 ++ TDot :: TLP :: (tT ++ TRP :: nil))
  | CanConv : forall ctx c e0 tT t0,
      CanonTy (convty_ty c) tT -> CanonExpr 0 e0 t0 ->
      CanonExpr ctx (EConv c e0) (tT ++ TLP :: (t0 ++ TRP :: nil))
  | CanSliceLit : forall ctx t es tT tes,
      CanonTy t tT -> CanonArgs es tes ->
      CanonExpr ctx (ESliceLit t es) (TLB :: TRB :: (tT ++ TLC :: (tes ++ TRC :: nil)))
  | CanMapLit : forall ctx kt vt kvs tT tkvs,
      CanonTy (GTMap kt vt) tT -> CanonPairs kvs tkvs ->
      CanonExpr ctx (EMapLit kt vt kvs) (tT ++ TLC :: (tkvs ++ TRC :: nil))
with CanonArgs : list GExpr -> list Token -> Prop :=
  | CanArgs0 : CanonArgs nil nil
  | CanArgs1 : forall a r ta tr,
      CanonExpr 0 a ta -> CanonArgsTl r tr -> CanonArgs (a :: r) (ta ++ tr)
with CanonArgsTl : list GExpr -> list Token -> Prop :=
  | CanArgsTl0 : CanonArgsTl nil nil
  | CanArgsTl1 : forall b m tb tm,
      CanonExpr 0 b tb -> CanonArgsTl m tm -> CanonArgsTl (b :: m) (TComma :: (tb ++ tm))
with CanonPairs : list (GExpr * GExpr) -> list Token -> Prop :=
  | CanPairs0 : CanonPairs nil nil
  | CanPairs1 : forall k v r tk tv tr,
      CanonExpr 0 k tk -> CanonExpr 0 v tv -> CanonPairsTl r tr ->
      CanonPairs ((k, v) :: r) (tk ++ TColon :: (tv ++ tr))
with CanonPairsTl : list (GExpr * GExpr) -> list Token -> Prop :=
  | CanPairsTl0 : CanonPairsTl nil nil
  | CanPairsTl1 : forall k v m tk tv tm,
      CanonExpr 0 k tk -> CanonExpr 0 v tv -> CanonPairsTl m tm ->
      CanonPairsTl ((k, v) :: m) (TComma :: (tk ++ TColon :: (tv ++ tm))).

Scheme CanonExpr_mind := Minimality for CanonExpr Sort Prop
  with CanonArgs_mind := Minimality for CanonArgs Sort Prop
  with CanonArgsTl_mind := Minimality for CanonArgsTl Sort Prop
  with CanonPairs_mind := Minimality for CanonPairs Sort Prop
  with CanonPairsTl_mind := Minimality for CanonPairsTl Sort Prop.
Combined Scheme CanonExpr_mutind from
  CanonExpr_mind, CanonArgs_mind, CanonArgsTl_mind, CanonPairs_mind, CanonPairsTl_mind.

(** TOKEN-FUNCTIONALITY of the grammar: a derivation's token list is EXACTLY the
    printer's canonical assignment — the relation adds productions, never freedom. *)
Lemma canon_ty_tokens : forall t ts, CanonTy t ts -> ts = gttokens_ty t.
Proof.
  induction 1; cbn [gttokens_ty]; subst; reflexivity.
Qed.

(** token analog of [gparen] + the re-fold lemmas (mirror [gprint_ESel]/[gprint_EIndex]). *)
Definition gtparen (e0 : GExpr) : list Token :=
  if op_needs_paren e0 then (TLP :: (gtokens 0 e0 ++ TRP :: nil))%list else gtokens 0 e0.
(** [gtokens]'s EUn case as a rewrite (mirrors [gprint_EUn]): [prefix_token o] then the operand tokens,
    wrapped in [TLP … TRP] iff [unop_paren o e0]. *)
Lemma gtokens_EUn : forall ctx o e0,
  gtokens ctx (EUn o e0) = (prefix_token o :: (if unop_paren o e0 then TLP :: (gtokens 0 e0 ++ TRP :: nil) else gtokens 0 e0))%list.
Proof. reflexivity. Qed.
Lemma gtokens_EUn_paren : forall ctx o e0, unop_paren o e0 = true ->
  gtokens ctx (EUn o e0) = (prefix_token o :: TLP :: (gtokens 0 e0 ++ TRP :: nil))%list.
Proof. intros ctx o e0 H. rewrite gtokens_EUn, H. reflexivity. Qed.
Lemma gtokens_EUn_bare : forall ctx o e0, unop_paren o e0 = false ->
  gtokens ctx (EUn o e0) = (prefix_token o :: gtokens 0 e0)%list.
Proof. intros ctx o e0 H. rewrite gtokens_EUn, H. reflexivity. Qed.
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

(** [op_token] right-inverts the parser's ONLY token→op classifier [infix_op] (prefix ops have no
    classifier — [parse_atom] recognizes [prefix_token] inline). *)
Lemma infix_op_token : forall o, infix_op (op_token o) = Some o.
Proof. destruct o; reflexivity. Qed.


(** ---- LEXER ROUND-TRIP groundwork ---- the seam predicate + the scanner-splitting lemmas.
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

(** HEX-scan analogues of the decimal lemmas above (for the [0x]-hex literal body). *)
Lemma is_hex_is_idc : forall c, is_hex c = true -> is_idc c = true.
Proof.
  intro c. unfold is_hex, is_idc. set (n := nat_of_ascii c). intro H.
  apply Bool.orb_true_iff in H. destruct H as [H | H].
  - (* '0'-'9' *) rewrite H. reflexivity.
  - (* 'a'-'f' (97-102) is within the 'a'-'z' (97-122) id-char range *)
    apply andb_prop in H. destruct H as [H1 H2]. apply Nat.leb_le in H1, H2.
    replace (Nat.leb 97 n) with true by (symmetry; apply Nat.leb_le; exact H1).
    replace (Nat.leb n 122) with true by (symmetry; apply Nat.leb_le; lia).
    cbn [andb orb]. rewrite Bool.orb_true_r. reflexivity.
Qed.
Lemma scan_hex_clean : forall b, clean_start b = true -> scan_hex b = (EmptyString, b).
Proof.
  intros [ | c b' ] H; [ reflexivity | ].
  unfold clean_start in H. cbn [scan_hex]. destruct (is_hex c) eqn:E; [ | reflexivity ].
  apply is_hex_is_idc in E. rewrite E in H. discriminate H.
Qed.
Lemma scan_hex_app : forall a b, all_hex a = true -> clean_start b = true -> scan_hex (a ++ b) = (a, b).
Proof.
  induction a as [ | c a' IH ]; intros b Ha Hb.
  - apply scan_hex_clean; exact Hb.
  - cbn [all_hex] in Ha. apply andb_prop in Ha. destruct Ha as [Hc Ha'].
    cbn [String.append scan_hex]. rewrite Hc. rewrite (IH b Ha' Hb). reflexivity.
Qed.
(** the rendered hex body is all-hex (each emitted nibble is [is_hex]). *)
Lemma all_hex_render : forall ds acc, Forall (fun d => (d < 16)%nat) ds ->
  all_hex acc = true -> all_hex (render_digits hexdig ds acc) = true.
Proof.
  induction ds as [| d tl IH]; intros acc Hall Hacc; [ exact Hacc | ].
  inversion Hall; subst.
  change (render_digits hexdig (d :: tl) acc)
    with (render_digits hexdig tl (String (hexdig d) acc)).
  apply IH; [ assumption | cbn [all_hex]; rewrite is_hex_hexdig by assumption; exact Hacc ].
Qed.
(** a render of a non-empty digit list is non-empty (every printed digit body has a
    leading digit, so the lexer's first-char dispatch sees one). *)
Lemma render_digits_ne : forall dig ds acc, ds <> nil -> render_digits dig ds acc <> ""%string.
Proof.
  intros dig ds; induction ds as [| d tl IH]; intros acc Hne; [ contradiction | ].
  change (render_digits dig (d :: tl) acc) with (render_digits dig tl (String (dig d) acc)).
  destruct tl as [| d2 tl']; [ cbn; discriminate | apply IH; discriminate ].
Qed.
(** [HexZ] proof-irrelevance (the [0 <=? z = true] proof is UNIQUE by UIP-on-bool) — equal values are equal
    sigs.  Mirrors [ident_eq]; lets [lex]/[gtokens] agree on the carried proof. *)
Lemma hexz_eq : forall a b : HexZ, proj1_sig a = proj1_sig b -> a = b.
Proof.
  intros [x p] [y q] H; cbn in H; subst y.
  assert (E : p = q) by apply (Eqdep_dec.UIP_dec Bool.bool_dec). rewrite E. reflexivity.
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
    tokens — given a clean seam.  ([gtokens (EId i) = [TId i]].) *)
Lemma lex_gprint_id : forall (i : Ident) rest tr,
  clean_start rest = true ->
  lex rest = Some tr ->
  lex (proj1_sig i ++ rest) = Some (TId i :: tr).
Proof.
  intros [s Hs] rest tr Hclean Hrest. simpl proj1_sig in *.
  destruct s as [ | c0 s0 ]; [ vm_compute in Hs; discriminate Hs | ].
  pose proof Hs as Hgo. unfold go_ident in Hgo. apply andb_prop in Hgo. destruct Hgo as [Hia _].
  apply andb_prop in Hia. destruct Hia as [Hidstart Hallidc].
  cbn [String.append].
  rewrite (lex_eq_id c0 (s0 ++ rest)%string (String c0 s0) rest
             (is_idstart_not_space _ Hidstart) Hidstart
             (scan_id_app (String c0 s0) rest Hallidc Hclean)).
  rewrite (lex_ident_go (String c0 s0) Hs).
  rewrite Hrest. reflexivity.
Qed.

(** Digit-shape facts for the integer leaf (proved from scratch for GoPrint). *)
Lemma is_dec_char_dec_digit : forall n, (n < 10)%nat -> is_dec_char (dec_digit n) = true.
Proof.
  intros n Hn. unfold dec_digit, is_dec_char.
  rewrite Ascii.nat_ascii_embedding by lia.
  apply andb_true_intro. split; apply Nat.leb_le; lia.
Qed.

Lemma all_dec_render : forall ds acc, Forall (fun d => (d < 10)%nat) ds ->
  all_dec acc = true -> all_dec (render_digits dec_digit ds acc) = true.
Proof.
  induction ds as [| d tl IH]; intros acc Hall Hacc; [ exact Hacc | ].
  inversion Hall; subst.
  change (render_digits dec_digit (d :: tl) acc)
    with (render_digits dec_digit tl (String (dec_digit d) acc)).
  apply IH; [ assumption | cbn [all_dec]; rewrite is_dec_char_dec_digit by assumption; exact Hacc ].
Qed.

(** Lexing a non-empty all-decimal run [D] (no leading '-') yields [TInt (parse_Z D)] then [rest]. *)
Lemma lex_pos_dec : forall D rest tr,
  all_dec D = true -> D <> EmptyString -> clean_start rest = true ->
  lex rest = Some tr ->
  lex (D ++ rest) = Some (TInt (parse_Z D) :: tr).
Proof.
  intros D rest tr Hdec Hne Hclean Hrest.
  destruct D as [ | d0 D' ]; [ contradiction | ].
  cbn [all_dec] in Hdec. apply andb_prop in Hdec. destruct Hdec as [Hd0 HD'].
  assert (HdecD : all_dec (String d0 D') = true) by (cbn [all_dec]; rewrite Hd0; exact HD').
  (* the [0x] hex guard is FALSE: the char after [d0] is a decimal digit (D' nonempty) or a clean-start
     char (D' empty, by [Hclean]) — never 'x' *)
  assert (Hnotx : match (D' ++ rest)%string with String c1 _ => Ascii.eqb c1 (ch 120) = false | EmptyString => True end).
  { destruct D' as [ | d1 D'' ]; cbn [String.append].
    - destruct rest as [ | r0 rest' ]; [ exact I | ].
      cbn [clean_start] in Hclean. apply Bool.negb_true_iff in Hclean.
      destruct (Ascii.eqb r0 (ch 120)) eqn:Ex; [ | reflexivity ].
      apply Ascii.eqb_eq in Ex; subst r0. vm_compute in Hclean; discriminate.
    - cbn [all_dec] in HD'. apply andb_prop in HD'. destruct HD' as [Hd1 _].
      destruct (Ascii.eqb d1 (ch 120)) eqn:Ex; [ | reflexivity ].
      apply Ascii.eqb_eq in Ex; subst d1. vm_compute in Hd1; discriminate. }
  cbn [String.append].
  rewrite (lex_eq_dec d0 (D' ++ rest)%string Hd0 Hnotx).
  replace (scan_digits (String d0 (D' ++ rest))) with (String d0 D', rest)
    by (symmetry; change (String d0 (D' ++ rest)) with ((String d0 D') ++ rest);
        apply (scan_digits_app (String d0 D') rest HdecD Hclean)).
  cbv beta iota. rewrite Hrest. reflexivity.
Qed.

(** Lexing a NEGATIVE literal ['-' ++ D] (D a non-empty all-decimal run) yields [TInt (parse_Z ('-'++D))]
    via the lexer's negative-literal branch (binary '-' is always SPACED in the printer, so an unspaced
    '-'+digit is unambiguously a literal). *)
Lemma lex_neg_dec : forall D rest tr,
  all_dec D = true -> D <> EmptyString -> clean_start rest = true ->
  lex rest = Some tr ->
  lex (String (ch 45) D ++ rest) = Some (TInt (parse_Z (String (ch 45) D)) :: tr).
Proof.
  intros D rest tr Hdec Hne Hclean Hrest.
  destruct D as [ | d0 D' ]; [ contradiction | ].
  cbn [all_dec] in Hdec. apply andb_prop in Hdec. destruct Hdec as [Hd0 HD'].
  assert (HdecD : all_dec (String d0 D') = true) by (cbn [all_dec]; rewrite Hd0; exact HD').
  cbn [String.append].
  rewrite (lex_eq_neg d0 (D' ++ rest)%string Hd0).
  replace (scan_digits (String d0 (D' ++ rest))) with (String d0 D', rest)
    by (symmetry; change (String d0 (D' ++ rest)) with ((String d0 D') ++ rest);
        apply (scan_digits_app (String d0 D') rest HdecD Hclean)).
  cbv beta iota. rewrite Hrest. reflexivity.
Qed.

(** LEAF (integer): lexing [gprint (EInt z) ++ rest = print_Z z ++ rest] yields [TInt z] then [rest].
    Case on [print_Z]'s shape (0 / positive digits / '-'+digits) via the reflect views (which also reduce
    the [if]s); recover [z] from the scanned run by [print_parse_Z]. *)
Lemma lex_gprint_int : forall z rest tr,
  clean_start rest = true ->
  lex rest = Some tr ->
  lex (print_Z z ++ rest) = Some (TInt z :: tr).
Proof.
  intros z rest tr Hclean Hrest.
  replace (TInt z) with (TInt (parse_Z (print_Z z))) by (rewrite print_parse_Z; reflexivity).
  destruct z as [| p | p]; cbn [print_Z] in *.
  - apply lex_pos_dec; [ reflexivity | discriminate | exact Hclean | exact Hrest ].
  - unfold print_Z_pos in *.
    apply lex_pos_dec;
      [ apply all_dec_render; [ apply pos_digits_bound; lia | reflexivity ]
      | apply render_digits_ne, pos_digits_nonnil | exact Hclean | exact Hrest ].
  - change (("-" ++ print_Z_pos p)%string) with (String (ch 45) (print_Z_pos p)) in *.
    unfold print_Z_pos in *.
    apply lex_neg_dec;
      [ apply all_dec_render; [ apply pos_digits_bound; lia | reflexivity ]
      | apply render_digits_ne, pos_digits_nonnil | exact Hclean | exact Hrest ].
Qed.

(** LEAF (hex): lexing [gprint (EHex zc) ++ rest = print_hex z ++ rest] (z = [proj1_sig zc] >= 0) yields
    [THex zc] then [rest].  [print_hex z = "0x" ++ HD] with [HD] the all-hex, non-empty digit body; the
    lexer's [0x] branch [scan_hex]s [HD] off (clean seam), recovers [z] by [print_parse_hex], and the
    [bool_dec] proof equals the carried [HexZ] proof by UIP ([hexz_eq]). *)
Lemma lex_gprint_hex : forall (zc : HexZ) rest tr,
  clean_start rest = true ->
  lex rest = Some tr ->
  lex (print_hex (Z.to_N (proj1_sig zc)) ++ rest) = Some (THex zc :: tr).
Proof.
  intros [z Hz] rest tr Hclean Hrest. cbn [proj1_sig] in *.
  assert (Hznn : (0 <= z)%Z) by (apply Z.leb_le; exact Hz).
  pose (HD := print_hex_body (Z.to_N z)).
  assert (EprintHD : print_hex (Z.to_N z) = ("0x" ++ HD)%string) by (unfold print_hex, HD; reflexivity).
  assert (HhexHD : all_hex HD = true)
    by (unfold HD; destruct (Z.to_N z) as [| p]; cbn [print_hex_body];
        [ reflexivity | apply all_hex_render; [ apply pos_digits_bound; lia | reflexivity ] ]).
  assert (HneHD : HD <> ""%string)
    by (unfold HD; destruct (Z.to_N z) as [| p]; cbn [print_hex_body];
        [ discriminate | apply render_digits_ne, pos_digits_nonnil ]).
  assert (HparseHD : parseHex_pos 0 HD = z).
  { pose proof (print_parse_hex (Z.to_N z)) as Hpp.
    rewrite EprintHD, parse_hex_0x, Z2N.id in Hpp by exact Hznn. exact Hpp. }
  rewrite EprintHD. clearbody HD. clear EprintHD.
  destruct HD as [ | hc hd' ]; [ exfalso; apply HneHD; reflexivity | ].
  replace ((("0x" ++ String hc hd') ++ rest)%string)
     with (String (ch 48) (String (ch 120) (String hc hd' ++ rest)))
     by (cbn [append]; reflexivity).
  rewrite lex_eq_hex.
  rewrite (scan_hex_app (String hc hd') rest HhexHD Hclean). cbv beta iota.
  destruct (bool_dec ((0 <=? parseHex_pos 0 (String hc hd'))%Z) true) as [Hpos | Hpos];
    [ | exfalso; apply Hpos; rewrite HparseHD; exact Hz ].
  rewrite Hrest.
  do 3 f_equal. apply hexz_eq. cbn [proj1_sig]. exact HparseHD.
Qed.

(** BINOP SEAM: [binop_text o] is [" op "] (spaced both sides), so lexing [binop_text o ++ X] skips the
    leading space, lexes the operator to [op_token o], skips the trailing space, and continues on [X] —
    3 lexer steps, then [X].  The trailing space isolates [X] (no constraint on its head). *)
Lemma lex_binop_app : forall o X tX,
  lex X = Some tX ->
  lex (binop_text o ++ X) = Some (op_token o :: tX).
Proof.
  intros o X tX HX.
  destruct o; cbn [binop_text String.append];
    erewrite lex_eq_space by reflexivity;
    erewrite lex_eq_op by reflexivity;
    erewrite lex_eq_space by reflexivity;
    rewrite HX; reflexivity.
Qed.

(** Single-char delimiter seams: '(' -> TLP, ')' -> TRP (one lexer step), and the [UNeg] prefix "-(" ->
    TMinus, TLP (two steps — '-' followed by '(' is NOT a negative literal, so it lexes as TMinus). *)
Lemma lex_lparen_app : forall X tX,
  lex X = Some tX -> lex (String (ch 40) X) = Some (TLP :: tX).
Proof.
  intros X tX HX. erewrite lex_eq_op by reflexivity. rewrite HX. reflexivity.
Qed.

Lemma lex_rparen_app : forall X tX,
  lex X = Some tX -> lex (String (ch 41) X) = Some (TRP :: tX).
Proof.
  intros X tX HX. erewrite lex_eq_op by reflexivity. rewrite HX. reflexivity.
Qed.

Lemma lex_minuslp_app : forall X tX,
  lex X = Some tX -> lex (String (ch 45) (String (ch 40) X)) = Some (TMinus :: TLP :: tX).
Proof.
  intros X tX HX.
  erewrite lex_eq_op by reflexivity.
  erewrite lex_eq_op by reflexivity.
  rewrite HX. reflexivity.
Qed.

(** KEYWORD SEAM: the printed prefix "return " lexes to the reserved [TReturn] token, so the rest [X]
    lexes unchanged after it.  This makes a [return e] statement DISJOINT from any expression statement at
    the lexer level (a leading [TReturn] is rejected by the expression parser). *)
Lemma lex_return_app : forall X tX,
  lex X = Some tX ->
  lex ("return " ++ X)%string = Some (TReturn :: tX).
Proof.
  intros X tX HX.
  (* keep "return" and the trailing space as appends so [scan_id_app] applies (don't fully unfold append) *)
  change ("return " ++ X)%string with (String "r"%char ("eturn" ++ String " "%char X))%string.
  rewrite (lex_eq_id "r"%char ("eturn" ++ String " "%char X)%string "return"%string (String " "%char X)
             eq_refl eq_refl
             (scan_id_app "return"%string (String " "%char X) eq_refl eq_refl)).
  cbn [lex_ident String.eqb Ascii.eqb].
  erewrite lex_eq_space by reflexivity.
  rewrite HX. reflexivity.
Qed.

(** PARENTHESISED-UNOP SEAM (the [unop_paren o e = true] case — a non-leaf operand, or [UNeg]): [unop_text o]
    (o <> UNeg) is a single char ['!'/'^'/'*'/'&'] followed by '(' — a CONCRETE char that can never
    maximal-munch into a 2-char operator — so it lexes to [prefix_token o] then TLP then [X].  No
    first-char side condition is needed because the next char is fixed.  (The minimal BARE case — a leaf
    operand with NO parens — is [lex_unop_app] just below.) *)
Lemma lex_unop_lp_app : forall o X tX,
  o <> UNeg ->
  lex X = Some tX ->
  lex (unop_text o ++ String (ch 40) X) = Some (prefix_token o :: TLP :: tX).
Proof.
  intros o X tX HoNeg HX.
  destruct o; try (exfalso; apply HoNeg; reflexivity);
    cbn [unop_text String.append prefix_token];
    erewrite lex_eq_op by reflexivity;
    erewrite lex_eq_op by reflexivity;
    rewrite HX; reflexivity.
Qed.

Lemma length_app : forall a b, String.length (a ++ b) = String.length a + String.length b.
Proof. induction a as [ | c a' IH ]; intro b; [ reflexivity | cbn; rewrite IH; reflexivity ]. Qed.

(** ---- BARE-UNARY SEAM (the minimal [^x] / [!b] / [*p] / [&x] without the operand parens) ----
    [unop_head_clean X] = TRUE iff [X]'s first byte is NOT one of ['&'(38) / '^'(94) / '='(61)] — the three
    chars a prefix ['!'/'&'] could MAXIMAL-MUNCH with into a 2-char token ([!=]->TNe, [&&]->TLand,
    [&^]->TAndNot).  ['*']/['^'] never munch (single-char tokens), so they impose no condition; the predicate
    is the shared precondition of [lex_unop_app].  ([gprint_head_clean] discharges it for every BARE operand:
    a leaf atom's first byte is an idstart / a digit / ['-'] / a dquote — never one of the three.) *)
Definition unop_head_clean (X : string) : bool :=
  match X with
  | EmptyString => true
  | String d _  => andb (negb (Ascii.eqb d (ch 38))) (andb (negb (Ascii.eqb d (ch 94))) (negb (Ascii.eqb d (ch 61))))
  end.

Lemma unop_head_clean_cons : forall d rest,
  Ascii.eqb d (ch 38) = false -> Ascii.eqb d (ch 94) = false -> Ascii.eqb d (ch 61) = false ->
  unop_head_clean (String d rest) = true.
Proof. intros d rest H38 H94 H61. cbn [unop_head_clean]. rewrite H38, H94, H61. reflexivity. Qed.

(** An idstart / dec-digit head is unop-clean (none of the three chars is an idstart or a digit). *)
Lemma is_idstart_unop_clean : forall c rest, is_idstart c = true -> unop_head_clean (String c rest) = true.
Proof.
  intros c rest H. apply unop_head_clean_cons;
    match goal with |- Ascii.eqb c (ch ?n) = false =>
      destruct (Ascii.eqb c (ch n)) eqn:E; [ apply Ascii.eqb_eq in E; subst c; vm_compute in H; discriminate | reflexivity ] end.
Qed.
Lemma is_dec_char_unop_clean : forall c rest, is_dec_char c = true -> unop_head_clean (String c rest) = true.
Proof.
  intros c rest H. apply unop_head_clean_cons;
    match goal with |- Ascii.eqb c (ch ?n) = false =>
      destruct (Ascii.eqb c (ch n)) eqn:E; [ apply Ascii.eqb_eq in E; subst c; vm_compute in H; discriminate | reflexivity ] end.
Qed.

(** [print_Z z] is unop-clean: its head is ['0'] / a digit / a leading ['-'(45)] — all clean. *)
Lemma unop_head_clean_print_Z : forall z rest, unop_head_clean (print_Z z ++ rest) = true.
Proof.
  intros z rest. destruct z as [| p | p]; cbn [print_Z].
  - cbn [append]. apply is_dec_char_unop_clean; reflexivity.
  - destruct (render_digits_head (pos_digits 10 p) "" (pos_digits_nonnil 10 p)
                (pos_digits_bound 10 p ltac:(lia))) as [k [r [Hk Hr]]].
    unfold print_Z_pos. rewrite Hr. cbn [append]. apply is_dec_char_unop_clean.
    apply is_dec_char_dec_digit; exact Hk.
  - cbn [append]. apply unop_head_clean_cons; reflexivity.
Qed.

(** ★ Every BARE unary operand ([unop_needs_paren e0 = false], i.e. a LEAF atom) prints with a unop-clean
    head, so the bare prefix lexes cleanly (no left-munch).  Direct case analysis (no induction): a leaf is
    [EId] (idstart head) / [EInt] ([print_Z] head) / [EStr] (dquote head) / [EHex] ([print_hex] head, a [0]). *)
Lemma gprint_head_clean : forall e0, unop_needs_paren e0 = false ->
  forall ctx rest, unop_head_clean (gprint ctx e0 ++ rest) = true.
Proof.
  intros e0 Hbare ctx rest. destruct e0; try discriminate Hbare.
  - (* EId i *) cbn [gprint]. destruct i as [s Hs]. cbn [proj1_sig].
    destruct s as [ | c0 s0 ]; [ vm_compute in Hs; discriminate Hs | ].
    cbn [append]. apply is_idstart_unop_clean.
    pose proof Hs as Hgo. unfold go_ident in Hgo. apply andb_prop in Hgo. destruct Hgo as [Hia _].
    apply andb_prop in Hia. destruct Hia as [Hidstart _]. exact Hidstart.
  - (* EInt z *) cbn [gprint]. apply unop_head_clean_print_Z.
  - (* EStr s *) cbn [gprint]. unfold print_string_lit. cbn [append]. apply unop_head_clean_cons; reflexivity.
  - (* EHex zc *) cbn [gprint].
    match goal with |- context[print_hex ?n] => destruct (print_hex_head n) as [r Hr]; rewrite Hr end.
    cbn [append]. apply is_dec_char_unop_clean. reflexivity.
Qed.

(** BARE-UNOP SEAM: [unop_text o] (o <> UNeg) is a single char ['!'/'^'/'*'/'&']; given a unop-clean [X]
    (so a ['!']/['&'] cannot munch with [X]'s head), it lexes to [prefix_token o] then [X].  The mirror of
    [lex_unop_lp_app] for the BARE operand (no intervening ['(']). *)
Lemma lex_unop_app : forall o X tX,
  o <> UNeg ->
  unop_head_clean X = true ->
  lex X = Some tX ->
  lex (unop_text o ++ X) = Some (prefix_token o :: tX).
Proof.
  intros o X tX HoNeg Hhd HX.
  destruct o; try (exfalso; apply HoNeg; reflexivity); cbn [unop_text append prefix_token].
  - (* UNot, '!' *)
    assert (Hop : lex_op "!"%char X = Some (TBang, X)).
    { destruct X as [ | d X' ]; [ reflexivity | ].
      cbn [unop_head_clean] in Hhd. apply andb_prop in Hhd. destruct Hhd as [_ Hhd].
      apply andb_prop in Hhd. destruct Hhd as [_ H61]. apply negb_true_iff in H61.
      change (lex_op "!"%char (String d X'))
        with (if Ascii.eqb d (ch 61) then Some (TNe, X') else Some (TBang, String d X')).
      rewrite H61. reflexivity. }
    rewrite (lex_eq_op "!"%char X TBang X ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
               ltac:(reflexivity) ltac:(reflexivity) Hop).
    rewrite HX. reflexivity.
  - (* UXor, '^' *)
    rewrite (lex_eq_op "^"%char X TCaret X ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
               ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)).
    rewrite HX. reflexivity.
  - (* UDeref, '*' *)
    rewrite (lex_eq_op "*"%char X TStar X ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
               ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)).
    rewrite HX. reflexivity.
  - (* UAddr, '&' *)
    assert (Hop : lex_op "&"%char X = Some (TAmp, X)).
    { destruct X as [ | d X' ]; [ reflexivity | ].
      cbn [unop_head_clean] in Hhd. apply andb_prop in Hhd. destruct Hhd as [H38 Hhd].
      apply andb_prop in Hhd. destruct Hhd as [H94 _].
      apply negb_true_iff in H38. apply negb_true_iff in H94.
      change (lex_op "&"%char (String d X'))
        with (if Ascii.eqb d (ch 38) then Some (TLand, X')
              else if Ascii.eqb d (ch 94) then Some (TAndNot, X') else Some (TAmp, String d X')).
      rewrite H38, H94. reflexivity. }
    rewrite (lex_eq_op "&"%char X TAmp X ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
               ltac:(reflexivity) ltac:(reflexivity) Hop).
    rewrite HX. reflexivity.
Qed.

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
Lemma lex_gprint_str : forall s rest tr,
  clean_start rest = true ->
  lex rest = Some tr ->
  lex (print_string_lit s ++ rest) = Some (TStr s :: tr).
Proof.
  intros s rest tr _ Hrest.
  unfold print_string_lit.
  replace (((String (ch 34) (esc_string s ++ String (ch 34) "")) ++ rest)%string)
     with (String (ch 34) (esc_string s ++ String (ch 34) rest))
     by (cbn [append]; rewrite str_app_assoc; cbn [append]; reflexivity).
  rewrite lex_eq_quote.
  rewrite scan_quote_esc_string. cbv beta iota. rewrite esc_string_roundtrip_opt. cbv beta iota.
  rewrite Hrest. reflexivity.
Qed.

(** SELECTOR-DOT SEAM: '.' (ch 46) is a single delimiter char — never id/digit/space, [lex_op] maps it
    to [TDot] — so it lexes to [TDot] then [X] (like the paren seams). *)
Lemma lex_dot_app : forall X tX,
  lex X = Some tX -> lex (String (ch 46) X) = Some (TDot :: tX).
Proof.
  intros X tX HX. erewrite lex_eq_op by reflexivity. rewrite HX. reflexivity.
Qed.

(** INDEX-BRACKET SEAMS: '[' (ch 91) → TLB and ']' (ch 93) → TRB are single delimiter chars (like parens). *)
Lemma lex_lbrack_app : forall X tX,
  lex X = Some tX -> lex (String (ch 91) X) = Some (TLB :: tX).
Proof.
  intros X tX HX. erewrite lex_eq_op by reflexivity. rewrite HX. reflexivity.
Qed.
Lemma lex_rbrack_app : forall X tX,
  lex X = Some tX -> lex (String (ch 93) X) = Some (TRB :: tX).
Proof.
  intros X tX HX. erewrite lex_eq_op by reflexivity. rewrite HX. reflexivity.
Qed.
(** COMPOSITE-BRACE SEAMS: '{' (ch 123) → TLC and '}' (ch 125) → TRC are single delimiter chars (like the
    index brackets); used by the slice-composite-literal [[]T{..}] round-trip. *)
Lemma lex_lbrace_app : forall X tX,
  lex X = Some tX -> lex (String (ch 123) X) = Some (TLC :: tX).
Proof.
  intros X tX HX. erewrite lex_eq_op by reflexivity. rewrite HX. reflexivity.
Qed.
Lemma lex_rbrace_app : forall X tX,
  lex X = Some tX -> lex (String (ch 125) X) = Some (TRC :: tX).
Proof.
  intros X tX HX. erewrite lex_eq_op by reflexivity. rewrite HX. reflexivity.
Qed.
(** SLICE-COLON SEAM: ':' (ch 58) → TColon, a single delimiter char (like the brackets). *)
Lemma lex_colon_app : forall X tX,
  lex X = Some tX -> lex (String (ch 58) X) = Some (TColon :: tX).
Proof.
  intros X tX HX. erewrite lex_eq_op by reflexivity. rewrite HX. reflexivity.
Qed.
(** CALL-COMMA SEAM: ',' (ch 44) → TComma, a single delimiter char. *)
Lemma lex_comma_app : forall X tX,
  lex X = Some tX -> lex (String (ch 44) X) = Some (TComma :: tX).
Proof.
  intros X tX HX. erewrite lex_eq_op by reflexivity. rewrite HX. reflexivity.
Qed.
(** POINTER SEAM: '*' (ch 42) → TStar (single-char op, like the brackets). *)
Lemma lex_star_app : forall X tX,
  lex X = Some tX -> lex (String (ch 42) X) = Some (TStar :: tX).
Proof.
  intros X tX HX. erewrite lex_eq_op by reflexivity. rewrite HX. reflexivity.
Qed.
(** WHITESPACE SKIP: a leading space is consumed (no token), then the rest lexes. *)
Lemma lex_space_app : forall Z tZ,
  lex Z = Some tZ -> lex (String (ch 32) Z) = Some tZ.
Proof.
  intros Z tZ HZ. erewrite lex_eq_space by reflexivity. exact HZ.
Qed.
(** KEYWORD SEAM: an identifier RUN [kw] (here [chan]/[map]) lexing to its keyword token, then the rest.
    Mirrors [lex_gprint_id] but with an arbitrary [lex_ident kw] classification. *)
Lemma lex_kw_app : forall c0 kw0 tok Y tY,
  is_idstart c0 = true -> all_idc (String c0 kw0) = true ->
  lex_ident (String c0 kw0) = Some tok ->
  clean_start Y = true -> lex Y = Some tY ->
  lex ((String c0 kw0 ++ Y)%string) = Some (tok :: tY).
Proof.
  intros c0 kw0 tok Y tY Hidstart Hallidc Hkw Hclean HY.
  cbn [String.append].
  rewrite (lex_eq_id c0 (kw0 ++ Y)%string (String c0 kw0) Y
             (is_idstart_not_space _ Hidstart) Hidstart
             (scan_id_app (String c0 kw0) Y Hallidc Hclean)).
  rewrite Hkw. rewrite HY. reflexivity.
Qed.

(** OPERAND SEAM for a selector: [gparen e0] (the bare-or-parenthesised operand) lexes to [gtparen e0]
    then [X], using the per-[e0] round-trip [IHe0] (bare cases directly; paren cases via the '('/')' seams). *)
(** THE TYPE LEX ROUND-TRIP: [lex (print_ty t)] yields [gttokens_ty t] — connecting the string type printer
    [print_ty] to the token layer (rest-threaded, like [lex_gprint_app]).  Scalars/named via [lex_gprint_id];
    [*]/[[]] via the bracket seams; [chan ]/[map[] via [lex_kw_app] (+ [lex_space_app] for chan's space). *)
Lemma gttokens_ty_lex : forall t rest tr,
  clean_start rest = true ->
  lex rest = Some tr ->
  lex (print_ty t ++ rest)%string = Some (gttokens_ty t ++ tr)%list.
Proof.
  induction t as [ | | | | | | | | | | | | | | u IHt | u IHt | u IHt | t1 IHt1 t2 IHt2 | n ];
    intros rest tr Hclean Hrest.
  1-14: cbn [print_ty gttokens_ty app];
        match goal with |- _ = Some (TId ?i :: _) => apply (lex_gprint_id i) end;
        [ exact Hclean | exact Hrest ].
  - (* GTPtr u: "*" ++ print_ty u *)
    cbn [print_ty gttokens_ty].
    assert (Hu : lex (print_ty u ++ rest) = Some (gttokens_ty u ++ tr)%list)
      by (apply IHt; [ exact Hclean | exact Hrest ]).
    rewrite str_app_assoc.
    change ("*" ++ (print_ty u ++ rest))%string with (String (ch 42) (print_ty u ++ rest)).
    rewrite (lex_star_app _ _ Hu).
    cbn [app]; reflexivity.
  - (* GTSlice u: "[]" ++ print_ty u *)
    cbn [print_ty gttokens_ty].
    assert (Hu : lex (print_ty u ++ rest) = Some (gttokens_ty u ++ tr)%list)
      by (apply IHt; [ exact Hclean | exact Hrest ]).
    assert (Hrb : lex (String (ch 93) (print_ty u ++ rest)) = Some (TRB :: (gttokens_ty u ++ tr))%list)
      by (apply lex_rbrack_app; exact Hu).
    rewrite str_app_assoc.
    change ("[]" ++ (print_ty u ++ rest))%string with (String (ch 91) (String (ch 93) (print_ty u ++ rest))).
    rewrite (lex_lbrack_app _ _ Hrb).
    cbn [app]; reflexivity.
  - (* GTChan u: "chan " ++ print_ty u *)
    cbn [print_ty gttokens_ty].
    assert (Hsp : lex (String (ch 32) (print_ty u ++ rest)) = Some (gttokens_ty u ++ tr)%list)
      by (apply lex_space_app; apply IHt; [ exact Hclean | exact Hrest ]).
    rewrite str_app_assoc.
    change ("chan " ++ (print_ty u ++ rest))%string
      with ((String (ch 99) "han") ++ (String (ch 32) (print_ty u ++ rest)))%string.
    rewrite (lex_kw_app (ch 99) "han" TChan (String (ch 32) (print_ty u ++ rest)) (gttokens_ty u ++ tr)
               ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) Hsp).
    cbn [app]; reflexivity.
  - (* GTMap k v: "map[" ++ print_ty k ++ "]" ++ print_ty v *)
    cbn [print_ty gttokens_ty].
    assert (Hv : lex (print_ty t2 ++ rest) = Some (gttokens_ty t2 ++ tr)%list)
      by (apply IHt2; [ exact Hclean | exact Hrest ]).
    assert (Hrbv : lex (String (ch 93) (print_ty t2 ++ rest)) = Some (TRB :: (gttokens_ty t2 ++ tr))%list)
      by (apply lex_rbrack_app; exact Hv).
    assert (Hk : lex (print_ty t1 ++ String (ch 93) (print_ty t2 ++ rest))
               = Some (gttokens_ty t1 ++ (TRB :: (gttokens_ty t2 ++ tr)))%list)
      by (apply IHt1; [ reflexivity | exact Hrbv ]).
    assert (Hlb : lex (String (ch 91) (print_ty t1 ++ String (ch 93) (print_ty t2 ++ rest)))
                = Some (TLB :: (gttokens_ty t1 ++ (TRB :: (gttokens_ty t2 ++ tr))))%list)
      by (apply lex_lbrack_app; exact Hk).
    rewrite !str_app_assoc.
    change ("map[" ++ (print_ty t1 ++ ("]" ++ (print_ty t2 ++ rest))))%string
      with ((String (ch 109) "ap") ++ (String (ch 91) (print_ty t1 ++ String (ch 93) (print_ty t2 ++ rest))))%string.
    rewrite (lex_kw_app (ch 109) "ap" TMap (String (ch 91) (print_ty t1 ++ String (ch 93) (print_ty t2 ++ rest)))
               (TLB :: (gttokens_ty t1 ++ (TRB :: (gttokens_ty t2 ++ tr))))
               ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) Hlb).
    cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
  - (* GTNamed n: the nominal name (a go_ident) *)
    cbn [print_ty gttokens_ty app].
    match goal with |- _ = Some (TId ?i :: _) => apply (lex_gprint_id i) end;
      [ exact Hclean | exact Hrest ].
Qed.

(** GENERIC "[(]operand[)]" lexer seam: for ANY operand [e0] (given its lex IH), the parenthesised wrap
    [(gprint 0 e0)] lexes to [TLP … TRP].  Factored so [lex_gparen]'s two LOOSE cases ([EUn]/[EBn], the only
    operands [op_needs_paren] wraps) share ONE proof instead of a copy-pasted block each. *)
Lemma lex_paren_wrap : forall e0 X tX,
  (forall ctx rest tr, clean_start rest = true ->
     lex rest = Some tr ->
     lex (gprint ctx e0 ++ rest) = Some ((gtokens ctx e0 ++ tr)%list)) ->
  lex X = Some tX ->
  lex (("(" ++ gprint 0 e0 ++ ")") ++ X) = Some ((TLP :: (gtokens 0 e0 ++ TRP :: nil)) ++ tX)%list.
Proof.
  intros e0 X tX IHe0 HX.
  assert (Hrp : lex (String (ch 41) X) = Some (TRP :: tX))
    by (apply lex_rparen_app; exact HX).
  assert (Hin : lex (gprint 0 e0 ++ String (ch 41) X) = Some (gtokens 0 e0 ++ TRP :: tX)%list)
    by (apply IHe0; [ reflexivity | exact Hrp ]).
  rewrite !str_app_assoc.
  change ("(" ++ (gprint 0 e0 ++ (")" ++ X)))%string
    with (String (ch 40) (gprint 0 e0 ++ String (ch 41) X)).
  rewrite (lex_lparen_app _ _ Hin).
  cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
Qed.

Lemma lex_gparen : forall e0 X tX,
  (forall ctx rest tr, clean_start rest = true ->
     lex rest = Some tr ->
     lex (gprint ctx e0 ++ rest) = Some ((gtokens ctx e0 ++ tr)%list)) ->
  clean_start X = true ->
  lex X = Some tX ->
  lex (gparen e0 ++ X) = Some ((gtparen e0 ++ tX)%list).
Proof.
  intros e0 X tX IHe0 HXc HX.
  destruct e0 as [ i0 | z0 | u0 eu | b0 lb rb | es fs | ei ii | esl elo ehi | ecf ecargs | eaf eaT | ecc ece | eslt esles | ekt evt ekvs | sv | hz ]; cbn [gparen gtparen op_needs_paren].
  1,2,5,6,7,8,9,10,11,12,13,14: apply IHe0; [ exact HXc | exact HX ].
  (* the two LOOSE operands [EUn]/[EBn] — both parenthesised, one shared seam *)
  all: apply lex_paren_wrap; [ exact IHe0 | exact HX ].
Qed.

(** ---- THE LEXER ROUND-TRIP ---- [lex (gprint ctx e ++ rest) = gtokens ctx e ++ (lex rest)] for clean
    [rest]; by induction on [e].  Leaves via the leaf lemmas; [EUn]/[EBn] thread the seams
    around the IHs, every boundary clean (a space / a ')' / [rest]).  String scope is open, so the token
    appends are written [%list]. *)
Lemma lex_gprint_app : forall e ctx rest tr,
  clean_start rest = true ->
  lex rest = Some tr ->
  lex (gprint ctx e ++ rest) = Some ((gtokens ctx e ++ tr)%list).
Proof.
  induction e as [ i | z | o e IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 i IHi | e0 IHe0 lo IHlo hi IHhi | e0 IHe0 args IHargs | e0 IHe0 T | c0 ec0 IHec0 | slt sles IHsles | mkt mvt mkvs IHmkvs | sv | hz ]
    using GExpr_ind';
    intros ctx rest tr Hclean Hrest.
  - cbn [gprint gtokens app] in *. apply lex_gprint_id; assumption.
  - cbn [gprint gtokens app] in *. apply lex_gprint_int; assumption.
  - (* EUn: PAREN (UNeg / non-leaf operand) is [<op>( gprint 0 e )]; BARE (leaf operand) is [<op> gprint 0 e].
       [Hbody] (the operand lexed with a trailing ')') serves both paren shapes; the bare shape uses [IHe]
       directly + the unop-clean head ([gprint_head_clean]) + [lex_unop_app]. *)
    rewrite gprint_EUn, gtokens_EUn.
    assert (Hbody : lex (gprint 0 e ++ String (ch 41) rest)
                  = Some ((gtokens 0 e ++ TRP :: tr)%list)).
    { apply IHe; [ reflexivity | apply lex_rparen_app; exact Hrest ]. }
    destruct o; cbn [unop_paren].
    (* UNot / UXor / UDeref / UAddr: wrapped iff [unop_needs_paren e] *)
    1-4: destruct (unop_needs_paren e) eqn:Eb; cbv beta iota;
         [ (* paren *) rewrite !str_app_assoc;
           change (")" ++ rest)%string with (String (ch 41) rest);
           change ("(" ++ (gprint 0 e ++ String (ch 41) rest))%string
             with (String (ch 40) (gprint 0 e ++ String (ch 41) rest));
           erewrite lex_unop_lp_app;
             [ cbn [app]; rewrite <- app_assoc; reflexivity
             | discriminate
             | exact Hbody ]
         | (* bare: e is a leaf, prints [<op> gprint 0 e] *)
           rewrite str_app_assoc; cbn [app];
           apply lex_unop_app;
             [ discriminate
             | apply (gprint_head_clean e Eb 0 rest)
             | apply IHe; [ exact Hclean | exact Hrest ] ] ].
    (* UNeg: ALWAYS paren — body is [-( gprint 0 e )] *)
    cbn [unop_text prefix_token].
    rewrite !str_app_assoc.
    change (")" ++ rest)%string with (String (ch 41) rest).
    change ("-" ++ ("(" ++ (gprint 0 e ++ String (ch 41) rest)))%string
      with (String (ch 45) (String (ch 40) (gprint 0 e ++ String (ch 41) rest))).
    rewrite (lex_minuslp_app _ _ Hbody).
    cbn [app]; rewrite <- app_assoc; reflexivity.
  - (* EBn: inner = gprint p l ++ binop_text o ++ gprint (S p) r *)
    cbn [gprint gtokens].
    set (p := binop_prec o) in *.
    assert (Hinner : forall X tX, clean_start X = true ->
              lex X = Some tX ->
              lex (gprint p l ++ binop_text o ++ gprint (S p) r ++ X)
                = Some (((gtokens p l ++ op_token o :: gtokens (S p) r) ++ tX)%list)).
    { intros X tX HXc HX.
      assert (Hr : lex (gprint (S p) r ++ X) = Some ((gtokens (S p) r ++ tX)%list))
        by (apply IHr; [ exact HXc | exact HX ]).
      assert (Hb : lex (binop_text o ++ gprint (S p) r ++ X)
                 = Some ((op_token o :: (gtokens (S p) r ++ tX))%list))
        by (apply lex_binop_app; exact Hr).
      rewrite <- app_assoc. cbn [app].
      apply IHl; [ apply clean_start_binop | exact Hb ]. }
    destruct (Nat.ltb p ctx); cbn [gprint gtokens].
    + (* wrapped: "(" ++ inner ++ ")" *)
      assert (Hrp : lex (String (ch 41) rest) = Some (TRP :: tr))
        by (apply lex_rparen_app; exact Hrest).
      assert (Hin : lex (gprint p l ++ binop_text o ++ gprint (S p) r ++ String (ch 41) rest)
                  = Some (((gtokens p l ++ op_token o :: gtokens (S p) r) ++ TRP :: tr)%list))
        by (apply Hinner; [ reflexivity | exact Hrp ]).
      rewrite !str_app_assoc.
      change ("(" ++ (gprint p l ++ (binop_text o ++ (gprint (S p) r ++ (")" ++ rest)))))%string
        with (String (ch 40) (gprint p l ++ binop_text o ++ gprint (S p) r ++ String (ch 41) rest)).
      rewrite (lex_lparen_app _ _ Hin).
      cbn [app]. rewrite <- !app_assoc. cbn [app]. reflexivity.
    + (* unwrapped: inner *)
      rewrite !str_app_assoc.
      rewrite (Hinner rest tr Hclean Hrest).
      reflexivity.
  - (* ESel e0 f: [gparen e0] ++ "." ++ field — operand seam ([lex_gparen]) then the '.'+field seam *)
    rewrite gprint_ESel, gtokens_ESel.
    assert (Hfield : lex (proj1_sig f ++ rest) = Some (TId f :: tr))
      by (apply lex_gprint_id; [ exact Hclean | exact Hrest ]).
    assert (Hdot : lex (String (ch 46) (proj1_sig f ++ rest)) = Some (TDot :: TId f :: tr))
      by (apply lex_dot_app; exact Hfield).
    rewrite !str_app_assoc.
    change ("." ++ (proj1_sig f ++ rest))%string with (String (ch 46) (proj1_sig f ++ rest)).
    rewrite (lex_gparen e0 (String (ch 46) (proj1_sig f ++ rest)) (TDot :: TId f :: tr)
               IHe0 eq_refl Hdot).
    cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
  - (* EIndex e0 i: [gparen e0] ++ "[" ++ index ++ "]" — operand seam then '['+index+']' seam *)
    rewrite gprint_EIndex, gtokens_EIndex.
    assert (Hrb : lex (String (ch 93) rest) = Some (TRB :: tr))
      by (apply lex_rbrack_app; exact Hrest).
    assert (Hidx : lex (gprint 0 i ++ String (ch 93) rest) = Some (gtokens 0 i ++ TRB :: tr)%list)
      by (apply IHi; [ reflexivity | exact Hrb ]).
    assert (Hlb : lex (String (ch 91) (gprint 0 i ++ String (ch 93) rest))
                = Some (TLB :: (gtokens 0 i ++ TRB :: tr))%list)
      by (apply lex_lbrack_app; exact Hidx).
    rewrite !str_app_assoc.
    change ("[" ++ (gprint 0 i ++ ("]" ++ rest)))%string
      with (String (ch 91) (gprint 0 i ++ String (ch 93) rest)).
    rewrite (lex_gparen e0 (String (ch 91) (gprint 0 i ++ String (ch 93) rest))
               (TLB :: (gtokens 0 i ++ TRB :: tr)) IHe0 eq_refl Hlb).
    cbn [app]; rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
  - (* ESlice e0 lo hi: [gparen e0] ++ "[" ++ lo ++ ":" ++ hi ++ "]" — operand seam then '['+lo+':'+hi+']' *)
    rewrite gprint_ESlice, gtokens_ESlice.
    assert (Hrb : lex (String (ch 93) rest) = Some (TRB :: tr))
      by (apply lex_rbrack_app; exact Hrest).
    assert (Hhi : lex (gprint 0 hi ++ String (ch 93) rest) = Some (gtokens 0 hi ++ TRB :: tr)%list)
      by (apply IHhi; [ reflexivity | exact Hrb ]).
    assert (Hcolon : lex (String (ch 58) (gprint 0 hi ++ String (ch 93) rest))
                   = Some (TColon :: (gtokens 0 hi ++ TRB :: tr))%list)
      by (apply lex_colon_app; exact Hhi).
    assert (Hlo : lex (gprint 0 lo ++ String (ch 58) (gprint 0 hi ++ String (ch 93) rest))
                = Some (gtokens 0 lo ++ (TColon :: (gtokens 0 hi ++ TRB :: tr)))%list)
      by (apply IHlo; [ reflexivity | exact Hcolon ]).
    assert (Hlb : lex (String (ch 91) (gprint 0 lo ++ String (ch 58) (gprint 0 hi ++ String (ch 93) rest)))
                = Some (TLB :: (gtokens 0 lo ++ (TColon :: (gtokens 0 hi ++ TRB :: tr))))%list)
      by (apply lex_lbrack_app; exact Hlo).
    rewrite !str_app_assoc.
    change ("[" ++ (gprint 0 lo ++ (":" ++ (gprint 0 hi ++ ("]" ++ rest)))))%string
      with (String (ch 91) (gprint 0 lo ++ String (ch 58) (gprint 0 hi ++ String (ch 93) rest))).
    rewrite (lex_gparen e0 (String (ch 91) (gprint 0 lo ++ String (ch 58) (gprint 0 hi ++ String (ch 93) rest)))
               (TLB :: (gtokens 0 lo ++ (TColon :: (gtokens 0 hi ++ TRB :: tr)))) IHe0 eq_refl Hlb).
    cbn [app]; rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; cbn [app];
      rewrite <- !app_assoc; cbn [app]; reflexivity.
  - (* ECall e0 args: [gparen e0] ++ "(" ++ gprint_args args ++ ")" — operand seam then '('+args+')' *)
    rewrite gprint_ECall, gtokens_ECall.
    (* the comma-prefixed arg-tail lexes, by induction on the list using the per-arg [Forall] IH. *)
    assert (Htl : forall l Y tY,
              List.Forall (fun a => forall ctx0 rest0 tr0, clean_start rest0 = true ->
                  lex rest0 = Some tr0 ->
                  lex (gprint ctx0 a ++ rest0) = Some (gtokens ctx0 a ++ tr0)%list) l ->
              clean_start Y = true -> lex Y = Some tY ->
              lex (gprint_args_tl l ++ Y) = Some (gtokens_args_tl l ++ tY)%list).
    { induction l as [ | b m IHm ]; intros Y tY Hfa HYc HY.
      - cbn [gprint_args_tl gtokens_args_tl Datatypes.app] in *. exact HY.
      - cbn [gprint_args_tl gtokens_args_tl].
        assert (Hcs : clean_start (gprint_args_tl m ++ Y) = true)
          by (destruct m as [ | b' m' ]; [ cbn [gprint_args_tl Datatypes.app]; exact HYc | reflexivity ]).
        assert (Hm : lex (gprint_args_tl m ++ Y) = Some (gtokens_args_tl m ++ tY)%list)
          by (apply IHm; [ exact (List.Forall_inv_tail Hfa) | exact HYc | exact HY ]).
        assert (Hb : lex (gprint 0 b ++ gprint_args_tl m ++ Y)
                   = Some (gtokens 0 b ++ (gtokens_args_tl m ++ tY))%list)
          by (apply (List.Forall_inv Hfa); [ exact Hcs | exact Hm ]).
        rewrite !str_app_assoc.
        change ("," ++ (gprint 0 b ++ (gprint_args_tl m ++ Y)))%string
          with (String (ch 44) (gprint 0 b ++ gprint_args_tl m ++ Y)).
        rewrite (lex_comma_app _ _ Hb).
        cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity. }
    assert (Hrp : lex (String (ch 41) rest) = Some (TRP :: tr))
      by (apply lex_rparen_app; exact Hrest).
    assert (Hargs : lex (gprint_args args ++ String (ch 41) rest)
                  = Some (gtokens_args args ++ TRP :: tr)%list).
    { destruct args as [ | a r ].
      - cbn [gprint_args gtokens_args String.append Datatypes.app]. exact Hrp.
      - cbn [gprint_args gtokens_args].
        assert (Hcs : clean_start (gprint_args_tl r ++ String (ch 41) rest) = true)
          by (destruct r as [ | b' r' ]; [ cbn [gprint_args_tl Datatypes.app]; reflexivity | reflexivity ]).
        assert (Htlr : lex (gprint_args_tl r ++ String (ch 41) rest)
                     = Some (gtokens_args_tl r ++ TRP :: tr)%list)
          by (apply (Htl r (String (ch 41) rest) (TRP :: tr));
              [ exact (List.Forall_inv_tail IHargs) | reflexivity | exact Hrp ]).
        rewrite str_app_assoc, <- app_assoc.
        apply (List.Forall_inv IHargs); [ exact Hcs | exact Htlr ]. }
    assert (Hlp : lex (String (ch 40) (gprint_args args ++ String (ch 41) rest))
                = Some (TLP :: (gtokens_args args ++ TRP :: tr))%list)
      by (apply lex_lparen_app; exact Hargs).
    rewrite !str_app_assoc.
    change ("(" ++ (gprint_args args ++ (")" ++ rest)))%string
      with (String (ch 40) (gprint_args args ++ String (ch 41) rest)).
    rewrite (lex_gparen e0 (String (ch 40) (gprint_args args ++ String (ch 41) rest))
               (TLP :: (gtokens_args args ++ TRP :: tr)) IHe0 eq_refl Hlp).
    cbn [app]; rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
  - (* EAssert e0 T: [gparen e0] ++ ".(" ++ print_ty T ++ ")" — operand seam then '.'+'('+type+')' *)
    rewrite gprint_EAssert, gtokens_EAssert.
    assert (Hrp : lex (String (ch 41) rest) = Some (TRP :: tr))
      by (apply lex_rparen_app; exact Hrest).
    assert (Hty : lex (print_ty T ++ String (ch 41) rest) = Some (gttokens_ty T ++ TRP :: tr)%list)
      by (apply gttokens_ty_lex; [ reflexivity | exact Hrp ]).
    assert (Hlp : lex (String (ch 40) (print_ty T ++ String (ch 41) rest))
                = Some (TLP :: (gttokens_ty T ++ TRP :: tr))%list)
      by (apply lex_lparen_app; exact Hty).
    assert (Hdot : lex (String (ch 46) (String (ch 40) (print_ty T ++ String (ch 41) rest)))
                 = Some (TDot :: TLP :: (gttokens_ty T ++ TRP :: tr))%list)
      by (apply lex_dot_app; exact Hlp).
    rewrite !str_app_assoc.
    change (".(" ++ (print_ty T ++ (")" ++ rest)))%string
      with (String (ch 46) (String (ch 40) (print_ty T ++ String (ch 41) rest))).
    rewrite (lex_gparen e0 (String (ch 46) (String (ch 40) (print_ty T ++ String (ch 41) rest)))
               (TDot :: TLP :: (gttokens_ty T ++ TRP :: tr)) IHe0 eq_refl Hdot).
    cbn [app]; rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
  - (* EConv c0 ec0: print_ty(convty_ty c0) ++ "(" ++ gprint 0 ec0 ++ ")" — TYPE prefix then '(' operand ')'.
       Mirrors EAssert's [gttokens_ty_lex] type handling but with the type at the FRONT (outermost seam). *)
    rewrite gprint_EConv, gtokens_EConv.
    assert (Hrp : lex (String (ch 41) rest) = Some (TRP :: tr))
      by (apply lex_rparen_app; exact Hrest).
    assert (Hbody : lex (gprint 0 ec0 ++ String (ch 41) rest) = Some (gtokens 0 ec0 ++ TRP :: tr)%list)
      by (apply IHec0; [ reflexivity | exact Hrp ]).
    assert (Hlp : lex (String (ch 40) (gprint 0 ec0 ++ String (ch 41) rest))
                = Some (TLP :: (gtokens 0 ec0 ++ TRP :: tr))%list)
      by (apply lex_lparen_app; exact Hbody).
    rewrite !str_app_assoc.
    change ("(" ++ (gprint 0 ec0 ++ (")" ++ rest)))%string
      with (String (ch 40) (gprint 0 ec0 ++ String (ch 41) rest)).
    rewrite (gttokens_ty_lex (convty_ty c0) (String (ch 40) (gprint 0 ec0 ++ String (ch 41) rest))
               (TLP :: (gtokens 0 ec0 ++ TRP :: tr)) ltac:(reflexivity) Hlp).
    cbn [app]; rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
  - (* ESliceLit slt sles: "[]" ++ print_ty slt ++ "{" ++ gprint_args sles ++ "}" — the type prefix [[]T] IS
       [print_ty (GTSlice slt)] (so [gttokens_ty_lex] handles the '['']'+type), then '{' element-list '}'.  The
       element list lexes by induction on [sles] exactly like ECall's args (the shared [Htl] helper), but closes
       with '}' (TRC) instead of ')' (TRP). *)
    rewrite gprint_ESliceLit, gtokens_ESliceLit.
    assert (Htl : forall l Y tY,
              List.Forall (fun a => forall ctx0 rest0 tr0, clean_start rest0 = true ->
                  lex rest0 = Some tr0 ->
                  lex (gprint ctx0 a ++ rest0) = Some (gtokens ctx0 a ++ tr0)%list) l ->
              clean_start Y = true -> lex Y = Some tY ->
              lex (gprint_args_tl l ++ Y) = Some (gtokens_args_tl l ++ tY)%list).
    { induction l as [ | b m IHm ]; intros Y tY Hfa HYc HY.
      - cbn [gprint_args_tl gtokens_args_tl Datatypes.app] in *. exact HY.
      - cbn [gprint_args_tl gtokens_args_tl].
        assert (Hcs : clean_start (gprint_args_tl m ++ Y) = true)
          by (destruct m as [ | b' m' ]; [ cbn [gprint_args_tl Datatypes.app]; exact HYc | reflexivity ]).
        assert (Hm : lex (gprint_args_tl m ++ Y) = Some (gtokens_args_tl m ++ tY)%list)
          by (apply IHm; [ exact (List.Forall_inv_tail Hfa) | exact HYc | exact HY ]).
        assert (Hb : lex (gprint 0 b ++ gprint_args_tl m ++ Y)
                   = Some (gtokens 0 b ++ (gtokens_args_tl m ++ tY))%list)
          by (apply (List.Forall_inv Hfa); [ exact Hcs | exact Hm ]).
        rewrite !str_app_assoc.
        change ("," ++ (gprint 0 b ++ (gprint_args_tl m ++ Y)))%string
          with (String (ch 44) (gprint 0 b ++ gprint_args_tl m ++ Y)).
        rewrite (lex_comma_app _ _ Hb).
        cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity. }
    assert (Hrc : lex (String (ch 125) rest) = Some (TRC :: tr))
      by (apply lex_rbrace_app; exact Hrest).
    assert (Helems : lex (gprint_args sles ++ String (ch 125) rest)
                  = Some (gtokens_args sles ++ TRC :: tr)%list).
    { destruct sles as [ | a r ].
      - cbn [gprint_args gtokens_args String.append Datatypes.app]. exact Hrc.
      - cbn [gprint_args gtokens_args].
        assert (Hcs : clean_start (gprint_args_tl r ++ String (ch 125) rest) = true)
          by (destruct r as [ | b' r' ]; [ cbn [gprint_args_tl Datatypes.app]; reflexivity | reflexivity ]).
        assert (Htlr : lex (gprint_args_tl r ++ String (ch 125) rest)
                     = Some (gtokens_args_tl r ++ TRC :: tr)%list)
          by (apply (Htl r (String (ch 125) rest) (TRC :: tr));
              [ exact (List.Forall_inv_tail IHsles) | reflexivity | exact Hrc ]).
        rewrite str_app_assoc, <- app_assoc.
        apply (List.Forall_inv IHsles); [ exact Hcs | exact Htlr ]. }
    assert (Hlc : lex (String (ch 123) (gprint_args sles ++ String (ch 125) rest))
                = Some (TLC :: (gtokens_args sles ++ TRC :: tr))%list)
      by (apply lex_lbrace_app; exact Helems).
    rewrite !str_app_assoc.
    change ("[]" ++ (print_ty slt ++ ("{" ++ (gprint_args sles ++ ("}" ++ rest)))))%string
      with (print_ty (GTSlice slt) ++ String (ch 123) (gprint_args sles ++ String (ch 125) rest))%string.
    rewrite (gttokens_ty_lex (GTSlice slt) (String (ch 123) (gprint_args sles ++ String (ch 125) rest))
               (TLC :: (gtokens_args sles ++ TRC :: tr)) ltac:(reflexivity) Hlc).
    cbn [gttokens_ty app]; rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
  - (* EMapLit mkt mvt mkvs: print_ty(GTMap mkt mvt) ++ "{" ++ gprint_pairs mkvs ++ "}" — the type prefix is
       [print_ty (GTMap mkt mvt)] (handled by [gttokens_ty_lex]), then '{' the KEYED pair-list '}'.  Each pair
       is [k: v] with SPACE seams ([lex_colon_app]+[lex_space_app]) and ", " between pairs ([lex_comma_app]+
       [lex_space_app]); the lexer SKIPS the printed spaces so the token list carries none. *)
    rewrite gprint_EMapLit, gtokens_EMapLit.
    assert (Htl : forall l Y tY,
              List.Forall (fun p => (forall ctx0 rest0 tr0, clean_start rest0 = true ->
                  lex rest0 = Some tr0 ->
                  lex (gprint ctx0 (fst p) ++ rest0) = Some (gtokens ctx0 (fst p) ++ tr0)%list)
                /\ (forall ctx0 rest0 tr0, clean_start rest0 = true ->
                  lex rest0 = Some tr0 ->
                  lex (gprint ctx0 (snd p) ++ rest0) = Some (gtokens ctx0 (snd p) ++ tr0)%list)) l ->
              clean_start Y = true -> lex Y = Some tY ->
              lex (gprint_pairs_tl l ++ Y) = Some (gtokens_pairs_tl l ++ tY)%list).
    { induction l as [ | [k v] m IHm ]; intros Y tY Hfa HYc HY.
      - cbn [gprint_pairs_tl gtokens_pairs_tl Datatypes.app] in *. exact HY.
      - cbn [gprint_pairs_tl gtokens_pairs_tl].
        destruct (List.Forall_inv Hfa) as [ Hlexk Hlexv ]. cbn [fst snd] in Hlexk, Hlexv.
        assert (Hcs : clean_start (gprint_pairs_tl m ++ Y) = true)
          by (destruct m as [ | [k' v'] m' ]; [ cbn [gprint_pairs_tl Datatypes.app]; exact HYc | reflexivity ]).
        assert (Hm : lex (gprint_pairs_tl m ++ Y) = Some (gtokens_pairs_tl m ++ tY)%list)
          by (apply IHm; [ exact (List.Forall_inv_tail Hfa) | exact HYc | exact HY ]).
        assert (Hv : lex (gprint 0 v ++ gprint_pairs_tl m ++ Y)
                   = Some (gtokens 0 v ++ (gtokens_pairs_tl m ++ tY))%list)
          by (apply Hlexv; [ exact Hcs | exact Hm ]).
        assert (Hspv : lex (String (ch 32) (gprint 0 v ++ gprint_pairs_tl m ++ Y))
                     = Some (gtokens 0 v ++ (gtokens_pairs_tl m ++ tY))%list)
          by (apply lex_space_app; exact Hv).
        assert (Hcolon : lex (String (ch 58) (String (ch 32) (gprint 0 v ++ gprint_pairs_tl m ++ Y)))
                       = Some (TColon :: (gtokens 0 v ++ (gtokens_pairs_tl m ++ tY)))%list)
          by (apply lex_colon_app; exact Hspv).
        assert (Hk : lex (gprint 0 k ++ String (ch 58) (String (ch 32) (gprint 0 v ++ gprint_pairs_tl m ++ Y)))
                   = Some (gtokens 0 k ++ (TColon :: (gtokens 0 v ++ (gtokens_pairs_tl m ++ tY))))%list)
          by (apply Hlexk; [ reflexivity | exact Hcolon ]).
        assert (Hspk : lex (String (ch 32) (gprint 0 k ++ String (ch 58) (String (ch 32) (gprint 0 v ++ gprint_pairs_tl m ++ Y))))
                     = Some (gtokens 0 k ++ (TColon :: (gtokens 0 v ++ (gtokens_pairs_tl m ++ tY))))%list)
          by (apply lex_space_app; exact Hk).
        rewrite !str_app_assoc.
        change (", " ++ (gprint 0 k ++ (": " ++ (gprint 0 v ++ (gprint_pairs_tl m ++ Y)))))%string
          with (String (ch 44) (String (ch 32) (gprint 0 k ++ String (ch 58) (String (ch 32) (gprint 0 v ++ gprint_pairs_tl m ++ Y))))).
        rewrite (lex_comma_app _ _ Hspk).
        cbn [app]; rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; reflexivity. }
    assert (Hrc : lex (String (ch 125) rest) = Some (TRC :: tr))
      by (apply lex_rbrace_app; exact Hrest).
    assert (Hpairs : lex (gprint_pairs mkvs ++ String (ch 125) rest)
                  = Some (gtokens_pairs mkvs ++ TRC :: tr)%list).
    { destruct mkvs as [ | [k v] r ].
      - cbn [gprint_pairs gtokens_pairs String.append Datatypes.app]. exact Hrc.
      - cbn [gprint_pairs gtokens_pairs].
        destruct (List.Forall_inv IHmkvs) as [ Hlexk Hlexv ]. cbn [fst snd] in Hlexk, Hlexv.
        assert (Hcs : clean_start (gprint_pairs_tl r ++ String (ch 125) rest) = true)
          by (destruct r as [ | [k' v'] r' ]; [ cbn [gprint_pairs_tl Datatypes.app]; reflexivity | reflexivity ]).
        assert (Htlr : lex (gprint_pairs_tl r ++ String (ch 125) rest)
                     = Some (gtokens_pairs_tl r ++ TRC :: tr)%list)
          by (apply (Htl r (String (ch 125) rest) (TRC :: tr));
              [ exact (List.Forall_inv_tail IHmkvs) | reflexivity | exact Hrc ]).
        assert (Hv : lex (gprint 0 v ++ gprint_pairs_tl r ++ String (ch 125) rest)
                   = Some (gtokens 0 v ++ (gtokens_pairs_tl r ++ TRC :: tr))%list)
          by (apply Hlexv; [ exact Hcs | exact Htlr ]).
        assert (Hspv : lex (String (ch 32) (gprint 0 v ++ gprint_pairs_tl r ++ String (ch 125) rest))
                     = Some (gtokens 0 v ++ (gtokens_pairs_tl r ++ TRC :: tr))%list)
          by (apply lex_space_app; exact Hv).
        assert (Hcolon : lex (String (ch 58) (String (ch 32) (gprint 0 v ++ gprint_pairs_tl r ++ String (ch 125) rest)))
                       = Some (TColon :: (gtokens 0 v ++ (gtokens_pairs_tl r ++ TRC :: tr)))%list)
          by (apply lex_colon_app; exact Hspv).
        rewrite !str_app_assoc.
        change (": " ++ (gprint 0 v ++ (gprint_pairs_tl r ++ String (ch 125) rest)))%string
          with (String (ch 58) (String (ch 32) (gprint 0 v ++ gprint_pairs_tl r ++ String (ch 125) rest))).
        rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc.
        apply Hlexk; [ reflexivity | exact Hcolon ]. }
    assert (Hlc : lex (String (ch 123) (gprint_pairs mkvs ++ String (ch 125) rest))
                = Some (TLC :: (gtokens_pairs mkvs ++ TRC :: tr))%list)
      by (apply lex_lbrace_app; exact Hpairs).
    rewrite !str_app_assoc.
    change (print_ty (GTMap mkt mvt) ++ ("{" ++ (gprint_pairs mkvs ++ ("}" ++ rest))))%string
      with (print_ty (GTMap mkt mvt) ++ String (ch 123) (gprint_pairs mkvs ++ String (ch 125) rest))%string.
    rewrite (gttokens_ty_lex (GTMap mkt mvt) (String (ch 123) (gprint_pairs mkvs ++ String (ch 125) rest))
               (TLC :: (gtokens_pairs mkvs ++ TRC :: tr)) ltac:(reflexivity) Hlc).
    rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; cbn [app]; reflexivity.
  - (* EStr sv: the string-literal leaf — [print_string_lit sv] lexes to [TStr sv] (mirrors EId/EInt) *)
    cbn [gprint gtokens app] in *. apply lex_gprint_str; assumption.
  - (* EHex hz: the hex-literal leaf — [print_hex] lexes to [THex hz] (mirrors EId/EInt) *)
    cbn [gprint gtokens app] in *. apply lex_gprint_hex; assumption.
Qed.

(** THE HEADLINE (lexer half): [lex (gprint ctx e) = Some (gtokens ctx e)] — the printed AST lexes to its
    canonical token list, for EVERY expression. *)
Theorem gtokens_lex : forall e ctx, lex (gprint ctx e) = Some (gtokens ctx e).
Proof.
  intros e ctx.
  pose proof (lex_gprint_app e ctx "" nil eq_refl lex_empty) as H.
  rewrite str_app_nil_r in H. rewrite app_nil_r in H. exact H.
Qed.

(** TOKEN-FUNCTIONALITY, all five relations at once: a derivation's tokens ARE the
    printer's canonical assignment. *)
Lemma canon_expr_tokens_mut :
  (forall ctx e ts, CanonExpr ctx e ts -> ts = gtokens ctx e)
  /\ (forall args ts, CanonArgs args ts -> ts = gtokens_args args)
  /\ (forall args ts, CanonArgsTl args ts -> ts = gtokens_args_tl args)
  /\ (forall kvs ts, CanonPairs kvs ts -> ts = gtokens_pairs kvs)
  /\ (forall kvs ts, CanonPairsTl kvs ts -> ts = gtokens_pairs_tl kvs).
Proof.
  apply CanonExpr_mutind; intros; subst;
    rewrite ?gtokens_ECall, ?gtokens_ESliceLit, ?gtokens_EMapLit,
            ?gtokens_EAssert, ?gtokens_EConv, ?gtokens_EIndex, ?gtokens_ESlice, ?gtokens_EUn;
    repeat match goal with
           | H : CanonTy _ _ |- _ => apply canon_ty_tokens in H; subst
           end;
    cbn [gtokens gtokens_args gtokens_args_tl gtokens_pairs gtokens_pairs_tl];
    unfold gtparen;
    repeat match goal with H : _ = true |- _ => rewrite H; clear H
                         | H : _ = false |- _ => rewrite H; clear H end;
    reflexivity.
Qed.
Theorem canon_expr_tokens : forall ctx e ts, CanonExpr ctx e ts -> ts = gtokens ctx e.
Proof. exact (proj1 canon_expr_tokens_mut). Qed.

(** CANONICITY: the printer's token assignment inhabits the grammar, at every context. *)
Lemma gttokens_ty_canonical : forall t, CanonTy t (gttokens_ty t).
Proof. induction t; cbn [gttokens_ty]; constructor; assumption. Qed.
Lemma canon_args_intro : forall args,
  Forall (fun a => CanonExpr 0 a (gtokens 0 a)) args ->
  CanonArgs args (gtokens_args args)
  /\ CanonArgsTl args (gtokens_args_tl args).
Proof.
  induction 1 as [ | a r Ha Hr [IH1 IH2] ].
  - split; constructor.
  - split.
    + cbn [gtokens_args]. apply CanArgs1; [ exact Ha | exact IH2 ].
    + cbn [gtokens_args_tl]. apply CanArgsTl1; [ exact Ha | exact IH2 ].
Qed.
Lemma canon_pairs_intro : forall kvs,
  Forall (fun p => CanonExpr 0 (fst p) (gtokens 0 (fst p))
                   /\ CanonExpr 0 (snd p) (gtokens 0 (snd p))) kvs ->
  CanonPairs kvs (gtokens_pairs kvs)
  /\ CanonPairsTl kvs (gtokens_pairs_tl kvs).
Proof.
  induction 1 as [ | [k v] r [Hk Hv] Hr [IH1 IH2] ].
  - split; constructor.
  - split.
    + cbn [gtokens_pairs]. apply CanPairs1; [ exact Hk | exact Hv | exact IH2 ].
    + cbn [gtokens_pairs_tl]. apply CanPairsTl1; [ exact Hk | exact Hv | exact IH2 ].
Qed.

Theorem gprint_expr_canonical : forall e ctx, CanonExpr ctx e (gtokens ctx e).
Proof.
  induction e using GExpr_ind'; intro ctx.
  - apply CanId.
  - apply CanInt.
  - (* EUn *) rewrite gtokens_EUn.
    destruct (unop_paren o e) eqn:Ep.
    + apply CanUnP; [ exact Ep | apply IHe ].
    + apply CanUnN; [ exact Ep | apply IHe ].
  - (* EBn *) cbn [gtokens].
    destruct (Nat.ltb (binop_prec o) ctx) eqn:Ep.
    + apply CanBnP; [ exact Ep | apply IHe1 | apply IHe2 ].
    + apply CanBnN; [ exact Ep | apply IHe1 | apply IHe2 ].
  - (* ESel *) cbn [gtokens].
    destruct (op_needs_paren e) eqn:Ep.
    + apply CanSelP; [ exact Ep | apply IHe ].
    + apply CanSelN; [ exact Ep | apply IHe ].
  - (* EIndex *) rewrite gtokens_EIndex. unfold gtparen.
    destruct (op_needs_paren e1) eqn:Ep.
    + apply CanIndexP; [ exact Ep | apply IHe1 | apply IHe2 ].
    + apply CanIndexN; [ exact Ep | apply IHe1 | apply IHe2 ].
  - (* ESlice *) rewrite gtokens_ESlice. unfold gtparen.
    destruct (op_needs_paren e1) eqn:Ep.
    + apply CanSliceP; [ exact Ep | apply IHe1 | apply IHe2 | apply IHe3 ].
    + apply CanSliceN; [ exact Ep | apply IHe1 | apply IHe2 | apply IHe3 ].
  - (* ECall *) rewrite gtokens_ECall. unfold gtparen.
    destruct (canon_args_intro args ltac:(eapply Forall_impl; [ | exact H ]; cbn; intros a Ha; apply Ha)) as [Hargs _].
    destruct (op_needs_paren e) eqn:Ep.
    + apply CanCallP; [ exact Ep | apply IHe | exact Hargs ].
    + apply CanCallN; [ exact Ep | apply IHe | exact Hargs ].
  - (* EAssert *) rewrite gtokens_EAssert. unfold gtparen.
    destruct (op_needs_paren e) eqn:Ep.
    + apply CanAssertP; [ exact Ep | apply IHe | apply gttokens_ty_canonical ].
    + apply CanAssertN; [ exact Ep | apply IHe | apply gttokens_ty_canonical ].
  - (* EConv *) rewrite gtokens_EConv.
    apply CanConv; [ apply gttokens_ty_canonical | apply IHe ].
  - (* ESliceLit *) rewrite gtokens_ESliceLit.
    destruct (canon_args_intro es ltac:(eapply Forall_impl; [ | exact H ]; cbn; intros a Ha; apply Ha)) as [Hes _].
    apply CanSliceLit; [ apply gttokens_ty_canonical | exact Hes ].
  - (* EMapLit *) rewrite gtokens_EMapLit.
    destruct (canon_pairs_intro kvs ltac:(eapply Forall_impl; [ | exact H ]; cbn;
                intros p Hp; split; [ exact (proj1 Hp 0) | exact (proj2 Hp 0) ])) as [Hkvs _].
    apply CanMapLit; [ apply gttokens_ty_canonical | exact Hkvs ].
  - apply CanStr.
  - apply CanHex.
Qed.

(** ---- Phase 3a: the BRACKET-BALANCE toolkit + type-level uniqueness ----
    [sqd ts d]: the square-bracket depth after scanning [ts] from depth [d] ([None] = a
    [TRB] at depth 0 — a dip below the start).  Canonical token lists are BALANCED, so in
    [ts ++ TRB :: r] the appended [TRB] is the FIRST dip — both sides of an equation
    identify the same split point, giving the cancellation the [TMap]/bracket productions
    need.  Parser-free by construction: uniqueness is proved on the token-assignment
    FUNCTIONS (via [canon_ty_tokens]-style functionality), never via [parse]. *)
Fixpoint sqd (ts : list Token) (d : nat) : option nat :=
  match ts with
  | nil => Some d
  | TLB :: r => sqd r (S d)
  | TRB :: r => match d with O => None | S d' => sqd r d' end
  | _ :: r => sqd r d
  end.
Lemma sqd_app : forall a b d,
  sqd (a ++ b) d = match sqd a d with Some d' => sqd b d' | None => None end.
Proof.
  induction a as [ | t a IH ]; intros b d; [ reflexivity | ].
  destruct t; cbn [sqd app]; try apply IH.
  destruct d; [ reflexivity | apply IH ].
Qed.
Lemma sqd_up : forall ts d e, sqd ts d = Some e -> sqd ts (S d) = Some (S e).
Proof.
  induction ts as [ | t ts IH ]; intros d e H; cbn [sqd] in *.
  - injection H as <-. reflexivity.
  - destruct t; try (apply IH; exact H).
    (* TRB, the only survivor: the head consumed one depth level *)
    destruct d as [ | d ]; [ discriminate H | apply IH; exact H ].
Qed.
(** the index of the first dip below the start depth (None = never dips) *)
Fixpoint firstdip (ts : list Token) (d : nat) : option nat :=
  match ts with
  | nil => None
  | TLB :: r => option_map S (firstdip r (S d))
  | TRB :: r => match d with O => Some O | S d' => option_map S (firstdip r d') end
  | _ :: r => option_map S (firstdip r d)
  end.
Lemma firstdip_app_nodip : forall a b d d',
  sqd a d = Some d' ->
  firstdip (a ++ b) d = option_map (fun i => length a + i) (firstdip b d').
Proof.
  induction a as [ | t a IH ]; intros b d d' H; cbn [sqd] in H.
  - injection H as E. rewrite <- E. cbn [app length].
    destruct (firstdip b d); reflexivity.
  - destruct t; cbn [firstdip app length];
      try (rewrite (IH b _ _ H); destruct (firstdip b d'); reflexivity).
    (* TRB, the only survivor: no dip here since sqd stayed defined *)
    destruct d as [ | d0 ]; [ discriminate H | ].
    rewrite (IH b _ _ H). destruct (firstdip b d'); reflexivity.
Qed.
Lemma firstdip_balanced_rb : forall ts r,
  sqd ts 0 = Some 0 ->
  firstdip (ts ++ TRB :: r) 0 = Some (length ts).
Proof.
  intros ts r H. rewrite (firstdip_app_nodip ts (TRB :: r) 0 0 H).
  cbn [firstdip option_map]. f_equal. lia.
Qed.
Lemma app_eq_length : forall {A} (a1 a2 b1 b2 : list A),
  length a1 = length a2 -> (a1 ++ b1)%list = (a2 ++ b2)%list -> a1 = a2 /\ b1 = b2.
Proof.
  induction a1 as [ | x a1 IH ]; intros a2 b1 b2 HL HE; destruct a2 as [ | y a2 ];
    cbn [length app] in *; try discriminate HL.
  - split; [ reflexivity | exact HE ].
  - injection HL as HL. injection HE as -> HE.
    destruct (IH a2 b1 b2 HL HE) as [-> ->]. split; reflexivity.
Qed.
(** THE bracket-cancellation lemma: two balanced prefixes before an unmatched [TRB]
    in the SAME list coincide. *)
Lemma balanced_rb_split : forall ts1 ts2 r1 r2,
  sqd ts1 0 = Some 0 -> sqd ts2 0 = Some 0 ->
  (ts1 ++ TRB :: r1)%list = (ts2 ++ TRB :: r2)%list ->
  ts1 = ts2 /\ r1 = r2.
Proof.
  intros ts1 ts2 r1 r2 H1 H2 HE.
  assert (HL : length ts1 = length ts2).
  { pose proof (firstdip_balanced_rb ts1 r1 H1) as F1.
    pose proof (firstdip_balanced_rb ts2 r2 H2) as F2.
    rewrite HE in F1. rewrite F2 in F1. injection F1 as F1. symmetry. exact F1. }
  destruct (app_eq_length ts1 ts2 (TRB :: r1) (TRB :: r2) HL HE) as [-> HT].
  injection HT as ->. split; reflexivity.
Qed.
(** the type token assignment is balanced *)
Lemma gttokens_ty_balanced : forall t, sqd (gttokens_ty t) 0 = Some 0.
Proof.
  induction t; cbn [gttokens_ty sqd]; try reflexivity; try assumption.
  (* TMap: TMap :: TLB :: (tk ++ TRB :: tv) — key at depth 1, then the value at 0 *)
  rewrite sqd_app, (sqd_up _ _ _ IHt1). cbn [sqd]. exact IHt2.
Qed.
(** the head-identifier string of a token list (the leaf/named discrimination handle) *)
Definition tok0_str (ts : list Token) : string :=
  match ts with TId i :: _ => proj1_sig i | _ => EmptyString end.
(** ★TYPE-LEVEL TOKEN INJECTIVITY, parser-free: equal canonical token lists mean equal
    types.  Leaf collisions with [GTNamed] are killed by the [nominal_type_ident]
    validity (a type keyword is unrepresentable as a [TyName]); [TMap]'s two children
    split by bracket cancellation. *)
Lemma gttokens_ty_inj : forall t1 t2, gttokens_ty t1 = gttokens_ty t2 -> t1 = t2.
Proof.
  induction t1 as [ | | | | | | | | | | | | | | u IHu | u IHu | u IHu | k IHk v IHv | n ];
    destruct t2 as [ | | | | | | | | | | | | | | u2 | u2 | u2 | k2 v2 | n2 ];
    cbn [gttokens_ty]; intro E; try reflexivity; try discriminate E;
    (* GTNamed vs a primitive leaf (either side): the head-string equality contradicts
       the keyword-exclusion validity carried by the TyName *)
    try (exfalso; apply (f_equal tok0_str) in E;
         match goal with nm : TyName |- _ => destruct nm as [sn Hn] end;
         cbn in E; subst sn; cbn in Hn; discriminate Hn).
  - (* GTPtr *) apply (f_equal (@tl Token)) in E. cbn in E.
    rewrite (IHu _ E). reflexivity.
  - (* GTSlice *) apply (f_equal (@tl Token)) in E. apply (f_equal (@tl Token)) in E.
    cbn in E. rewrite (IHu _ E). reflexivity.
  - (* GTChan *) apply (f_equal (@tl Token)) in E. cbn in E.
    rewrite (IHu _ E). reflexivity.
  - (* GTMap *) apply (f_equal (@tl Token)) in E. apply (f_equal (@tl Token)) in E.
    cbn in E.
    destruct (balanced_rb_split _ _ _ _ (gttokens_ty_balanced k) (gttokens_ty_balanced k2) E)
      as [E1 E2].
    rewrite (IHk _ E1), (IHv _ E2). reflexivity.
  - (* GTNamed vs GTNamed *)
    apply (f_equal tok0_str) in E.
    destruct n as [s1 H1]; destruct n2 as [s2 H2]; cbn in E; subst s2.
    assert (EH : H1 = H2) by apply (Eqdep_dec.UIP_dec Bool.bool_dec).
    subst H2. reflexivity.
Qed.
(** ★CANONICAL TYPE UNIQUENESS (CLAUDE.md's [canon_*_unique] shape at the type layer):
    one token list, one type — via functionality + token injectivity, parser-free. *)
Theorem canon_ty_unique : forall t1 t2 ts,
  CanonTy t1 ts -> CanonTy t2 ts -> t1 = t2.
Proof.
  intros t1 t2 ts H1 H2.
  apply canon_ty_tokens in H1. apply canon_ty_tokens in H2. subst.
  apply gttokens_ty_inj. congruence.
Qed.

(** ---- Phase 3b: the THREE-BRACKET balance toolkit (generalizes Phase 3a's square-only
    [sqd] to parens/square/brace) — the foundation for parser-free EXPRESSION token
    injectivity.  [bd ts d]: NET all-kinds bracket depth ([None] on a below-zero dip).
    Canonical expression token lists are uniformly balanced ([gtokens_balanced]): every
    sub-token-list a production wraps returns to depth 0 and never dips — which is what the
    group-split lemmas cancel on.  Uniform (kind-agnostic) depth is sound HERE because
    canonical output is always properly nested (no crossing brackets). *)
Fixpoint bd (ts : list Token) (d : nat) : option nat :=
  match ts with
  | nil => Some d
  | TLP :: r => bd r (S d)
  | TLB :: r => bd r (S d)
  | TLC :: r => bd r (S d)
  | TRP :: r => match d with O => None | S d' => bd r d' end
  | TRB :: r => match d with O => None | S d' => bd r d' end
  | TRC :: r => match d with O => None | S d' => bd r d' end
  | _ :: r => bd r d
  end.
Lemma bd_app : forall a b d,
  bd (a ++ b) d = match bd a d with Some d' => bd b d' | None => None end.
Proof.
  induction a as [ | t a IH ]; intros b d; [ reflexivity | ].
  destruct t; cbn [bd app]; try apply IH; destruct d; solve [ reflexivity | apply IH ].
Qed.
(** the workhorse: a defined prefix passes its exit depth into the suffix scan *)
Lemma bd_app_pass : forall a b d e, bd a d = Some e -> bd (a ++ b) d = bd b e.
Proof. intros a b d e H. rewrite bd_app, H. reflexivity. Qed.
Lemma bd_up : forall ts d e, bd ts d = Some e -> bd ts (S d) = Some (S e).
Proof.
  induction ts as [ | t ts IH ]; intros d e H; cbn [bd] in *.
  - injection H as <-. reflexivity.
  - destruct t; try (apply IH; exact H);
      destruct d as [ | d0 ]; solve [ discriminate H | apply IH; exact H ].
Qed.
(** operator/prefix tokens are never brackets, so they leave the depth unchanged *)
Lemma bd_op_token : forall o r d, bd (op_token o :: r) d = bd r d.
Proof. destruct o; reflexivity. Qed.
Lemma bd_prefix_token : forall o r d, bd (prefix_token o :: r) d = bd r d.
Proof. destruct o; reflexivity. Qed.
(** the parenthesizer preserves balance (either the bare operand, or [TLP … TRP] around it) *)
Lemma bd_gtparen : forall e0, bd (gtokens 0 e0) 0 = Some 0 -> bd (gtparen e0) 0 = Some 0.
Proof.
  intros e0 H. unfold gtparen. destruct (op_needs_paren e0); [ | exact H ].
  cbn [bd]. rewrite (bd_app_pass _ _ _ _ (bd_up _ _ _ H)). reflexivity.
Qed.
(** the comma-joined arg/pair lists are balanced when every element is *)
Lemma gtokens_args_tl_bd : forall r,
  Forall (fun b => bd (gtokens 0 b) 0 = Some 0) r -> bd (gtokens_args_tl r) 0 = Some 0.
Proof.
  induction r as [ | b m IH ]; intro Hf; [ reflexivity | ].
  cbn [gtokens_args_tl bd]. rewrite (bd_app_pass _ _ _ _ (Forall_inv Hf)).
  apply IH. exact (Forall_inv_tail Hf).
Qed.
Lemma gtokens_args_bd : forall args,
  Forall (fun a => bd (gtokens 0 a) 0 = Some 0) args -> bd (gtokens_args args) 0 = Some 0.
Proof.
  intros [ | a r ] Hf; [ reflexivity | ].
  cbn [gtokens_args]. rewrite (bd_app_pass _ _ _ _ (Forall_inv Hf)).
  apply gtokens_args_tl_bd. exact (Forall_inv_tail Hf).
Qed.
Lemma gtokens_pairs_tl_bd : forall r,
  Forall (fun p => bd (gtokens 0 (fst p)) 0 = Some 0 /\ bd (gtokens 0 (snd p)) 0 = Some 0) r ->
  bd (gtokens_pairs_tl r) 0 = Some 0.
Proof.
  induction r as [ | p m IH ]; intro Hf; [ reflexivity | ].
  destruct p as [k v]. pose proof (Forall_inv Hf) as Hp. destruct Hp as [Hk Hv]; cbn in Hk, Hv.
  cbn [gtokens_pairs_tl bd]. rewrite (bd_app_pass _ _ _ _ Hk). cbn [bd].
  rewrite (bd_app_pass _ _ _ _ Hv). apply IH. exact (Forall_inv_tail Hf).
Qed.
Lemma gtokens_pairs_bd : forall kvs,
  Forall (fun p => bd (gtokens 0 (fst p)) 0 = Some 0 /\ bd (gtokens 0 (snd p)) 0 = Some 0) kvs ->
  bd (gtokens_pairs kvs) 0 = Some 0.
Proof.
  intros [ | p r ] Hf; [ reflexivity | ].
  destruct p as [k v]. pose proof (Forall_inv Hf) as Hp. destruct Hp as [Hk Hv]; cbn in Hk, Hv.
  cbn [gtokens_pairs bd]. rewrite (bd_app_pass _ _ _ _ Hk). cbn [bd].
  rewrite (bd_app_pass _ _ _ _ Hv). apply gtokens_pairs_tl_bd. exact (Forall_inv_tail Hf).
Qed.
(** the [bd] (all-kinds) balance of a TYPE token list — types carry only square brackets, but
    [gtokens_balanced] scans with [bd], so it needs this [bd]-form (not Phase 3a's [sqd] one). *)
Lemma gttokens_ty_bd : forall t, bd (gttokens_ty t) 0 = Some 0.
Proof.
  induction t as [ | | | | | | | | | | | | | | u IHu | u IHu | u IHu | k IHk v IHv | n ];
    cbn [gttokens_ty]; try reflexivity.
  - (* GTPtr *) cbn [bd]. exact IHu.
  - (* GTSlice *) cbn [bd]. exact IHu.
  - (* GTChan *) cbn [bd]. exact IHu.
  - (* GTMap *) cbn [bd]. rewrite (bd_app_pass _ _ _ _ (bd_up _ _ _ IHk)). cbn [bd]. exact IHv.
Qed.
(** ★ every canonical expression token list is uniformly balanced *)
Lemma gtokens_balanced : forall e ctx, bd (gtokens ctx e) 0 = Some 0.
Proof.
  induction e using GExpr_ind'; intro ctx.
  - (* EId *) reflexivity.
  - (* EInt *) reflexivity.
  - (* EUn *) rewrite gtokens_EUn, bd_prefix_token.
    destruct (unop_paren o e); [ | exact (IHe 0) ].
    cbn [bd]. rewrite (bd_app_pass _ _ _ _ (bd_up _ _ _ (IHe 0))). reflexivity.
  - (* EBn *) cbn [gtokens].
    assert (Hin : bd (gtokens (binop_prec o) e1 ++ op_token o :: gtokens (S (binop_prec o)) e2) 0 = Some 0)
      by (rewrite (bd_app_pass _ _ _ _ (IHe1 (binop_prec o))), bd_op_token; exact (IHe2 (S (binop_prec o)))).
    destruct (Nat.ltb (binop_prec o) ctx); [ | exact Hin ].
    cbn [bd]. rewrite (bd_app_pass _ _ _ _ (bd_up _ _ _ Hin)). reflexivity.
  - (* ESel *)
    replace (gtokens ctx (ESel e f)) with (gtparen e ++ TDot :: TId f :: nil)%list by reflexivity.
    rewrite (bd_app_pass _ _ _ _ (bd_gtparen e (IHe 0))). reflexivity.
  - (* EIndex *) rewrite gtokens_EIndex, (bd_app_pass _ _ _ _ (bd_gtparen e1 (IHe1 0))).
    cbn [bd]. rewrite (bd_app_pass _ _ _ _ (bd_up _ _ _ (IHe2 0))). reflexivity.
  - (* ESlice *) rewrite gtokens_ESlice, (bd_app_pass _ _ _ _ (bd_gtparen e1 (IHe1 0))).
    cbn [bd]. rewrite (bd_app_pass _ _ _ _ (bd_up _ _ _ (IHe2 0))). cbn [bd].
    rewrite (bd_app_pass _ _ _ _ (bd_up _ _ _ (IHe3 0))). reflexivity.
  - (* ECall *) rewrite gtokens_ECall, (bd_app_pass _ _ _ _ (bd_gtparen e (IHe 0))).
    cbn [bd].
    assert (Ha : bd (gtokens_args args) 0 = Some 0)
      by (apply gtokens_args_bd; eapply Forall_impl; [ | exact H ]; cbn; intros a Ha; exact (Ha 0)).
    rewrite (bd_app_pass _ _ _ _ (bd_up _ _ _ Ha)). reflexivity.
  - (* EAssert *) rewrite gtokens_EAssert, (bd_app_pass _ _ _ _ (bd_gtparen e (IHe 0))).
    cbn [bd]. rewrite (bd_app_pass _ _ _ _ (bd_up _ _ _ (gttokens_ty_bd T))). reflexivity.
  - (* EConv *) rewrite gtokens_EConv, (bd_app_pass _ _ _ _ (gttokens_ty_bd (convty_ty c))).
    cbn [bd]. rewrite (bd_app_pass _ _ _ _ (bd_up _ _ _ (IHe 0))). reflexivity.
  - (* ESliceLit *) rewrite gtokens_ESliceLit. cbn [bd].
    rewrite (bd_app_pass _ _ _ _ (gttokens_ty_bd t)). cbn [bd].
    assert (Ha : bd (gtokens_args es) 0 = Some 0)
      by (apply gtokens_args_bd; eapply Forall_impl; [ | exact H ]; cbn; intros a Ha; exact (Ha 0)).
    rewrite (bd_app_pass _ _ _ _ (bd_up _ _ _ Ha)). reflexivity.
  - (* EMapLit *) rewrite gtokens_EMapLit.
    rewrite (bd_app_pass _ _ _ _ (gttokens_ty_bd (GTMap kt vt))).
    cbn [bd].
    assert (Hp : bd (gtokens_pairs kvs) 0 = Some 0)
      by (apply gtokens_pairs_bd; eapply Forall_impl; [ | exact H ]; cbn;
          intros p Hp; split; [ exact (proj1 Hp 0) | exact (proj2 Hp 0) ]).
    rewrite (bd_app_pass _ _ _ _ (bd_up _ _ _ Hp)). reflexivity.
  - (* EStr *) reflexivity.
  - (* EHex *) reflexivity.
Qed.

(** ---- Phase 3b slice 2: the [last0] group-split tool (plans/canonical-grammar.md).  A trailing
    delimited group [P ++ OPEN :: body ++ CLOSE :: nil] ([P]/[body] balanced) is split by the LAST
    depth-0 TOKEN index, which is the framing [OPEN] at index [length P] — after it depth stays ≥1.
    Computed on the SHARED complete list, so both decompositions force [length P_a = length P_b]. *)
Definition bstep (t : Token) (d : nat) : nat :=
  match t with
  | TLP => S d | TLB => S d | TLC => S d
  | TRP => Nat.pred d | TRB => Nat.pred d | TRC => Nat.pred d
  | _ => d
  end.
Fixpoint nd (ts : list Token) (d : nat) : nat :=   (* nat depth after scanning [ts] from [d] *)
  match ts with nil => d | t :: r => nd r (bstep t d) end.
(** [bd] (option, dip-tracking) and [nd] (nat, clamped) agree while no dip occurs *)
Lemma bd_nd : forall a d e, bd a d = Some e -> nd a d = e.
Proof.
  induction a as [ | t a IH ]; intros d e H; cbn [bd nd] in *.
  - injection H as <-. reflexivity.
  - destruct t; try (apply IH; exact H);
      (destruct d as [ | d0 ]; [ discriminate H | cbn [bstep Nat.pred]; apply IH; exact H ]).
Qed.
(** last depth-0 TOKEN index: scan tracking the last index whose depth-BEFORE is 0 *)
Fixpoint last0_aux (ts : list Token) (d i best : nat) : nat :=
  match ts with
  | nil => best
  | t :: r => last0_aux r (bstep t d) (S i) (if Nat.eqb d 0 then i else best)
  end.
Definition last0 (ts : list Token) : nat := last0_aux ts 0 0 0.
Lemma last0_aux_app : forall a b d i best,
  last0_aux (a ++ b) d i best = last0_aux b (nd a d) (i + length a) (last0_aux a d i best).
Proof.
  induction a as [ | t a IH ]; intros b d i best; cbn [app nd last0_aux length].
  - rewrite PeanoNat.Nat.add_0_r. reflexivity.
  - rewrite IH. rewrite PeanoNat.Nat.add_succ_r. reflexivity.
Qed.
(** scanning from a HIGHER start depth just shifts the running depth (no over-close clamp,
    since [bd a c <> None] means [a] never dips below 0 from [c]).  Induction generalizes [c]. *)
Lemma nd_add : forall a c d, bd a c <> None -> nd a (c + d) = nd a c + d.
Proof.
  induction a as [ | t a IH ]; intros c d H; cbn [bd nd] in *; [ reflexivity | ].
  destruct t; cbn [bstep];
    try (apply IH; exact H);
    try (change (S (c + d)) with (S c + d); apply IH; exact H);
    (destruct c as [ | c0 ]; [ exfalso; apply H; reflexivity | ];
     cbn [Nat.pred]; change (c0 + d) with (c0 + d); apply IH; exact H).
Qed.
(** a prefix of a non-dipping list never dips *)
Lemma bd_prefix_defined : forall k a, bd a 0 <> None -> bd (firstn k a) 0 <> None.
Proof.
  intros k a H. rewrite <- (firstn_skipn k a) in H. rewrite bd_app in H.
  destruct (bd (firstn k a) 0); [ discriminate | exact H ].
Qed.
(** scanning a list all of whose prefix-depths (from [d]) are ≥1 never records a new best *)
Lemma last0_aux_inv : forall a d j best,
  (forall k, k < length a -> 1 <= nd (firstn k a) d) -> last0_aux a d j best = best.
Proof.
  induction a as [ | t a IH ]; intros d j best H; cbn [last0_aux]; [ reflexivity | ].
  assert (Hd : 1 <= d) by (specialize (H 0 (PeanoNat.Nat.lt_0_succ _)); cbn [firstn nd] in H; exact H).
  replace (Nat.eqb d 0) with false by (destruct d; [ inversion Hd | reflexivity ]).
  apply IH. intros k Hk. specialize (H (S k) (proj1 (PeanoNat.Nat.succ_lt_mono _ _) Hk)).
  cbn [firstn nd] in H. exact H.
Qed.
(** ★ the group split: on a trailing balanced group [P ++ OPEN :: body ++ CLOSE :: nil] the last
    depth-0 token is the framing OPEN at index [length P] — [last0] pins the prefix length.  The
    final token [cl] is UNCONSTRAINED (it is at depth-before 1, so never records a best); the
    lemma is therefore stated without a closer hypothesis on [cl]. *)
Lemma last0_group : forall P body op cl,
  bd P 0 = Some 0 -> bd body 0 = Some 0 ->
  (op = TLP \/ op = TLB \/ op = TLC) ->
  last0 (P ++ op :: body ++ cl :: nil) = length P.
Proof.
  intros P body op cl HP Hbody Hop. unfold last0.
  rewrite last0_aux_app, (bd_nd P 0 0 HP).
  cbn [last0_aux]. rewrite PeanoNat.Nat.add_0_l.
  assert (Hopd : bstep op 0 = 1) by (destruct Hop as [E|[E|E]]; subst op; reflexivity).
  rewrite Hopd. cbn [Nat.eqb]. rewrite last0_aux_app.
  assert (Hbnn : bd body 0 <> None) by (rewrite Hbody; discriminate).
  assert (Hbody1 : last0_aux body 1 (S (length P)) (length P) = length P).
  { apply last0_aux_inv. intros k Hk. replace 1 with (0 + 1) by reflexivity.
    rewrite (nd_add (firstn k body) 0 1 (bd_prefix_defined k body Hbnn)). lia. }
  rewrite Hbody1.
  assert (Hndbody : nd body 1 = 1)
    by (apply bd_nd; replace 1 with (S 0) by reflexivity; apply bd_up; exact Hbody).
  rewrite Hndbody. cbn [last0_aux Nat.eqb]. reflexivity.
Qed.

(** ---- the INNER-list / paren split: [balanced_close_split] cancels a balanced prefix before
    a matched CLOSER (used to peel a group's [body] off its final closer, and the paren-wrapped
    operand off its [TRP]).  [bdip]: index of the first token that dips [bd] below the start
    depth ([firstdip]'s all-kinds analogue); a balanced prefix never dips, so in [ts ++ cl :: r]
    the [cl] is the first dip at index [length ts]. *)
Fixpoint bdip (ts : list Token) (d : nat) : option nat :=
  match ts with
  | nil => None
  | TLP :: r => option_map S (bdip r (S d))
  | TLB :: r => option_map S (bdip r (S d))
  | TLC :: r => option_map S (bdip r (S d))
  | TRP :: r => match d with O => Some O | S d' => option_map S (bdip r d') end
  | TRB :: r => match d with O => Some O | S d' => option_map S (bdip r d') end
  | TRC :: r => match d with O => Some O | S d' => option_map S (bdip r d') end
  | _ :: r => option_map S (bdip r d)
  end.
Lemma bdip_app_nodip : forall a b d d',
  bd a d = Some d' ->
  bdip (a ++ b) d = option_map (fun i => length a + i) (bdip b d').
Proof.
  induction a as [ | t a IH ]; intros b d d' H; cbn [bd] in H.
  - injection H as H; subst d'. cbn [app length]. destruct (bdip b d) as [n | ]; reflexivity.
  - destruct t; cbn [bdip app length];
      try (rewrite (IH b _ _ H); destruct (bdip b d'); reflexivity);
      (destruct d as [ | d0 ]; [ discriminate H | rewrite (IH b _ _ H); destruct (bdip b d'); reflexivity ]).
Qed.
(** both split lemmas take the CLEAN closer condition [cl = TRP \/ TRB \/ TRC]; the operational
    [bdip (cl :: r) 0 = Some 0] never leaves a proof body. *)
Lemma bdip_balanced_close : forall ts cl r,
  bd ts 0 = Some 0 -> (cl = TRP \/ cl = TRB \/ cl = TRC) ->
  bdip (ts ++ cl :: r) 0 = Some (length ts).
Proof.
  intros ts cl r Hb Hcl.
  assert (Hbdip : bdip (cl :: r) 0 = Some 0) by (destruct Hcl as [E|[E|E]]; subst cl; reflexivity).
  rewrite (bdip_app_nodip ts (cl :: r) 0 0 Hb), Hbdip. cbn [option_map].
  f_equal. apply PeanoNat.Nat.add_0_r.
Qed.
Lemma balanced_close_split : forall cl ts1 ts2 r1 r2,
  (cl = TRP \/ cl = TRB \/ cl = TRC) ->
  bd ts1 0 = Some 0 -> bd ts2 0 = Some 0 ->
  (ts1 ++ cl :: r1)%list = (ts2 ++ cl :: r2)%list ->
  ts1 = ts2 /\ r1 = r2.
Proof.
  intros cl ts1 ts2 r1 r2 Hcl H1 H2 HE.
  assert (HL : length ts1 = length ts2).
  { pose proof (bdip_balanced_close ts1 cl r1 H1 Hcl) as F1.
    pose proof (bdip_balanced_close ts2 cl r2 H2 Hcl) as F2.
    rewrite HE in F1. rewrite F2 in F1. injection F1 as F1. symmetry. exact F1. }
  destruct (app_eq_length ts1 ts2 (cl :: r1) (cl :: r2) HL HE) as [-> HT].
  injection HT as ->. split; reflexivity.
Qed.

(** ---- the SEPARATOR split.  [TComma]/[TColon] are DEPTH-NEUTRAL (not closers), so [bdip] cannot
    find them.  [fsep ts d]: index of the first [TComma]/[TColon] at depth 0.  A balanced list with
    NO depth-0 separator ([fsep ts 0 = None]) followed by one has that separator FIRST at index
    [length ts] — [sep_split] cancels it, the tool the [gtokens_args]/[gtokens_pairs] list
    injectivity will use.  Clean interfaces: the closer/separator hypotheses are token disjunctions. *)
Fixpoint fsep (ts : list Token) (d : nat) : option nat :=
  match ts with
  | nil => None
  | TLP :: r => option_map S (fsep r (S d))
  | TLB :: r => option_map S (fsep r (S d))
  | TLC :: r => option_map S (fsep r (S d))
  | TRP :: r => option_map S (fsep r (Nat.pred d))
  | TRB :: r => option_map S (fsep r (Nat.pred d))
  | TRC :: r => option_map S (fsep r (Nat.pred d))
  | TComma :: r => match d with O => Some O | S _ => option_map S (fsep r d) end
  | TColon :: r => match d with O => Some O | S _ => option_map S (fsep r d) end
  | _ :: r => option_map S (fsep r d)
  end.
Lemma option_map_S_none : forall x : option nat, option_map S x = None -> x = None.
Proof. intros [i | ]; cbn [option_map]; [ discriminate | reflexivity ]. Qed.
Lemma fsep_app_none : forall a b d e,
  fsep a d = None -> bd a d = Some e ->
  fsep (a ++ b) d = option_map (fun i => length a + i) (fsep b e).
Proof.
  induction a as [ | t a IH ]; intros b d e Hf Hb.
  - cbn [bd] in Hb. injection Hb as <-. cbn [app fsep length].
    destruct (fsep b d) as [n | ]; reflexivity.
  - destruct t; cbn [bd fsep app length] in Hf, Hb |- *;
      try (destruct d as [ | d0 ]; [ solve [ discriminate Hf | discriminate Hb ]
                                    | cbn [fsep bd Nat.pred] in Hf, Hb |- * ]);
      apply option_map_S_none in Hf;
      lazymatch goal with
      | [ |- context [ fsep (a ++ b) ?dd ] ] => rewrite (IH b dd e Hf Hb)
      end;
      cbn [option_map]; destruct (fsep b e) as [n | ]; cbn [option_map];
      (reflexivity || (f_equal; lia)).
Qed.
Lemma fsep_balanced_sep : forall ts sep r,
  bd ts 0 = Some 0 -> fsep ts 0 = None -> (sep = TComma \/ sep = TColon) ->
  fsep (ts ++ sep :: r) 0 = Some (length ts).
Proof.
  intros ts sep r Hb Hf Hsep.
  rewrite (fsep_app_none ts (sep :: r) 0 0 Hf Hb).
  assert (Hs0 : fsep (sep :: r) 0 = Some 0) by (destruct Hsep as [E|E]; subst sep; reflexivity).
  rewrite Hs0. cbn [option_map]. f_equal. apply PeanoNat.Nat.add_0_r.
Qed.
Lemma sep_split : forall sep ts1 ts2 r1 r2,
  (sep = TComma \/ sep = TColon) ->
  bd ts1 0 = Some 0 -> bd ts2 0 = Some 0 -> fsep ts1 0 = None -> fsep ts2 0 = None ->
  (ts1 ++ sep :: r1)%list = (ts2 ++ sep :: r2)%list ->
  ts1 = ts2 /\ r1 = r2.
Proof.
  intros sep ts1 ts2 r1 r2 Hsep H1 H2 F1 F2 HE.
  assert (HL : length ts1 = length ts2).
  { pose proof (fsep_balanced_sep ts1 sep r1 H1 F1 Hsep) as G1.
    pose proof (fsep_balanced_sep ts2 sep r2 H2 F2 Hsep) as G2.
    rewrite HE in G1. rewrite G2 in G1. injection G1 as G1. symmetry. exact G1. }
  destruct (app_eq_length ts1 ts2 (sep :: r1) (sep :: r2) HL HE) as [-> HT].
  injection HT as ->. split; reflexivity.
Qed.
(** ---- Phase 3b slice 2d: [no_depth0_sep] — a SINGLE expression's canonical tokens expose NO
    depth-0 separator ([TComma]/[TColon] occur only INSIDE brackets, at depth ≥ 1).  This discharges
    the [fsep _ 0 = None] premises of [sep_split]; the [gtokens_args]/[gtokens_pairs] list injectivity
    (next slice) rests on it.  Proved on the token FUNCTIONS (structural on [GExpr_ind']), never via
    [parse].  Two shifted forms are needed: [bd (gtokens ..) d = Some d] (any start depth), and the
    args/pairs [fsep] vanish at start depth [S d] — their top-level separators sit at depth ≥ 1, where
    [fsep] (which records only at depth 0) skips them. *)
Lemma bd_gtokens_d : forall e ctx d, bd (gtokens ctx e) d = Some d.
Proof. intros e ctx d. induction d as [ | d IH ]; [ apply gtokens_balanced | apply bd_up; exact IH ]. Qed.
Lemma bd_ty_d : forall t d, bd (gttokens_ty t) d = Some d.
Proof. intros t d. induction d as [ | d IH ]; [ apply gttokens_ty_bd | apply bd_up; exact IH ]. Qed.
Lemma bd_gtparen_d : forall e0 d, bd (gtparen e0) d = Some d.
Proof.
  intros e0 d. unfold gtparen. destruct (op_needs_paren e0); [ | apply bd_gtokens_d ].
  cbn [bd]. rewrite (bd_app_pass _ _ _ _ (bd_gtokens_d e0 0 (S d))). reflexivity.
Qed.
Lemma bd_args_d : forall args d, bd (gtokens_args args) d = Some d.
Proof.
  intros args d. induction d as [ | d IH ];
    [ apply gtokens_args_bd, Forall_forall; intros a _; apply gtokens_balanced
    | apply bd_up; exact IH ].
Qed.
Lemma bd_pairs_d : forall kvs d, bd (gtokens_pairs kvs) d = Some d.
Proof.
  intros kvs d. induction d as [ | d IH ];
    [ apply gtokens_pairs_bd, Forall_forall; intros p _; split; apply gtokens_balanced
    | apply bd_up; exact IH ].
Qed.
(** operator/prefix tokens are never separators, so [fsep] steps past them unchanged (the [fsep] twins
    of [bd_op_token]/[bd_prefix_token]). *)
Lemma fsep_prefix_token : forall o r d, fsep (prefix_token o :: r) d = option_map S (fsep r d).
Proof. destruct o; reflexivity. Qed.
Lemma fsep_op_token : forall o r d, fsep (op_token o :: r) d = option_map S (fsep r d).
Proof. destruct o; reflexivity. Qed.
(** TYPE token lists carry NO [TComma]/[TColon] (only ids/brackets/[*]/[chan]/[map]), so [fsep] never
    records — at any start depth. *)
Lemma fsep_ty_none : forall t d, fsep (gttokens_ty t) d = None.
Proof.
  induction t as [ | | | | | | | | | | | | | | u IHu | u IHu | u IHu | k IHk v IHv | n ];
    intro d; cbn [gttokens_ty]; try reflexivity.
  - (* GTPtr *) cbn [fsep]. rewrite IHu. reflexivity.
  - (* GTSlice *) cbn [fsep Nat.pred]. rewrite IHu. reflexivity.
  - (* GTChan *) cbn [fsep]. rewrite IHu. reflexivity.
  - (* GTMap *) cbn [fsep Nat.pred].
    rewrite (fsep_app_none (gttokens_ty k) (TRB :: gttokens_ty v) (S d) (S d) (IHk (S d)) (bd_ty_d k (S d))).
    cbn [fsep Nat.pred]. rewrite IHv. reflexivity.
Qed.
(** the parenthesizer keeps [fsep] at [None]: bare = the operand's tokens; [TLP … TRP] wraps them one
    deeper, so any inner separator would need depth 0 but sits at depth ≥ 1. *)
Lemma fsep_gtparen : forall e0 d,
  (forall ctx d', fsep (gtokens ctx e0) d' = None) -> fsep (gtparen e0) d = None.
Proof.
  intros e0 d IH. unfold gtparen. destruct (op_needs_paren e0); [ | apply IH ].
  cbn [fsep].
  rewrite (fsep_app_none (gtokens 0 e0) (TRP :: nil) (S d) (S d) (IH 0 (S d)) (bd_gtokens_d e0 0 (S d))).
  reflexivity.
Qed.
(** the comma/colon-joined arg/pair lists have NO depth-0 separator once scanned at depth [S d] (they
    live one bracket deep inside their group): every top-level [TComma]/[TColon] sits at depth [S d]. *)
Lemma fsep_args_tl : forall r d,
  Forall (fun b => forall ctx d', fsep (gtokens ctx b) d' = None) r ->
  fsep (gtokens_args_tl r) (S d) = None.
Proof.
  induction r as [ | b m IH ]; intros d Hf; [ reflexivity | ].
  cbn [gtokens_args_tl fsep].
  rewrite (fsep_app_none (gtokens 0 b) (gtokens_args_tl m) (S d) (S d)
             (Forall_inv Hf 0 (S d)) (bd_gtokens_d b 0 (S d))),
          (IH d (Forall_inv_tail Hf)).
  reflexivity.
Qed.
Lemma fsep_args : forall args d,
  Forall (fun a => forall ctx d', fsep (gtokens ctx a) d' = None) args ->
  fsep (gtokens_args args) (S d) = None.
Proof.
  intros [ | a r ] d Hf; [ reflexivity | ].
  cbn [gtokens_args].
  rewrite (fsep_app_none (gtokens 0 a) (gtokens_args_tl r) (S d) (S d)
             (Forall_inv Hf 0 (S d)) (bd_gtokens_d a 0 (S d))),
          (fsep_args_tl r d (Forall_inv_tail Hf)).
  reflexivity.
Qed.
Lemma fsep_pairs_tl : forall r d,
  Forall (fun p => (forall ctx d', fsep (gtokens ctx (fst p)) d' = None)
                /\ (forall ctx d', fsep (gtokens ctx (snd p)) d' = None)) r ->
  fsep (gtokens_pairs_tl r) (S d) = None.
Proof.
  induction r as [ | p m IH ]; intros d Hf; [ reflexivity | ].
  destruct p as [k v]. pose proof (Forall_inv Hf) as Hp. destruct Hp as [Hk Hv]; cbn in Hk, Hv.
  cbn [gtokens_pairs_tl fsep].
  rewrite (fsep_app_none (gtokens 0 k) (TColon :: (gtokens 0 v ++ gtokens_pairs_tl m)) (S d) (S d)
             (Hk 0 (S d)) (bd_gtokens_d k 0 (S d))).
  cbn [fsep].
  rewrite (fsep_app_none (gtokens 0 v) (gtokens_pairs_tl m) (S d) (S d)
             (Hv 0 (S d)) (bd_gtokens_d v 0 (S d))),
          (IH d (Forall_inv_tail Hf)).
  reflexivity.
Qed.
Lemma fsep_pairs : forall kvs d,
  Forall (fun p => (forall ctx d', fsep (gtokens ctx (fst p)) d' = None)
                /\ (forall ctx d', fsep (gtokens ctx (snd p)) d' = None)) kvs ->
  fsep (gtokens_pairs kvs) (S d) = None.
Proof.
  intros [ | p r ] d Hf; [ reflexivity | ].
  destruct p as [k v]. pose proof (Forall_inv Hf) as Hp. destruct Hp as [Hk Hv]; cbn in Hk, Hv.
  cbn [gtokens_pairs].
  rewrite (fsep_app_none (gtokens 0 k) (TColon :: (gtokens 0 v ++ gtokens_pairs_tl r)) (S d) (S d)
             (Hk 0 (S d)) (bd_gtokens_d k 0 (S d))).
  cbn [fsep].
  rewrite (fsep_app_none (gtokens 0 v) (gtokens_pairs_tl r) (S d) (S d)
             (Hv 0 (S d)) (bd_gtokens_d v 0 (S d))),
          (fsep_pairs_tl r d (Forall_inv_tail Hf)).
  reflexivity.
Qed.
(** ★ every SINGLE canonical expression token list has NO depth-0 separator — [fsep] vanishes at any
    start depth (separators are always bracket-nested).  Structural on [GExpr_ind']. *)
Lemma no_depth0_sep : forall e ctx d, fsep (gtokens ctx e) d = None.
Proof.
  induction e using GExpr_ind'; intros ctx d.
  - (* EId *) reflexivity.
  - (* EInt *) reflexivity.
  - (* EUn *) rewrite gtokens_EUn, fsep_prefix_token.
    destruct (unop_paren o e).
    + cbn [fsep].
      rewrite (fsep_app_none (gtokens 0 e) (TRP :: nil) (S d) (S d) (IHe 0 (S d)) (bd_gtokens_d e 0 (S d))).
      reflexivity.
    + rewrite (IHe 0 d). reflexivity.
  - (* EBn *) cbn [gtokens].
    assert (Hbd : forall dd, bd (gtokens (binop_prec o) e1 ++ op_token o :: gtokens (S (binop_prec o)) e2) dd = Some dd)
      by (intro dd; rewrite (bd_app_pass _ _ _ _ (bd_gtokens_d e1 (binop_prec o) dd)), bd_op_token; apply bd_gtokens_d).
    assert (Hin : forall dd, fsep (gtokens (binop_prec o) e1 ++ op_token o :: gtokens (S (binop_prec o)) e2) dd = None)
      by (intro dd; rewrite (fsep_app_none _ _ _ _ (IHe1 (binop_prec o) dd) (bd_gtokens_d e1 (binop_prec o) dd)),
            fsep_op_token, (IHe2 (S (binop_prec o)) dd); reflexivity).
    destruct (Nat.ltb (binop_prec o) ctx).
    + cbn [fsep]. rewrite (fsep_app_none _ _ _ _ (Hin (S d)) (Hbd (S d))). reflexivity.
    + apply Hin.
  - (* ESel *) rewrite gtokens_ESel.
    rewrite (fsep_app_none _ _ _ _ (fsep_gtparen e d IHe) (bd_gtparen_d e d)). reflexivity.
  - (* EIndex *) rewrite gtokens_EIndex.
    rewrite (fsep_app_none _ _ _ _ (fsep_gtparen e1 d IHe1) (bd_gtparen_d e1 d)).
    cbn [fsep].
    rewrite (fsep_app_none _ _ _ _ (IHe2 0 (S d)) (bd_gtokens_d e2 0 (S d))). reflexivity.
  - (* ESlice *) rewrite gtokens_ESlice.
    rewrite (fsep_app_none _ _ _ _ (fsep_gtparen e1 d IHe1) (bd_gtparen_d e1 d)).
    cbn [fsep].
    rewrite (fsep_app_none _ _ _ _ (IHe2 0 (S d)) (bd_gtokens_d e2 0 (S d))).
    cbn [fsep].
    rewrite (fsep_app_none _ _ _ _ (IHe3 0 (S d)) (bd_gtokens_d e3 0 (S d))). reflexivity.
  - (* ECall *) rewrite gtokens_ECall.
    rewrite (fsep_app_none _ _ _ _ (fsep_gtparen e d IHe) (bd_gtparen_d e d)).
    cbn [fsep].
    rewrite (fsep_app_none _ _ _ _ (fsep_args args d H) (bd_args_d args (S d))). reflexivity.
  - (* EAssert *) rewrite gtokens_EAssert.
    rewrite (fsep_app_none _ _ _ _ (fsep_gtparen e d IHe) (bd_gtparen_d e d)).
    cbn [fsep].
    rewrite (fsep_app_none _ _ _ _ (fsep_ty_none T (S d)) (bd_ty_d T (S d))). reflexivity.
  - (* EConv *) rewrite gtokens_EConv.
    rewrite (fsep_app_none _ _ _ _ (fsep_ty_none (convty_ty c) d) (bd_ty_d (convty_ty c) d)).
    cbn [fsep].
    rewrite (fsep_app_none _ _ _ _ (IHe 0 (S d)) (bd_gtokens_d e 0 (S d))). reflexivity.
  - (* ESliceLit *) rewrite gtokens_ESliceLit. cbn [fsep Nat.pred].
    rewrite (fsep_app_none _ _ _ _ (fsep_ty_none t d) (bd_ty_d t d)).
    cbn [fsep].
    rewrite (fsep_app_none _ _ _ _ (fsep_args es d H) (bd_args_d es (S d))). reflexivity.
  - (* EMapLit *) rewrite gtokens_EMapLit.
    rewrite (fsep_app_none _ _ _ _ (fsep_ty_none (GTMap kt vt) d) (bd_ty_d (GTMap kt vt) d)).
    cbn [fsep].
    rewrite (fsep_app_none _ _ _ _ (fsep_pairs kvs d H) (bd_pairs_d kvs (S d))). reflexivity.
  - (* EStr *) reflexivity.
  - (* EHex *) reflexivity.
Qed.

(** ---- Phase 3b slice 2e: [gtokens_args_inj] — the ARGUMENT-list injectivity (ECall / ESliceLit
    element lists).  Given element injectivity (the outer [gtokens_inj] IH, carried as a [Forall]),
    equal [gtokens_args] lists ARE equal argument lists.  The split: [gtokens_args (a::b::m) =
    gtokens 0 a ++ TComma :: gtokens_args (b::m)], so [sep_split] (fed by [no_depth0_sep] +
    [gtokens_balanced]) peels the first element off the first top-level [TComma] and recurses;
    [no_depth0_sep] also DISCRIMINATES lengths — a singleton's tokens carry no depth-0 comma, a
    multi-element list's do (via [fsep]).  Parser-free. *)
Lemma app_cons_nonnil : forall (A : Type) (l1 : list A) (x : A) (l2 : list A), (l1 ++ x :: l2)%list <> nil.
Proof. intros A l1 x l2. destruct l1; discriminate. Qed.
Lemma gtokens_nonnil : forall ctx e, gtokens ctx e <> nil.
Proof.
  intros ctx e; destruct e; cbn [gtokens];
    repeat match goal with |- context [ if ?b then _ else _ ] => destruct b end;
    solve [ discriminate | apply app_cons_nonnil ].
Qed.
Lemma gtokens_args_nonnil : forall a r, gtokens_args (a :: r) <> nil.
Proof.
  intros a r. cbn [gtokens_args]. destruct (gtokens 0 a) eqn:E;
    [ exfalso; exact (gtokens_nonnil 0 a E) | discriminate ].
Qed.
Lemma gtokens_args_single : forall a, gtokens_args (a :: nil) = gtokens 0 a.
Proof. intro a. cbn [gtokens_args gtokens_args_tl]. apply app_nil_r. Qed.
Lemma gtokens_args_cons2 : forall a b m,
  gtokens_args (a :: b :: m) = (gtokens 0 a ++ TComma :: gtokens_args (b :: m))%list.
Proof. intros a b m. cbn [gtokens_args gtokens_args_tl]. reflexivity. Qed.
Lemma gtokens_args_inj : forall args1 args2,
  Forall (fun a => forall a' c, gtokens c a = gtokens c a' -> a = a') args1 ->
  gtokens_args args1 = gtokens_args args2 -> args1 = args2.
Proof.
  induction args1 as [ | a1 r1 IH ]; intros args2 Hall HE.
  - destruct args2 as [ | a2 r2 ]; [ reflexivity | ].
    exfalso. exact (gtokens_args_nonnil a2 r2 (eq_sym HE)).
  - destruct args2 as [ | a2 r2 ].
    + exfalso. exact (gtokens_args_nonnil a1 r1 HE).
    + destruct r1 as [ | b1 m1 ]; destruct r2 as [ | b2 m2 ].
      * rewrite !gtokens_args_single in HE.
        f_equal. exact (Forall_inv Hall a2 0 HE).
      * exfalso. rewrite gtokens_args_single, gtokens_args_cons2 in HE.
        pose proof (no_depth0_sep a1 0 0) as Hf. rewrite HE in Hf.
        rewrite (fsep_balanced_sep (gtokens 0 a2) TComma (gtokens_args (b2 :: m2))
                   (gtokens_balanced a2 0) (no_depth0_sep a2 0 0) (or_introl eq_refl)) in Hf.
        discriminate Hf.
      * exfalso. rewrite gtokens_args_single, gtokens_args_cons2 in HE.
        pose proof (no_depth0_sep a2 0 0) as Hf. rewrite <- HE in Hf.
        rewrite (fsep_balanced_sep (gtokens 0 a1) TComma (gtokens_args (b1 :: m1))
                   (gtokens_balanced a1 0) (no_depth0_sep a1 0 0) (or_introl eq_refl)) in Hf.
        discriminate Hf.
      * rewrite !gtokens_args_cons2 in HE.
        destruct (sep_split TComma (gtokens 0 a1) (gtokens 0 a2)
                   (gtokens_args (b1 :: m1)) (gtokens_args (b2 :: m2))
                   (or_introl eq_refl) (gtokens_balanced a1 0) (gtokens_balanced a2 0)
                   (no_depth0_sep a1 0 0) (no_depth0_sep a2 0 0) HE) as [Ha Htail].
        f_equal;
          [ exact (Forall_inv Hall a2 0 Ha)
          | exact (IH (b2 :: m2) (Forall_inv_tail Hall) Htail) ].
Qed.

(** ---- Phase 3b slice 2f: [gtokens_pairs_inj] — the KEYED-PAIR-list injectivity (EMapLit).  Each pair
    prints as `k TColon v`, pairs comma-joined, so a pair carries an INTERNAL depth-0 `TColon` besides the
    inter-pair `TComma`.  Peeling one pair is therefore TWO `sep_split`s: first on `TColon` (the key ends
    at the first depth-0 separator, since [no_depth0_sep] gives the key no depth-0 sep), then on `TComma`
    (the value ends at the next), then recurse.  Length discrimination is again the [no_depth0_sep]/[fsep]
    None-vs-Some contradiction.  Parser-free. *)
Lemma gtokens_pairs_tl_cons : forall p m, gtokens_pairs_tl (p :: m) = (TComma :: gtokens_pairs (p :: m))%list.
Proof. intros [k v] m. cbn [gtokens_pairs_tl gtokens_pairs]. reflexivity. Qed.
Lemma gtokens_pairs_nonnil : forall p r, gtokens_pairs (p :: r) <> nil.
Proof.
  intros [k v] r. cbn [gtokens_pairs]. destruct (gtokens 0 k) eqn:E;
    [ exfalso; exact (gtokens_nonnil 0 k E) | discriminate ].
Qed.
Lemma gtokens_pairs_single : forall k v,
  gtokens_pairs ((k, v) :: nil) = (gtokens 0 k ++ TColon :: gtokens 0 v)%list.
Proof. intros k v. cbn [gtokens_pairs gtokens_pairs_tl]. rewrite app_nil_r. reflexivity. Qed.
Lemma gtokens_pairs_cons2 : forall k v q m,
  gtokens_pairs ((k, v) :: q :: m) =
  (gtokens 0 k ++ TColon :: (gtokens 0 v ++ TComma :: gtokens_pairs (q :: m)))%list.
Proof. intros k v q m. cbn [gtokens_pairs]. rewrite gtokens_pairs_tl_cons. reflexivity. Qed.
Lemma gtokens_pairs_inj : forall kvs1 kvs2,
  Forall (fun p => (forall a' c, gtokens c (fst p) = gtokens c a' -> fst p = a')
                /\ (forall a' c, gtokens c (snd p) = gtokens c a' -> snd p = a')) kvs1 ->
  gtokens_pairs kvs1 = gtokens_pairs kvs2 -> kvs1 = kvs2.
Proof.
  induction kvs1 as [ | [k1 v1] r1 IH ]; intros kvs2 Hall HE.
  - destruct kvs2 as [ | p2 r2 ]; [ reflexivity | ].
    exfalso. exact (gtokens_pairs_nonnil p2 r2 (eq_sym HE)).
  - destruct kvs2 as [ | [k2 v2] r2 ].
    + exfalso. exact (gtokens_pairs_nonnil (k1, v1) r1 HE).
    + pose proof (Forall_inv Hall) as Hp1. destruct Hp1 as [Hk1 Hv1]; cbn [fst snd] in Hk1, Hv1.
      destruct r1 as [ | q1 m1 ]; destruct r2 as [ | q2 m2 ].
      * rewrite !gtokens_pairs_single in HE.
        destruct (sep_split TColon (gtokens 0 k1) (gtokens 0 k2) (gtokens 0 v1) (gtokens 0 v2)
                   (or_intror eq_refl) (gtokens_balanced k1 0) (gtokens_balanced k2 0)
                   (no_depth0_sep k1 0 0) (no_depth0_sep k2 0 0) HE) as [Hk Hv].
        assert (k1 = k2) as -> by exact (Hk1 k2 0 Hk).
        assert (v1 = v2) as -> by exact (Hv1 v2 0 Hv). reflexivity.
      * exfalso. rewrite gtokens_pairs_single, gtokens_pairs_cons2 in HE.
        destruct (sep_split TColon (gtokens 0 k1) (gtokens 0 k2)
                   (gtokens 0 v1) (gtokens 0 v2 ++ TComma :: gtokens_pairs (q2 :: m2))
                   (or_intror eq_refl) (gtokens_balanced k1 0) (gtokens_balanced k2 0)
                   (no_depth0_sep k1 0 0) (no_depth0_sep k2 0 0) HE) as [_ Hrest].
        pose proof (no_depth0_sep v1 0 0) as Hf. rewrite Hrest in Hf.
        rewrite (fsep_balanced_sep (gtokens 0 v2) TComma (gtokens_pairs (q2 :: m2))
                   (gtokens_balanced v2 0) (no_depth0_sep v2 0 0) (or_introl eq_refl)) in Hf.
        discriminate Hf.
      * exfalso. rewrite gtokens_pairs_single, gtokens_pairs_cons2 in HE.
        destruct (sep_split TColon (gtokens 0 k1) (gtokens 0 k2)
                   (gtokens 0 v1 ++ TComma :: gtokens_pairs (q1 :: m1)) (gtokens 0 v2)
                   (or_intror eq_refl) (gtokens_balanced k1 0) (gtokens_balanced k2 0)
                   (no_depth0_sep k1 0 0) (no_depth0_sep k2 0 0) HE) as [_ Hrest].
        pose proof (no_depth0_sep v2 0 0) as Hf. rewrite <- Hrest in Hf.
        rewrite (fsep_balanced_sep (gtokens 0 v1) TComma (gtokens_pairs (q1 :: m1))
                   (gtokens_balanced v1 0) (no_depth0_sep v1 0 0) (or_introl eq_refl)) in Hf.
        discriminate Hf.
      * rewrite !gtokens_pairs_cons2 in HE.
        destruct (sep_split TColon (gtokens 0 k1) (gtokens 0 k2)
                   (gtokens 0 v1 ++ TComma :: gtokens_pairs (q1 :: m1))
                   (gtokens 0 v2 ++ TComma :: gtokens_pairs (q2 :: m2))
                   (or_intror eq_refl) (gtokens_balanced k1 0) (gtokens_balanced k2 0)
                   (no_depth0_sep k1 0 0) (no_depth0_sep k2 0 0) HE) as [Hk Hrest].
        destruct (sep_split TComma (gtokens 0 v1) (gtokens 0 v2)
                   (gtokens_pairs (q1 :: m1)) (gtokens_pairs (q2 :: m2))
                   (or_introl eq_refl) (gtokens_balanced v1 0) (gtokens_balanced v2 0)
                   (no_depth0_sep v1 0 0) (no_depth0_sep v2 0 0) Hrest) as [Hv Htail].
        assert (k1 = k2) as -> by exact (Hk1 k2 0 Hk).
        assert (v1 = v2) as -> by exact (Hv1 v2 0 Hv).
        f_equal. exact (IH (q2 :: m2) (Forall_inv_tail Hall) Htail).
Qed.

(** ---- Phase 3b slice 2g: the PAREN/BARE operand discrimination.  [gtparen] wraps an operand in
    [TLP … TRP] iff [op_needs_paren] ([true] exactly for [EUn]/[EBn]).  The one hard sub-step of the
    operand step is: a BARE non-operator expression's tokens can NEVER equal a single parenthesized
    group [TLP :: g ++ TRP :: nil].  THREE discrimination paths by constructor:
    (a) atoms / [EConv] / [ESliceLit] / [EMapLit] — the LEADING token is not [TLP] (leading-token
        mismatch);
    (b) [EIndex]/[ESlice]/[ECall]/[EAssert] — end in a bracket group whose OPENER sits at a depth-0
        position INTERIOR to the list (at [length (gtparen operand)], or one past it for [EAssert]'s
        [.(T)]), so [last0 ≥ 1] via [last0_group] — whereas the single group has [last0 = 0] (only the
        leading [TLP] at depth 0);
    (c) [ESel] — no trailing bracket group, so discriminated by its LAST token ([TId f] ≠ [TRP], via
        [app_inj_tail]).  Parser-free. *)
Lemma gtparen_nonnil : forall e0, gtparen e0 <> nil.
Proof. intro e0. unfold gtparen. destruct (op_needs_paren e0); [ discriminate | apply gtokens_nonnil ]. Qed.
Lemma last0_paren_group : forall g, bd g 0 = Some 0 -> last0 (TLP :: (g ++ TRP :: nil)) = 0.
Proof. intros g Hg. exact (last0_group nil g TLP TRP eq_refl Hg (or_introl eq_refl)). Qed.
Lemma bare_not_paren_group : forall e g,
  op_needs_paren e = false -> bd g 0 = Some 0 -> gtokens 0 e <> (TLP :: (g ++ TRP :: nil))%list.
Proof.
  intros e g Hop Hg;
    destruct e as [ i | z | o e0 | o e1 e2 | e0 f | e0 i0 | e0 lo hi | e0 args | e0 T | c e0
                  | t es | kt vt kvs | s | zc ];
    cbn [op_needs_paren] in Hop; try discriminate Hop.
  - (* EId *) discriminate.
  - (* EInt *) discriminate.
  - (* ESel *) rewrite gtokens_ESel. intro HE.
    assert (Hr : (gtparen e0 ++ TDot :: TId f :: nil = (gtparen e0 ++ TDot :: nil) ++ TId f :: nil)%list)
      by (rewrite <- app_assoc; reflexivity).
    rewrite Hr in HE. change (TLP :: (g ++ TRP :: nil))%list with ((TLP :: g) ++ TRP :: nil)%list in HE.
    apply app_inj_tail in HE. destruct HE as [_ HE]. discriminate HE.
  - (* EIndex *) rewrite gtokens_EIndex. intro HE.
    pose proof (f_equal last0 HE) as HL.
    rewrite (last0_group (gtparen e0) (gtokens 0 i0) TLB TRB
               (bd_gtparen e0 (gtokens_balanced e0 0)) (gtokens_balanced i0 0)
               (or_intror (or_introl eq_refl))) in HL.
    rewrite (last0_paren_group g Hg) in HL.
    apply length_zero_iff_nil in HL. exact (gtparen_nonnil e0 HL).
  - (* ESlice *) rewrite gtokens_ESlice. intro HE.
    pose proof (f_equal last0 HE) as HL.
    assert (Hbody : bd (gtokens 0 lo ++ TColon :: gtokens 0 hi)%list 0 = Some 0)
      by (rewrite (bd_app_pass _ _ _ _ (gtokens_balanced lo 0)); cbn [bd]; apply gtokens_balanced).
    assert (Hr : (gtparen e0 ++ TLB :: (gtokens 0 lo ++ TColon :: (gtokens 0 hi ++ TRB :: nil))
               = gtparen e0 ++ TLB :: ((gtokens 0 lo ++ TColon :: gtokens 0 hi) ++ TRB :: nil))%list)
      by (rewrite <- (app_assoc (gtokens 0 lo) (TColon :: gtokens 0 hi) (TRB :: nil)); reflexivity).
    rewrite Hr in HL.
    rewrite (last0_group (gtparen e0) (gtokens 0 lo ++ TColon :: gtokens 0 hi)%list TLB TRB
               (bd_gtparen e0 (gtokens_balanced e0 0)) Hbody (or_intror (or_introl eq_refl))) in HL.
    rewrite (last0_paren_group g Hg) in HL.
    apply length_zero_iff_nil in HL. exact (gtparen_nonnil e0 HL).
  - (* ECall *) rewrite gtokens_ECall. intro HE.
    pose proof (f_equal last0 HE) as HL.
    rewrite (last0_group (gtparen e0) (gtokens_args args) TLP TRP
               (bd_gtparen e0 (gtokens_balanced e0 0)) (bd_args_d args 0) (or_introl eq_refl)) in HL.
    rewrite (last0_paren_group g Hg) in HL.
    apply length_zero_iff_nil in HL. exact (gtparen_nonnil e0 HL).
  - (* EAssert *) rewrite gtokens_EAssert. intro HE.
    pose proof (f_equal last0 HE) as HL.
    assert (HP : bd (gtparen e0 ++ TDot :: nil)%list 0 = Some 0)
      by (rewrite (bd_app_pass _ _ _ _ (bd_gtparen e0 (gtokens_balanced e0 0))); reflexivity).
    assert (Hr : (gtparen e0 ++ TDot :: TLP :: (gttokens_ty T ++ TRP :: nil)
               = (gtparen e0 ++ TDot :: nil) ++ TLP :: (gttokens_ty T ++ TRP :: nil))%list)
      by (rewrite <- app_assoc; reflexivity).
    rewrite Hr in HL.
    rewrite (last0_group (gtparen e0 ++ TDot :: nil)%list (gttokens_ty T) TLP TRP HP
               (gttokens_ty_bd T) (or_introl eq_refl)) in HL.
    rewrite (last0_paren_group g Hg) in HL.
    rewrite List.length_app in HL. cbn [length] in HL. lia.
  - (* EConv *) rewrite gtokens_EConv. intro HE. destruct (convty_ty c) eqn:Ec; discriminate HE.
  - (* ESliceLit *) rewrite gtokens_ESliceLit. discriminate.
  - (* EMapLit *) rewrite gtokens_EMapLit. discriminate.
  - (* EStr *) discriminate.
  - (* EHex *) discriminate.
Qed.
(** the OPERAND step: [gtparen] is injective given the operand's injectivity IH.  bare/bare and
    paren/paren strip to [gtokens 0 e1 = gtokens 0 e2] (⇒ IH); the paren/bare mismatch is impossible
    by [bare_not_paren_group]. *)
Lemma gtparen_inj : forall e1 e2,
  (forall e', gtokens 0 e1 = gtokens 0 e' -> e1 = e') ->
  gtparen e1 = gtparen e2 -> e1 = e2.
Proof.
  intros e1 e2 IH HE. unfold gtparen in HE.
  destruct (op_needs_paren e1) eqn:H1; destruct (op_needs_paren e2) eqn:H2.
  - injection HE as HE.
    destruct (balanced_close_split TRP (gtokens 0 e1) (gtokens 0 e2) nil nil
               (or_introl eq_refl) (gtokens_balanced e1 0) (gtokens_balanced e2 0) HE) as [Hk _].
    exact (IH e2 Hk).
  - exfalso. symmetry in HE.
    exact (bare_not_paren_group e2 (gtokens 0 e1) H2 (gtokens_balanced e1 0) HE).
  - exfalso.
    exact (bare_not_paren_group e1 (gtokens 0 e2) H1 (gtokens_balanced e2 0) HE).
  - exact (IH e2 HE).
Qed.

(** ---- Phase 3b slice 2h: the operator-token injectivities — foundations of the EBn crux.
    [op_token] maps the 19 [BinOp]s to DISTINCT tokens and [prefix_token] the 5 [UnaryOp]s to
    distinct tokens, so each is injective ON ITS OWN DOMAIN.  ⚠ NOTE they OVERLAP each other:
    [op_token BSub = prefix_token UNeg = TMinus], likewise [TStar] (BMul/UDeref), [TAmp]
    (BAnd/UAddr), [TCaret] (BXor/UXor) — so a depth-0 [TMinus]/[TStar]/[TAmp]/[TCaret] can be a
    binary operator OR a unary prefix; the EBn split must be located by the prefix/infix POSITION
    (a binary op follows a complete operand), never by token identity alone. *)
Lemma op_token_inj : forall o1 o2, op_token o1 = op_token o2 -> o1 = o2.
Proof. intros o1 o2 H. destruct o1; destruct o2; solve [ reflexivity | discriminate H ]. Qed.
Lemma prefix_token_inj : forall o1 o2, prefix_token o1 = prefix_token o2 -> o1 = o2.
Proof. intros o1 o2 H. destruct o1; destruct o2; solve [ reflexivity | discriminate H ]. Qed.

(** ---- Phase 3b slice 2i: [skip_gty] — a PURE token-skipper for the EBn scan's type-context.
    Returns the tokens AFTER one type (it does NOT build a [GoTy], so it is a token utility like [bd],
    NOT a second type-parser and NOT the parser — keeping the coming [gtokens_inj] parser-free).
    [Acc]-recursive on length ([map[K]V]'s key-then-value skip is non-structural).  Correctness
    [skip_gty_types] ([skip_gty (gttokens_ty t ++ rest) = Some rest]) is proved by induction on [t]. *)
Fixpoint skip_gty_acc (toks : list Token) (a : Acc lt (List.length toks)) {struct a}
  : option { r : list Token | List.length r < List.length toks } :=
  match toks return Acc lt (List.length toks) ->
                    option { r : list Token | List.length r < List.length toks } with
  | nil => fun _ => None
  | tok :: rest0 => fun a =>
    match tok with
    | TId _ => Some (exist _ rest0 (tlt1 _))
    | TStar =>
        match skip_gty_acc rest0 (Acc_inv a (tlt1 (List.length rest0))) with
        | Some (exist _ r Hr) => Some (exist _ r (Nat.lt_lt_succ_r _ _ Hr))
        | None => None
        end
    | TChan =>
        match skip_gty_acc rest0 (Acc_inv a (tlt1 (List.length rest0))) with
        | Some (exist _ r Hr) => Some (exist _ r (Nat.lt_lt_succ_r _ _ Hr))
        | None => None
        end
    | TLB =>
        match rest0 as r0 return Acc lt (S (List.length r0)) ->
                                 option { r : list Token | List.length r < S (List.length r0) } with
        | TRB :: rest => fun a =>
            match skip_gty_acc rest (Acc_inv a (tlt2 (List.length rest))) with
            | Some (exist _ r Hr) => Some (exist _ r (slt2 _ _ Hr))
            | None => None
            end
        | _ => fun _ => None
        end a
    | TMap =>
        match rest0 as r0 return Acc lt (S (List.length r0)) ->
                                 option { r : list Token | List.length r < S (List.length r0) } with
        | TLB :: r0' => fun a =>
            match skip_gty_acc r0' (Acc_inv a (tlt2 (List.length r0'))) with
            | Some (exist _ (TRB :: r1) H1) =>
                match skip_gty_acc r1 (Acc_inv a (strmap_acc _ _ H1)) with
                | Some (exist _ r2 H2) => Some (exist _ r2 (smap _ _ _ H2 H1))
                | None => None
                end
            | _ => None
            end
        | _ => fun _ => None
        end a
    | _ => None
    end
  end a.
Definition skip_gty (toks : list Token) : option (list Token) :=
  match skip_gty_acc toks (lt_wf (List.length toks)) with Some (exist _ r _) => Some r | None => None end.
(** [skip_gty_acc] returns EXACTLY the post-type remainder — proved on the token FUNCTION by
    induction on [t]; the [forall a] subsumes [Acc]-proof-irrelevance (the recursive certs need no pin). *)
Lemma skip_gty_acc_types : forall t rest a,
  match skip_gty_acc (gttokens_ty t ++ rest) a with Some (exist _ r _) => r = rest | None => False end.
Proof.
  induction t as [ | | | | | | | | | | | | | | u IHu | u IHu | u IHu | k IHk v IHv | n ];
    intros rest a.
  all: try (destruct a as [f]; cbn [gttokens_ty app skip_gty_acc]; reflexivity).  (* scalars + GTNamed *)
  - (* GTPtr *) destruct a as [f]; cbn [gttokens_ty app skip_gty_acc].
    specialize (IHu rest (f _ (tlt1 (List.length (gttokens_ty u ++ rest))))).
    destruct (skip_gty_acc (gttokens_ty u ++ rest) _) as [[r Hr] | ]; [ exact IHu | exact IHu ].
  - (* GTSlice *) destruct a as [f]; cbn [gttokens_ty app skip_gty_acc].
    specialize (IHu rest (f _ (tlt2 (List.length (gttokens_ty u ++ rest))))).
    destruct (skip_gty_acc (gttokens_ty u ++ rest) _) as [[r Hr] | ]; [ exact IHu | exact IHu ].
  - (* GTChan *) destruct a as [f]; cbn [gttokens_ty app skip_gty_acc].
    specialize (IHu rest (f _ (tlt1 (List.length (gttokens_ty u ++ rest))))).
    destruct (skip_gty_acc (gttokens_ty u ++ rest) _) as [[r Hr] | ]; [ exact IHu | exact IHu ].
  - (* GTMap — reassociate the WHOLE arg (with its Acc cert) before unfolding, so IHk/IHv apply *)
    assert (Heq : (gttokens_ty (GTMap k v) ++ rest)%list
                = (TMap :: TLB :: gttokens_ty k ++ TRB :: (gttokens_ty v ++ rest))%list)
      by (cbn [gttokens_ty app]; rewrite <- (app_assoc (gttokens_ty k) (TRB :: gttokens_ty v) rest); reflexivity).
    revert a; rewrite Heq; intro a. destruct a as [f]. cbn [skip_gty_acc].
    specialize (IHk (TRB :: gttokens_ty v ++ rest) (f _ (tlt2 (List.length (gttokens_ty k ++ TRB :: gttokens_ty v ++ rest))))).
    destruct (skip_gty_acc (gttokens_ty k ++ TRB :: gttokens_ty v ++ rest) _) as [[r1 H1] | ]; [ | exact IHk ].
    subst r1. cbn [skip_gty_acc].
    specialize (IHv rest (f _ (strmap_acc _ _ H1))).
    destruct (skip_gty_acc (gttokens_ty v ++ rest) _) as [[r2 H2] | ]; [ exact IHv | exact IHv ].
Qed.
Lemma skip_gty_types : forall t rest, skip_gty (gttokens_ty t ++ rest) = Some rest.
Proof.
  intros t rest. unfold skip_gty.
  pose proof (skip_gty_acc_types t rest (lt_wf (List.length (gttokens_ty t ++ rest)))) as H.
  destruct (skip_gty_acc (gttokens_ty t ++ rest) _) as [[r Hr] | ]; [ rewrite H; reflexivity | contradiction ].
Qed.
(** SOUNDNESS / progress: a successful [skip_gty] consumes ≥ 1 token (types are non-empty), so it
    STRICTLY shortens the list — the well-foundedness the coming precedence scan needs to recurse.
    Now a trivial projection of [skip_gty_acc]'s STRICT result sig. *)
Lemma skip_gty_lt : forall toks rest, skip_gty toks = Some rest -> List.length rest < List.length toks.
Proof.
  intros toks rest H. unfold skip_gty in H.
  destruct (skip_gty_acc toks (lt_wf (List.length toks))) as [[r Hr] | ]; [ injection H as <-; exact Hr | discriminate H ].
Qed.

(** The EBn precedence-split LOCATOR.  For the unwrapped tokens of a binary node [inner = gtokens (prec o) l
    ++ op_token o :: gtokens (S (prec o)) r], [eb_find] returns [Some (R, o)] where [o] is the RIGHTMOST
    depth-0 infix operator of MINIMAL precedence (the top constructor, by left-associativity) and [R] is the
    tokens after it (a genuine suffix — [inner = L ++ op_token o :: R]).  Operand-vs-operator is disambiguated
    by [oc] (operand-complete): at [oc=false] [TStar]/[TAmp]/[TCaret] are unary prefixes and [TMinus TLP] is
    [UNeg]; at [oc=true] they are the infix [BMul]/[BAnd]/[BXor]/[BSub].  Type-led operands ([]/map/chan
    composites and conversions) are skipped WHOLE by [skip_gty] so a pointer-[TStar] inside a type is never
    misread as [BMul]; [skip_gty_lt] is the strict decrease that makes that recursion well-founded.  Bracket
    interiors ([d > 0]) are depth-tracked and their operators ignored.  This is a PURE token utility (no
    parser / [gtokens_parse]) — the authority for the EBn case of the coming [gtokens_inj]. *)
Fixpoint eb_find_acc (toks : list Token) (d : nat) (oc : bool) (a : Acc lt (List.length toks)) {struct a}
  : option (list Token * BinOp) :=
  match toks return Acc lt (List.length toks) -> option (list Token * BinOp) with
  | nil => fun _ => None
  | tok :: rest0 => fun a =>
    match d with
    | S d' =>
      (* inside brackets: track depth, ignore operators; operand-complete once depth returns to 0 *)
      let nd := match tok with
                | TLP | TLB | TLC => S d
                | TRP | TRB | TRC => d'
                | _ => d
                end in
      eb_find_acc rest0 nd (match nd with 0 => true | _ => oc end) (Acc_inv a (tlt1 (List.length rest0)))
    | 0 =>
      if oc then
        match infix_op tok with
        | Some o =>
            match eb_find_acc rest0 0 false (Acc_inv a (tlt1 (List.length rest0))) with
            | Some (r', o') => if Nat.leb (binop_prec o') (binop_prec o) then Some (r', o') else Some (rest0, o)
            | None => Some (rest0, o)
            end
        | None =>
            match tok with
            | TDot =>
                match rest0 as r0 return Acc lt (S (List.length r0)) -> option (list Token * BinOp) with
                | TId _ :: rest1 => fun a => eb_find_acc rest1 0 true (Acc_inv a (tlt2 (List.length rest1)))
                | TLP :: rest1 => fun a => eb_find_acc rest1 1 true (Acc_inv a (tlt2 (List.length rest1)))
                | _ => fun _ => None
                end a
            | TLP => eb_find_acc rest0 1 true (Acc_inv a (tlt1 (List.length rest0)))
            | TLB => eb_find_acc rest0 1 true (Acc_inv a (tlt1 (List.length rest0)))
            | _ => None
            end
        end
      else
        match tok with
        | TBang | TCaret | TStar | TAmp => eb_find_acc rest0 0 false (Acc_inv a (tlt1 (List.length rest0)))
        | TMinus =>
            match rest0 as r0 return Acc lt (S (List.length r0)) -> option (list Token * BinOp) with
            | TLP :: rest1 => fun a => eb_find_acc rest1 1 true (Acc_inv a (tlt2 (List.length rest1)))
            | _ => fun _ => None
            end a
        | TId _ | TInt _ | TStr _ | THex _ => eb_find_acc rest0 0 true (Acc_inv a (tlt1 (List.length rest0)))
        | TLP => eb_find_acc rest0 1 true (Acc_inv a (tlt1 (List.length rest0)))
        | TLB | TMap | TChan =>
            (* type-led composite/conversion: skip the whole type; [skip_gty_acc]'s STRICT sig hands the
               length proof [Hlt] directly (no convoy), so the value-group recursion is well-founded *)
            match skip_gty_acc (tok :: rest0) (lt_wf _) with
            | Some (exist _ (TLC :: g) Hlt) =>
                eb_find_acc g 1 true (Acc_inv a (Nat.lt_trans _ _ _ (tlt1 (List.length g)) Hlt))
            | Some (exist _ (TLP :: g) Hlt) =>
                eb_find_acc g 1 true (Acc_inv a (Nat.lt_trans _ _ _ (tlt1 (List.length g)) Hlt))
            | _ => None
            end
        | _ => None
        end
    end
  end a.
Definition eb_find (toks : list Token) : option (list Token * BinOp) :=
  eb_find_acc toks 0 false (lt_wf (List.length toks)).

(** PROGRESS: the located split's right part [R] is a STRICT suffix — [eb_find] always consumes ≥ 1 token
    (the operator plus its left operand), so the coming [gtokens_inj] EBn recursion on [R] is well-founded. *)
Ltac ebtl f IH Hn :=
  destruct (skip_gty_acc _ (lt_wf _)) as [ [ [ | t1 g ] Hlt ] | ]; try exact I; destruct t1; try exact I;
  pose proof (IH g 1 true (f _ (Nat.lt_trans _ _ _ (tlt1 (List.length g)) Hlt))
                ltac:(cbn [List.length] in Hlt, Hn; lia)) as Hr;
  destruct (eb_find_acc g 1 true _) as [[r' o'] | ]; first [ cbn [List.length] in Hlt, Hr |- *; lia | exact I ].
Lemma eb_find_acc_len : forall n toks d oc (a : Acc lt (List.length toks)), List.length toks < n ->
  match eb_find_acc toks d oc a with Some (r, _) => List.length r < List.length toks | None => True end.
Proof.
  induction n as [ | n IH ]; intros toks d oc a Hn; [ lia | ].
  destruct a as [f]. destruct toks as [ | tok rest0 ]; [ destruct d, oc; exact I | ].
  cbn [List.length] in Hn.
  destruct d as [ | d' ]; cbn [eb_find_acc].
  - (* d = 0 *)
    destruct oc.
    + (* oc = true *)
      destruct (infix_op tok) as [ o | ] eqn:Eio.
      * (* infix operator o : candidate; recursion finds the rightmost-min to its right *)
        pose proof (IH rest0 0 false (f _ (tlt1 (List.length rest0))) ltac:(lia)) as Hr.
        destruct (eb_find_acc rest0 0 false _) as [[r' o'] | ];
          [ destruct (Nat.leb (binop_prec o') (binop_prec o)); cbn [List.length] in Hr |- *; lia
          | cbn [List.length]; lia ].
      * (* non-infix while operand-complete: postfix TLP / TLB / TDot (Token order) *)
        destruct tok; try exact I.
        -- (* TLP call *) pose proof (IH rest0 1 true (f _ (tlt1 (List.length rest0))) ltac:(lia)) as Hr.
           destruct (eb_find_acc rest0 1 true _) as [[r' o'] | ]; [ cbn [List.length] in Hr |- *; lia | exact I ].
        -- (* TLB index *) pose proof (IH rest0 1 true (f _ (tlt1 (List.length rest0))) ltac:(lia)) as Hr.
           destruct (eb_find_acc rest0 1 true _) as [[r' o'] | ]; [ cbn [List.length] in Hr |- *; lia | exact I ].
        -- (* TDot: .field / .(assert) *) destruct rest0 as [ | t1 rest1 ]; [ exact I | ]. destruct t1; try exact I.
           ++ (* TId field *) pose proof (IH rest1 0 true (f _ (tlt2 (List.length rest1))) ltac:(cbn [List.length] in Hn; lia)) as Hr.
              destruct (eb_find_acc rest1 0 true _) as [[r' o'] | ]; [ cbn [List.length] in Hr |- *; lia | exact I ].
           ++ (* TLP assert *) pose proof (IH rest1 1 true (f _ (tlt2 (List.length rest1))) ltac:(cbn [List.length] in Hn; lia)) as Hr.
              destruct (eb_find_acc rest1 1 true _) as [[r' o'] | ]; [ cbn [List.length] in Hr |- *; lia | exact I ].
    + (* oc = false : operand-expecting (Token order: atoms, TMinus, prefixes, TLP, type-leads) *)
      destruct tok; try exact I.
      -- (* TId atom *) pose proof (IH rest0 0 true (f _ (tlt1 (List.length rest0))) ltac:(lia)) as Hr.
         destruct (eb_find_acc rest0 0 true _) as [[r' o'] | ]; [ cbn [List.length] in Hr |- *; lia | exact I ].
      -- (* TInt atom *) pose proof (IH rest0 0 true (f _ (tlt1 (List.length rest0))) ltac:(lia)) as Hr.
         destruct (eb_find_acc rest0 0 true _) as [[r' o'] | ]; [ cbn [List.length] in Hr |- *; lia | exact I ].
      -- (* TStr atom *) pose proof (IH rest0 0 true (f _ (tlt1 (List.length rest0))) ltac:(lia)) as Hr.
         destruct (eb_find_acc rest0 0 true _) as [[r' o'] | ]; [ cbn [List.length] in Hr |- *; lia | exact I ].
      -- (* THex atom *) pose proof (IH rest0 0 true (f _ (tlt1 (List.length rest0))) ltac:(lia)) as Hr.
         destruct (eb_find_acc rest0 0 true _) as [[r' o'] | ]; [ cbn [List.length] in Hr |- *; lia | exact I ].
      -- (* TMinus : UNeg needs TLP *) destruct rest0 as [ | t1 rest1 ]; [ exact I | ]. destruct t1; try exact I.
         pose proof (IH rest1 1 true (f _ (tlt2 (List.length rest1))) ltac:(cbn [List.length] in Hn; lia)) as Hr.
         destruct (eb_find_acc rest1 1 true _) as [[r' o'] | ]; [ cbn [List.length] in Hr |- *; lia | exact I ].
      -- (* TStar prefix *) pose proof (IH rest0 0 false (f _ (tlt1 (List.length rest0))) ltac:(lia)) as Hr.
         destruct (eb_find_acc rest0 0 false _) as [[r' o'] | ]; [ cbn [List.length] in Hr |- *; lia | exact I ].
      -- (* TAmp prefix *) pose proof (IH rest0 0 false (f _ (tlt1 (List.length rest0))) ltac:(lia)) as Hr.
         destruct (eb_find_acc rest0 0 false _) as [[r' o'] | ]; [ cbn [List.length] in Hr |- *; lia | exact I ].
      -- (* TCaret prefix *) pose proof (IH rest0 0 false (f _ (tlt1 (List.length rest0))) ltac:(lia)) as Hr.
         destruct (eb_find_acc rest0 0 false _) as [[r' o'] | ]; [ cbn [List.length] in Hr |- *; lia | exact I ].
      -- (* TBang prefix *) pose proof (IH rest0 0 false (f _ (tlt1 (List.length rest0))) ltac:(lia)) as Hr.
         destruct (eb_find_acc rest0 0 false _) as [[r' o'] | ]; [ cbn [List.length] in Hr |- *; lia | exact I ].
      -- (* TLP paren operand *) pose proof (IH rest0 1 true (f _ (tlt1 (List.length rest0))) ltac:(lia)) as Hr.
         destruct (eb_find_acc rest0 1 true _) as [[r' o'] | ]; [ cbn [List.length] in Hr |- *; lia | exact I ].
      -- (* TLB []-composite: type-lead *) ebtl f IH Hn.
      -- (* TChan chan-composite: type-lead *) ebtl f IH Hn.
      -- (* TMap map-composite: type-lead *) ebtl f IH Hn.
  - (* d = S d' : inside brackets — operators ignored, depth tracked *)
    match goal with |- context [eb_find_acc rest0 ?nd ?ocx _] =>
      pose proof (IH rest0 nd ocx (f _ (tlt1 (List.length rest0))) ltac:(lia)) as Hr end.
    destruct (eb_find_acc rest0 _ _ _) as [[r' o'] | ]; [ cbn [List.length] in Hr |- *; lia | exact I ].
Qed.
Lemma eb_find_lt : forall toks r o, eb_find toks = Some (r, o) -> List.length r < List.length toks.
Proof.
  intros toks r o H. unfold eb_find in H.
  pose proof (eb_find_acc_len (S (List.length toks)) toks 0 false (lt_wf (List.length toks)) (tlt1 _)) as Hlt.
  destruct (eb_find_acc toks 0 false _) as [[r' o'] | ]; [ injection H as <- <-; exact Hlt | discriminate H ].
Qed.
(** [eb_find_acc]'s result does not depend on WHICH [Acc] witness is supplied — proof-irrelevance in the
    descent certificate.  Lets the coming correctness proof reason EQUATIONALLY about [eb_find_acc] across
    the [Acc_inv]-derived certs its own recursion produces (which differ from a fresh [lt_wf]). *)
Lemma eb_find_acc_pi : forall n toks d oc (a a' : Acc lt (List.length toks)), List.length toks < n ->
  eb_find_acc toks d oc a = eb_find_acc toks d oc a'.
Proof.
  induction n as [ | n IH ]; intros toks d oc a a' Hn; [ lia | ].
  destruct a as [f]. destruct a' as [f']. destruct toks as [ | tok rest0 ]; [ reflexivity | ].
  cbn [List.length] in Hn. destruct d as [ | d' ]; cbn [eb_find_acc].
  - destruct oc.
    + (* oc = true *)
      destruct (infix_op tok) as [ o | ] eqn:Eio.
      * erewrite (IH rest0 0 false) by lia; reflexivity.
      * destruct tok; try reflexivity.
        -- (* TLP *) apply IH; lia.
        -- (* TLB *) apply IH; lia.
        -- (* TDot *) destruct rest0 as [ | t1 rest1 ]; [ reflexivity | ]. destruct t1; try reflexivity;
             apply IH; cbn [List.length] in Hn; lia.
    + (* oc = false *)
      destruct tok; try reflexivity.
      -- (* TId *)   apply IH; lia.
      -- (* TInt *)  apply IH; lia.
      -- (* TStr *)  apply IH; lia.
      -- (* THex *)  apply IH; lia.
      -- (* TMinus *) destruct rest0 as [ | t1 rest1 ]; [ reflexivity | ]. destruct t1; try reflexivity;
           apply IH; cbn [List.length] in Hn; lia.
      -- (* TStar *)  apply IH; lia.
      -- (* TAmp *)   apply IH; lia.
      -- (* TCaret *) apply IH; lia.
      -- (* TBang *)  apply IH; lia.
      -- (* TLP *)    apply IH; lia.
      -- (* TLB type-lead *)   destruct (skip_gty_acc _ (lt_wf _)) as [ [ [ | t1 g ] Hlt ] | ]; try reflexivity;
           destruct t1; try reflexivity; apply IH; pose proof (Nat.lt_lt_succ_r _ _ Hlt); cbn [List.length] in Hlt, Hn; lia.
      -- (* TChan type-lead *)  destruct (skip_gty_acc _ (lt_wf _)) as [ [ [ | t1 g ] Hlt ] | ]; try reflexivity;
           destruct t1; try reflexivity; apply IH; cbn [List.length] in Hlt, Hn; lia.
      -- (* TMap type-lead *)   destruct (skip_gty_acc _ (lt_wf _)) as [ [ [ | t1 g ] Hlt ] | ]; try reflexivity;
           destruct t1; try reflexivity; apply IH; cbn [List.length] in Hlt, Hn; lia.
  - (* d = S d' : depth-tracking *) apply IH; lia.
Qed.
Lemma eb_find_pi : forall toks d oc (a : Acc lt (List.length toks)),
  eb_find_acc toks d oc a = eb_find_acc toks d oc (lt_wf (List.length toks)).
Proof. intros; apply (eb_find_acc_pi (S (List.length toks))); apply tlt1. Qed.
(* one-token DEPTH steps at depth ≥ 1 (operators ignored): opener → +1, closer → −1, neutral → same.
   [destruct a] exposes [Acc_intro] so [cbn] can unfold the [Acc]-Fixpoint; the two witnesses reconcile
   by [eb_find_acc_pi]. *)
Ltac eb_step_by := match goal with |- eb_find_acc (_ :: _) _ _ ?A = _ => destruct A as [accf] end;
  cbn [eb_find_acc]; eapply eb_find_acc_pi; apply tlt1.
Lemma eb_step_open : forall t rest d oc (a : Acc lt (List.length (t :: rest))) a2, (t = TLP \/ t = TLB \/ t = TLC) ->
  eb_find_acc (t :: rest) (S d) oc a = eb_find_acc rest (S (S d)) oc a2.
Proof. intros t rest d oc a a2 H; destruct H as [ -> | [ -> | -> ] ]; eb_step_by. Qed.
Lemma eb_step_close : forall t rest d oc (a : Acc lt (List.length (t :: rest))) a2, (t = TRP \/ t = TRB \/ t = TRC) ->
  eb_find_acc (t :: rest) (S (S d)) oc a = eb_find_acc rest (S d) oc a2.
Proof. intros t rest d oc a a2 H; destruct H as [ -> | [ -> | -> ] ]; eb_step_by. Qed.
(* a token is neutral iff it leaves the bracket depth unchanged — decided by the EXISTING balance
   authority [bd] ([bd (t :: nil) 1 = Some 1]), NOT a second bracket classifier.  ONE lemma covers every
   neutral token (atoms, every [op_token]/[prefix_token] via [bd_op_token]/[bd_prefix_token], type
   keywords, separators); the [destruct t] is structurally exhaustive — a bracket makes [bd] disagree with
   [Some 1] and is discharged by [discriminate]. *)
Lemma eb_step_neutral : forall t rest d oc (a : Acc lt (List.length (t :: rest))) a2,
  bd (t :: nil) 1 = Some 1 -> eb_find_acc (t :: rest) (S d) oc a = eb_find_acc rest (S d) oc a2.
Proof. intros t rest d oc a a2 H; destruct t; cbn in H; try discriminate H; eb_step_by. Qed.
(* chaining tactics for the depth law: consume the canonical token stream at depth ≥ 1 down to [suffix]. *)
Ltac eb_fin := eapply eb_find_acc_pi; apply tlt1.
Ltac eb_op := erewrite (eb_step_open _ _ _ _ _ (lt_wf _)) by (solve [ left; reflexivity | right; left; reflexivity | right; right; reflexivity ]).
Ltac eb_cl := erewrite (eb_step_close _ _ _ _ _ (lt_wf _)) by (solve [ left; reflexivity | right; left; reflexivity | right; right; reflexivity ]).
Ltac eb_neu := erewrite (eb_step_neutral _ _ _ _ _ (lt_wf _)) by reflexivity.
(* skip a sub-block via an IH/depth lemma [L] whose last explicit arg is the RHS [Acc] (pinned [lt_wf]) *)
Ltac eb_ih L := erewrite (L _ _ _ _ (lt_wf _)).
(** DEPTH law for TYPES: [gttokens_ty t] is skipped whole at depth ≥ 1 (used by the composite/conversion
    cases of the expression depth law). *)
Lemma eb_depth_ty : forall t more sd oc (a : Acc lt (List.length (gttokens_ty t ++ more))) a2,
  eb_find_acc (gttokens_ty t ++ more) (S sd) oc a = eb_find_acc more (S sd) oc a2.
Proof.
  induction t as [ | | | | | | | | | | | | | | u IHu | u IHu | u IHu | k IHk v IHv | n ];
    intros more sd oc a a2; cbn [gttokens_ty app]; try (eb_neu; eb_fin).
  - (* GTPtr *) eb_neu; eb_ih IHu; eb_fin.
  - (* GTSlice *) eb_op; eb_cl; eb_ih IHu; eb_fin.
  - (* GTChan *) eb_neu; eb_ih IHu; eb_fin.
  - (* GTMap *) eb_neu; eb_op; rewrite <- app_assoc; cbn [app]; eb_ih IHk; eb_cl; eb_ih IHv; eb_fin.
Qed.

(** LEXICAL FAITHFULNESS through the grammar: printing then lexing yields EXACTLY a
    canonical derivation's tokens — the composed [lex_gprint_expr] shape CLAUDE.md names. *)
Theorem lex_gprint_expr : forall ctx e,
  lex (gprint ctx e) = Some (gtokens ctx e) /\ CanonExpr ctx e (gtokens ctx e).
Proof. intros ctx e. split; [ apply gtokens_lex | apply gprint_expr_canonical ]. Qed.


(** ==================================================================================================
    ---- THE PARSER ROUND-TRIP ----  [parse_expr] inverts [gtokens]: the canonical token list of
    [e] (printed at any context [ctx >= k]) parses back to [e], leaving any clean tail [rest] untouched.
    Proved by the classic PRECEDENCE-CLIMBING decomposition — peel [e]'s left spine into a [base] primary
    and a list of [(op, right)] pairs ([lspine]); [parse_primary] reads the base, [parse_climb] folds the
    spine ([parse_climb_pairs]).  Composed with [gtokens_lex] this gives the end-to-end
    [parse_str (gprint 0 e) = Some (e, [])].
    ================================================================================================== *)

(** node count — the PROOF-LAYER induction measure for the round-trip argument (never a runtime budget). *)
Fixpoint esize (e : GExpr) : nat :=
  match e with
  | EId _ => 1 | EInt _ => 1 | EStr _ => 1 | EHex _ => 1
  | EUn o e => if unop_paren o e then S (S (S (esize e))) else S (esize e)
      (* PAREN (UNeg / non-leaf operand): +3 — the [op] [(] [)] wrapper tokens.  BARE (leaf operand): +1 —
         just the [op] prefix.  Keyed on [unop_paren o e] so [esize] tracks the two printed shapes. *)
  | EBn _ l r => S (esize l + esize r)
  | ESel e _ => S (S (esize e))      (* +2: the TDot + field tokens *)
  | EIndex e i => S (S (esize e + esize i))   (* +2: the TLB + TRB brackets (around the index child) *)
  | ESlice e lo hi => S (S (S (esize e + esize lo + esize hi)))  (* +3: TLB + TColon + TRB *)
  | ECall e args => S (esize e + (fix esa (l : list GExpr) : nat :=
                                    match l with nil => 0 | a :: r => S (esize a + esa r) end) args)
      (* args contribute [sum (esize a) + length args] — one unit per arg covers its printed comma. *)
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
Proof. intro e; destruct e; cbn [esize]; try lia; destruct (unop_paren _ _); lia. Qed.
(** [esize] of a unary operand is strictly smaller than [esize] of the [EUn] node (both [if] branches add). *)
Lemma esize_lt_unop : forall o e0, esize e0 < esize (EUn o e0).
Proof. intros o e0. cbn [esize]; destruct (unop_paren o e0); lia. Qed.
Lemma esize_EUn_paren : forall o e0, unop_paren o e0 = true -> esize (EUn o e0) = S (S (S (esize e0))).
Proof. intros o e0 H. cbn [esize]. rewrite H. reflexivity. Qed.
Lemma esize_EUn_bare : forall o e0, unop_paren o e0 = false -> esize (EUn o e0) = S (esize e0).
Proof. intros o e0 H. cbn [esize]. rewrite H. reflexivity. Qed.
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





(** [tail_ok k rest] — a tail at which [parse_climb k] STOPS: empty, led by a NON-infix token, or led by
    an infix operator binding LOOSER than [k] (precedence [< k]).  Discrete tokens make it a one-line
    match. *)
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

(** [parse_args] on a NON-empty (not ')'-led) token stream takes the parse-an-expr branch.  This sidesteps
    the opaque-head reduction: the arg tokens begin with [gtokens]'s first token, never [TRP]. *)
Definition starts_TRP (toks : list Token) : bool := match toks with TRP :: _ => true | _ => false end.
Lemma parse_args_cons : forall toks, starts_TRP toks = false ->
  parse_args toks = match parse_expr 0 toks with
    | Some (a, r0) => match parse_args_tl r0 with Some (args, r1) => Some (a :: args, r1) | None => None end
    | None => None
    end.
Proof. intros toks H. rewrite parse_args_eq. destruct toks as [ | t r ]; [ reflexivity | destruct t; try reflexivity; discriminate H ]. Qed.
(** [parse_elems] on a non-'}'-led stream takes the parse-an-expr branch — VERBATIM [parse_args_cons]
    with terminator [TRP] replaced by [TRC]. *)
Definition starts_TRC (toks : list Token) : bool := match toks with TRC :: _ => true | _ => false end.
Lemma parse_elems_cons : forall toks, starts_TRC toks = false ->
  parse_elems toks = match parse_expr 0 toks with
    | Some (a, r0) => match parse_elems_tl r0 with Some (es, r1) => Some (a :: es, r1) | None => None end
    | None => None
    end.
Proof. intros toks H. rewrite parse_elems_eq. destruct toks as [ | t r ]; [ reflexivity | destruct t; try reflexivity; discriminate H ]. Qed.
(** [parse_map_elems] on a non-'}'-led stream parses a KEY, expects [TColon], then a VALUE. *)
Lemma parse_map_elems_cons : forall toks, starts_TRC toks = false ->
  parse_map_elems toks = match parse_expr 0 toks with
    | Some (k, TColon :: r0) =>
        match parse_expr 0 r0 with
        | Some (v, r1) => match parse_map_elems_tl r1 with Some (kvs, r2) => Some ((k, v) :: kvs, r2) | None => None end
        | None => None
        end
    | _ => None
    end.
Proof. intros toks H. rewrite parse_map_elems_eq. destruct toks as [ | t r ]; [ reflexivity | destruct t; try reflexivity; discriminate H ]. Qed.

(** [parse_climb] stops cleanly at a [tail_ok] tail, returning the accumulated left operand untouched. *)
Lemma tail_ok_climb_stop : forall k rest l, tail_ok k rest -> parse_climb k l rest = Some (l, rest).
Proof.
  intros k rest l H. rewrite parse_climb_eq.
  destruct rest as [ | t rs ]; [ reflexivity | ].
  cbn [tail_ok] in H. destruct H as [ _ Hi ]. destruct (infix_op t) eqn:E; [ | reflexivity ].
  rewrite (proj2 (Nat.leb_gt _ _) Hi). reflexivity.
Qed.

(** [parse_postfix] stops (the loop consumes nothing) at a tail whose head is not a postfix starter. *)
Lemma parse_postfix_stop : forall a r,
  (match r with nil => True | t :: _ => is_postfix_start t = false end) ->
  parse_postfix a r = Some (a, r).
Proof.
  intros a r H. rewrite parse_postfix_eq. destruct r as [ | t rest ]; [ reflexivity | ].
  destruct t; cbn [is_postfix_start] in H; solve [ reflexivity | discriminate H ].
Qed.

(** The per-tree round-trip property, carried as a hypothesis for sub-operands inside the spine fold. *)
Definition Pexpr (e : GExpr) : Prop :=
  forall k ctx rest, k <= ctx -> tail_ok k rest ->
    parse_expr k (gtokens ctx e ++ rest)%list = Some (e, rest).

(** A LEFT-LEANING spine: a [base] operand and a list of [(operator, right-operand)] pairs printed in
    sequence.  [fold_pairs] rebuilds the (left-associative) tree, [gtok_pairs] the token surface. *)
Fixpoint gtok_pairs (ps : list (BinOp * GExpr)) : list Token :=
  match ps with
  | nil => nil
  | (o, r) :: ps' => op_token o :: (gtokens (S (binop_prec o)) r ++ gtok_pairs ps')%list
  end.
Fixpoint fold_pairs (base : GExpr) (ps : list (BinOp * GExpr)) : GExpr :=
  match ps with nil => base | (o, r) :: ps' => fold_pairs (EBn o base r) ps' end.
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
Lemma parse_climb_pairs : forall ps k base rest,
  spine_ok k ps -> tail_ok k rest ->
  parse_climb k base (gtok_pairs ps ++ rest)%list = Some (fold_pairs base ps, rest).
Proof.
  induction ps as [ | [o r] ps' IH ]; intros k base rest Hsp Htl.
  - cbn [gtok_pairs fold_pairs app] in *. apply tail_ok_climb_stop; exact Htl.
  - destruct Hsp as [ Hk [ Hpr [ Hnext Hsp' ] ] ].
    cbn [gtok_pairs fold_pairs]. rewrite parse_climb_eq.
    cbn [app]. rewrite infix_op_token.
    rewrite (proj2 (Nat.leb_le _ _) Hk).
    assert (Htl2 : tail_ok (S (binop_prec o)) (gtok_pairs ps' ++ rest)%list).
    { destruct ps' as [ | [o2 r2] ps'' ].
      - cbn [gtok_pairs app]. apply (tail_ok_mono k); [ exact Htl | lia ].
      - cbn [gtok_pairs app]. cbn [tail_ok]. rewrite infix_op_token. split; [ destruct o2; reflexivity | lia ]. }
    rewrite <- app_assoc.
    rewrite (Hpr (S (binop_prec o)) (S (binop_prec o)) (gtok_pairs ps' ++ rest)%list (le_n _) Htl2).
    apply IH; [ exact Hsp' | exact Htl ].
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
  | EHex zc => (fl, EHex zc, nil)
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
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | es IHs fs | eb IHb ix IHx | esl IHsl slo IHlo shi IHhi | ec IHec ecargs | ea IHea T | ecv ece IHec | eslt esles | ekt evt ekvs | sv | hz ]; intros fl bfl base ps H.
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
  - (* EHex hz *) cbn in H. inversion H; subst. cbn [gtok_pairs]. rewrite app_nil_r. reflexivity.
Qed.

Lemma lspine_fold : forall e fl bfl base ps,
  lspine fl e = (bfl, base, ps) -> fold_pairs base ps = e.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | es IHs fs | eb IHb ix IHx | esl IHsl slo IHlo shi IHhi | ec IHec ecargs | ea IHea T | ecv ece IHec | eslt esles | ekt evt ekvs | sv | hz ]; intros fl bfl base ps H.
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
  - (* EHex hz *) cbn in H. inversion H; subst. reflexivity.
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
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | es IHs fs | eb IHb ix IHx | esl IHsl slo IHlo shi IHhi | ec IHec ecargs | ea IHea T | ecv ece IHec | eslt esles | ekt evt ekvs | sv | hz ]; intros fl bfl base ps Hsih H.
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
  - (* EHex hz *) cbn in H. inversion H; subst. exact I.
Qed.

(** The base is a PRIMARY: a literal/unary leaf, or an [EBn] wrapped because [bfl] exceeds its operator
    precedence (so it prints parenthesised). *)
Lemma lspine_base : forall e fl bfl base ps,
  lspine fl e = (bfl, base, ps) ->
  match base with EBn o' _ _ => binop_prec o' < bfl | _ => True end.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | es IHs fs | eb IHb ix IHx | esl IHsl slo IHlo shi IHhi | ec IHec ecargs | ea IHea T | ecv ece IHec | eslt esles | ekt evt ekvs | sv | hz ]; intros fl bfl base ps H.
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
  - (* EHex hz *) cbn in H. inversion H; subst. exact I.
Qed.

Lemma lspine_base_le : forall e fl bfl base ps, lspine fl e = (bfl, base, ps) -> esize base <= esize e.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | es IHs fs | eb IHb ix IHx | esl IHsl slo IHlo shi IHhi | ec IHec ecargs | ea IHea T | ecv ece IHec | eslt esles | ekt evt ekvs | sv | hz ]; intros fl bfl base ps H.
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
  - (* EHex hz *) cbn in H. inversion H; subst. cbn [esize]. lia.
Qed.



(** a PRIMARY is its atom when the postfix loop consumes nothing (or folds a chain via [parse_postfix_pairs]). *)
Lemma parse_primary_of_atom : forall toks a r,
  parse_atom toks = Some (a, r) ->
  (match r with nil => True | t :: _ => is_postfix_start t = false end) ->
  parse_primary toks = Some (a, r).
Proof. intros toks a r H Hr. rewrite parse_primary_eq, H. apply parse_postfix_stop; exact Hr. Qed.

(** [parse_atom] reads a unary node.  PAREN shape ([op]([gprint e0]), for UNeg or a non-leaf operand): the
    operand is parsed inside the parens via [Pexpr] (the strong IH).  BARE shape ([op][gprint e0], for a
    LEAF operand): [op] dispatches to [parse_atom] on the operand, read by one [parse_atom_eq] step. *)
Lemma parse_atom_unary : forall o e0 ctx TAIL,
  Pexpr e0 ->
  parse_atom (gtokens ctx (EUn o e0) ++ TAIL)%list = Some (EUn o e0, TAIL).
Proof.
  intros o e0 ctx TAIL HP.
  assert (Hpar : parse_atom (TLP :: (gtokens 0 e0 ++ TRP :: TAIL))%list = Some (e0, TAIL)).
  { rewrite parse_atom_eq.
    rewrite (HP 0 0 (TRP :: TAIL) (le_n 0) (conj eq_refl I)). reflexivity. }
  destruct o.
  (* UNot / UXor / UDeref / UAddr — wrapped iff [unop_needs_paren e0] *)
  1-4: destruct (unop_needs_paren e0) eqn:Eb;
       [ (* PAREN *) rewrite gtokens_EUn_paren by exact Eb;
         cbn [prefix_token app]; rewrite <- app_assoc; cbn [app];
         rewrite parse_atom_eq; rewrite Hpar; reflexivity
       | (* BARE — [e0] is a leaf atom *) rewrite gtokens_EUn_bare by exact Eb;
         destruct e0; try discriminate Eb;
           (cbn [gtokens prefix_token app];
            rewrite parse_atom_eq; rewrite parse_atom_eq; reflexivity) ].
  (* UNeg — ALWAYS paren *)
  rewrite gtokens_EUn_paren by reflexivity.
  cbn [prefix_token app]; rewrite <- app_assoc; cbn [app].
  rewrite parse_atom_eq.
  rewrite (HP 0 0 (TRP :: TAIL) (le_n 0) (conj eq_refl I)). reflexivity.
Qed.
Lemma parse_primary_unary : forall o e0 ctx TAIL,
  Pexpr e0 -> (match TAIL with nil => True | t :: _ => is_postfix_start t = false end) ->
  parse_primary (gtokens ctx (EUn o e0) ++ TAIL)%list = Some (EUn o e0, TAIL).
Proof.
  intros o e0 ctx TAIL HP Hcl.
  apply parse_primary_of_atom; [ apply parse_atom_unary; exact HP | exact Hcl ].
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
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T | c0 ece0 IHc0 | eslt esles | ekt evt ekvs | sv | hz ]; cbn [pspine]; try reflexivity;
    destruct (pspine e0) as [ b ops ] eqn:Ep; cbn [fst snd] in *;
    rewrite fold_pops_app; cbn [fold_pops]; rewrite IHe0; reflexivity.
Qed.
Lemma pspine_base_kind : forall e,
  match fst (pspine e) with ESel _ _ => False | EIndex _ _ => False | ESlice _ _ _ => False | ECall _ _ => False | EAssert _ _ => False | _ => True end.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T | c0 ece0 IHc0 | eslt esles | ekt evt ekvs | sv | hz ]; cbn [pspine]; try exact I;
    destruct (pspine e0) as [ b ops ] eqn:Ep; cbn [fst] in *; exact IHe0.
Qed.
Lemma pspine_esize : forall e, esize (fst (pspine e)) <= esize e.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T | c0 ece0 IHc0 | eslt esles | ekt evt ekvs | sv | hz ];
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
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T | c0 ece0 IHc0 | eslt esles | ekt evt ekvs | sv | hz ]; cbn [pspine];
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
  induction e as [ i0 | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T | c0 ece0 IHc0 | eslt esles | ekt evt ekvs | sv | hz ]; intros i Hin;
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
  induction e as [ i0 | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T | c0 ece0 IHc0 | eslt esles | ekt evt ekvs | sv | hz ]; intros lo hi Hin;
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
  induction e as [ i0 | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T | c0 ece0 IHc0 | eslt esles | ekt evt ekvs | sv | hz ]; intros args Hin;
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
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T | c0 ece0 IHc0 | eslt esles | ekt evt ekvs | sv | hz ]; intros ctx Z.
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
  - (* EHex hz *) reflexivity.
Qed.
(** the [TRC] analogue — [gtokens] never starts with the composite-literal closer either (used by
    [parse_elems_roundtrip], exactly as [gtokens_hd_TRP_false] serves [parse_args_roundtrip]). *)
Lemma gtokens_hd_TRC_false : forall e ctx Z, starts_TRC (gtokens ctx e ++ Z)%list = false.
Proof.
  induction e as [ i | z | o e0 IHe | o l IHl r IHr | e0 IHe0 f | e0 IHe0 ix IHx | e0 IHe0 slo IHlo shi IHhi | e0 IHe0 ecargs | e0 IHe0 T | c0 ece0 IHc0 | eslt esles | ekt evt ekvs | sv | hz ]; intros ctx Z.
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
  - (* EHex hz *) reflexivity.
Qed.

(** the argument list parses back: [parse_args]/[parse_args_tl] invert [gtokens_args]/[gtokens_args_tl] up to
    and including the ')'.  Each arg round-trips via its [Pexpr] (from the [Forall]). *)
Lemma parse_args_tl_roundtrip : forall args rest,
  List.Forall Pexpr args ->
  parse_args_tl (gtokens_args_tl args ++ TRP :: rest)%list = Some (args, rest).
Proof.
  induction args as [ | a r IH ]; intros rest Hfa.
  - cbn [gtokens_args_tl app]. rewrite parse_args_tl_eq. reflexivity.
  - cbn [gtokens_args_tl]. cbn [app]. rewrite parse_args_tl_eq. rewrite <- app_assoc.
    assert (Htlok : tail_ok 0 (gtokens_args_tl r ++ TRP :: rest)%list)
      by (destruct r as [ | b r' ]; cbn [gtokens_args_tl Datatypes.app tail_ok is_postfix_start infix_op]; split; (reflexivity || exact I)).
    rewrite (List.Forall_inv Hfa 0 0 (gtokens_args_tl r ++ TRP :: rest)%list (le_n 0) Htlok).
    cbv beta iota.
    rewrite (IH rest (List.Forall_inv_tail Hfa)).
    reflexivity.
Qed.
Lemma parse_args_roundtrip : forall args rest,
  List.Forall Pexpr args ->
  parse_args (gtokens_args args ++ TRP :: rest)%list = Some (args, rest).
Proof.
  intros args rest Hfa. destruct args as [ | a r ].
  - cbn [gtokens_args app]. rewrite parse_args_eq. reflexivity.
  - cbn [gtokens_args]. rewrite <- app_assoc.
    rewrite (parse_args_cons (gtokens 0 a ++ gtokens_args_tl r ++ TRP :: rest)%list
               ltac:(apply gtokens_hd_TRP_false)).
    assert (Htlok : tail_ok 0 (gtokens_args_tl r ++ TRP :: rest)%list)
      by (destruct r as [ | b r' ]; cbn [gtokens_args_tl Datatypes.app tail_ok is_postfix_start infix_op]; split; (reflexivity || exact I)).
    rewrite (List.Forall_inv Hfa 0 0 (gtokens_args_tl r ++ TRP :: rest)%list (le_n 0) Htlok).
    cbv beta iota.
    rewrite (parse_args_tl_roundtrip r rest (List.Forall_inv_tail Hfa)).
    reflexivity.
Qed.
(** the ELEMENT list parses back: [parse_elems]/[parse_elems_tl] invert [gtokens_args]/[gtokens_args_tl] up to
    and including the '}'.  VERBATIM the [parse_args] round-trips with terminator [TRP]→[TRC] (elements reuse
    the same comma machinery; only the closer token differs). *)
Lemma parse_elems_tl_roundtrip : forall es rest,
  List.Forall Pexpr es ->
  parse_elems_tl (gtokens_args_tl es ++ TRC :: rest)%list = Some (es, rest).
Proof.
  induction es as [ | a r IH ]; intros rest Hfa.
  - cbn [gtokens_args_tl app]. rewrite parse_elems_tl_eq. reflexivity.
  - cbn [gtokens_args_tl]. cbn [app]. rewrite parse_elems_tl_eq. rewrite <- app_assoc.
    assert (Htlok : tail_ok 0 (gtokens_args_tl r ++ TRC :: rest)%list)
      by (destruct r as [ | b r' ]; cbn [gtokens_args_tl Datatypes.app tail_ok is_postfix_start infix_op]; split; (reflexivity || exact I)).
    rewrite (List.Forall_inv Hfa 0 0 (gtokens_args_tl r ++ TRC :: rest)%list (le_n 0) Htlok).
    cbv beta iota.
    rewrite (IH rest (List.Forall_inv_tail Hfa)).
    reflexivity.
Qed.
Lemma parse_elems_roundtrip : forall es rest,
  List.Forall Pexpr es ->
  parse_elems (gtokens_args es ++ TRC :: rest)%list = Some (es, rest).
Proof.
  intros es rest Hfa. destruct es as [ | a r ].
  - cbn [gtokens_args app]. rewrite parse_elems_eq. reflexivity.
  - cbn [gtokens_args]. rewrite <- app_assoc.
    rewrite (parse_elems_cons (gtokens 0 a ++ gtokens_args_tl r ++ TRC :: rest)%list
               ltac:(apply gtokens_hd_TRC_false)).
    assert (Htlok : tail_ok 0 (gtokens_args_tl r ++ TRC :: rest)%list)
      by (destruct r as [ | b r' ]; cbn [gtokens_args_tl Datatypes.app tail_ok is_postfix_start infix_op]; split; (reflexivity || exact I)).
    rewrite (List.Forall_inv Hfa 0 0 (gtokens_args_tl r ++ TRC :: rest)%list (le_n 0) Htlok).
    cbv beta iota.
    rewrite (parse_elems_tl_roundtrip r rest (List.Forall_inv_tail Hfa)).
    reflexivity.
Qed.
(** the KEYED pair list parses back: [parse_map_elems]/[parse_map_elems_tl] invert [gtokens_pairs]/[gtokens_pairs_tl]
    up to and including the '}'.  Each pair's KEY parses (stopping at the [TColon]) then its VALUE (stopping at the
    pair separator / closer), both via their [Pexpr] (from the [Forall]). *)
Lemma parse_map_elems_tl_roundtrip : forall kvs rest,
  List.Forall (fun p => Pexpr (fst p) /\ Pexpr (snd p)) kvs ->
  parse_map_elems_tl (gtokens_pairs_tl kvs ++ TRC :: rest)%list = Some (kvs, rest).
Proof.
  induction kvs as [ | [k v] r IH ]; intros rest Hfa.
  - cbn [gtokens_pairs_tl app]. rewrite parse_map_elems_tl_eq. reflexivity.
  - destruct (List.Forall_inv Hfa) as [ Hpk Hpv ]. cbn [fst snd] in Hpk, Hpv.
    cbn [gtokens_pairs_tl app]. rewrite parse_map_elems_tl_eq.
    rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc.
    assert (Htlk : tail_ok 0 (TColon :: (gtokens 0 v ++ (gtokens_pairs_tl r ++ TRC :: rest)))%list)
      by (cbn [tail_ok is_postfix_start infix_op]; split; (reflexivity || exact I)).
    rewrite (Hpk 0 0 (TColon :: (gtokens 0 v ++ (gtokens_pairs_tl r ++ TRC :: rest)))%list (le_n 0) Htlk).
    cbv beta iota.
    assert (Htlv : tail_ok 0 (gtokens_pairs_tl r ++ TRC :: rest)%list)
      by (destruct r as [ | [k' v'] r' ]; cbn [gtokens_pairs_tl Datatypes.app tail_ok is_postfix_start infix_op]; split; (reflexivity || exact I)).
    rewrite (Hpv 0 0 (gtokens_pairs_tl r ++ TRC :: rest)%list (le_n 0) Htlv).
    cbv beta iota.
    rewrite (IH rest (List.Forall_inv_tail Hfa)).
    reflexivity.
Qed.
Lemma parse_map_elems_roundtrip : forall kvs rest,
  List.Forall (fun p => Pexpr (fst p) /\ Pexpr (snd p)) kvs ->
  parse_map_elems (gtokens_pairs kvs ++ TRC :: rest)%list = Some (kvs, rest).
Proof.
  intros kvs rest Hfa. destruct kvs as [ | [k v] r ].
  - cbn [gtokens_pairs app]. rewrite parse_map_elems_eq. reflexivity.
  - destruct (List.Forall_inv Hfa) as [ Hpk Hpv ]. cbn [fst snd] in Hpk, Hpv.
    cbn [gtokens_pairs]. rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc.
    rewrite (parse_map_elems_cons (gtokens 0 k ++ TColon :: (gtokens 0 v ++ (gtokens_pairs_tl r ++ TRC :: rest)))%list
               ltac:(apply gtokens_hd_TRC_false)).
    assert (Htlk : tail_ok 0 (TColon :: (gtokens 0 v ++ (gtokens_pairs_tl r ++ TRC :: rest)))%list)
      by (cbn [tail_ok is_postfix_start infix_op]; split; (reflexivity || exact I)).
    rewrite (Hpk 0 0 (TColon :: (gtokens 0 v ++ (gtokens_pairs_tl r ++ TRC :: rest)))%list (le_n 0) Htlk).
    cbv beta iota.
    assert (Htlv : tail_ok 0 (gtokens_pairs_tl r ++ TRC :: rest)%list)
      by (destruct r as [ | [k' v'] r' ]; cbn [gtokens_pairs_tl Datatypes.app tail_ok is_postfix_start infix_op]; split; (reflexivity || exact I)).
    rewrite (Hpv 0 0 (gtokens_pairs_tl r ++ TRC :: rest)%list (le_n 0) Htlv).
    cbv beta iota.
    rewrite (parse_map_elems_tl_roundtrip r rest (List.Forall_inv_tail Hfa)).
    reflexivity.
Qed.

(** THE TYPE-PARSER ROUND-TRIP: [parse_gty] inverts [gttokens_ty] (leaving any clean tail [rest]). *)
Lemma parse_gty_roundtrip : forall t rest, parse_gty (gttokens_ty t ++ rest)%list = Some (t, rest).
Proof.
  induction t as [ | | | | | | | | | | | | | | u IHt | u IHt | u IHt | t1 IHt1 t2 IHt2 | n ];
    intro rest.
  1-14: cbn [gttokens_ty app]; rewrite parse_gty_eq_id; reflexivity.
  - (* GTPtr u *) cbn [gttokens_ty app]. rewrite parse_gty_eq_star. rewrite (IHt rest). reflexivity.
  - (* GTSlice u *) cbn [gttokens_ty app]. rewrite parse_gty_eq_slice. rewrite (IHt rest). reflexivity.
  - (* GTChan u *) cbn [gttokens_ty app]. rewrite parse_gty_eq_chan. rewrite (IHt rest). reflexivity.
  - (* GTMap k v *) cbn [gttokens_ty]. cbn [app]. rewrite <- app_assoc. cbn [app]. rewrite parse_gty_eq_map.
    rewrite (IHt1 (TRB :: gttokens_ty t2 ++ rest)%list).
    rewrite (IHt2 rest). reflexivity.
  - (* GTNamed n *) cbn [gttokens_ty app]. rewrite parse_gty_eq_id.
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
Lemma parse_postfix_pairs : forall ops b rest,
  (forall i, List.In (PIdx i) ops -> Pexpr i) ->
  (forall lo hi, List.In (PSlice lo hi) ops -> Pexpr lo /\ Pexpr hi) ->
  (forall args, List.In (PCall args) ops -> List.Forall Pexpr args) ->
  (match rest with nil => True | t :: _ => is_postfix_start t = false end) ->
  parse_postfix b (gtokens_pops ops ++ rest)%list = Some (fold_pops b ops, rest).
Proof.
  induction ops as [ | op ops IH ]; intros b rest Hpe Hps Hpc Hcl.
  - cbn [gtokens_pops app fold_pops]. apply parse_postfix_stop; exact Hcl.
  - destruct op as [ f | i | lo hi | args | T ]; cbn [gtokens_pops fold_pops].
    + (* PSel f *) cbn [app]. rewrite parse_postfix_eq.
      apply IH; [ intros j Hj; apply Hpe; right; exact Hj
                | intros lo hi Hj; apply Hps; right; exact Hj
                | intros args Hj; apply Hpc; right; exact Hj | exact Hcl ].
    + (* PIdx i *) cbn [app]. rewrite parse_postfix_eq. rewrite <- app_assoc. cbn [app].
      rewrite (Hpe i (or_introl eq_refl) 0 0 (TRB :: gtokens_pops ops ++ rest)%list (le_n 0) (conj eq_refl I)).
      apply IH; [ intros j Hj; apply Hpe; right; exact Hj
                | intros lo hi Hj; apply Hps; right; exact Hj
                | intros args Hj; apply Hpc; right; exact Hj | exact Hcl ].
    + (* PSlice lo hi *) destruct (Hps lo hi (or_introl eq_refl)) as [ Hplo Hphi ].
      cbn [app]. rewrite parse_postfix_eq.
      rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; cbn [app].
      rewrite (Hplo 0 0 (TColon :: (gtokens 0 hi ++ TRB :: (gtokens_pops ops ++ rest)))%list (le_n 0) (conj eq_refl I)).
      cbv beta iota.
      rewrite (Hphi 0 0 (TRB :: (gtokens_pops ops ++ rest))%list (le_n 0) (conj eq_refl I)).
      apply IH; [ intros j Hj; apply Hpe; right; exact Hj
                | intros lo' hi' Hj; apply Hps; right; exact Hj
                | intros args Hj; apply Hpc; right; exact Hj | exact Hcl ].
    + (* PCall args *) cbn [app]. rewrite parse_postfix_eq. rewrite <- app_assoc. cbn [app].
      rewrite (parse_args_roundtrip args (gtokens_pops ops ++ rest)%list
                 (Hpc args (or_introl eq_refl))).
      apply IH; [ intros j Hj; apply Hpe; right; exact Hj
                | intros lo hi Hj; apply Hps; right; exact Hj
                | intros args' Hj; apply Hpc; right; exact Hj | exact Hcl ].
    + (* PAssert T *) cbn [app]. rewrite parse_postfix_eq. rewrite <- app_assoc. cbn [app].
      rewrite (parse_gty_roundtrip T (TRP :: gtokens_pops ops ++ rest)%list).
      cbv beta iota.
      apply IH; [ intros j Hj; apply Hpe; right; exact Hj
                | intros lo hi Hj; apply Hps; right; exact Hj
                | intros args Hj; apply Hpc; right; exact Hj | exact Hcl ].
Qed.

(** [parse_atom] reads a type-form CONVERSION operand [EConv c e0] ([]T(x) / chan T(x) / map[K]V(x)).  At
    ATOM position a type lead ([]/chan/map) is unambiguous (no preceding operand to index), so [parse_atom]
    dispatches on it, [parse_gty] consumes [convty_ty c] ([parse_gty_roundtrip]), then the parenthesised
    operand round-trips via its [Pexpr e0].  The analogue of [parse_atom_unary] for the type-prefixed primary;
    [op_needs_paren (EConv …) = false] (a conversion is a Go PrimaryExpr — never self-parenthesised).  Both
    [parse_gty_roundtrip] and the goal are [cbn]'d identically so the head-token dispatch lines up syntactically. *)
Lemma parse_atom_conv : forall c e0 ctx TAIL,
  Pexpr e0 ->
  parse_atom (gtokens ctx (EConv c e0) ++ TAIL)%list = Some (EConv c e0, TAIL).
Proof.
  intros c e0 ctx TAIL HP. rewrite gtokens_EConv.
  (* normalise the operand tail to [gtokens 0 e0 ++ TRP :: TAIL] (push [app_assoc] past the stuck
     [gtokens 0 e0] — needs the alternating dance, as the [PSlice] case does). *)
  rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; cbn [app].
  destruct c as [ u | u | k v ].
  - (* CTSlice u — []u(e0) *)
    pose proof (parse_gty_roundtrip (GTSlice u) (TLP :: (gtokens 0 e0 ++ TRP :: TAIL))) as Hg.
    rewrite parse_atom_eq. cbn [convty_ty gttokens_ty app] in Hg |- *.
    rewrite Hg. cbv beta iota.
    rewrite (HP 0 0 (TRP :: TAIL) (le_n 0) (conj eq_refl I)). reflexivity.
  - (* CTChan u — chan u(e0) *)
    pose proof (parse_gty_roundtrip (GTChan u) (TLP :: (gtokens 0 e0 ++ TRP :: TAIL))) as Hg.
    rewrite parse_atom_eq. cbn [convty_ty gttokens_ty app] in Hg |- *.
    rewrite Hg. cbv beta iota.
    rewrite (HP 0 0 (TRP :: TAIL) (le_n 0) (conj eq_refl I)). reflexivity.
  - (* CTMap k v — map[k]v(e0) *)
    pose proof (parse_gty_roundtrip (GTMap k v) (TLP :: (gtokens 0 e0 ++ TRP :: TAIL))) as Hg.
    rewrite parse_atom_eq. cbn [convty_ty gttokens_ty app] in Hg |- *.
    rewrite Hg. cbv beta iota.
    rewrite (HP 0 0 (TRP :: TAIL) (le_n 0) (conj eq_refl I)). reflexivity.
Qed.

(** [parse_atom] reads a slice composite literal [ESliceLit t es] ([[]T{e1,..,en}]).  At ATOM position the
    [[]T] lead is a type ([parse_gty] consumes [GTSlice t]); the NEXT token '{' (TLC) — vs the conversion's
    '(' (TLP) — selects the literal, then [parse_elems] consumes the brace-delimited element list
    ([parse_elems_roundtrip]).  Each element round-trips via its [Pexpr] (from the [Forall]).  The type-led
    analogue of [parse_atom_conv]; [op_needs_paren (ESliceLit …) = false] (a Go PrimaryExpr). *)
Lemma parse_atom_slicelit : forall t es ctx TAIL,
  List.Forall Pexpr es ->
  parse_atom (gtokens ctx (ESliceLit t es) ++ TAIL)%list = Some (ESliceLit t es, TAIL).
Proof.
  intros t es ctx TAIL Hfa. rewrite gtokens_ESliceLit.
  (* normalise the input to [TLB :: TRB :: gttokens_ty t ++ TLC :: (gtokens_args es ++ TRC :: TAIL)] — push the
     stuck [gttokens_ty t]/[gtokens_args es] appends right (alternating, as the EConv case does, +1 round for
     the leading '['']' conses). *)
  cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; cbn [app].
  pose proof (parse_gty_roundtrip (GTSlice t) (TLC :: (gtokens_args es ++ TRC :: TAIL))) as Hg.
  rewrite parse_atom_eq. cbn [gttokens_ty app] in Hg |- *.
  rewrite Hg. cbv beta iota.
  rewrite (parse_elems_roundtrip es TAIL Hfa).
  reflexivity.
Qed.

(** [parse_atom] reads a map composite literal [EMapLit kt vt kvs] ([map[K]V{k1: v1,..,kn: vn}]).  At ATOM
    position the [map[K]V] lead is a type ([parse_gty] consumes [GTMap kt vt]); the NEXT token '{' (TLC) — vs the
    conversion's '(' (TLP) — selects the literal, then [parse_map_elems] consumes the brace-delimited KEYED pair
    list ([parse_map_elems_roundtrip]).  Each key/value round-trips via its [Pexpr].  Type-led analogue of
    [parse_atom_slicelit]; [op_needs_paren (EMapLit …) = false]. *)
Lemma parse_atom_maplit : forall kt vt kvs ctx TAIL,
  List.Forall (fun p => Pexpr (fst p) /\ Pexpr (snd p)) kvs ->
  parse_atom (gtokens ctx (EMapLit kt vt kvs) ++ TAIL)%list = Some (EMapLit kt vt kvs, TAIL).
Proof.
  intros kt vt kvs ctx TAIL Hfa. rewrite gtokens_EMapLit.
  (* normalise the [++ TAIL] into the type's clean tail, keeping [gttokens_ty (GTMap kt vt)] folded as the head *)
  rewrite <- ?app_assoc; cbn [app]; rewrite <- ?app_assoc; cbn [app].
  pose proof (parse_gty_roundtrip (GTMap kt vt) (TLC :: (gtokens_pairs kvs ++ TRC :: TAIL))) as Hg.
  rewrite parse_atom_eq. cbn [gttokens_ty app] in Hg |- *.
  rewrite Hg. cbv beta iota.
  rewrite (parse_map_elems_roundtrip kvs TAIL Hfa).
  reflexivity.
Qed.

(** [parse_atom] reads a [gparen]-printed operand (a non-postfix base: literal/unary/paren-binop/conversion). *)
Lemma parse_atom_gparen : forall b TAIL,
  match b with ESel _ _ => False | EIndex _ _ => False | ESlice _ _ _ => False | ECall _ _ => False | EAssert _ _ => False | _ => True end ->
  (forall e', esize e' < esize b -> Pexpr e') ->   (* size-IH — the conversion operand needs its own [Pexpr] *)
  Pexpr b ->
  parse_atom (gtparen b ++ TAIL)%list = Some (b, TAIL).
Proof.
  intros b TAIL Hkind Hsih HP.
  destruct b as [ i | z | o e0 | o' l' r' | es fs | es ix | es slo shi | es eargs | es eaT | ecc ece | eslt esles | ekt evt ekvs | sv | hz ];
    [ | | | | exfalso; exact Hkind | exfalso; exact Hkind | exfalso; exact Hkind | exfalso; exact Hkind | exfalso; exact Hkind | | | | | ].
  - cbn [gtparen gtokens app]. rewrite parse_atom_eq. reflexivity.
  - cbn [gtparen gtokens app]. rewrite parse_atom_eq. reflexivity.
  - cbn [gtparen op_needs_paren]. cbn [app]. rewrite <- app_assoc. cbn [app]. rewrite parse_atom_eq.
    rewrite (HP 0 0 (TRP :: TAIL) (le_n 0) (conj eq_refl I)). reflexivity.
  - cbn [gtparen op_needs_paren]. cbn [app]. rewrite <- app_assoc. cbn [app]. rewrite parse_atom_eq.
    rewrite (HP 0 0 (TRP :: TAIL) (le_n 0) (conj eq_refl I)). reflexivity.
  - (* EConv ecc ece — [op_needs_paren = false], so [gtparen] is just [gtokens 0]; read via [parse_atom_conv]. *)
    cbn [gtparen op_needs_paren].
    apply parse_atom_conv. apply Hsih; cbn [esize]; lia.
  - (* ESliceLit eslt esles — [op_needs_paren = false]; read via [parse_atom_slicelit], elements' [Pexpr] from the size-IH *)
    cbn [gtparen op_needs_paren].
    apply parse_atom_slicelit.
    apply List.Forall_forall; intros a Ha; apply Hsih; rewrite esize_ESliceLit; pose proof (esa_in esles a Ha); lia.
  - (* EMapLit ekt evt ekvs — [op_needs_paren = false]; read via [parse_atom_maplit], pairs' [Pexpr] from the size-IH *)
    cbn [gtparen op_needs_paren].
    apply parse_atom_maplit.
    apply List.Forall_forall; intros p Hp; split;
      (apply Hsih; rewrite esize_EMapLit; pose proof (mpa_in ekvs p Hp); lia).
  - (* EStr sv — a leaf atom (like EId/EInt) *)
    cbn [gtparen gtokens app]. rewrite parse_atom_eq. reflexivity.
  - (* EHex hz — a leaf atom (like EId/EInt) *)
    cbn [gtparen gtokens app]. rewrite parse_atom_eq. reflexivity.
Qed.

(** [parse_atom] reads a standalone (non-selector) base [gtokens bfl base] — literal/unary direct, a
    wrapped binop via the paren rule. *)
Lemma parse_atom_base : forall base bfl TAIL,
  (forall e', esize e' < esize base -> Pexpr e') ->
  Pexpr base ->
  match base with ESel _ _ => False | EIndex _ _ => False | ESlice _ _ _ => False | ECall _ _ => False | EAssert _ _ => False | EBn o' _ _ => binop_prec o' < bfl | _ => True end ->
  parse_atom (gtokens bfl base ++ TAIL)%list = Some (base, TAIL).
Proof.
  intros base bfl TAIL Hsih HPbase Hprim.
  destruct base as [ i | z | o e0 | o' l' r' | es fs | es ix | es slo shi | es eargs | es eaT | ecc ece | eslt esles | ekt evt ekvs | sv | hz ];
    [ | | | | exfalso; exact Hprim | exfalso; exact Hprim | exfalso; exact Hprim | exfalso; exact Hprim | exfalso; exact Hprim | | | | | ].
  - cbn [gtokens app]. rewrite parse_atom_eq. reflexivity.
  - cbn [gtokens app]. rewrite parse_atom_eq. reflexivity.
  - apply parse_atom_unary. apply Hsih; apply esize_lt_unop.
  - assert (Hw : Nat.ltb (binop_prec o') bfl = true) by (apply Nat.ltb_lt; exact Hprim).
    rewrite (gtokens_wrapped o' l' r' bfl Hw).
    cbn [app]. rewrite <- app_assoc. cbn [app]. rewrite parse_atom_eq.
    rewrite (HPbase 0 (binop_prec o') (TRP :: TAIL) (Nat.le_0_l _) (conj eq_refl I)).
    reflexivity.
  - (* EConv ecc ece — read via [parse_atom_conv]; the operand [Pexpr] comes from the size-IH. *)
    apply parse_atom_conv. apply Hsih; cbn [esize]; lia.
  - (* ESliceLit eslt esles — read via [parse_atom_slicelit]; elements' [Pexpr] from the size-IH *)
    apply parse_atom_slicelit.
    apply List.Forall_forall; intros a Ha; apply Hsih; rewrite esize_ESliceLit; pose proof (esa_in esles a Ha); lia.
  - (* EMapLit ekt evt ekvs — read via [parse_atom_maplit]; pairs' [Pexpr] from the size-IH *)
    apply parse_atom_maplit.
    apply List.Forall_forall; intros p Hp; split;
      (apply Hsih; rewrite esize_EMapLit; pose proof (mpa_in ekvs p Hp); lia).
  - (* EStr sv — a leaf atom (like EId/EInt) *)
    cbn [gtokens app]. rewrite parse_atom_eq. reflexivity.
  - (* EHex hz — a leaf atom (like EId/EInt) *)
    cbn [gtokens app]. rewrite parse_atom_eq. reflexivity.
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
Lemma parse_primary_chain : forall e ctx TAIL,
  is_chain e ->
  (forall e', esize e' < esize e -> Pexpr e') ->
  (match TAIL with nil => True | t :: _ => is_postfix_start t = false end) ->
  parse_primary (gtokens ctx e ++ TAIL)%list = Some (e, TAIL).
Proof.
  intros e ctx TAIL Hch Hsih Hcl.
  destruct (pspine e) as [ base' ops ] eqn:Eps.
  pose proof (pspine_base_kind e) as Hbk. rewrite Eps in Hbk. cbn [fst] in Hbk.
  pose proof (pspine_fold e) as Hfo. rewrite Eps in Hfo. cbn [fst snd] in Hfo.
  pose proof (pspine_esize_lt_chain e Hch) as Hlt. rewrite Eps in Hlt. cbn [fst] in Hlt.
  pose proof (pspine_pidx_esize e) as Hpx. rewrite Eps in Hpx. cbn [snd] in Hpx.
  pose proof (pspine_pslice_esize e) as Hpsx. rewrite Eps in Hpsx. cbn [snd] in Hpsx.
  pose proof (pspine_pcall_esize e) as Hpcx. rewrite Eps in Hpcx. cbn [snd] in Hpcx.
  rewrite (gtokens_chain_gtparen ctx e Hch), (gtparen_pspine e), Eps. cbn [fst snd].
  rewrite <- app_assoc.
  rewrite parse_primary_eq.
  rewrite (parse_atom_gparen base' (gtokens_pops ops ++ TAIL)%list Hbk
             ltac:(intros e' He'; apply Hsih; lia)
             ltac:(apply Hsih; exact Hlt)).
  rewrite (parse_postfix_pairs ops base' TAIL
             ltac:(intros i Hi; apply Hsih; apply Hpx; exact Hi)
             ltac:(intros lo hi Hi; destruct (Hpsx lo hi Hi) as [ Hl Hh ]; split; [ apply Hsih; exact Hl | apply Hsih; exact Hh ])
             ltac:(intros args Hi; eapply List.Forall_impl; [ intros a Ha; apply Hsih; exact Ha | exact (Hpcx args Hi) ])
             Hcl).
  rewrite Hfo. reflexivity.
Qed.

(** [parse_primary] reads the decomposed [base] EXACTLY: a non-selector base via [parse_atom_base] then an
    empty postfix loop; a selector chain via [parse_primary_sel]. *)
Lemma parse_primary_base : forall base bfl TAIL,
  (forall e', esize e' < esize base -> Pexpr e') ->
  Pexpr base ->
  match base with EBn o' _ _ => binop_prec o' < bfl | _ => True end ->
  (match TAIL with nil => True | t :: _ => is_postfix_start t = false end) ->
  parse_primary (gtokens bfl base ++ TAIL)%list = Some (base, TAIL).
Proof.
  intros base bfl TAIL Hsih HPbase Hprim Hcl.
  destruct base as [ i | z | o e0 | o' l' r' | es fs | es ix | es slo shi | es eargs | es eaT | ecc ece | eslt esles | ekt evt ekvs | sv | hz ].
  (* ESel / EIndex / ESlice / ECall / EAssert chain — via the postfix spine ([parse_primary_chain]) *)
  5-9: apply parse_primary_chain; [ exact I | exact Hsih | exact Hcl ].
  (* EId / EInt / EUn / EBn / EConv / ESliceLit / EMapLit — a non-chain base via [parse_atom_base] then an empty postfix loop *)
  all: apply parse_primary_of_atom; [ apply parse_atom_base; [ exact Hsih | exact HPbase | exact Hprim ] | exact Hcl ].
Qed.

(** [parse_primary] reads a type-form conversion [EConv c e0] (analogue of [parse_primary_unary]). *)
Lemma parse_primary_conv : forall c e0 ctx TAIL,
  Pexpr e0 -> (match TAIL with nil => True | t :: _ => is_postfix_start t = false end) ->
  parse_primary (gtokens ctx (EConv c e0) ++ TAIL)%list = Some (EConv c e0, TAIL).
Proof.
  intros c e0 ctx TAIL HP Hcl. apply parse_primary_of_atom; [ apply parse_atom_conv; exact HP | exact Hcl ].
Qed.
(** [parse_primary] reads a slice composite literal [ESliceLit t es] (analogue of [parse_primary_conv]). *)
Lemma parse_primary_slicelit : forall t es ctx TAIL,
  List.Forall Pexpr es -> (match TAIL with nil => True | t0 :: _ => is_postfix_start t0 = false end) ->
  parse_primary (gtokens ctx (ESliceLit t es) ++ TAIL)%list = Some (ESliceLit t es, TAIL).
Proof.
  intros t es ctx TAIL Hfa Hcl. apply parse_primary_of_atom; [ apply parse_atom_slicelit; exact Hfa | exact Hcl ].
Qed.
(** [parse_primary] reads a map composite literal [EMapLit kt vt kvs] (analogue of [parse_primary_slicelit]). *)
Lemma parse_primary_maplit : forall kt vt kvs ctx TAIL,
  List.Forall (fun p => Pexpr (fst p) /\ Pexpr (snd p)) kvs ->
  (match TAIL with nil => True | t0 :: _ => is_postfix_start t0 = false end) ->
  parse_primary (gtokens ctx (EMapLit kt vt kvs) ++ TAIL)%list = Some (EMapLit kt vt kvs, TAIL).
Proof.
  intros kt vt kvs ctx TAIL Hfa Hcl. apply parse_primary_of_atom; [ apply parse_atom_maplit; exact Hfa | exact Hcl ].
Qed.

(** ---- THE EXPRESSION ROUND-TRIP ---- every [e] satisfies [Pexpr] (strong induction on [esize]).  An
    UNWRAPPED [e] (at a context [<=] its top precedence) parses via the left-spine decomposition
    ([parse_primary_base] reads the base, [parse_climb_pairs] folds the spine); a WRAPPED binop parses via
    the paren rule, recursing on its own unwrapped form. *)
Lemma all_Pexpr : forall n e, esize e <= n -> Pexpr e.
Proof.
  induction n as [ | n IH ]; intros e Hsz.
  - pose proof (esize_pos e); lia.
  - assert (Hunwr : forall k ctx rest, k <= ctx -> tail_ok k rest ->
              match e with EBn o _ _ => ctx <= binop_prec o | ESel _ _ => False | EIndex _ _ => False | ESlice _ _ _ => False | ECall _ _ => False | EAssert _ _ => False | _ => True end ->
              parse_expr k (gtokens ctx e ++ rest)%list = Some (e, rest)).
    { intros k ctx rest Hk Htl Hctx. destruct e as [ i | z | o e0 | o l r | es fs | es ix | es slo shi | es eargs | es eaT | ec0 ece0 | slt sles | mkt mvt mkvs | sv | hz ].
      - (* EId *) cbn [gtokens app]. rewrite parse_expr_eq.
        rewrite (parse_primary_of_atom (TId i :: rest) (EId i) rest
                   ltac:(rewrite parse_atom_eq; reflexivity) (tail_ok_pclean _ _ Htl)).
        apply tail_ok_climb_stop; exact Htl.
      - (* EInt *) cbn [gtokens app]. rewrite parse_expr_eq.
        rewrite (parse_primary_of_atom (TInt z :: rest) (EInt z) rest
                   ltac:(rewrite parse_atom_eq; reflexivity) (tail_ok_pclean _ _ Htl)).
        apply tail_ok_climb_stop; exact Htl.
      - (* EUn *) rewrite parse_expr_eq.
        rewrite (parse_primary_unary o e0 ctx rest
                   ltac:(apply IH; pose proof (esize_lt_unop o e0); lia) (tail_ok_pclean _ _ Htl)).
        apply tail_ok_climb_stop; exact Htl.
      - (* EBn unwrapped: Hctx : ctx <= binop_prec o *)
        cbn [esize] in Hsz.
        assert (Hleb : Nat.leb ctx (binop_prec o) = true) by (apply Nat.leb_le; exact Hctx).
        destruct (lspine (binop_prec o) l) as [ [ bfl base ] ps0 ] eqn:El.
        assert (Els : lspine ctx (EBn o l r) = (bfl, base, (ps0 ++ (o, r) :: nil)%list))
          by (cbn [lspine]; rewrite Hleb, El; reflexivity).
        pose proof (lspine_fold _ _ _ _ _ Els) as Hfold.
        pose proof (lspine_base _ _ _ _ _ Els) as Hprim.
        pose proof (lspine_base_le _ _ _ _ _ El) as Hble.
        assert (HPbase : Pexpr base) by (apply (IH base); lia).
        assert (Hspine : spine_ok k (ps0 ++ (o, r) :: nil)%list).
        { apply (spine_ok_weaken _ ctx); [ | exact Hk ].
          eapply lspine_spine_ok; [ | exact Els ].
          intros e' He'. apply (IH e'). cbn [esize] in He'. lia. }
        rewrite (lspine_print _ _ _ _ _ Els), <- app_assoc.
        rewrite parse_expr_eq.
        rewrite (parse_primary_base base bfl (gtok_pairs (ps0 ++ (o, r) :: nil) ++ rest)%list
                   ltac:(intros e' He'; apply (IH e'); lia) HPbase Hprim
                   (gtok_pairs_snoc_pclean ps0 o r rest)).
        change (parse_climb k base (gtok_pairs (ps0 ++ (o, r) :: nil) ++ rest)%list = Some (EBn o l r, rest)).
        rewrite (parse_climb_pairs (ps0 ++ (o, r) :: nil) k base rest Hspine Htl).
        rewrite Hfold. reflexivity.
      - (* ESel — Hctx : False (postfix chains handled directly in the outer case) *) destruct Hctx.
      - (* EIndex — Hctx : False (postfix chains handled directly in the outer case) *) destruct Hctx.
      - (* ESlice — Hctx : False (postfix chains handled directly in the outer case) *) destruct Hctx.
      - (* ECall — Hctx : False (postfix chains handled directly in the outer case) *) destruct Hctx.
      - (* EAssert — Hctx : False (postfix chains handled directly in the outer case) *) destruct Hctx.
      - (* EConv ec0 ece0 — a primary (never wrapped); read via [parse_primary_conv] *)
        rewrite parse_expr_eq.
        rewrite (parse_primary_conv ec0 ece0 ctx rest
                   ltac:(apply IH; cbn [esize] in Hsz; lia) (tail_ok_pclean _ _ Htl)).
        apply tail_ok_climb_stop; exact Htl.
      - (* ESliceLit slt sles — a primary (never wrapped); read via [parse_primary_slicelit] *)
        rewrite parse_expr_eq.
        rewrite (parse_primary_slicelit slt sles ctx rest
                   ltac:(apply List.Forall_forall; intros a Ha; apply IH; rewrite esize_ESliceLit in Hsz; pose proof (esa_in sles a Ha); lia)
                   (tail_ok_pclean _ _ Htl)).
        apply tail_ok_climb_stop; exact Htl.
      - (* EMapLit mkt mvt mkvs — a primary (never wrapped); read via [parse_primary_maplit] *)
        rewrite parse_expr_eq.
        rewrite (parse_primary_maplit mkt mvt mkvs ctx rest
                   ltac:(apply List.Forall_forall; intros p Hp; split;
                           (apply IH; rewrite esize_EMapLit in Hsz; pose proof (mpa_in mkvs p Hp); lia))
                   (tail_ok_pclean _ _ Htl)).
        apply tail_ok_climb_stop; exact Htl.
      - (* EStr sv — a leaf atom (like EId/EInt) *)
        cbn [gtokens app]. rewrite parse_expr_eq.
        rewrite (parse_primary_of_atom (TStr sv :: rest) (EStr sv) rest
                   ltac:(rewrite parse_atom_eq; reflexivity) (tail_ok_pclean _ _ Htl)).
        apply tail_ok_climb_stop; exact Htl.
      - (* EHex hz — a leaf atom (like EId/EInt) *)
        cbn [gtokens app]. rewrite parse_expr_eq.
        rewrite (parse_primary_of_atom (THex hz :: rest) (EHex hz) rest
                   ltac:(rewrite parse_atom_eq; reflexivity) (tail_ok_pclean _ _ Htl)).
        apply tail_ok_climb_stop; exact Htl. }
    unfold Pexpr. intros k ctx rest Hk Htl.
    destruct e as [ i | z | o e0 | o l r | es fs | es ix | es slo shi | es eargs | es eaT | ecc ece | eslt esles | ekt evt ekvs | sv | hz ].
    + apply Hunwr; [ exact Hk | exact Htl | exact I ].
    + apply Hunwr; [ exact Hk | exact Htl | exact I ].
    + apply Hunwr; [ exact Hk | exact Htl | exact I ].
    + destruct (Nat.ltb (binop_prec o) ctx) eqn:Ewrap.
      * (* wrapped *)
        rewrite (gtokens_wrapped o l r ctx Ewrap).
        cbn [app]. rewrite <- app_assoc. cbn [app].
        rewrite parse_expr_eq.
        rewrite (parse_primary_of_atom
                   (TLP :: (gtokens (binop_prec o) (EBn o l r) ++ TRP :: rest))%list (EBn o l r) rest
                   ltac:(rewrite parse_atom_eq;
                         rewrite (Hunwr 0 (binop_prec o) (TRP :: rest) (Nat.le_0_l _) (conj eq_refl I) (le_n _));
                         reflexivity)
                   (tail_ok_pclean _ _ Htl)).
        apply tail_ok_climb_stop; exact Htl.
      * (* unwrapped *)
        apply Hunwr; [ exact Hk | exact Htl | apply Nat.ltb_ge in Ewrap; exact Ewrap ].
    + (* ESel es fs — a primary (never wrapped), via the postfix spine *)
      rewrite parse_expr_eq.
      rewrite (parse_primary_chain (ESel es fs) ctx rest I
                 ltac:(intros e' He'; apply (IH e'); cbn [esize] in Hsz, He'; lia)
                 (tail_ok_pclean _ _ Htl)).
      apply tail_ok_climb_stop; exact Htl.
    + (* EIndex es ix — a primary (never wrapped), via the postfix spine *)
      rewrite parse_expr_eq.
      rewrite (parse_primary_chain (EIndex es ix) ctx rest I
                 ltac:(intros e' He'; apply (IH e'); cbn [esize] in Hsz, He'; lia)
                 (tail_ok_pclean _ _ Htl)).
      apply tail_ok_climb_stop; exact Htl.
    + (* ESlice es slo shi — a primary (never wrapped), via the postfix spine *)
      rewrite parse_expr_eq.
      rewrite (parse_primary_chain (ESlice es slo shi) ctx rest I
                 ltac:(intros e' He'; apply (IH e'); cbn [esize] in Hsz, He'; lia)
                 (tail_ok_pclean _ _ Htl)).
      apply tail_ok_climb_stop; exact Htl.
    + (* ECall es eargs — a primary (never wrapped), via the postfix spine *)
      rewrite parse_expr_eq.
      rewrite (parse_primary_chain (ECall es eargs) ctx rest I
                 ltac:(intros e' He'; apply (IH e'); cbn [esize] in Hsz, He'; lia)
                 (tail_ok_pclean _ _ Htl)).
      apply tail_ok_climb_stop; exact Htl.
    + (* EAssert es eaT — a primary (never wrapped), via the postfix spine *)
      rewrite parse_expr_eq.
      rewrite (parse_primary_chain (EAssert es eaT) ctx rest I
                 ltac:(intros e' He'; apply (IH e'); cbn [esize] in Hsz, He'; lia)
                 (tail_ok_pclean _ _ Htl)).
      apply tail_ok_climb_stop; exact Htl.
    + (* EConv ecc ece — a primary (never wrapped); the unwrapped path ([op_needs_paren = false]) *)
      apply Hunwr; [ exact Hk | exact Htl | exact I ].
    + (* ESliceLit eslt esles — a primary (never wrapped); the unwrapped path ([op_needs_paren = false]) *)
      apply Hunwr; [ exact Hk | exact Htl | exact I ].
    + (* EMapLit ekt evt ekvs — a primary (never wrapped); the unwrapped path ([op_needs_paren = false]) *)
      apply Hunwr; [ exact Hk | exact Htl | exact I ].
    + (* EStr sv — a leaf atom (never wrapped) *)
      apply Hunwr; [ exact Hk | exact Htl | exact I ].
    + (* EHex hz — a leaf atom (never wrapped) *)
      apply Hunwr; [ exact Hk | exact Htl | exact I ].
Qed.

(** THE HEADLINE (parser half): [parse] inverts [gtokens] — the canonical token list parses back to [e]. *)
Theorem gtokens_parse : forall e, parse (gtokens 0 e) = Some (e, nil).
Proof.
  intro e. unfold parse.
  pose proof (all_Pexpr (esize e) e (le_n _) 0 0 nil (le_n 0) I) as HP.
  rewrite app_nil_r in HP. exact HP.
Qed.

(** ★ THE END-TO-END EXPRESSION ROUND-TRIP — printing then parsing (lex + parse) recovers the AST EXACTLY.
    Composes [gtokens_lex] (printer→tokens) with [gtokens_parse] (tokens→AST).  HONEST SCOPE: printer/parser
    SELF-CONSISTENCY for the clean Rocq grammar — NOT yet a theorem about Go's own parser (a SEPARATE,
    unproven Go-syntax recognition gap; Go's toolchain is trusted — NOT the plugin's gap #10). *)
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
    ---- TOKEN-LEVEL TYPE LAYER ----  a Go type as a TOKEN list ([gttokens_ty], mirroring [print_ty]'s
    surface) + a recursive-descent token parser ([parse_gty]) + the round-trip [parse_gty_roundtrip] —
    the gateway for type-form conversions / composite literals / type assertions.  Self-contained:
    additive over [GoTy], no [GExpr] dependency.  [GoTy] has no list child, so ordinary induction
    suffices; [parse_gty] is Acc-structural on token length (no budget of any kind).
    ================================================================================== *)


(** composed: the printed type lexes to its token list. *)
Lemma lex_print_ty : forall t, lex (print_ty t) = Some (gttokens_ty t).
Proof.
  intro t.
  pose proof (gttokens_ty_lex t "" nil eq_refl lex_empty) as H.
  rewrite str_app_nil_r in H. rewrite app_nil_r in H. exact H.
Qed.

(** ★THE END-TO-END TYPE ROUND-TRIP: the printed type [print_ty t] lexes and parses back to [t]. *)
Theorem parse_gty_print_ty : forall t,
  match lex (print_ty t) with Some toks => parse_gty toks | None => None end = Some (t, nil).
Proof.
  intro t. rewrite lex_print_ty.
  rewrite <- (app_nil_r (gttokens_ty t)). apply parse_gty_roundtrip.
Qed.


(** ---- The CONVERSION type-form layer ----  A type-form conversion [convform(x)] needs a target that is
    SYNTACTICALLY unambiguous at expression-atom position — its printed form must NOT begin with an
    identifier, or [T(x)] would be the call [ECall (EId T) [x]] instead.  [ConvTy] is exactly that subset
    of [GoTy]: the three bracket/keyword-led composite heads ([]T / chan T / map[K]V).  A dedicated
    3-constructor inductive makes the restriction STRUCTURAL — illegal states unrepresentable, ZERO proof
    obligations — and [convty_ty] embeds it into [GoTy] so the type printer/lexer/parser are reused
    VERBATIM.  This is the conversion-type layer BEHIND the [EConv] expression form (round-trip:
    [parse_convty_roundtrip] / [parse_conv_print]).  (Pointer [*T] is excluded: a bare [*T(x)] is
    ambiguous with a deref; primitives and named types are identifier-led, so they ARE the call form
    already.) *)
Definition conv_print  (c : ConvTy) : string     := print_ty (convty_ty c).
Definition conv_tokens (c : ConvTy) : list Token := gttokens_ty (convty_ty c).

(** the printed conversion-type lexes to its token list (inherited from [lex_print_ty]). *)
Lemma conv_print_lex : forall c, lex (conv_print c) = Some (conv_tokens c).
Proof. intro c. apply lex_print_ty. Qed.

(** [parse_convty] = [parse_gty] keeping ONLY the three conversion heads; anything else (a primitive, a
    pointer, or a named type — all identifier/[*]-led, i.e. NOT a syntactic conversion form) is rejected. *)
Definition parse_convty (toks : list Token) : option (ConvTy * list Token) :=
  match parse_gty toks with
  | Some (GTSlice u, r) => Some (CTSlice u, r)
  | Some (GTChan u, r)  => Some (CTChan u, r)
  | Some (GTMap k v, r) => Some (CTMap k v, r)
  | _ => None
  end.

(** round-trip: a conversion-type's tokens parse back to it (reusing [parse_gty_roundtrip]). *)
Lemma parse_convty_roundtrip : forall c rest,
  parse_convty (conv_tokens c ++ rest)%list = Some (c, rest).
Proof.
  intros c rest. unfold parse_convty, conv_tokens.
  destruct c as [ u | u | k v ]; cbn [convty_ty];
    rewrite (parse_gty_roundtrip _ rest); reflexivity.
Qed.

(** ★END-TO-END: the printed conversion-type lexes and parses back to itself. *)
Theorem parse_conv_print : forall c,
  match lex (conv_print c) with Some toks => parse_convty toks | None => None end = Some (c, nil).
Proof.
  intro c. rewrite conv_print_lex.
  rewrite <- (app_nil_r (conv_tokens c)). apply parse_convty_roundtrip.
Qed.

(** FAITHFULNESS — the type printer is INJECTIVE, derived from the token-level round-trip
    [parse_gty_print_ty]: distinct [GoTy]s print to distinct strings (a keyword-prefixed name [int8x] is
    never confused with the keyword [int8]; a keyword [int] is never a nominal name). *)
Theorem print_ty_inj : forall t1 t2, print_ty t1 = print_ty t2 -> t1 = t2.
Proof.
  intros t1 t2 H.
  pose proof (parse_gty_print_ty t1) as Q1.
  pose proof (parse_gty_print_ty t2) as Q2.
  rewrite <- H in Q2. rewrite Q1 in Q2. congruence.
Qed.

(** ---- PROGRAM PRINTER ---- prints a [GoAst.Program] to Go source: `package <pkg>` then `func main()`
    whose body is the program's [GoStmt] list, ONE tab-indented statement per line (gofmt's layout).  An
    expression statement reuses the machine-checked [gprint]; the package name is a validated [Ident] (no
    raw text).  GoEmit's blessed [emit_compiled] is exactly [print_program], gated by a
    [GoCompile] certificate. *)
Definition go_nl : string := String (Ascii.ascii_of_nat 10) EmptyString.
Definition go_tab : string := String (Ascii.ascii_of_nat 9) EmptyString.
Definition print_stmt (s : GoStmt) : string :=
  match s with
  | GsExprStmt e    => gprint 0 e
  | GsReturn        => "return"
  | GsReturnVal e   => ("return " ++ gprint 0 e)%string
  | GsBlankAssign e => ("_ = " ++ gprint 0 e)%string
  | GsDefer e       => ("defer " ++ gprint 0 e)%string
  | GsShortDecl x e => (proj1_sig x ++ " := " ++ gprint 0 e)%string
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
    [parse] of any [TReturn]-led list is [None]. *)
Lemma parse_expr_TReturn_None : forall rest, parse_expr 0 (TReturn :: rest) = None.
Proof. intros rest. rewrite parse_expr_eq, parse_primary_eq, parse_atom_eq. reflexivity. Qed.
Lemma parse_TReturn_None : forall rest, parse (TReturn :: rest) = None.
Proof. intros rest. unfold parse. apply parse_expr_TReturn_None. Qed.

(** A printed [return e] (the [GsReturnVal] text "return " ++ gprint 0 e) does NOT parse back: it LEXES to a
    leading [TReturn] ([lex_return_app] over [gtokens_lex]), which [parse] rejects.  So no [gprint] output can
    equal "return " ++ gprint 0 e — the [GsExprStmt] / [GsReturnVal] disjointness. *)
Lemma parse_str_return_gprint : forall e, parse_str ("return " ++ gprint 0 e)%string = None.
Proof.
  intro e. unfold parse_str.
  rewrite (lex_return_app (gprint 0 e) (gtokens 0 e) (gtokens_lex e 0)).
  apply parse_TReturn_None.
Qed.
Lemma gprint_neq_return_val : forall e1 e2, gprint 0 e2 <> ("return " ++ gprint 0 e1)%string.
Proof.
  intros e1 e2 H. pose proof (parse_print_roundtrip e2) as R. rewrite H in R.
  rewrite parse_str_return_gprint in R. discriminate R.
Qed.

(** A printed [_ = e] (the [GsBlankAssign] text "_ = " ++ X) does NOT parse back: a LONE '=' fails to lex
    ([lex_op] yields [None] unless the next char is '='), so [lex ("_ = " ++ X) = None] and thus
    [parse_str ("_ = " ++ X) = None].  Hence no [gprint] output equals "_ = " ++ gprint 0 e — the
    [GsExprStmt] / [GsBlankAssign] disjointness.  (The reject is decided by the fixed "_ = " prefix, so
    [vm_compute] closes it for any tail [X].) *)
Lemma parse_str_blank_None : forall X, parse_str ("_ = " ++ X)%string = None.
Proof. intro X. vm_compute. reflexivity. Qed.
Lemma gprint_neq_blank : forall e1 e2, gprint 0 e2 <> ("_ = " ++ gprint 0 e1)%string.
Proof.
  intros e1 e2 H. pose proof (parse_print_roundtrip e2) as R. rewrite H in R.
  rewrite parse_str_blank_None in R. discriminate R.
Qed.

(** A printed [defer <call>] (the [GsDefer] text "defer " ++ X) does NOT parse back: "defer" is a Go
    RESERVED WORD, so [lex_ident "defer" = None] FAILS the whole lex — [lex ("defer " ++ X) = None] for
    any suffix [X].  Hence no [gprint] output equals "defer " ++ gprint 0 e — the [GsExprStmt] / [GsDefer]
    disjointness. *)
Lemma scan_id_defer : forall X, scan_id ("defer " ++ X)%string = ("defer"%string, (" " ++ X)%string).
Proof. intro X. reflexivity. Qed.
Lemma lex_ident_defer : lex_ident "defer" = None.
Proof. reflexivity. Qed.
Lemma lex_defer : forall X, lex ("defer " ++ X)%string = None.
Proof.
  intro X.
  change ("defer " ++ X)%string with (String "d"%char ("efer " ++ X))%string.
  rewrite (lex_eq_id "d"%char ("efer " ++ X)%string "defer"%string (String " "%char X)
             eq_refl eq_refl (scan_id_defer X)).
  rewrite lex_ident_defer. reflexivity.
Qed.
Lemma parse_str_defer_gprint : forall e, parse_str ("defer " ++ gprint 0 e)%string = None.
Proof.
  intro e. unfold parse_str. rewrite lex_defer. reflexivity.
Qed.
Lemma gprint_neq_defer : forall e1 e2, gprint 0 e2 <> ("defer " ++ gprint 0 e1)%string.
Proof.
  intros e1 e2 H. pose proof (parse_print_roundtrip e2) as R. rewrite H in R.
  rewrite parse_str_defer_gprint in R. discriminate R.
Qed.

(** A printed [x := e] (the [GsShortDecl] text) does NOT parse back as an expression: the ident LEXES
    ([lex_ident_go]) and ':' lexes ([TColon]), but the following LONE '=' fails [lex_op] (which accepts
    only "=="), so the whole lex is [None] — the [GsExprStmt] / [GsShortDecl] disjointness. *)
Lemma lex_defassign : forall X, lex (" := " ++ X)%string = None.
Proof.
  intro X.
  change (" := " ++ X)%string with (String " "%char (String ":"%char (String "="%char (String " "%char X)))).
  erewrite lex_eq_space by reflexivity.
  erewrite lex_eq_op by reflexivity.
  erewrite lex_eq_op_None by reflexivity.
  reflexivity.
Qed.
(** An ident head lexes and RECURSES, so a failing rest fails the whole lex — the [None] mirror of
    [lex_gprint_id]'s success case (same [scan_id_app]/[lex_ident_go] spine). *)
Lemma lex_ident_None : forall s rest,
  go_ident s = true -> clean_start rest = true -> lex rest = None ->
  lex (s ++ rest)%string = None.
Proof.
  intros s rest Hs Hclean Hrest.
  destruct s as [ | c0 s0 ]; [ vm_compute in Hs; discriminate Hs | ].
  pose proof Hs as Hgo. unfold go_ident in Hgo. apply andb_prop in Hgo. destruct Hgo as [Hia _].
  apply andb_prop in Hia. destruct Hia as [Hidstart Hallidc].
  cbn [String.append].
  rewrite (lex_eq_id c0 (s0 ++ rest)%string (String c0 s0) rest
             (is_idstart_not_space _ Hidstart) Hidstart
             (scan_id_app (String c0 s0) rest Hallidc Hclean)).
  rewrite (lex_ident_go (String c0 s0) Hs).
  rewrite Hrest. reflexivity.
Qed.
Lemma lex_shortdecl_None : forall x X,
  go_ident x = true -> lex (x ++ (" := " ++ X))%string = None.
Proof.
  intros x X Hx.
  apply (lex_ident_None _ _ Hx); [ reflexivity | apply lex_defassign ].
Qed.
Lemma parse_str_shortdecl_None : forall x X,
  go_ident x = true -> parse_str (x ++ (" := " ++ X))%string = None.
Proof. intros x X Hx. unfold parse_str. rewrite (lex_shortdecl_None x X Hx). reflexivity. Qed.
Lemma gprint_neq_shortdecl : forall x e1 e2, go_ident x = true ->
  gprint 0 e2 <> (x ++ " := " ++ gprint 0 e1)%string.
Proof.
  intros x e1 e2 Hx H. pose proof (parse_print_roundtrip e2) as R. rewrite H in R.
  rewrite (parse_str_shortdecl_None x (gprint 0 e1) Hx) in R. discriminate R.
Qed.

(** Ident equality from its underlying string (the [go_ident] bool proof is unique — UIP on bool). *)
Lemma ident_eq : forall i j : Ident, proj1_sig i = proj1_sig j -> i = j.
Proof.
  intros [s p] [t q] H. simpl in H. subst t.
  assert (E : p = q) by apply (UIP_dec Bool.bool_dec). rewrite E. reflexivity.
Qed.
(** A valid ident is an all-idchar run (a projection of [go_ident]'s conjunction). *)
Lemma ident_all_idc : forall i : Ident, all_idc (proj1_sig i) = true.
Proof.
  intros [s Hs]. simpl. destruct s as [ | c0 s0 ]; [ vm_compute in Hs; discriminate Hs | ].
  unfold go_ident in Hs. apply andb_prop in Hs. destruct Hs as [Hia _].
  apply andb_prop in Hia. exact (proj2 Hia).
Qed.
(** The ident/rest SPLIT is unique — no new scanner: applying [scan_id] to both sides of an
    equality of all-idchar-head ++ clean-start-rest concatenations recovers the components via the
    existing [scan_id_app]. *)
Lemma idc_split : forall a1 a2 r1 r2,
  all_idc a1 = true -> all_idc a2 = true -> clean_start r1 = true -> clean_start r2 = true ->
  (a1 ++ r1)%string = (a2 ++ r2)%string -> a1 = a2 /\ r1 = r2.
Proof.
  intros a1 a2 r1 r2 H1 H2 C1 C2 H.
  pose proof (scan_id_app a1 r1 H1 C1) as E1. rewrite H in E1.
  rewrite (scan_id_app a2 r2 H2 C2) in E1. injection E1 as -> ->. split; reflexivity.
Qed.
(** The [GsShortDecl] cross-case helper: a printed short decl is ident ++ " := " ++ expr, so any
    equal all-idchar-head/clean-rest concatenation must agree componentwise. *)
Lemma shortdecl_split : forall (x : Ident) g a r,
  all_idc a = true -> clean_start r = true ->
  (a ++ r)%string = (proj1_sig x ++ (" := " ++ g))%string ->
  a = proj1_sig x /\ r = (" := " ++ g)%string.
Proof.
  intros x g a r Ha Cr H.
  exact (idc_split a (proj1_sig x) r (" := " ++ g)%string Ha (ident_all_idc x) Cr eq_refl H).
Qed.

(** Statement-printer INJECTIVITY — distinct statements print to distinct text.  Case-per-constructor-
    pair: the diagonal lifts from [gprint_inj]; cross cases close by the [gprint_neq_*] disjointness
    lemmas, string [discriminate], [sapp_inv_head] on a shared prefix, or [shortdecl_split].  The
    program-level lift is [print_program_inj] below. *)
Lemma print_stmt_inj : forall s1 s2, print_stmt s1 = print_stmt s2 -> s1 = s2.
Proof.
  intros [e1| |r1|b1|d1|x1 v1] [e2| |r2|b2|d2|x2 v2] H; simpl in H.
  (* s1 = GsExprStmt e1 *)
  - f_equal. exact (gprint_inj e1 e2 H).
  - exfalso. exact (gprint_neq_return e1 H).
  - exfalso. exact (gprint_neq_return_val r2 e1 H).
  - exfalso. exact (gprint_neq_blank b2 e1 H).
  - exfalso. exact (gprint_neq_defer d2 e1 H).
  - exfalso. exact (gprint_neq_shortdecl (proj1_sig x2) v2 e1 (proj2_sig x2) H).
  (* s1 = GsReturn *)
  - exfalso. symmetry in H. exact (gprint_neq_return e2 H).
  - reflexivity.
  - exfalso. cbn in H. discriminate H.
  - exfalso. cbn in H. discriminate H.
  - exfalso. cbn in H. discriminate H.
  - exfalso.
    destruct (shortdecl_split x2 (gprint 0 v2) "return" "" eq_refl eq_refl H) as [_ Hr].
    cbn [append] in Hr. discriminate Hr.
  (* s1 = GsReturnVal r1 *)
  - exfalso. symmetry in H. exact (gprint_neq_return_val r1 e2 H).
  - exfalso. symmetry in H. cbn in H. discriminate H.
  - f_equal. apply (sapp_inv_head "return ") in H. exact (gprint_inj r1 r2 H).
  - exfalso. cbn in H. discriminate H.
  - exfalso. cbn in H. discriminate H.
  - exfalso.
    destruct (shortdecl_split x2 (gprint 0 v2) "return" (" " ++ gprint 0 r1)%string
                eq_refl eq_refl H) as [Hk _].
    pose proof (proj2_sig x2) as Hgx. rewrite <- Hk in Hgx. vm_compute in Hgx. discriminate Hgx.
  (* s1 = GsBlankAssign b1 *)
  - exfalso. symmetry in H. exact (gprint_neq_blank b1 e2 H).
  - exfalso. symmetry in H. cbn in H. discriminate H.
  - exfalso. symmetry in H. cbn in H. discriminate H.
  - f_equal. apply (sapp_inv_head "_ = ") in H. exact (gprint_inj b1 b2 H).
  - exfalso. cbn in H. discriminate H.
  - exfalso.
    destruct (shortdecl_split x2 (gprint 0 v2) "_" (" = " ++ gprint 0 b1)%string
                eq_refl eq_refl H) as [_ Hr].
    cbn [append] in Hr. discriminate Hr.
  (* s1 = GsDefer d1 *)
  - exfalso. symmetry in H. exact (gprint_neq_defer d1 e2 H).
  - exfalso. cbn in H. discriminate H.
  - exfalso. cbn in H. discriminate H.
  - exfalso. cbn in H. discriminate H.
  - f_equal. apply (sapp_inv_head "defer ") in H. exact (gprint_inj d1 d2 H).
  - exfalso.
    destruct (shortdecl_split x2 (gprint 0 v2) "defer" (" " ++ gprint 0 d1)%string
                eq_refl eq_refl H) as [Hk _].
    pose proof (proj2_sig x2) as Hgx. rewrite <- Hk in Hgx. vm_compute in Hgx. discriminate Hgx.
  (* s1 = GsShortDecl x1 v1 — the five symmetric cross cases, then the diagonal *)
  - exfalso. symmetry in H. exact (gprint_neq_shortdecl (proj1_sig x1) v1 e2 (proj2_sig x1) H).
  - exfalso. symmetry in H.
    destruct (shortdecl_split x1 (gprint 0 v1) "return" "" eq_refl eq_refl H) as [_ Hr].
    cbn [append] in Hr. discriminate Hr.
  - exfalso. symmetry in H.
    destruct (shortdecl_split x1 (gprint 0 v1) "return" (" " ++ gprint 0 r2)%string
                eq_refl eq_refl H) as [Hk _].
    pose proof (proj2_sig x1) as Hgx. rewrite <- Hk in Hgx. vm_compute in Hgx. discriminate Hgx.
  - exfalso. symmetry in H.
    destruct (shortdecl_split x1 (gprint 0 v1) "_" (" = " ++ gprint 0 b2)%string
                eq_refl eq_refl H) as [_ Hr].
    cbn [append] in Hr. discriminate Hr.
  - exfalso. symmetry in H.
    destruct (shortdecl_split x1 (gprint 0 v1) "defer" (" " ++ gprint 0 d2)%string
                eq_refl eq_refl H) as [Hk _].
    pose proof (proj2_sig x1) as Hgx. rewrite <- Hk in Hgx. vm_compute in Hgx. discriminate Hgx.
  - destruct (shortdecl_split x2 (gprint 0 v2) (proj1_sig x1) (" := " ++ gprint 0 v1)%string
                (ident_all_idc x1) eq_refl H) as [Hx Hr].
    apply ident_eq in Hx. apply (sapp_inv_head " := ") in Hr. apply gprint_inj in Hr.
    subst. reflexivity.
Qed.

(** ============================================================================
    PROGRAM-PRINTER INJECTIVITY — [print_program] is INJECTIVE: distinct programs emit distinct Go source.
    Crux: every printed expression is NEWLINE-FREE ([no_nl_gprint]), so the body's '\n'-delimited statement
    lines (and the package name's terminating '\n') are recoverable.  SCOPE: print INJECTIVITY only — NOT a
    parse round-trip and NOT a proof that the emitted text is accepted by a Go grammar; statement
    re-parsing (ASI/semicolons) and Go syntax acceptance are separate, deferred. *)
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
Lemma no_nl_render_dec : forall ds acc, Forall (fun d => (d < 10)%nat) ds -> no_nl acc ->
  no_nl (render_digits dec_digit ds acc).
Proof.
  induction ds as [| d tl IH]; intros acc Hall Hacc; [ exact Hacc | ].
  inversion Hall; subst.
  change (render_digits dec_digit (d :: tl) acc)
    with (render_digits dec_digit tl (String (dec_digit d) acc)).
  apply IH; [ assumption | cbn [no_nl]; split; [ apply is_nl_dec_digit; assumption | exact Hacc ] ].
Qed.
Lemma no_nl_print_Z : forall z, no_nl (print_Z z).
Proof.
  intro z. destruct z as [| p | p]; cbn [print_Z].
  - no_nl_lit.
  - unfold print_Z_pos. apply no_nl_render_dec; [ apply pos_digits_bound; lia | exact I ].
  - apply no_nl_app;
      [ no_nl_lit
      | unfold print_Z_pos; apply no_nl_render_dec; [ apply pos_digits_bound; lia | exact I ] ].
Qed.
Lemma no_nl_render_hex : forall ds acc, Forall (fun d => (d < 16)%nat) ds -> no_nl acc ->
  no_nl (render_digits hexdig ds acc).
Proof.
  induction ds as [| d tl IH]; intros acc Hall Hacc; [ exact Hacc | ].
  inversion Hall; subst.
  change (render_digits hexdig (d :: tl) acc)
    with (render_digits hexdig tl (String (hexdig d) acc)).
  apply IH;
    [ assumption
    | cbn [no_nl]; split; [ apply is_nl_idc, is_hex_is_idc, is_hex_hexdig; assumption | exact Hacc ] ].
Qed.
Lemma no_nl_print_hex : forall n, no_nl (print_hex n).
Proof.
  intro n. unfold print_hex. apply no_nl_app; [ no_nl_lit | ].
  destruct n as [| p]; cbn [print_hex_body];
    [ no_nl_lit
    | apply no_nl_render_hex; [ apply pos_digits_bound; lia | exact I ] ].
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
                 | e0 IHe0 lo IHlo hi IHhi | e0 IHe0 args IHargs | e0 IHe0 T | ec0 ece0 IHec0 | slt sles IHsles | mkt mvt mkvs IHmkvs | sv | hz ]
    using GExpr_ind'; intro ctx.
  - cbn [gprint]. apply no_nl_ident.
  - cbn [gprint]. apply no_nl_print_Z.
  - rewrite gprint_EUn. apply no_nl_app; [ apply no_nl_unop_text | ].
    destruct (unop_paren o e0);
      [ apply no_nl_app; [ no_nl_lit | apply no_nl_app; [ apply IHe0 | no_nl_lit ] ] | apply IHe0 ].
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
  - (* EHex hz — the hex-literal printer is newline-free *)
    cbn [gprint]. apply no_nl_print_hex.
Qed.
Lemma no_nl_print_stmt : forall s, no_nl (print_stmt s).
Proof.
  intros [e| |r|b|d|x v]; cbn [print_stmt].
  - apply no_nl_gprint.
  - no_nl_lit.
  - apply no_nl_app; [ no_nl_lit | apply no_nl_gprint ].
  - apply no_nl_app; [ no_nl_lit | apply no_nl_gprint ].
  - apply no_nl_app; [ no_nl_lit | apply no_nl_gprint ].
  - apply no_nl_app; [ apply no_nl_ident | apply no_nl_app; [ no_nl_lit | apply no_nl_gprint ] ].
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

(** GATE — digits.v + GoAst.v + GoPrint.v are the CERTIFIED printer spine (VERIFIED, not trusted): the
    EXTRACTED printer is governed by these theorems, so they MUST stay axiom-free — that is what keeps the
    spine from adding project axioms to the TCB.  The build (Dockerfile prover stage) compiles all three
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
Print Assumptions gprint_expr_canonical.
Print Assumptions canon_expr_tokens.
Print Assumptions lex_gprint_expr.
Print Assumptions canon_ty_unique.
Print Assumptions gttokens_ty_inj.
Print Assumptions gtokens_balanced.
Print Assumptions last0_group.
Print Assumptions balanced_close_split.
Print Assumptions sep_split.
Print Assumptions no_depth0_sep.
Print Assumptions gtokens_args_inj.
Print Assumptions gtokens_pairs_inj.
Print Assumptions bare_not_paren_group.
Print Assumptions gtparen_inj.
Print Assumptions op_token_inj.
Print Assumptions prefix_token_inj.
Print Assumptions skip_gty_types.
Print Assumptions skip_gty_lt.
Print Assumptions eb_find_lt.
Print Assumptions eb_find_pi.
Print Assumptions eb_depth_ty.

(** Extract the Rocq printers to the OCaml the plugin calls. *)
Require Import Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "printer.ml" print_ty print_Z print_string_lit print_hex print_float_hex f64_bounded print_sep nominal_type_ident go_ident hexz_ok binop_prec binop_text gprint.
