From Stdlib Require Import String Ascii NArith ZArith List Bool Lia.
From Fido Require Import Decimal Float Complex ModulePath Version Names Syntax.
Import ListNotations.
Open Scope string_scope.

Definition nl_c : ascii := ascii_of_nat 10.
Definition tab_c : ascii := ascii_of_nat 9.
Definition nl : string := String nl_c EmptyString.
Definition tab : string := String tab_c EmptyString.

(* The exact first line of every generated file; note the two spaces after the period. *)
Definition header : string := "// fido was here.  woof woof.  do not edit.".

(* The canonical Go interpreted string literal: one spelling per semantic byte sequence. *)

Definition cr_c     : ascii := ascii_of_nat 13.
Definition dquote_c : ascii := ascii_of_nat 34.   (* the double-quote byte 0x22 *)
Definition bslash_c : ascii := ascii_of_nat 92.

Definition hex_digit (k : nat) : ascii :=
  if Nat.ltb k 10 then ascii_of_nat (48 + k) else ascii_of_nat (87 + k).

Definition hex_escape (c : ascii) : string :=
  let n := nat_of_ascii c in
  String bslash_c (String "x"%char
    (String (hex_digit (Nat.div n 16)) (String (hex_digit (Nat.modulo n 16)) EmptyString))).

Definition string_byte (c : ascii) : string :=
  let n := nat_of_ascii c in
  if Nat.eqb n 34 then String bslash_c (String dquote_c EmptyString)
  else if Nat.eqb n 92 then String bslash_c (String bslash_c EmptyString)
  else if Nat.eqb n 10 then String bslash_c (String "n"%char EmptyString)
  else if Nat.eqb n 9  then String bslash_c (String "t"%char EmptyString)
  else if Nat.eqb n 13 then String bslash_c (String "r"%char EmptyString)
  else if andb (Nat.leb 32 n) (Nat.leb n 126) then String c EmptyString
  else hex_escape c.

Fixpoint string_body (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => string_byte c ++ string_body s'
  end.

Definition string_literal (s : string) : string :=
  String dquote_c (string_body s ++ String dquote_c EmptyString).

Definition signed_Z (z : Z) : string :=
  if Z.ltb z 0 then String "-"%char (Decimal.integer (Z.opp z)) else Decimal.integer z.

(* The exponent field carries an explicit sign, so every canonical float spelling is self-delimiting. *)
Definition signed_exp (e : Z) : string :=
  if Z.ltb e 0 then String "-"%char (Decimal.integer (Z.opp e)) else String "+"%char (Decimal.integer e).

(* The one canonical decimal float spelling: `0.0`, or `<coefficient>.0e<signed exponent>`. *)
Definition decimal (d : Float.Decimal) : string :=
  if Z.eqb (Float.coefficient d) 0 then "0.0"
  else signed_Z (Float.coefficient d) ++ ".0e" ++ signed_exp (Float.exponent d).

(* The one canonical complex spelling, `complex(<real>, <imag>)`; this is not a general call renderer. *)
Definition complex_literal (dc : Complex.Decimal) : string :=
  "complex(" ++ decimal (Complex.decimal_real dc) ++ ", " ++ decimal (Complex.decimal_imaginary dc) ++ ")".

(* A conversion type name renders its retained source identifier, not its resolved semantic type. *)
Definition type_expr (ts : Syntax.TypeExpr) : string :=
  Names.render_supported (Syntax.type_expr_supported ts).

Lemma type_expr_spelling : forall ts,
  type_expr ts = Names.type_name_spelling (Syntax.type_expr_name ts).
Proof. intro ts; unfold type_expr, Names.render_supported, Syntax.type_expr_name; apply Names.supported_render. Qed.

Lemma type_expr_inj : forall ts1 ts2,
  type_expr ts1 = type_expr ts2 -> ts1 = ts2.
Proof.
  intros [[s1]] [[s2]] H.
  unfold type_expr, Syntax.type_expr_supported, Names.render_supported, Names.render_identifier in H; cbn in H.
  f_equal; f_equal; apply Names.supported_equal, Names.identifier_equal; exact H.
Qed.

Lemma conv_byte_neq_uint8 :
  type_expr (Syntax.type_expr_of_name Names.Byte) <> type_expr (Syntax.type_expr_of_name Names.Uint8).
Proof. unfold type_expr; rewrite !Syntax.type_expr_supported_of; apply Names.render_supported_byte_neq_uint8. Qed.
Lemma conv_rune_neq_int32 :
  type_expr (Syntax.type_expr_of_name Names.Rune) <> type_expr (Syntax.type_expr_of_name Names.Int32).
Proof. unfold type_expr; rewrite !Syntax.type_expr_supported_of; apply Names.render_supported_rune_neq_int32. Qed.

Fixpoint expr (e : Syntax.Expr) : string :=
  match e with
  | Syntax.BoolLiteral true  => "true"
  | Syntax.BoolLiteral false => "false"
  | Syntax.IntegerLiteral n => Decimal.integer (Z.of_N n)
  | Syntax.NegatedIntegerLiteral n => String "-"%char (Decimal.integer (Z.of_N n))
  | Syntax.StringLiteral s => string_literal s
  | Syntax.FloatLiteral d => decimal d
  | Syntax.ComplexLiteral dc => complex_literal dc
  | Syntax.Convert ts e' => type_expr ts ++ "(" ++ expr e' ++ ")"
  end.

Fixpoint arguments (es : list Syntax.Expr) : string :=
  match es with
  | []       => ""
  | [e]      => expr e
  | e :: es' => expr e ++ ", " ++ arguments es'
  end.

Definition stmt (s : Syntax.Stmt) : string :=
  match s with Syntax.Println args => tab ++ "println(" ++ arguments args ++ ")" ++ nl end.

Fixpoint statements (ss : list Syntax.Stmt) : string :=
  match ss with [] => "" | s :: ss' => stmt s ++ statements ss' end.

Definition decl (d : Syntax.Decl) : string :=
  match d with Syntax.Main body => "func main() {" ++ nl ++ statements body ++ "}" ++ nl end.

(* Each top-level declaration is preceded by a blank line, matching gofmt spacing. *)
Fixpoint declarations (ds : list Syntax.Decl) : string :=
  match ds with [] => "" | d :: ds' => nl ++ decl d ++ declarations ds' end.

(* The package clause as rendered bytes, owned by the source rather than derived. *)
Definition package_clause (pc : Syntax.PackageClause) : string :=
  match pc with Syntax.MainPackage => "main" end.

(* [file] consumes the import list structurally, so a future constructor forces a renderer update. *)
Definition import_spec (i : Syntax.ImportSpec) : string := match i with end.
Fixpoint imports (xs : list Syntax.ImportSpec) : string :=
  match xs with [] => "" | i :: rest => import_spec i ++ imports rest end.

Lemma imports_nil_bytes : forall xs, imports xs = ""%string.
Proof. intros [|i rest]; [ reflexivity | destruct i ]. Qed.

Definition file (f : Syntax.File) : string :=
  header ++ String nl_c (nl ++ "package " ++ package_clause (Syntax.package f) ++ nl
                            ++ imports (Syntax.imports f)
                            ++ declarations (Syntax.declarations f)).

(* The header is exactly the first line, which is strictly stronger than being a prefix. *)
Lemma file_first_line : forall f, exists rest, file f = header ++ String nl_c rest.
Proof. intros f. unfold file. eexists. reflexivity. Qed.

(* The canonical go.mod: the header line, then `module <path>` and `go <version>`, and nothing else. *)
Definition module_file (ms : ModuleSpec) : string :=
  header ++ String nl_c
    (nl ++ "module " ++ ModulePath.text (module_path ms) ++ nl ++ nl
        ++ "go " ++ Version.render (Syntax.module_version ms) ++ nl).

Lemma module_file_first_line : forall ms, exists rest, module_file ms = header ++ String nl_c rest.
Proof. intro ms. unfold module_file. eexists. reflexivity. Qed.

Lemma module_file_exact : forall ms,
  module_file ms = header ++ String nl_c
    (nl ++ "module " ++ ModulePath.text (module_path ms) ++ nl ++ nl
        ++ "go " ++ Version.render (Syntax.module_version ms) ++ nl).
Proof. reflexivity. Qed.


Lemma str_ascii_app : forall a b, Names.str_ascii (a ++ b) = Names.str_ascii a && Names.str_ascii b.
Proof.
  induction a as [ | c a' IH ]; intro b; simpl; [ reflexivity | rewrite IH, andb_assoc; reflexivity ].
Qed.

Lemma type_expr_ascii : forall ts, Names.str_ascii (type_expr ts) = true.
Proof. intro ts; rewrite type_expr_spelling; destruct (Syntax.type_expr_name ts); reflexivity. Qed.

Lemma str_ascii_cons : forall c s, Names.str_ascii (String c s) = Names.is_ascii_c c && Names.str_ascii s.
Proof. reflexivity. Qed.

Lemma digit_ascii : forall d, (d < 10)%nat -> Names.is_ascii_c (Decimal.digit d) = true.
Proof. intros d Hd. do 10 (destruct d as [ | d ]; [ reflexivity | ]). lia. Qed.

Lemma digits_step : forall dig a ds acc,
  Decimal.render dig (a :: ds) acc = Decimal.render dig ds (String (dig a) acc).
Proof. reflexivity. Qed.

Lemma digits_ascii : forall ds acc,
  (forall d, In d ds -> Names.is_ascii_c (Decimal.digit d) = true) ->
  Names.str_ascii (Decimal.render Decimal.digit ds acc) = Names.str_ascii acc.
Proof.
  induction ds as [ | a ds' IH ]; intros acc Hall.
  - reflexivity.
  - rewrite digits_step, IH.
    + cbn [Names.str_ascii]. rewrite (Hall a (or_introl eq_refl)). reflexivity.
    + intros d Hd. apply Hall. right. exact Hd.
Qed.

Lemma positive_ascii : forall p, Names.str_ascii (Decimal.positive p) = true.
Proof.
  intro p. unfold Decimal.positive. rewrite digits_ascii; [ reflexivity | ].
  intros d Hd. apply digit_ascii.
  pose proof (Decimal.positive_digits_bound 10 p ltac:(lia)) as Hb. rewrite Forall_forall in Hb. apply Hb; exact Hd.
Qed.

Lemma integer_ascii : forall z, Names.str_ascii (Decimal.integer z) = true.
Proof.
  intros [ | p | p ].
  - reflexivity.
  - apply positive_ascii.
  - cbn [Decimal.integer]. rewrite str_ascii_app, positive_ascii. reflexivity.
Qed.

(* String rendering stays ASCII even for high bytes, which appear only as `\xhh` escapes. *)

Lemma nat_of_ascii_lt_256 : forall c, (nat_of_ascii c < 256)%nat.
Proof.
  intro c. destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0, b1, b2, b3, b4, b5, b6, b7; cbn; lia.
Qed.

Lemma hex_digit_ascii : forall k, (k < 16)%nat -> Names.is_ascii_c (hex_digit k) = true.
Proof.
  intros k Hk. unfold hex_digit, Names.is_ascii_c. destruct (Nat.ltb k 10) eqn:E.
  - apply Nat.ltb_lt in E. rewrite nat_ascii_embedding by lia.
    rewrite (proj2 (Nat.ltb_lt _ _)) by lia; reflexivity.
  - apply Nat.ltb_ge in E. rewrite nat_ascii_embedding by lia.
    rewrite (proj2 (Nat.ltb_lt _ _)) by lia; reflexivity.
Qed.

Lemma hex_escape_ascii : forall c, Names.str_ascii (hex_escape c) = true.
Proof.
  intro c. unfold hex_escape.
  assert (Hhi : (Nat.div (nat_of_ascii c) 16 < 16)%nat).
  { pose proof (nat_of_ascii_lt_256 c) as Hb. apply Nat.Div0.div_lt_upper_bound. lia. }
  assert (Hlo : (Nat.modulo (nat_of_ascii c) 16 < 16)%nat) by (apply Nat.mod_upper_bound; lia).
  cbn [Names.str_ascii]. rewrite (hex_digit_ascii _ Hhi), (hex_digit_ascii _ Hlo). reflexivity.
Qed.

Lemma string_byte_ascii : forall c, Names.str_ascii (string_byte c) = true.
Proof.
  intro c. unfold string_byte.
  destruct (Nat.eqb (nat_of_ascii c) 34); [ reflexivity | ].
  destruct (Nat.eqb (nat_of_ascii c) 92); [ reflexivity | ].
  destruct (Nat.eqb (nat_of_ascii c) 10); [ reflexivity | ].
  destruct (Nat.eqb (nat_of_ascii c) 9);  [ reflexivity | ].
  destruct (Nat.eqb (nat_of_ascii c) 13); [ reflexivity | ].
  destruct (andb (Nat.leb 32 (nat_of_ascii c)) (Nat.leb (nat_of_ascii c) 126)) eqn:Hp.
  - cbn [Names.str_ascii]. rewrite Bool.andb_true_r.
    apply Bool.andb_true_iff in Hp as [_ Hle]. apply Nat.leb_le in Hle.
    unfold Names.is_ascii_c. assert (Hlt : (nat_of_ascii c < 128)%nat) by lia.
    rewrite (proj2 (Nat.ltb_lt _ _) Hlt). reflexivity.
  - apply hex_escape_ascii.
Qed.

Lemma string_body_ascii : forall s, Names.str_ascii (string_body s) = true.
Proof.
  induction s as [ | c s' IH ]; [ reflexivity | ].
  cbn [string_body]. rewrite str_ascii_app, string_byte_ascii, IH. reflexivity.
Qed.

Lemma string_literal_ascii : forall s, Names.str_ascii (string_literal s) = true.
Proof.
  intro s. unfold string_literal. cbn [Names.str_ascii].
  rewrite str_ascii_app, string_body_ascii. reflexivity.
Qed.

Lemma signed_Z_ascii : forall z, Names.str_ascii (signed_Z z) = true.
Proof.
  intro z; unfold signed_Z; destruct (Z.ltb z 0).
  - cbn [Names.str_ascii]; rewrite integer_ascii; reflexivity.
  - apply integer_ascii.
Qed.
Lemma signed_exp_ascii : forall e, Names.str_ascii (signed_exp e) = true.
Proof. intro e; unfold signed_exp; destruct (Z.ltb e 0); cbn [Names.str_ascii]; rewrite integer_ascii; reflexivity. Qed.
Lemma decimal_ascii : forall d, Names.str_ascii (decimal d) = true.
Proof.
  intro d; unfold decimal; destruct (Z.eqb (Float.coefficient d) 0).
  - reflexivity.
  - rewrite !str_ascii_app, signed_Z_ascii, signed_exp_ascii; reflexivity.
Qed.
Lemma complex_literal_ascii : forall dc, Names.str_ascii (complex_literal dc) = true.
Proof.
  intro dc; unfold complex_literal.
  rewrite !str_ascii_app, !decimal_ascii; reflexivity.
Qed.

Lemma expr_ascii : forall e, Names.str_ascii (expr e) = true.
Proof.
  induction e as [ [] | n | n | s | d | dc | ts e' IHe' ]; cbn [expr].
  - reflexivity.
  - reflexivity.
  - apply integer_ascii.
  - cbn [Names.str_ascii]. rewrite integer_ascii. reflexivity.
  - apply string_literal_ascii.
  - apply decimal_ascii.
  - apply complex_literal_ascii.
  - rewrite !str_ascii_app, type_expr_ascii, IHe'; reflexivity.
Qed.

Lemma arguments_ascii : forall es, Names.str_ascii (arguments es) = true.
Proof.
  induction es as [ | e es' IH ]; [ reflexivity | ].
  destruct es' as [ | e2 es'' ].
  - apply expr_ascii.
  - change (arguments (e :: e2 :: es''))
      with (expr e ++ ", " ++ arguments (e2 :: es'')).
    rewrite !str_ascii_app, expr_ascii. simpl. exact IH.
Qed.

Lemma stmt_ascii : forall s, Names.str_ascii (stmt s) = true.
Proof. intros [ args ]. cbn [stmt]. rewrite !str_ascii_app, arguments_ascii. reflexivity. Qed.

Lemma statements_ascii : forall ss, Names.str_ascii (statements ss) = true.
Proof.
  induction ss as [ | s ss' IH ]; [ reflexivity | ].
  cbn [statements]. rewrite str_ascii_app, stmt_ascii, IH. reflexivity.
Qed.

Lemma decl_ascii : forall d, Names.str_ascii (decl d) = true.
Proof. intros [ body ]. cbn [decl]. rewrite !str_ascii_app, statements_ascii. reflexivity. Qed.

Lemma declarations_ascii : forall ds, Names.str_ascii (declarations ds) = true.
Proof.
  induction ds as [ | d ds' IH ]; [ reflexivity | ].
  cbn [declarations]. rewrite !str_ascii_app, decl_ascii, IH. reflexivity.
Qed.

Lemma imports_ascii : forall xs, Names.str_ascii (imports xs) = true.
Proof. intros xs; rewrite imports_nil_bytes; reflexivity. Qed.

Theorem file_ascii : forall f, Names.str_ascii (file f) = true.
Proof.
  intros f. unfold file. rewrite str_ascii_app. cbn [Names.str_ascii].
  rewrite !str_ascii_app, declarations_ascii, imports_ascii.
  destruct (Syntax.package f); reflexivity.
Qed.


Lemma all_path_chars_ascii : forall s, ModulePath.all_path_chars s = true -> Names.str_ascii s = true.
Proof.
  induction s as [ | c s' IH ]; intro H; [ reflexivity | ].
  cbn [ModulePath.all_path_chars] in H; apply Bool.andb_true_iff in H as [Hc Hs].
  cbn [Names.str_ascii]; unfold Names.is_ascii_c.
  rewrite (proj2 (Nat.ltb_lt _ _) (ModulePath.path_char_lt_128 c Hc)); cbn [andb].
  apply IH; exact Hs.
Qed.

Lemma module_path_text_ascii : forall p, Names.str_ascii (ModulePath.text p) = true.
Proof. intro p. apply all_path_chars_ascii, ModulePath.path_ok_all_chars. exact (ModulePath.valid p). Qed.

Theorem module_file_ascii : forall ms, Names.str_ascii (module_file ms) = true.
Proof.
  intro ms. unfold module_file.
  rewrite str_ascii_app, str_ascii_cons, !str_ascii_app, module_path_text_ascii.
  destruct (Syntax.module_version ms); reflexivity.
Qed.

(* Decimal faithfulness: an emitted decimal denotes exactly its value, with no leading zero. *)

Definition ascii_digit (c : ascii) : nat := nat_of_ascii c - 48.

Fixpoint dval (s : string) (acc : Z) : Z :=
  match s with EmptyString => acc | String c s' => dval s' (acc * 10 + Z.of_nat (ascii_digit c)) end.
Definition dval0 (s : string) : Z := dval s 0.

Lemma ascii_digit_is_digit : forall d, (d < 10)%nat -> ascii_digit (Decimal.digit d) = d.
Proof. intros d Hd. do 10 (destruct d as [ | d ]; [ reflexivity | ]). lia. Qed.

Lemma digits_dval : forall ds base,
  (forall d, In d ds -> (d < 10)%nat) ->
  dval (Decimal.render Decimal.digit ds base) 0 = dval base (Decimal.value 10 ds).
Proof.
  induction ds as [ | d ds' IH ]; intros base Hall.
  - reflexivity.
  - rewrite digits_step, (IH (String (Decimal.digit d) base))
      by (intros x Hx; apply Hall; right; exact Hx).
    cbn [dval]. rewrite ascii_digit_is_digit by (apply Hall; left; reflexivity).
    cbn [Decimal.value]. f_equal. change (Z.of_nat 10) with 10%Z. lia.
Qed.

Lemma positive_digit_value : forall p, dval0 (Decimal.positive p) = Z.pos p.
Proof.
  intro p. unfold dval0, Decimal.positive. rewrite digits_dval.
  - cbn [dval]. rewrite Decimal.positive_digits_val by lia. reflexivity.
  - intros d Hd. pose proof (Decimal.positive_digits_bound 10 p ltac:(lia)) as Hb.
    rewrite Forall_forall in Hb. apply Hb; exact Hd.
Qed.

Theorem integer_decimal_faithful : forall z, (0 <= z)%Z -> dval0 (Decimal.integer z) = z.
Proof.
  intros [ | p | p ] H.
  - reflexivity.
  - apply positive_digit_value.
  - exfalso; lia.
Qed.

Definition head_not_zero (s : string) : Prop :=
  match s with EmptyString => False | String c _ => c <> Decimal.digit 0 end.

Lemma digits_snoc : forall ds a base,
  Decimal.render Decimal.digit (ds ++ [a]) base = String (Decimal.digit a) (Decimal.render Decimal.digit ds base).
Proof. intros. unfold Decimal.render. rewrite fold_left_app. reflexivity. Qed.

Theorem positive_no_leading_zero : forall p, head_not_zero (Decimal.positive p).
Proof.
  intro p. unfold Decimal.positive.
  destruct (exists_last (Decimal.positive_digits_nonnil 10 p)) as [init [a Ha]].
  rewrite Ha, digits_snoc. cbn [head_not_zero].
  assert (Ha1 : (1 <= a)%nat).
  { pose proof (Decimal.positive_digits_last 10 p ltac:(lia)) as Hl. rewrite Ha, last_last in Hl. exact Hl. }
  assert (Ha10 : (a < 10)%nat).
  { pose proof (Decimal.positive_digits_bound 10 p ltac:(lia)) as Hb. rewrite Ha, Forall_forall in Hb.
    apply Hb, in_or_app; right; left; reflexivity. }
  intro Heq.
  assert (Hn : nat_of_ascii (Decimal.digit a) = nat_of_ascii (Decimal.digit 0)) by (rewrite Heq; reflexivity).
  unfold Decimal.digit in Hn.
  rewrite (nat_ascii_embedding (48 + a)) in Hn by lia.
  rewrite (nat_ascii_embedding (48 + 0)) in Hn by lia.
  lia.
Qed.

Definition read_go_int (s : string) : Z :=
  match s with
  | String c s' => if Ascii.eqb c "-"%char then Z.opp (dval0 s') else dval0 s
  | EmptyString => dval0 s
  end.

(* An independent decoder defined by its own recursion; it is a denotation tool, not a spelling recogniser. *)

Definition decode_hex_digit (c : ascii) : option nat :=
  if andb (Nat.leb 48 (nat_of_ascii c)) (Nat.leb (nat_of_ascii c) 57) then Some ((nat_of_ascii c - 48)%nat)
  else if andb (Nat.leb 97 (nat_of_ascii c)) (Nat.leb (nat_of_ascii c) 102) then Some ((nat_of_ascii c - 87)%nat)
  else None.

Fixpoint decode_string_body (s : string) : option string :=
  match s with
  | EmptyString => None                                         (* ran off the end without a closing quote *)
  | String c rest =>
      if Ascii.eqb c dquote_c then                              (* closing quote *)
        match rest with EmptyString => Some EmptyString | _ => None end   (* trailing bytes ⇒ reject *)
      else if Ascii.eqb c bslash_c then                         (* an escape *)
        match rest with
        | EmptyString => None
        | String e rest2 =>
            if Ascii.eqb e dquote_c then option_map (String dquote_c) (decode_string_body rest2)
            else if Ascii.eqb e bslash_c then option_map (String bslash_c) (decode_string_body rest2)
            else if Ascii.eqb e "n"%char then option_map (String nl_c) (decode_string_body rest2)
            else if Ascii.eqb e "t"%char then option_map (String tab_c) (decode_string_body rest2)
            else if Ascii.eqb e "r"%char then option_map (String cr_c) (decode_string_body rest2)
            else if Ascii.eqb e "x"%char then
              match rest2 with
              | String h1 (String h2 rest3) =>
                  match decode_hex_digit h1, decode_hex_digit h2 with
                  | Some v1, Some v2 =>
                      option_map (String (ascii_of_nat (v1 * 16 + v2))) (decode_string_body rest3)
                  | _, _ => None                                (* nonhex digit *)
                  end
              | _ => None                                       (* truncated \x *)
              end
            else None                                           (* unknown escape *)
        end
      else if andb (Nat.leb 32 (nat_of_ascii c)) (Nat.leb (nat_of_ascii c) 126) then
        option_map (String c) (decode_string_body rest)         (* a directly-emitted printable byte *)
      else None                                                 (* an unescaped control/newline byte ⇒ reject *)
  end.

Definition decode_string_literal (s : string) : option string :=
  match s with
  | String c rest => if Ascii.eqb c dquote_c then decode_string_body rest else None
  | EmptyString => None
  end.

Lemma str_app_assoc : forall a b d : string, (a ++ (b ++ d))%string = ((a ++ b) ++ d)%string.
Proof.
  intros a; induction a as [ | c a' IH ]; intros b d; simpl;
    [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma hex_digit_decode : forall k, (k < 16)%nat -> decode_hex_digit (hex_digit k) = Some k.
Proof.
  intros k Hk. unfold decode_hex_digit, hex_digit. destruct (Nat.ltb k 10) eqn:E.
  - apply Nat.ltb_lt in E. rewrite nat_ascii_embedding by lia.
    rewrite (proj2 (Nat.leb_le 48 (48 + k))) by lia.
    rewrite (proj2 (Nat.leb_le (48 + k) 57)) by lia. cbn [andb]. f_equal. lia.
  - apply Nat.ltb_ge in E. rewrite nat_ascii_embedding by lia.
    rewrite (proj2 (Nat.leb_le 48 (87 + k))) by lia.
    rewrite (proj2 (Nat.leb_gt (87 + k) 57)) by lia. cbn [andb].
    rewrite (proj2 (Nat.leb_le 97 (87 + k))) by lia.
    rewrite (proj2 (Nat.leb_le (87 + k) 102)) by lia. cbn [andb]. f_equal. lia.
Qed.

Lemma byte_reconstruct : forall c,
  ascii_of_nat (Nat.div (nat_of_ascii c) 16 * 16 + Nat.modulo (nat_of_ascii c) 16) = c.
Proof.
  intro c. pose proof (Nat.div_mod_eq (nat_of_ascii c) 16) as Hd.
  replace ((Nat.div (nat_of_ascii c) 16 * 16 + Nat.modulo (nat_of_ascii c) 16)%nat)
    with (nat_of_ascii c) by lia.
  apply ascii_nat_embedding.
Qed.

Opaque hex_digit decode_hex_digit.

Lemma decode_hex_prefix : forall hi lo tail,
  (hi < 16)%nat -> (lo < 16)%nat ->
  decode_string_body
    (String bslash_c (String "x"%char (String (hex_digit hi) (String (hex_digit lo) tail))))
  = option_map (String (ascii_of_nat (hi * 16 + lo))) (decode_string_body tail).
Proof.
  intros hi lo tail Hhi Hlo. cbn. rewrite (hex_digit_decode hi Hhi), (hex_digit_decode lo Hlo). reflexivity.
Qed.

Lemma hex_escape_exact : forall c tail,
  decode_string_body (hex_escape c ++ tail) = option_map (String c) (decode_string_body tail).
Proof.
  intros c tail. pose proof (nat_of_ascii_lt_256 c) as Hb.
  assert (Hhi : (Nat.div (nat_of_ascii c) 16 < 16)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
  assert (Hlo : (Nat.modulo (nat_of_ascii c) 16 < 16)%nat) by (apply Nat.mod_upper_bound; lia).
  unfold hex_escape. cbn [append].
  rewrite (decode_hex_prefix _ _ _ Hhi Hlo), byte_reconstruct. reflexivity.
Qed.

Lemma decode_render_byte : forall c tail,
  decode_string_body (string_byte c ++ tail) = option_map (String c) (decode_string_body tail).
Proof.
  intros c tail. pose proof (nat_of_ascii_lt_256 c) as Hb. unfold string_byte.
  destruct (Nat.eqb (nat_of_ascii c) 34) eqn:E34.
  { apply Nat.eqb_eq in E34.
    replace c with dquote_c by (unfold dquote_c; rewrite <- E34; apply ascii_nat_embedding). reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 92) eqn:E92.
  { apply Nat.eqb_eq in E92.
    replace c with bslash_c by (unfold bslash_c; rewrite <- E92; apply ascii_nat_embedding). reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 10) eqn:E10.
  { apply Nat.eqb_eq in E10.
    replace c with nl_c by (unfold nl_c; rewrite <- E10; apply ascii_nat_embedding). reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 9) eqn:E9.
  { apply Nat.eqb_eq in E9.
    replace c with tab_c by (unfold tab_c; rewrite <- E9; apply ascii_nat_embedding). reflexivity. }
  destruct (Nat.eqb (nat_of_ascii c) 13) eqn:E13.
  { apply Nat.eqb_eq in E13.
    replace c with cr_c by (unfold cr_c; rewrite <- E13; apply ascii_nat_embedding). reflexivity. }
  destruct (andb (Nat.leb 32 (nat_of_ascii c)) (Nat.leb (nat_of_ascii c) 126)) eqn:Hp.
  { cbn [append].
    assert (Hnd : Ascii.eqb c dquote_c = false).
    { apply Bool.not_true_is_false; intro Hq; apply Ascii.eqb_eq in Hq; subst c;
        unfold dquote_c in E34; rewrite nat_ascii_embedding in E34 by lia; discriminate E34. }
    assert (Hnb : Ascii.eqb c bslash_c = false).
    { apply Bool.not_true_is_false; intro Hq; apply Ascii.eqb_eq in Hq; subst c;
        unfold bslash_c in E92; rewrite nat_ascii_embedding in E92 by lia; discriminate E92. }
    cbn [decode_string_body]. rewrite Hnd, Hnb, Hp. reflexivity. }
  { apply hex_escape_exact. }
Qed.

Transparent hex_digit decode_hex_digit.

Lemma decode_body_render : forall s,
  decode_string_body (string_body s ++ String dquote_c EmptyString) = Some s.
Proof.
  induction s as [ | c s' IH ]; cbn [string_body].
  - cbn [append]. reflexivity.
  - rewrite <- str_app_assoc, decode_render_byte, IH. reflexivity.
Qed.

Theorem string_roundtrip : forall s, decode_string_literal (string_literal s) = Some s.
Proof.
  intro s. unfold string_literal. cbn [decode_string_literal].
  rewrite Ascii.eqb_refl. apply decode_body_render.
Qed.

(* The literal is quote-delimited and holds no raw newline or carriage return. *)
Definition byte_not_nl_cr (c : ascii) : bool :=
  andb (negb (Nat.eqb (nat_of_ascii c) 10)) (negb (Nat.eqb (nat_of_ascii c) 13)).
Fixpoint str_no_nl_cr (s : string) : bool :=
  match s with EmptyString => true | String c s' => andb (byte_not_nl_cr c) (str_no_nl_cr s') end.

Lemma str_no_nl_cr_app : forall a b, str_no_nl_cr (a ++ b) = andb (str_no_nl_cr a) (str_no_nl_cr b).
Proof.
  induction a as [ | c a' IH ]; intro b; simpl; [ reflexivity | rewrite IH, Bool.andb_assoc; reflexivity ].
Qed.

Lemma hex_digit_not_nl_cr : forall k, (k < 16)%nat -> byte_not_nl_cr (hex_digit k) = true.
Proof.
  intros k Hk. unfold byte_not_nl_cr, hex_digit. destruct (Nat.ltb k 10) eqn:E.
  - apply Nat.ltb_lt in E. rewrite nat_ascii_embedding by lia.
    rewrite (proj2 (Nat.eqb_neq (48 + k) 10)) by lia.
    rewrite (proj2 (Nat.eqb_neq (48 + k) 13)) by lia. reflexivity.
  - apply Nat.ltb_ge in E. rewrite nat_ascii_embedding by lia.
    rewrite (proj2 (Nat.eqb_neq (87 + k) 10)) by lia.
    rewrite (proj2 (Nat.eqb_neq (87 + k) 13)) by lia. reflexivity.
Qed.

Lemma hex_escape_no_nl_cr : forall c, str_no_nl_cr (hex_escape c) = true.
Proof.
  intro c. pose proof (nat_of_ascii_lt_256 c) as Hb.
  assert (Hhi : (Nat.div (nat_of_ascii c) 16 < 16)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
  assert (Hlo : (Nat.modulo (nat_of_ascii c) 16 < 16)%nat) by (apply Nat.mod_upper_bound; lia).
  unfold hex_escape. cbn [str_no_nl_cr].
  rewrite (hex_digit_not_nl_cr _ Hhi), (hex_digit_not_nl_cr _ Hlo). reflexivity.
Qed.

Lemma string_byte_no_nl_cr : forall c, str_no_nl_cr (string_byte c) = true.
Proof.
  intro c. unfold string_byte.
  destruct (Nat.eqb (nat_of_ascii c) 34); [ reflexivity | ].
  destruct (Nat.eqb (nat_of_ascii c) 92); [ reflexivity | ].
  destruct (Nat.eqb (nat_of_ascii c) 10) eqn:E10; [ reflexivity | ].
  destruct (Nat.eqb (nat_of_ascii c) 9);  [ reflexivity | ].
  destruct (Nat.eqb (nat_of_ascii c) 13) eqn:E13; [ reflexivity | ].
  destruct (andb (Nat.leb 32 (nat_of_ascii c)) (Nat.leb (nat_of_ascii c) 126)) eqn:Hp.
  - cbn [str_no_nl_cr]. unfold byte_not_nl_cr. rewrite E10, E13. reflexivity.
  - apply hex_escape_no_nl_cr.
Qed.

Lemma string_body_no_nl_cr : forall s, str_no_nl_cr (string_body s) = true.
Proof.
  induction s as [ | c s' IH ]; [ reflexivity | ].
  cbn [string_body]. rewrite str_no_nl_cr_app, string_byte_no_nl_cr, IH. reflexivity.
Qed.

Lemma string_literal_no_nl_cr : forall s, str_no_nl_cr (string_literal s) = true.
Proof.
  intro s. unfold string_literal. cbn [str_no_nl_cr].
  rewrite str_no_nl_cr_app, string_body_no_nl_cr. reflexivity.
Qed.

Lemma string_literal_quotes : forall s,
  string_literal s = String dquote_c (string_body s ++ String dquote_c EmptyString).
Proof. reflexivity. Qed.

Example byte_escape_quote  : string_byte (ascii_of_nat 34)  = String bslash_c (String dquote_c EmptyString).
Proof. reflexivity. Qed.
Example byte_escape_backslash : string_byte (ascii_of_nat 92)  = String bslash_c (String bslash_c EmptyString).
Proof. reflexivity. Qed.
Example byte_escape_nl : string_byte (ascii_of_nat 10) = String bslash_c (String "n"%char EmptyString).
Proof. reflexivity. Qed.
Example byte_escape_tab : string_byte (ascii_of_nat 9)  = String bslash_c (String "t"%char EmptyString).
Proof. reflexivity. Qed.
Example byte_escape_cr : string_byte (ascii_of_nat 13) = String bslash_c (String "r"%char EmptyString).
Proof. reflexivity. Qed.
Example byte_escape_nul : string_byte (ascii_of_nat 0)
  = String bslash_c (String "x"%char (String "0"%char (String "0"%char EmptyString))).
Proof. reflexivity. Qed.
Example byte_escape_del : string_byte (ascii_of_nat 127)
  = String bslash_c (String "x"%char (String "7"%char (String "f"%char EmptyString))).
Proof. reflexivity. Qed.
Example byte_escape_80 : string_byte (ascii_of_nat 128)
  = String bslash_c (String "x"%char (String "8"%char (String "0"%char EmptyString))).
Proof. reflexivity. Qed.
Example byte_escape_ff : string_byte (ascii_of_nat 255)
  = String bslash_c (String "x"%char (String "f"%char (String "f"%char EmptyString))).
Proof. reflexivity. Qed.
Example literal_empty : string_literal "" = String dquote_c (String dquote_c EmptyString).
Proof. reflexivity. Qed.
Example literal_ascii : string_literal "hi"
  = String dquote_c (String "h"%char (String "i"%char (String dquote_c EmptyString))).
Proof. reflexivity. Qed.

(* The render-time constant-status authority speaks the same untyped and typed vocabulary [Typing] owns. *)
Definition digit_value (c : ascii) : option nat :=
  let n := nat_of_ascii c in
  if andb (Nat.leb 48 n) (Nat.leb n 57) then Some (n - 48)%nat else None.

Definition head_not_digit (s : string) : Prop :=
  match s with EmptyString => True | String c _ => digit_value c = None end.

Fixpoint read_nat (s : string) (acc : Z) : Z * string :=
  match s with
  | EmptyString => (acc, s)
  | String c s' => match digit_value c with
                   | Some d => read_nat s' (acc * 10 + Z.of_nat d)
                   | None => (acc, s)
                   end
  end.

Definition read_signed_dec (s : string) : option (Z * string) :=
  match s with
  | EmptyString => None
  | String c s' =>
      if Ascii.eqb c "-"%char then let (m, r) := read_nat s' 0 in Some (Z.opp m, r)
      else if Ascii.eqb c "+"%char then let (m, r) := read_nat s' 0 in Some (m, r)
      else let (m, r) := read_nat s 0 in Some (m, r)
  end.

Definition decode_decimal_body (s : string) : option Float.Constant :=
  match read_signed_dec s with
  | Some (coeff, String a (String b (String c r2))) =>
      if andb (Ascii.eqb a "."%char) (andb (Ascii.eqb b "0"%char) (Ascii.eqb c "e"%char)) then
        match read_signed_dec r2 with
        | Some (exp, EmptyString) => Some (Float.decimal_to_constant coeff exp)
        | _ => None
        end
      else None
  | _ => None
  end.

Definition decode_decimal (s : string) : option Float.Constant :=
  match decode_decimal_body s with
  | Some q => Some q
  | None => if String.eqb s "0.0" then Some Float.constant_zero else None
  end.

Fixpoint str_all_digits (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => match digit_value c with Some _ => str_all_digits s' | None => false end
  end.

Lemma str_app_nil : forall s, (s ++ "")%string = s.
Proof. induction s as [ | c s' IH ]; simpl; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma digit_value_digit : forall d, (d < 10)%nat -> digit_value (Decimal.digit d) = Some d.
Proof.
  intros d Hd. unfold digit_value, Decimal.digit. rewrite nat_ascii_embedding by lia.
  rewrite (proj2 (Nat.leb_le 48 (48 + d))) by lia.
  rewrite (proj2 (Nat.leb_le (48 + d) 57)) by lia.
  cbn [andb]. f_equal. lia.
Qed.

Lemma str_all_digits_render_digits : forall ds acc,
  (forall d, In d ds -> (d < 10)%nat) -> str_all_digits acc = true ->
  str_all_digits (Decimal.render Decimal.digit ds acc) = true.
Proof.
  induction ds as [ | a ds' IH ]; intros acc Hall Hacc; [ exact Hacc | ].
  rewrite digits_step. apply IH; [ intros d Hd; apply Hall; right; exact Hd | ].
  cbn [str_all_digits]. rewrite digit_value_digit by (apply Hall; left; reflexivity). exact Hacc.
Qed.

Lemma str_all_digits_print_Z_pos : forall p, str_all_digits (Decimal.positive p) = true.
Proof.
  intro p; unfold Decimal.positive. apply str_all_digits_render_digits; [ | reflexivity ].
  intros d Hd. pose proof (Decimal.positive_digits_bound 10 p ltac:(lia)) as Hb. rewrite Forall_forall in Hb.
  apply Hb; exact Hd.
Qed.

Lemma str_all_digits_print_Z : forall z, (0 <= z)%Z -> str_all_digits (Decimal.integer z) = true.
Proof. intros [ | p | p ] H; [ reflexivity | apply str_all_digits_print_Z_pos | exfalso; lia ]. Qed.

Lemma read_nat_all_digits : forall s rest acc,
  str_all_digits s = true -> head_not_digit rest -> read_nat (s ++ rest) acc = (dval s acc, rest).
Proof.
  induction s as [ | c s' IH ]; intros rest acc Hdig Hrest.
  - destruct rest as [ | rc rr ]; cbn [append read_nat dval].
    + reflexivity.
    + cbn [head_not_digit] in Hrest. rewrite Hrest. reflexivity.
  - cbn [str_all_digits] in Hdig. destruct (digit_value c) as [d|] eqn:Hc; [| discriminate].
    cbn [append read_nat]. rewrite Hc.
    rewrite (IH rest (acc * 10 + Z.of_nat d) Hdig Hrest). cbn [dval].
    replace (ascii_digit c) with d; [ reflexivity | ].
    unfold ascii_digit; unfold digit_value in Hc.
    destruct (andb (Nat.leb 48 (nat_of_ascii c)) (Nat.leb (nat_of_ascii c) 57)); [| discriminate].
    injection Hc as <-; reflexivity.
Qed.

Lemma char_digit_not : forall c d,
  digit_value c = Some d -> Ascii.eqb c "-"%char = false /\ Ascii.eqb c "+"%char = false.
Proof.
  intros c d Hc; split; destruct (Ascii.eqb c _) eqn:E; try reflexivity;
    apply Ascii.eqb_eq in E; subst c; cbn in Hc; discriminate.
Qed.

Lemma integer_nonempty : forall z, (0 <= z)%Z -> Decimal.integer z <> EmptyString.
Proof.
  intros [ | p | p ] H Hc.
  - cbn [Decimal.integer] in Hc; discriminate.
  - pose proof (integer_decimal_faithful (Zpos p) ltac:(lia)) as Hf.
    rewrite Hc in Hf; cbn in Hf; discriminate Hf.
  - exfalso; lia.
Qed.

Lemma read_signed_dec_all_digits : forall s rest,
  str_all_digits s = true -> s <> EmptyString -> head_not_digit rest ->
  read_signed_dec (s ++ rest) = Some (dval0 s, rest).
Proof.
  intros [ | c s' ] rest Hdig Hne Hrest; [ contradiction | ].
  pose proof Hdig as Hdig'. cbn [str_all_digits] in Hdig.
  destruct (digit_value c) as [d|] eqn:Hc; [| discriminate].
  destruct (char_digit_not c d Hc) as [Hnd Hnp].
  cbn [append]. unfold read_signed_dec. rewrite Hnd, Hnp.
  change (String c (s' ++ rest)) with ((String c s') ++ rest).
  destruct (read_nat ((String c s') ++ rest) 0) as [m r] eqn:E.
  rewrite (read_nat_all_digits (String c s') rest 0 Hdig' Hrest) in E.
  injection E as <- <-. reflexivity.
Qed.

Lemma read_signed_dec_sign : forall sgn mag rest,
  (sgn = "-"%char \/ sgn = "+"%char) -> str_all_digits mag = true -> head_not_digit rest ->
  read_signed_dec (String sgn (mag ++ rest))
  = Some ((if Ascii.eqb sgn "-"%char then Z.opp (dval0 mag) else dval0 mag), rest).
Proof.
  intros sgn mag rest Hsgn Hdig Hrest. unfold read_signed_dec.
  destruct (read_nat (mag ++ rest) 0) as [m r] eqn:E.
  rewrite (read_nat_all_digits mag rest 0 Hdig Hrest) in E. injection E as <- <-.
  destruct Hsgn as [-> | ->]; reflexivity.
Qed.

Lemma read_signed_dec_render_signed_Z : forall z rest, head_not_digit rest ->
  read_signed_dec (signed_Z z ++ rest) = Some (z, rest).
Proof.
  intros z rest Hrest. unfold signed_Z. destruct (Z.ltb z 0) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. cbn [append].
    rewrite (read_signed_dec_sign "-"%char (Decimal.integer (- z)) rest (or_introl eq_refl)
               (str_all_digits_print_Z (- z) ltac:(lia)) Hrest).
    cbn [Ascii.eqb]. rewrite (integer_decimal_faithful (- z) ltac:(lia)). rewrite Z.opp_involutive; reflexivity.
  - apply Z.ltb_ge in Hlt.
    rewrite (read_signed_dec_all_digits (Decimal.integer z) rest (str_all_digits_print_Z z Hlt)
               (integer_nonempty z Hlt) Hrest).
    rewrite (integer_decimal_faithful z Hlt); reflexivity.
Qed.

Lemma read_signed_dec_render_signed_exp : forall z, read_signed_dec (signed_exp z) = Some (z, EmptyString).
Proof.
  intro z. unfold signed_exp. destruct (Z.ltb z 0) eqn:Hlt.
  - apply Z.ltb_lt in Hlt.
    replace (String "-"%char (Decimal.integer (- z))) with (String "-"%char (Decimal.integer (- z) ++ ""))
      by (rewrite str_app_nil; reflexivity).
    rewrite (read_signed_dec_sign "-"%char (Decimal.integer (- z)) "" (or_introl eq_refl)
               (str_all_digits_print_Z (- z) ltac:(lia)) I).
    cbn [Ascii.eqb]. rewrite (integer_decimal_faithful (- z) ltac:(lia)); rewrite Z.opp_involutive; reflexivity.
  - apply Z.ltb_ge in Hlt.
    replace (String "+"%char (Decimal.integer z)) with (String "+"%char (Decimal.integer z ++ ""))
      by (rewrite str_app_nil; reflexivity).
    rewrite (read_signed_dec_sign "+"%char (Decimal.integer z) "" (or_intror eq_refl)
               (str_all_digits_print_Z z Hlt) I).
    cbn [Ascii.eqb]. rewrite (integer_decimal_faithful z Hlt); reflexivity.
Qed.

Lemma head_not_digit_dot0e : forall s, head_not_digit (".0e" ++ s)%string.
Proof. reflexivity. Qed.

(* Without this shape guard the total prefix reader would let a float or `true` also denote an integer. *)
Definition go_int_lit (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c s' =>
      if Ascii.eqb c "-"%char
      then match s' with EmptyString => false | _ => str_all_digits s' end
      else match digit_value c with Some _ => str_all_digits s' | None => false end
  end.

Lemma go_int_lit_all_digits_nonempty : forall s,
  str_all_digits s = true -> s <> EmptyString -> go_int_lit s = true.
Proof.
  intros [ | c s' ] Hdig Hne; [ contradiction | ].
  pose proof Hdig as Hdig'. cbn [str_all_digits] in Hdig.
  destruct (digit_value c) as [d|] eqn:Hc; [| discriminate].
  unfold go_int_lit. rewrite (proj1 (char_digit_not c d Hc)). rewrite Hc.
  cbn [str_all_digits] in Hdig'; rewrite Hc in Hdig'; exact Hdig'.
Qed.

Lemma go_int_lit_neg : forall s,
  str_all_digits s = true -> s <> EmptyString -> go_int_lit (String "-"%char s) = true.
Proof.
  intros [ | c s' ] Hdig Hne; [ contradiction | ].
  unfold go_int_lit. rewrite Ascii.eqb_refl. exact Hdig.
Qed.

Lemma go_int_lit_integer_literal : forall n, go_int_lit (Decimal.integer (Z.of_N n)) = true.
Proof.
  intro n. apply go_int_lit_all_digits_nonempty;
    [ apply str_all_digits_print_Z; apply N2Z.is_nonneg
    | apply integer_nonempty; apply N2Z.is_nonneg ].
Qed.

Lemma go_int_lit_negated_integer_literal : forall n, go_int_lit (String "-"%char (Decimal.integer (Z.of_N n))) = true.
Proof.
  intro n. apply go_int_lit_neg;
    [ apply str_all_digits_print_Z; apply N2Z.is_nonneg
    | apply integer_nonempty; apply N2Z.is_nonneg ].
Qed.

Theorem decode_render_decimal : forall d, decode_decimal (decimal d) = Some (Float.decimal_value d).
Proof.
  intro d. unfold decimal. destruct (Z.eqb (Float.coefficient d) 0) eqn:Hc0.
  - apply Z.eqb_eq in Hc0.
    replace (Float.decimal_value d) with Float.constant_zero
      by (rewrite (decimal_zero_unique d Hc0); symmetry; apply decimal_value_zero).
    reflexivity.
  - unfold decode_decimal, decode_decimal_body.
    rewrite (read_signed_dec_render_signed_Z (Float.coefficient d) (".0e" ++ signed_exp (Float.exponent d))
               (head_not_digit_dot0e _)).
    cbn [append Ascii.eqb andb].
    rewrite (read_signed_dec_render_signed_exp (Float.exponent d)).
    reflexivity.
Qed.

Fixpoint strip_prefix (p s : string) : option string :=
  match p, s with
  | EmptyString, _ => Some s
  | String pc p', String sc s' => if Ascii.eqb pc sc then strip_prefix p' s' else None
  | String _ _, EmptyString => None
  end.

Lemma strip_prefix_app : forall p s, strip_prefix p (p ++ s) = Some s.
Proof. induction p as [ | c p' IH ]; intro s; [ reflexivity | cbn; rewrite Ascii.eqb_refl; apply IH ]. Qed.

Lemma strip_prefix_some : forall p s r, strip_prefix p s = Some r -> s = (p ++ r)%string.
Proof.
  induction p as [ | c p' IH ]; intros s r H; cbn [strip_prefix] in H.
  - injection H as <-; reflexivity.
  - destruct s as [ | sc s' ]; [ discriminate | ].
    destruct (Ascii.eqb c sc) eqn:E; [ | discriminate ].
    apply Ascii.eqb_eq in E; subst sc; cbn [append]; f_equal; apply IH; exact H.
Qed.

(* A leading `0.0` strips to positive zero and the remainder; the zero decimal has no `.0e` body. *)
Definition strip_zero_prefix (s : string) : option (Float.Constant * string) :=
  match s with
  | String c0 (String c1 (String c2 rem)) =>
      if andb (Ascii.eqb c0 "0"%char) (andb (Ascii.eqb c1 "."%char) (Ascii.eqb c2 "0"%char))
      then Some (Float.constant_zero, rem) else None
  | _ => None
  end.

Definition read_decimal_prefix (s : string) : option (Float.Constant * string) :=
  match read_signed_dec s with
  | Some (coeff, String a (String b (String e r2))) =>
      if andb (Ascii.eqb a "."%char) (andb (Ascii.eqb b "0"%char) (Ascii.eqb e "e"%char)) then
        match read_signed_dec r2 with
        | Some (exp, rem) => Some (Float.decimal_to_constant coeff exp, rem)
        | None => strip_zero_prefix s
        end
      else strip_zero_prefix s
  | _ => strip_zero_prefix s
  end.

Definition decode_complex_literal (s : string) : option Complex.Constant :=
  match strip_prefix "complex(" s with
  | Some rem =>
      match read_decimal_prefix rem with
      | Some (real, rem1) =>
          match strip_prefix ", " rem1 with
          | Some rem2 =>
              match read_decimal_prefix rem2 with
              | Some (imag, String p EmptyString) =>
                  if Ascii.eqb p ")"%char then Some (Complex.MakeConstant real imag) else None
              | _ => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Lemma read_signed_dec_render_signed_exp_rest : forall z rest, head_not_digit rest ->
  read_signed_dec (signed_exp z ++ rest) = Some (z, rest).
Proof.
  intros z rest Hrest. unfold signed_exp. destruct (Z.ltb z 0) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. cbn [append].
    rewrite (read_signed_dec_sign "-"%char (Decimal.integer (- z)) rest (or_introl eq_refl)
               (str_all_digits_print_Z (- z) ltac:(lia)) Hrest).
    cbn [Ascii.eqb]. rewrite (integer_decimal_faithful (- z) ltac:(lia)); rewrite Z.opp_involutive; reflexivity.
  - apply Z.ltb_ge in Hlt. cbn [append].
    rewrite (read_signed_dec_sign "+"%char (Decimal.integer z) rest (or_intror eq_refl)
               (str_all_digits_print_Z z Hlt) Hrest).
    cbn [Ascii.eqb]. rewrite (integer_decimal_faithful z Hlt); reflexivity.
Qed.

(* A suffix that neither extends a magnitude read nor spuriously completes a `.0e` body. *)
Definition dec_suffix_ok (suf : string) : Prop :=
  head_not_digit suf /\ match suf with String c _ => Ascii.eqb c "e"%char = false | EmptyString => True end.

Lemma read_decimal_prefix_render : forall d suf,
  dec_suffix_ok suf ->
  read_decimal_prefix (decimal d ++ suf) = Some (Float.decimal_value d, suf).
Proof.
  intros d suf [Hnd Hne]. unfold decimal. destruct (Z.eqb (Float.coefficient d) 0) eqn:Hc0.
  - (* zero: render is "0.0"; the ".0e" body check fails on the suffix head, so strip_zero_prefix fires *)
    apply Z.eqb_eq in Hc0.
    replace (Float.decimal_value d) with Float.constant_zero
      by (rewrite (decimal_zero_unique d Hc0); symmetry; apply decimal_value_zero).
    unfold read_decimal_prefix.
    assert (Hrsd : read_signed_dec ("0.0" ++ suf) = Some (0%Z, ".0" ++ suf)).
    { change ("0.0" ++ suf)%string with ("0" ++ (".0" ++ suf))%string.
      rewrite (read_signed_dec_all_digits "0" (".0" ++ suf)
                 ltac:(reflexivity) ltac:(discriminate) ltac:(reflexivity)); reflexivity. }
    rewrite Hrsd. destruct suf as [ | c suf' ].
    + reflexivity.
    + cbn [append andb Ascii.eqb] in Hne |- *. rewrite Hne. reflexivity.
  - (* nonzero: the general `<coeff>.0e<exp>` body reads through to the suffix *)
    unfold read_decimal_prefix. rewrite <- !str_app_assoc.
    rewrite (read_signed_dec_render_signed_Z (Float.coefficient d)
               (".0e" ++ (signed_exp (Float.exponent d) ++ suf)) (head_not_digit_dot0e _)).
    cbn [append Ascii.eqb andb].
    rewrite (read_signed_dec_render_signed_exp_rest (Float.exponent d) suf Hnd).
    reflexivity.
Qed.

Lemma dec_suffix_ok_comma : forall s, dec_suffix_ok (String ","%char s).
Proof. intro s; split; reflexivity. Qed.
Lemma dec_suffix_ok_rparen : forall s, dec_suffix_ok (String ")"%char s).
Proof. intro s; split; reflexivity. Qed.

Theorem decode_render_complex_literal : forall dc,
  decode_complex_literal (complex_literal dc) = Some (Complex.decimal_value dc).
Proof.
  intro dc. unfold decode_complex_literal, complex_literal.
  rewrite (strip_prefix_app "complex(").
  rewrite (read_decimal_prefix_render (Complex.decimal_real dc)
             (", " ++ decimal (Complex.decimal_imaginary dc) ++ ")") (dec_suffix_ok_comma _)).
  rewrite (strip_prefix_app ", ").
  rewrite (read_decimal_prefix_render (Complex.decimal_imaginary dc) ")" (dec_suffix_ok_rparen _)).
  cbn [Ascii.eqb]. reflexivity.
Qed.

Lemma positive_head_not_minus : forall p,
  match Decimal.positive p with String c _ => Ascii.eqb c "-"%char = false | EmptyString => False end.
Proof.
  intro p. unfold Decimal.positive.
  destruct (exists_last (Decimal.positive_digits_nonnil 10 p)) as [init [a Ha]].
  rewrite Ha, digits_snoc.
  assert (Ha10 : (a < 10)%nat).
  { pose proof (Decimal.positive_digits_bound 10 p ltac:(lia)) as Hb. rewrite Ha, Forall_forall in Hb.
    apply Hb, in_or_app; right; left; reflexivity. }
  destruct (Ascii.eqb (Decimal.digit a) "-"%char) eqn:E; [ | reflexivity ].
  apply Ascii.eqb_eq in E.
  assert (Hn : nat_of_ascii (Decimal.digit a) = nat_of_ascii "-"%char) by (rewrite E; reflexivity).
  unfold Decimal.digit in Hn. rewrite (nat_ascii_embedding (48 + a)) in Hn by lia.
  vm_compute (nat_of_ascii "-"%char) in Hn. lia.
Qed.

Lemma read_go_int_nonneg : forall z, (0 <= z)%Z -> read_go_int (Decimal.integer z) = dval0 (Decimal.integer z).
Proof.
  intros [ | p | p ] H.
  - reflexivity.
  - cbn [Decimal.integer]. pose proof (positive_head_not_minus p) as Hh.
    destruct (Decimal.positive p) as [ | c s' ] eqn:E; [ contradiction | ].
    unfold read_go_int; rewrite Hh; reflexivity.
  - exfalso; lia.
Qed.

Lemma read_go_int_integer_literal : forall n, read_go_int (expr (Syntax.IntegerLiteral n)) = Z.of_N n.
Proof.
  intro n. cbn [expr]. rewrite read_go_int_nonneg by apply N2Z.is_nonneg.
  apply integer_decimal_faithful, N2Z.is_nonneg.
Qed.

Lemma read_go_int_negated_integer_literal : forall n, read_go_int (expr (Syntax.NegatedIntegerLiteral n)) = - Z.of_N n.
Proof.
  intro n. cbn [expr]. unfold read_go_int; cbn [Ascii.eqb].
  rewrite integer_decimal_faithful by apply N2Z.is_nonneg. reflexivity.
Qed.

(* The type name is paren-free, so the leading `(` splits the conversion spelling uniquely. *)
Lemma conv_spelling_paren_inj : forall ts1 ts2 r1 r2,
  (type_expr ts1 ++ String "("%char r1)%string = (type_expr ts2 ++ String "("%char r2)%string ->
  ts1 = ts2 /\ r1 = r2.
Proof.
  intros ts1 ts2 r1 r2 H. rewrite !type_expr_spelling in H.
  destruct (Syntax.type_expr_name ts1) eqn:E1, (Syntax.type_expr_name ts2) eqn:E2; cbn in H;
    solve [ discriminate H
          | injection H; intros; subst;
            split; [ apply type_expr_inj; rewrite !type_expr_spelling, E1, E2; reflexivity
                   | reflexivity ] ].
Qed.

Example int8_127 : expr (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.IntegerLiteral 127)) = "int8(127)". Proof. reflexivity. Qed.
Example uint64_big : expr (Syntax.Convert (Syntax.type_expr_of_name Names.Uint64) (Syntax.IntegerLiteral 18446744073709551615)) = "uint64(18446744073709551615)". Proof. reflexivity. Qed.
Example nested : expr (Syntax.Convert (Syntax.type_expr_of_name Names.Int8) (Syntax.Convert (Syntax.type_expr_of_name Names.Int16) (Syntax.IntegerLiteral 127))) = "int8(int16(127))". Proof. reflexivity. Qed.

(* A bare integer stays untyped however large, which is why `uint64(2^63)` is valid. *)
Example repair_bare_render : expr (Syntax.IntegerLiteral 9223372036854775808) = "9223372036854775808".
Proof. reflexivity. Qed.

Example float_1p5   : expr (Syntax.FloatLiteral (Float.MakeDecimal 15 (-1) eq_refl)) = "15.0e-1". Proof. reflexivity. Qed.
Example float_zero  : expr (Syntax.FloatLiteral (Float.MakeDecimal 0 0 eq_refl)) = "0.0". Proof. reflexivity. Qed.
Example float_1e6   : expr (Syntax.FloatLiteral (Float.MakeDecimal 1 6 eq_refl)) = "1.0e+6". Proof. reflexivity. Qed.
Example float_neg   : expr (Syntax.FloatLiteral (Float.MakeDecimal (-15) (-1) eq_refl)) = "-15.0e-1". Proof. reflexivity. Qed.
Example conv_f32    : expr (Syntax.Convert (Syntax.type_expr_of_name Names.Float32) (Syntax.FloatLiteral (Float.MakeDecimal 15 (-1) eq_refl))) = "float32(15.0e-1)". Proof. reflexivity. Qed.
Example conv_f64    : expr (Syntax.Convert (Syntax.type_expr_of_name Names.Float64) (Syntax.FloatLiteral (Float.MakeDecimal 3 0 eq_refl))) = "float64(3.0e+0)". Proof. reflexivity. Qed.

Example cplx_lit  : expr (Syntax.ComplexLiteral (Complex.MakeDecimal (Float.MakeDecimal 15 (-1) eq_refl) (Float.MakeDecimal (-25) (-1) eq_refl)))
  = "complex(15.0e-1, -25.0e-1)". Proof. reflexivity. Qed.
Example cplx_zero : expr (Syntax.ComplexLiteral (Complex.MakeDecimal (Float.MakeDecimal 0 0 eq_refl) (Float.MakeDecimal 0 0 eq_refl)))
  = "complex(0.0, 0.0)". Proof. reflexivity. Qed.
Example conv_c64  : expr (Syntax.Convert (Syntax.type_expr_of_name Names.Complex64) (Syntax.ComplexLiteral (Complex.MakeDecimal (Float.MakeDecimal 15 (-1) eq_refl) (Float.MakeDecimal 0 0 eq_refl))))
  = "complex64(complex(15.0e-1, 0.0))". Proof. reflexivity. Qed.
Example conv_c128 : expr (Syntax.Convert (Syntax.type_expr_of_name Names.Complex128) (Syntax.ComplexLiteral (Complex.MakeDecimal (Float.MakeDecimal 15 (-1) eq_refl) (Float.MakeDecimal 0 0 eq_refl))))
  = "complex128(complex(15.0e-1, 0.0))". Proof. reflexivity. Qed.

