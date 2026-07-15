(** ============================================================================
    GoRender — the DIRECT renderer of one file's raw declarations to Go source bytes.  No tokenizer/
    lexer/parser/round-trip/second tree.  The package CLAUSE is emitted from the compiler-derived package
    name (a CompilationFacts result, passed in — not raw metadata); each [DMain] renders as a
    `func main()` declaration; the builtin [println] is the fixed spelling of [SPrintln].

    Every rendered file begins with the exact generated header as its FIRST LINE (part of the
    Rocq-rendered bytes — the sink never adds or alters it).  [render_file] is an INTERNAL helper; the
    PUBLIC capability is [GoEmit.render_program : SafeProgram -> DirectoryImage].  Proved here: all
    output ASCII; the ONE constant-status root [render_const_info_denotes] — rendering an expression denotes
    EXACTLY the [GoTypes.ConstInfo] it computes (a bare integer/float is an UNTYPED constant, not a typed
    [int]/[float64] — the §1 repair; an explicit conversion is a TYPED constant through [convert_const]), in
    the ONE [ConstInfo] vocabulary, under an INDEPENDENT decimal reader / float decoder / string decoder
    (parser-free; the milestone forbids a lexer/parser/round-trip in the certified path).  That denotation is
    FUNCTIONAL ([render_const_info_denotes_functional]): a rendered spelling denotes AT MOST ONE [ConstInfo], as
    the six recognisers (bool / bare integer / string / integer conversion / bare float / float conversion) are
    pairwise disjoint — a canonical bare-integer spelling (the guard [go_int_lit]) is neither the word `true`,
    a dotted float, a quoted string, nor a keyword-led conversion — so no spelling admits two conflicting
    constant statuses.  A bare float
    renders through ONE canonical decimal spelling with the §27 decode/render semantic round trip; a float
    conversion renders `float32`/`float64(...)`.  And [render_resolved_expr_denotes] ties the three
    authorities — a resolved [println] argument analyzes to a ConstInfo whose spelling denotes it and
    evaluates to a well-formed value of its resolved [GoType] (the runtime value being that constant's
    resolved-type interpretation — floats round) — plus decimal faithfulness / no-leading-zero and the int
    boundary facts.  Whether the REAL Go compiler parses these bytes to that value is claim (B) — external
    adequacy — exercised by the differential e2e, not a kernel theorem here.
    ============================================================================ *)
From Stdlib Require Import String Ascii NArith ZArith List Bool Lia.
From Fido Require Import digits Ints Floats ModulePath GoVersion GoAST GoTypes GoCompile GoSafe.
Import ListNotations.
Open Scope string_scope.

Definition nl_c : ascii := ascii_of_nat 10.
Definition tab_c : ascii := ascii_of_nat 9.
Definition nl : string := String nl_c EmptyString.
Definition tab : string := String tab_c EmptyString.

(** The exact first line of every generated .go file (two spaces after the period). *)
Definition header : string := "// fido generated.  do not edit.".

(** ---- the canonical Go interpreted string literal: ONE spelling per semantic byte sequence ---- *)

Definition cr_c     : ascii := ascii_of_nat 13.   (* carriage return *)
Definition dquote_c : ascii := ascii_of_nat 34.   (* the double-quote byte 0x22 *)
Definition bslash_c : ascii := ascii_of_nat 92.   (* \ *)

(** one lowercase hex digit for a nibble in [0,16): [0-9] then [a-f]. *)
Definition hex_digit (k : nat) : ascii :=
  if Nat.ltb k 10 then ascii_of_nat (48 + k) else ascii_of_nat (87 + k).

(** the fixed-width `\xhh` escape of one byte: backslash, `x`, then EXACTLY two lowercase hex digits (high
    nibble then low), representing the original byte exactly. *)
Definition render_hex_escape (c : ascii) : string :=
  let n := nat_of_ascii c in
  String bslash_c (String "x"%char
    (String (hex_digit (Nat.div n 16)) (String (hex_digit (Nat.modulo n 16)) EmptyString))).

(** the canonical source spelling of ONE semantic byte (§17): 0x22 (double quote) and 0x5c (backslash) each
    become a two-character backslash escape; 0x0a / 0x09 / 0x0d (LF / TAB / CR) become the short escapes for
    n / t / r; a byte in 0x20..0x7e other than those two is emitted directly; every other byte becomes a
    fixed-width hex escape (backslash, x, two lowercase hex digits). *)
Definition render_string_byte (c : ascii) : string :=
  let n := nat_of_ascii c in
  if Nat.eqb n 34 then String bslash_c (String dquote_c EmptyString)
  else if Nat.eqb n 92 then String bslash_c (String bslash_c EmptyString)
  else if Nat.eqb n 10 then String bslash_c (String "n"%char EmptyString)
  else if Nat.eqb n 9  then String bslash_c (String "t"%char EmptyString)
  else if Nat.eqb n 13 then String bslash_c (String "r"%char EmptyString)
  else if andb (Nat.leb 32 n) (Nat.leb n 126) then String c EmptyString
  else render_hex_escape c.

Fixpoint render_string_body (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => render_string_byte c ++ render_string_body s'
  end.

(** the whole literal: opening quote, the per-byte-encoded body, closing quote.  Exactly one spelling per
    semantic byte sequence — never a raw-string literal, never a choice between spellings. *)
Definition render_string_literal (s : string) : string :=
  String dquote_c (render_string_body s ++ String dquote_c EmptyString).

(** a signed decimal integer: a nonnegative magnitude, or a leading unary minus over the magnitude. *)
Definition render_signed_Z (z : Z) : string :=
  if Z.ltb z 0 then String "-"%char (print_Z (Z.opp z)) else print_Z z.

(** the exponent field carries an EXPLICIT sign (`+6` / `-1`), so every canonical float spelling is
    self-delimiting. *)
Definition render_signed_exp (e : Z) : string :=
  if Z.ltb e 0 then String "-"%char (print_Z (Z.opp e)) else String "+"%char (print_Z e).

(** the ONE canonical decimal float spelling (§26): zero is `0.0`; a nonzero value
    [dm_coeff * 10 ^ dm_exp10] renders as `<signed-coefficient>.0e<explicit-signed-exponent>`
    (e.g. 15*10^-1 -> `15.0e-1`, 1*10^6 -> `1.0e+6`).  One spelling per intrinsic literal value, all ASCII,
    no host float formatting. *)
Definition render_decimal (d : DecimalFloat) : string :=
  if Z.eqb (dm_coeff d) 0 then "0.0"
  else render_signed_Z (dm_coeff d) ++ ".0e" ++ render_signed_exp (dm_exp10 d).

Fixpoint render_expr (e : GoExpr) : string :=
  match e with
  | EBool true  => "true"
  | EBool false => "false"
  | EInt n => print_Z (Z.of_N n)
  | ENeg n => String "-"%char (print_Z (Z.of_N n))
  | EString s => render_string_literal s
  | EIntConvert it e' => integer_keyword it ++ "(" ++ render_expr e' ++ ")"
  | EFloat d => render_decimal d
  | EFloatConvert ft e' => float_keyword ft ++ "(" ++ render_expr e' ++ ")"
  end.

Fixpoint render_args (es : list GoExpr) : string :=
  match es with
  | []       => ""
  | [e]      => render_expr e
  | e :: es' => render_expr e ++ ", " ++ render_args es'
  end.

Definition render_stmt (s : GoStmt) : string :=
  match s with SPrintln args => tab ++ "println(" ++ render_args args ++ ")" ++ nl end.

Fixpoint render_stmts (ss : list GoStmt) : string :=
  match ss with [] => "" | s :: ss' => render_stmt s ++ render_stmts ss' end.

Definition render_decl (d : GoDecl) : string :=
  match d with DMain body => "func main() {" ++ nl ++ render_stmts body ++ "}" ++ nl end.

(** Each top-level declaration is preceded by a blank line (gofmt spacing). *)
Fixpoint render_decls (ds : list GoDecl) : string :=
  match ds with [] => "" | d :: ds' => nl ++ render_decl d ++ render_decls ds' end.

(** [render_file] is literally [header], the newline, then the package clause + declarations — so "the
    header is the exact first line" is definitional.  The package NAME comes from CompilationFacts. *)
Definition render_file (pkg : string) (f : GoFileAST) : string :=
  header ++ String nl_c (nl ++ "package " ++ pkg ++ nl ++ render_decls f).

(** The header is EXACTLY the first line (header, then the newline [nl_c]) — the ownership contract the
    sink reads with `input_line`, strictly stronger than "header is a prefix". *)
Lemma render_file_first_line : forall pkg f, exists rest, render_file pkg f = header ++ String nl_c rest.
Proof. intros pkg f. unfold render_file. eexists. reflexivity. Qed.

(** ---- the generated module file (go.mod), rendered directly from the ModuleSpec ---- *)

(** The canonical `go.mod`: the exact header first line, then `module <path>` and `go <version>` (each on
    its own line, gofmt-spaced).  Derived SOLELY from the [ModuleSpec] — no require/replace/toolchain/etc. *)
Definition render_go_mod (ms : ModuleSpec) : string :=
  header ++ String nl_c
    (nl ++ "module " ++ mp_string (module_path ms) ++ nl ++ nl
        ++ "go " ++ render_goversion (module_go_version ms) ++ nl).

(** The header is EXACTLY the first line of go.mod (the same ownership contract the sink reads). *)
Lemma render_go_mod_first_line : forall ms, exists rest, render_go_mod ms = header ++ String nl_c rest.
Proof. intro ms. unfold render_go_mod. eexists. reflexivity. Qed.

(** The EXACT bytes: header, then `module <mp_string>`, then `go <render_goversion>` — a pure function of
    the two [ModuleSpec] fields (so rendering depends only on the ModuleSpec), pinning the module-path and
    Go-version spellings in their exact positions. *)
Lemma render_go_mod_exact : forall ms,
  render_go_mod ms = header ++ String nl_c
    (nl ++ "module " ++ mp_string (module_path ms) ++ nl ++ nl
        ++ "go " ++ render_goversion (module_go_version ms) ++ nl).
Proof. reflexivity. Qed.

(** ---- all-ASCII output ---- *)

Definition is_ascii (c : ascii) : bool := Nat.ltb (nat_of_ascii c) 128.

Fixpoint str_ascii (s : string) : bool :=
  match s with EmptyString => true | String c s' => is_ascii c && str_ascii s' end.

Lemma str_ascii_app : forall a b, str_ascii (a ++ b) = str_ascii a && str_ascii b.
Proof.
  induction a as [ | c a' IH ]; intro b; simpl; [ reflexivity | rewrite IH, andb_assoc; reflexivity ].
Qed.

Lemma str_ascii_cons : forall c s, str_ascii (String c s) = is_ascii c && str_ascii s.
Proof. reflexivity. Qed.

Lemma dec_digit_ascii : forall d, (d < 10)%nat -> is_ascii (dec_digit d) = true.
Proof. intros d Hd. do 10 (destruct d as [ | d ]; [ reflexivity | ]). lia. Qed.

Lemma render_digits_step : forall dig a ds acc,
  render_digits dig (a :: ds) acc = render_digits dig ds (String (dig a) acc).
Proof. reflexivity. Qed.

Lemma render_digits_ascii : forall ds acc,
  (forall d, In d ds -> is_ascii (dec_digit d) = true) ->
  str_ascii (render_digits dec_digit ds acc) = str_ascii acc.
Proof.
  induction ds as [ | a ds' IH ]; intros acc Hall.
  - reflexivity.
  - rewrite render_digits_step, IH.
    + cbn [str_ascii]. rewrite (Hall a (or_introl eq_refl)). reflexivity.
    + intros d Hd. apply Hall. right. exact Hd.
Qed.

Lemma print_Z_pos_ascii : forall p, str_ascii (print_Z_pos p) = true.
Proof.
  intro p. unfold print_Z_pos. rewrite render_digits_ascii; [ reflexivity | ].
  intros d Hd. apply dec_digit_ascii.
  pose proof (pos_digits_bound 10 p ltac:(lia)) as Hb. rewrite Forall_forall in Hb. apply Hb; exact Hd.
Qed.

Lemma print_Z_ascii : forall z, str_ascii (print_Z z) = true.
Proof.
  intros [ | p | p ].
  - reflexivity.
  - apply print_Z_pos_ascii.
  - cbn [print_Z]. rewrite str_ascii_app, print_Z_pos_ascii. reflexivity.
Qed.

(** ---- string rendering is all-ASCII, even for bytes >= 128 (they appear only via `\xhh` escapes) ---- *)

Lemma nat_of_ascii_lt_256 : forall c, (nat_of_ascii c < 256)%nat.
Proof.
  intro c. destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0, b1, b2, b3, b4, b5, b6, b7; cbn; lia.
Qed.

Lemma hex_digit_ascii : forall k, (k < 16)%nat -> is_ascii (hex_digit k) = true.
Proof.
  intros k Hk. unfold hex_digit, is_ascii. destruct (Nat.ltb k 10) eqn:E.
  - apply Nat.ltb_lt in E. rewrite nat_ascii_embedding by lia.
    rewrite (proj2 (Nat.ltb_lt _ _)) by lia; reflexivity.
  - apply Nat.ltb_ge in E. rewrite nat_ascii_embedding by lia.
    rewrite (proj2 (Nat.ltb_lt _ _)) by lia; reflexivity.
Qed.

Lemma render_hex_escape_ascii : forall c, str_ascii (render_hex_escape c) = true.
Proof.
  intro c. unfold render_hex_escape.
  assert (Hhi : (Nat.div (nat_of_ascii c) 16 < 16)%nat).
  { pose proof (nat_of_ascii_lt_256 c) as Hb. apply Nat.Div0.div_lt_upper_bound. lia. }
  assert (Hlo : (Nat.modulo (nat_of_ascii c) 16 < 16)%nat) by (apply Nat.mod_upper_bound; lia).
  cbn [str_ascii]. rewrite (hex_digit_ascii _ Hhi), (hex_digit_ascii _ Hlo). reflexivity.
Qed.

Lemma render_string_byte_ascii : forall c, str_ascii (render_string_byte c) = true.
Proof.
  intro c. unfold render_string_byte.
  destruct (Nat.eqb (nat_of_ascii c) 34); [ reflexivity | ].
  destruct (Nat.eqb (nat_of_ascii c) 92); [ reflexivity | ].
  destruct (Nat.eqb (nat_of_ascii c) 10); [ reflexivity | ].
  destruct (Nat.eqb (nat_of_ascii c) 9);  [ reflexivity | ].
  destruct (Nat.eqb (nat_of_ascii c) 13); [ reflexivity | ].
  destruct (andb (Nat.leb 32 (nat_of_ascii c)) (Nat.leb (nat_of_ascii c) 126)) eqn:Hp.
  - cbn [str_ascii]. rewrite Bool.andb_true_r.
    apply Bool.andb_true_iff in Hp as [_ Hle]. apply Nat.leb_le in Hle.
    unfold is_ascii. assert (Hlt : (nat_of_ascii c < 128)%nat) by lia.
    rewrite (proj2 (Nat.ltb_lt _ _) Hlt). reflexivity.
  - apply render_hex_escape_ascii.
Qed.

Lemma render_string_body_ascii : forall s, str_ascii (render_string_body s) = true.
Proof.
  induction s as [ | c s' IH ]; [ reflexivity | ].
  cbn [render_string_body]. rewrite str_ascii_app, render_string_byte_ascii, IH. reflexivity.
Qed.

Lemma render_string_literal_ascii : forall s, str_ascii (render_string_literal s) = true.
Proof.
  intro s. unfold render_string_literal. cbn [str_ascii].
  rewrite str_ascii_app, render_string_body_ascii. reflexivity.
Qed.

Lemma integer_keyword_ascii : forall it, str_ascii (integer_keyword it) = true.
Proof. intros []; reflexivity. Qed.

Lemma render_signed_Z_ascii : forall z, str_ascii (render_signed_Z z) = true.
Proof.
  intro z; unfold render_signed_Z; destruct (Z.ltb z 0).
  - cbn [str_ascii]; rewrite print_Z_ascii; reflexivity.
  - apply print_Z_ascii.
Qed.
Lemma render_signed_exp_ascii : forall e, str_ascii (render_signed_exp e) = true.
Proof. intro e; unfold render_signed_exp; destruct (Z.ltb e 0); cbn [str_ascii]; rewrite print_Z_ascii; reflexivity. Qed.
Lemma render_decimal_ascii : forall d, str_ascii (render_decimal d) = true.
Proof.
  intro d; unfold render_decimal; destruct (Z.eqb (dm_coeff d) 0).
  - reflexivity.
  - rewrite !str_ascii_app, render_signed_Z_ascii, render_signed_exp_ascii; reflexivity.
Qed.
Lemma float_keyword_ascii : forall ft, str_ascii (float_keyword ft) = true.
Proof. intro ft; destruct ft; reflexivity. Qed.

Lemma render_expr_ascii : forall e, str_ascii (render_expr e) = true.
Proof.
  induction e as [ [] | n | n | s | it e' IHe' | d | ft e' IHe' ]; cbn [render_expr].
  - reflexivity.
  - reflexivity.
  - apply print_Z_ascii.
  - cbn [str_ascii]. rewrite print_Z_ascii. reflexivity.
  - apply render_string_literal_ascii.
  - rewrite !str_ascii_app, integer_keyword_ascii, IHe'; reflexivity.
  - apply render_decimal_ascii.
  - rewrite !str_ascii_app, float_keyword_ascii, IHe'; reflexivity.
Qed.

Lemma render_args_ascii : forall es, str_ascii (render_args es) = true.
Proof.
  induction es as [ | e es' IH ]; [ reflexivity | ].
  destruct es' as [ | e2 es'' ].
  - apply render_expr_ascii.
  - change (render_args (e :: e2 :: es''))
      with (render_expr e ++ ", " ++ render_args (e2 :: es'')).
    rewrite !str_ascii_app, render_expr_ascii. simpl. exact IH.
Qed.

Lemma render_stmt_ascii : forall s, str_ascii (render_stmt s) = true.
Proof. intros [ args ]. cbn [render_stmt]. rewrite !str_ascii_app, render_args_ascii. reflexivity. Qed.

Lemma render_stmts_ascii : forall ss, str_ascii (render_stmts ss) = true.
Proof.
  induction ss as [ | s ss' IH ]; [ reflexivity | ].
  cbn [render_stmts]. rewrite str_ascii_app, render_stmt_ascii, IH. reflexivity.
Qed.

Lemma render_decl_ascii : forall d, str_ascii (render_decl d) = true.
Proof. intros [ body ]. cbn [render_decl]. rewrite !str_ascii_app, render_stmts_ascii. reflexivity. Qed.

Lemma render_decls_ascii : forall ds, str_ascii (render_decls ds) = true.
Proof.
  induction ds as [ | d ds' IH ]; [ reflexivity | ].
  cbn [render_decls]. rewrite !str_ascii_app, render_decl_ascii, IH. reflexivity.
Qed.

(** The whole file is ASCII when the (compiler-derived) package name is. *)
Theorem render_file_ascii : forall pkg f, str_ascii pkg = true -> str_ascii (render_file pkg f) = true.
Proof.
  intros pkg f Hpkg. unfold render_file. rewrite str_ascii_app. cbn [str_ascii].
  rewrite !str_ascii_app, Hpkg, render_decls_ascii. reflexivity.
Qed.

(** ---- go.mod is all-ASCII (the module path is ASCII by its grammar; the version renders `1.23`) ---- *)

Lemma all_modpath_chars_ascii : forall s, all_modpath_chars s = true -> str_ascii s = true.
Proof.
  induction s as [ | c s' IH ]; intro H; [ reflexivity | ].
  cbn [all_modpath_chars] in H; apply Bool.andb_true_iff in H as [Hc Hs].
  cbn [str_ascii]; unfold is_ascii.
  rewrite (proj2 (Nat.ltb_lt _ _) (modpath_char_lt_128 c Hc)); cbn [andb].
  apply IH; exact Hs.
Qed.

Lemma mp_string_ascii : forall p, str_ascii (mp_string p) = true.
Proof. intro p. apply all_modpath_chars_ascii, modpath_ok_all_chars. exact (mp_ok p). Qed.

Theorem render_go_mod_ascii : forall ms, str_ascii (render_go_mod ms) = true.
Proof.
  intro ms. unfold render_go_mod.
  rewrite str_ascii_app, str_ascii_cons, !str_ascii_app, mp_string_ascii.
  destruct (module_go_version ms); reflexivity.
Qed.

(** ---- decimal faithfulness: emitted decimal denotes EXACTLY the value, no leading zero ---- *)

Definition ascii_digit (c : ascii) : nat := nat_of_ascii c - 48.

Fixpoint dval (s : string) (acc : Z) : Z :=
  match s with EmptyString => acc | String c s' => dval s' (acc * 10 + Z.of_nat (ascii_digit c)) end.
Definition dval0 (s : string) : Z := dval s 0.

Lemma ascii_digit_dec_digit : forall d, (d < 10)%nat -> ascii_digit (dec_digit d) = d.
Proof. intros d Hd. do 10 (destruct d as [ | d ]; [ reflexivity | ]). lia. Qed.

Lemma render_digits_dval : forall ds base,
  (forall d, In d ds -> (d < 10)%nat) ->
  dval (render_digits dec_digit ds base) 0 = dval base (dlist_val 10 ds).
Proof.
  induction ds as [ | d ds' IH ]; intros base Hall.
  - reflexivity.
  - rewrite render_digits_step, (IH (String (dec_digit d) base))
      by (intros x Hx; apply Hall; right; exact Hx).
    cbn [dval]. rewrite ascii_digit_dec_digit by (apply Hall; left; reflexivity).
    cbn [dlist_val]. f_equal. change (Z.of_nat 10) with 10%Z. lia.
Qed.

Lemma print_Z_pos_dval : forall p, dval0 (print_Z_pos p) = Z.pos p.
Proof.
  intro p. unfold dval0, print_Z_pos. rewrite render_digits_dval.
  - cbn [dval]. rewrite pos_digits_val by lia. reflexivity.
  - intros d Hd. pose proof (pos_digits_bound 10 p ltac:(lia)) as Hb.
    rewrite Forall_forall in Hb. apply Hb; exact Hd.
Qed.

Theorem print_Z_dec_faithful : forall z, (0 <= z)%Z -> dval0 (print_Z z) = z.
Proof.
  intros [ | p | p ] H.
  - reflexivity.
  - apply print_Z_pos_dval.
  - exfalso; lia.
Qed.

Definition head_not_zero (s : string) : Prop :=
  match s with EmptyString => False | String c _ => c <> dec_digit 0 end.

Lemma render_digits_snoc : forall ds a base,
  render_digits dec_digit (ds ++ [a]) base = String (dec_digit a) (render_digits dec_digit ds base).
Proof. intros. unfold render_digits. rewrite fold_left_app. reflexivity. Qed.

Theorem print_Z_pos_no_leading_zero : forall p, head_not_zero (print_Z_pos p).
Proof.
  intro p. unfold print_Z_pos.
  destruct (exists_last (pos_digits_nonnil 10 p)) as [init [a Ha]].
  rewrite Ha, render_digits_snoc. cbn [head_not_zero].
  assert (Ha1 : (1 <= a)%nat).
  { pose proof (pos_digits_last 10 p ltac:(lia)) as Hl. rewrite Ha, last_last in Hl. exact Hl. }
  assert (Ha10 : (a < 10)%nat).
  { pose proof (pos_digits_bound 10 p ltac:(lia)) as Hb. rewrite Ha, Forall_forall in Hb.
    apply Hb, in_or_app; right; left; reflexivity. }
  intro Heq.
  assert (Hn : nat_of_ascii (dec_digit a) = nat_of_ascii (dec_digit 0)) by (rewrite Heq; reflexivity).
  unfold dec_digit in Hn.
  rewrite (nat_ascii_embedding (48 + a)) in Hn by lia.
  rewrite (nat_ascii_embedding (48 + 0)) in Hn by lia.
  lia.
Qed.

(** ---- ROOT correspondence: rendered spelling denotes EXACTLY the semantic value (parser-free) ---- *)

(** Read a rendered Go integer literal: an optional leading unary minus over the decimal magnitude. *)
Definition read_go_int (s : string) : Z :=
  match s with
  | String c s' => if Ascii.eqb c "-"%char then Z.opp (dval0 s') else dval0 s
  | EmptyString => dval0 s
  end.

(** ---- an INDEPENDENT certified decoder that assigns EXACT BYTE MEANING to the canonical spelling this
    renderer emits.  It is NOT a general Go parser and does NOT consult the encoder to decide what it accepts;
    it is defined by its own structural recursion.  It understands the opening and closing double quote, a
    directly-emitted printable byte, the five short backslash escapes (for quote, backslash, n, t, r), and a
    backslash-x hex escape of EXACTLY two lowercase hex digits.  Because a byte with a shorter canonical form
    can still be written as a hex escape, the decoder ALSO accepts semantically equivalent NONCANONICAL
    spellings the renderer never emits — decoding is a DENOTATION tool, not a canonical-spelling recogniser.
    The proved property is the byte round trip [decode_string_literal (render_string_literal s) = Some s]; NO
    source-spelling inverse [render (decode source) = source] is claimed, and the decoder is NOT narrowed to
    make that prose easier.  It REJECTS a malformed / truncated / nonhex escape, an unescaped quote or control
    byte inside the body, and any trailing bytes after the closing quote. ---- *)

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

(** string-append associativity (local, over Rocq [string]). *)
Lemma str_app_assoc : forall a b d : string, (a ++ (b ++ d))%string = ((a ++ b) ++ d)%string.
Proof.
  intros a; induction a as [ | c a' IH ]; intros b d; simpl;
    [ reflexivity | rewrite IH; reflexivity ].
Qed.

(** one nibble round-trips (encoder digit -> decoder digit) for any nibble < 16. *)
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

(** the two nibbles reconstruct the exact original byte. *)
Lemma byte_reconstruct : forall c,
  ascii_of_nat (Nat.div (nat_of_ascii c) 16 * 16 + Nat.modulo (nat_of_ascii c) 16) = c.
Proof.
  intro c. pose proof (Nat.div_mod_eq (nat_of_ascii c) 16) as Hd.
  replace ((Nat.div (nat_of_ascii c) 16 * 16 + Nat.modulo (nat_of_ascii c) 16)%nat)
    with (nat_of_ascii c) by lia.
  apply ascii_nat_embedding.
Qed.

Opaque hex_digit decode_hex_digit.

(** the decoder consumes a rendered `\xhh` escape and yields exactly the encoded byte (§19-D hex exactness). *)
Lemma decode_hex_prefix : forall hi lo tail,
  (hi < 16)%nat -> (lo < 16)%nat ->
  decode_string_body
    (String bslash_c (String "x"%char (String (hex_digit hi) (String (hex_digit lo) tail))))
  = option_map (String (ascii_of_nat (hi * 16 + lo))) (decode_string_body tail).
Proof.
  intros hi lo tail Hhi Hlo. cbn. rewrite (hex_digit_decode hi Hhi), (hex_digit_decode lo Hlo). reflexivity.
Qed.

Lemma render_hex_escape_exact : forall c tail,
  decode_string_body (render_hex_escape c ++ tail) = option_map (String c) (decode_string_body tail).
Proof.
  intros c tail. pose proof (nat_of_ascii_lt_256 c) as Hb.
  assert (Hhi : (Nat.div (nat_of_ascii c) 16 < 16)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
  assert (Hlo : (Nat.modulo (nat_of_ascii c) 16 < 16)%nat) by (apply Nat.mod_upper_bound; lia).
  unfold render_hex_escape. cbn [append].
  rewrite (decode_hex_prefix _ _ _ Hhi Hlo), byte_reconstruct. reflexivity.
Qed.

(** the core: rendering one byte then decoding the result (over any tail) restores exactly that byte. *)
Lemma decode_render_byte : forall c tail,
  decode_string_body (render_string_byte c ++ tail) = option_map (String c) (decode_string_body tail).
Proof.
  intros c tail. pose proof (nat_of_ascii_lt_256 c) as Hb. unfold render_string_byte.
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
  { apply render_hex_escape_exact. }
Qed.

Transparent hex_digit decode_hex_digit.

(** ROUND TRIP (§19-A): the decoder inverts the encoder on the body, then on the whole literal. *)
Lemma decode_body_render : forall s,
  decode_string_body (render_string_body s ++ String dquote_c EmptyString) = Some s.
Proof.
  induction s as [ | c s' IH ]; cbn [render_string_body].
  - cbn [append]. reflexivity.
  - rewrite <- str_app_assoc, decode_render_byte, IH. reflexivity.
Qed.

Theorem render_string_roundtrip : forall s, decode_string_literal (render_string_literal s) = Some s.
Proof.
  intro s. unfold render_string_literal. cbn [decode_string_literal].
  rewrite Ascii.eqb_refl. apply decode_body_render.
Qed.

(** ---- quoting shape (§19-C): the literal begins and ends with a double quote and contains no raw newline
    or carriage-return byte (LF/CR only ever appear as the two-char escapes `\n`/`\r`). ---- *)
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

Lemma render_hex_escape_no_nl_cr : forall c, str_no_nl_cr (render_hex_escape c) = true.
Proof.
  intro c. pose proof (nat_of_ascii_lt_256 c) as Hb.
  assert (Hhi : (Nat.div (nat_of_ascii c) 16 < 16)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
  assert (Hlo : (Nat.modulo (nat_of_ascii c) 16 < 16)%nat) by (apply Nat.mod_upper_bound; lia).
  unfold render_hex_escape. cbn [str_no_nl_cr].
  rewrite (hex_digit_not_nl_cr _ Hhi), (hex_digit_not_nl_cr _ Hlo). reflexivity.
Qed.

Lemma render_string_byte_no_nl_cr : forall c, str_no_nl_cr (render_string_byte c) = true.
Proof.
  intro c. unfold render_string_byte.
  destruct (Nat.eqb (nat_of_ascii c) 34); [ reflexivity | ].
  destruct (Nat.eqb (nat_of_ascii c) 92); [ reflexivity | ].
  destruct (Nat.eqb (nat_of_ascii c) 10) eqn:E10; [ reflexivity | ].
  destruct (Nat.eqb (nat_of_ascii c) 9);  [ reflexivity | ].
  destruct (Nat.eqb (nat_of_ascii c) 13) eqn:E13; [ reflexivity | ].
  destruct (andb (Nat.leb 32 (nat_of_ascii c)) (Nat.leb (nat_of_ascii c) 126)) eqn:Hp.
  - cbn [str_no_nl_cr]. unfold byte_not_nl_cr. rewrite E10, E13. reflexivity.
  - apply render_hex_escape_no_nl_cr.
Qed.

Lemma render_string_body_no_nl_cr : forall s, str_no_nl_cr (render_string_body s) = true.
Proof.
  induction s as [ | c s' IH ]; [ reflexivity | ].
  cbn [render_string_body]. rewrite str_no_nl_cr_app, render_string_byte_no_nl_cr, IH. reflexivity.
Qed.

Lemma render_string_literal_no_nl_cr : forall s, str_no_nl_cr (render_string_literal s) = true.
Proof.
  intro s. unfold render_string_literal. cbn [str_no_nl_cr].
  rewrite str_no_nl_cr_app, render_string_body_no_nl_cr. reflexivity.
Qed.

(** begins and ends with a double quote (definitional: quote, then the body, then the closing quote). *)
Lemma render_string_literal_quotes : forall s,
  render_string_literal s = String dquote_c (render_string_body s ++ String dquote_c EmptyString).
Proof. reflexivity. Qed.

(** ---- canonical-spelling fixtures (§19-E), pinned at the per-byte encoder and the whole literal ---- *)
Example rb_quote  : render_string_byte (ascii_of_nat 34)  = String bslash_c (String dquote_c EmptyString).
Proof. reflexivity. Qed.
Example rb_bslash : render_string_byte (ascii_of_nat 92)  = String bslash_c (String bslash_c EmptyString).
Proof. reflexivity. Qed.
Example rb_nl : render_string_byte (ascii_of_nat 10) = String bslash_c (String "n"%char EmptyString).
Proof. reflexivity. Qed.
Example rb_tab : render_string_byte (ascii_of_nat 9)  = String bslash_c (String "t"%char EmptyString).
Proof. reflexivity. Qed.
Example rb_cr : render_string_byte (ascii_of_nat 13) = String bslash_c (String "r"%char EmptyString).
Proof. reflexivity. Qed.
Example rb_nul : render_string_byte (ascii_of_nat 0)
  = String bslash_c (String "x"%char (String "0"%char (String "0"%char EmptyString))).
Proof. reflexivity. Qed.
Example rb_del : render_string_byte (ascii_of_nat 127)
  = String bslash_c (String "x"%char (String "7"%char (String "f"%char EmptyString))).
Proof. reflexivity. Qed.
Example rb_80 : render_string_byte (ascii_of_nat 128)
  = String bslash_c (String "x"%char (String "8"%char (String "0"%char EmptyString))).
Proof. reflexivity. Qed.
Example rb_ff : render_string_byte (ascii_of_nat 255)
  = String bslash_c (String "x"%char (String "f"%char (String "f"%char EmptyString))).
Proof. reflexivity. Qed.
Example rl_empty : render_string_literal "" = String dquote_c (String dquote_c EmptyString).
Proof. reflexivity. Qed.
Example rl_ascii : render_string_literal "hi"
  = String dquote_c (String "h"%char (String "i"%char (String dquote_c EmptyString))).
Proof. reflexivity. Qed.

(** ---- the ONE render-time constant-status authority (§2): a rendered spelling denotes an exact [ConstInfo]
    — the SAME untyped/typed vocabulary [GoTypes] owns, never a per-family status relation that can drift.  A
    bare literal denotes an UNTYPED constant (a bare integer stays UNTYPED — it is NOT labelled [int]; that
    false premise was the §1 defect, which wrongly rejected a valid inner like the `2^63` of
    `uint64(2^63)`).  An explicit integer conversion denotes a TYPED constant of the destination type after
    the representability check, over a recursively-denoting inner spelling.  It reuses the exact GoTypes
    values and [integer_representableb], reimplementing no representability; it is a DENOTATION tool, NOT a
    general Go parser (real-Go acceptance is external adequacy).  Float cases are added in Part B. ---- *)
(** ---- an INDEPENDENT decoder for the canonical Fido decimal-float subset (§27): it recovers the EXACT
    untyped rational value of a canonical spelling.  It is NOT a general Go float parser; the proved property
    is the SEMANTIC round trip [decode_decimal (render_decimal d) = Some (decimal_value d)] (NOT a
    source-spelling inverse) — it reads an optional signed coefficient, the exact ".0e" body, and a signed
    exponent, and interprets them through the SAME [decimal_to_fc] the encoder uses (no reimplemented
    rounding). ---- *)
Definition dec_digit_val (c : ascii) : option nat :=
  let n := nat_of_ascii c in
  if andb (Nat.leb 48 n) (Nat.leb n 57) then Some (n - 48)%nat else None.

Definition head_not_digit (s : string) : Prop :=
  match s with EmptyString => True | String c _ => dec_digit_val c = None end.

Fixpoint read_nat (s : string) (acc : Z) : Z * string :=
  match s with
  | EmptyString => (acc, s)
  | String c s' => match dec_digit_val c with
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

Definition decode_decimal_body (s : string) : option FloatConst :=
  match read_signed_dec s with
  | Some (coeff, String a (String b (String c r2))) =>
      if andb (Ascii.eqb a "."%char) (andb (Ascii.eqb b "0"%char) (Ascii.eqb c "e"%char)) then
        match read_signed_dec r2 with
        | Some (exp, EmptyString) => Some (decimal_to_fc coeff exp)
        | _ => None
        end
      else None
  | _ => None
  end.

Definition decode_decimal (s : string) : option FloatConst :=
  match decode_decimal_body s with
  | Some q => Some q
  | None => if String.eqb s "0.0" then Some fc_zero else None
  end.

Fixpoint str_all_digits (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => match dec_digit_val c with Some _ => str_all_digits s' | None => false end
  end.

Lemma str_app_nil : forall s, (s ++ "")%string = s.
Proof. induction s as [ | c s' IH ]; simpl; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma dec_digit_val_dec_digit : forall d, (d < 10)%nat -> dec_digit_val (dec_digit d) = Some d.
Proof.
  intros d Hd. unfold dec_digit_val, dec_digit. rewrite nat_ascii_embedding by lia.
  rewrite (proj2 (Nat.leb_le 48 (48 + d))) by lia.
  rewrite (proj2 (Nat.leb_le (48 + d) 57)) by lia.
  cbn [andb]. f_equal. lia.
Qed.

Lemma str_all_digits_render_digits : forall ds acc,
  (forall d, In d ds -> (d < 10)%nat) -> str_all_digits acc = true ->
  str_all_digits (render_digits dec_digit ds acc) = true.
Proof.
  induction ds as [ | a ds' IH ]; intros acc Hall Hacc; [ exact Hacc | ].
  rewrite render_digits_step. apply IH; [ intros d Hd; apply Hall; right; exact Hd | ].
  cbn [str_all_digits]. rewrite dec_digit_val_dec_digit by (apply Hall; left; reflexivity). exact Hacc.
Qed.

Lemma str_all_digits_print_Z_pos : forall p, str_all_digits (print_Z_pos p) = true.
Proof.
  intro p; unfold print_Z_pos. apply str_all_digits_render_digits; [ | reflexivity ].
  intros d Hd. pose proof (pos_digits_bound 10 p ltac:(lia)) as Hb. rewrite Forall_forall in Hb.
  apply Hb; exact Hd.
Qed.

Lemma str_all_digits_print_Z : forall z, (0 <= z)%Z -> str_all_digits (print_Z z) = true.
Proof. intros [ | p | p ] H; [ reflexivity | apply str_all_digits_print_Z_pos | exfalso; lia ]. Qed.

Lemma read_nat_all_digits : forall s rest acc,
  str_all_digits s = true -> head_not_digit rest -> read_nat (s ++ rest) acc = (dval s acc, rest).
Proof.
  induction s as [ | c s' IH ]; intros rest acc Hdig Hrest.
  - destruct rest as [ | rc rr ]; cbn [append read_nat dval].
    + reflexivity.
    + cbn [head_not_digit] in Hrest. rewrite Hrest. reflexivity.
  - cbn [str_all_digits] in Hdig. destruct (dec_digit_val c) as [d|] eqn:Hc; [| discriminate].
    cbn [append read_nat]. rewrite Hc.
    rewrite (IH rest (acc * 10 + Z.of_nat d) Hdig Hrest). cbn [dval].
    replace (ascii_digit c) with d; [ reflexivity | ].
    unfold ascii_digit; unfold dec_digit_val in Hc.
    destruct (andb (Nat.leb 48 (nat_of_ascii c)) (Nat.leb (nat_of_ascii c) 57)); [| discriminate].
    injection Hc as <-; reflexivity.
Qed.

Lemma char_digit_not : forall c d,
  dec_digit_val c = Some d -> Ascii.eqb c "-"%char = false /\ Ascii.eqb c "+"%char = false.
Proof.
  intros c d Hc; split; destruct (Ascii.eqb c _) eqn:E; try reflexivity;
    apply Ascii.eqb_eq in E; subst c; cbn in Hc; discriminate.
Qed.

Lemma print_Z_nonempty : forall z, (0 <= z)%Z -> print_Z z <> EmptyString.
Proof.
  intros [ | p | p ] H Hc.
  - cbn [print_Z] in Hc; discriminate.
  - pose proof (print_Z_dec_faithful (Zpos p) ltac:(lia)) as Hf.
    rewrite Hc in Hf; cbn in Hf; discriminate Hf.
  - exfalso; lia.
Qed.

(** the reader inverts an all-digit NONEMPTY magnitude (no sign) up to a non-digit remainder. *)
Lemma read_signed_dec_all_digits : forall s rest,
  str_all_digits s = true -> s <> EmptyString -> head_not_digit rest ->
  read_signed_dec (s ++ rest) = Some (dval0 s, rest).
Proof.
  intros [ | c s' ] rest Hdig Hne Hrest; [ contradiction | ].
  pose proof Hdig as Hdig'. cbn [str_all_digits] in Hdig.
  destruct (dec_digit_val c) as [d|] eqn:Hc; [| discriminate].
  destruct (char_digit_not c d Hc) as [Hnd Hnp].
  cbn [append]. unfold read_signed_dec. rewrite Hnd, Hnp.
  change (String c (s' ++ rest)) with ((String c s') ++ rest).
  destruct (read_nat ((String c s') ++ rest) 0) as [m r] eqn:E.
  rewrite (read_nat_all_digits (String c s') rest 0 Hdig' Hrest) in E.
  injection E as <- <-. reflexivity.
Qed.

(** the reader inverts a "-"- / "+"-prefixed all-digit magnitude (negating for "-"). *)
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
  read_signed_dec (render_signed_Z z ++ rest) = Some (z, rest).
Proof.
  intros z rest Hrest. unfold render_signed_Z. destruct (Z.ltb z 0) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. cbn [append].
    rewrite (read_signed_dec_sign "-"%char (print_Z (- z)) rest (or_introl eq_refl)
               (str_all_digits_print_Z (- z) ltac:(lia)) Hrest).
    cbn [Ascii.eqb]. rewrite (print_Z_dec_faithful (- z) ltac:(lia)). rewrite Z.opp_involutive; reflexivity.
  - apply Z.ltb_ge in Hlt.
    rewrite (read_signed_dec_all_digits (print_Z z) rest (str_all_digits_print_Z z Hlt)
               (print_Z_nonempty z Hlt) Hrest).
    rewrite (print_Z_dec_faithful z Hlt); reflexivity.
Qed.

Lemma read_signed_dec_render_signed_exp : forall z, read_signed_dec (render_signed_exp z) = Some (z, EmptyString).
Proof.
  intro z. unfold render_signed_exp. destruct (Z.ltb z 0) eqn:Hlt.
  - apply Z.ltb_lt in Hlt.
    replace (String "-"%char (print_Z (- z))) with (String "-"%char (print_Z (- z) ++ ""))
      by (rewrite str_app_nil; reflexivity).
    rewrite (read_signed_dec_sign "-"%char (print_Z (- z)) "" (or_introl eq_refl)
               (str_all_digits_print_Z (- z) ltac:(lia)) I).
    cbn [Ascii.eqb]. rewrite (print_Z_dec_faithful (- z) ltac:(lia)); rewrite Z.opp_involutive; reflexivity.
  - apply Z.ltb_ge in Hlt.
    replace (String "+"%char (print_Z z)) with (String "+"%char (print_Z z ++ ""))
      by (rewrite str_app_nil; reflexivity).
    rewrite (read_signed_dec_sign "+"%char (print_Z z) "" (or_intror eq_refl)
               (str_all_digits_print_Z z Hlt) I).
    cbn [Ascii.eqb]. rewrite (print_Z_dec_faithful z Hlt); reflexivity.
Qed.

Lemma head_not_digit_dot0e : forall s, head_not_digit (".0e" ++ s)%string.
Proof. reflexivity. Qed.

(** ---- §30 CANONICAL BARE-INTEGER RECOGNISER: a spelling is a bare Go integer literal iff it is an optional
    leading `-` over a NONEMPTY run of decimal digits (no `.`, no letters, no quote).  This is the shape guard
    that makes the [RCDInt] denotation constructor DISJOINT from the bool / float / string / conversion
    constructors — without it, [read_go_int] (a total prefix reader) would let a dotted float spelling or the
    word `true` ALSO denote an integer, so the rendered-constant denotation would admit conflicting statuses.
    It is defined by its own structural recursion (via [str_all_digits] / [dec_digit_val]); it does NOT consult
    the encoder. ---- *)
Definition go_int_lit (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c s' =>
      if Ascii.eqb c "-"%char
      then match s' with EmptyString => false | _ => str_all_digits s' end
      else match dec_digit_val c with Some _ => str_all_digits s' | None => false end
  end.

(** a nonempty all-digit magnitude is a bare integer literal (no sign). *)
Lemma go_int_lit_all_digits_nonempty : forall s,
  str_all_digits s = true -> s <> EmptyString -> go_int_lit s = true.
Proof.
  intros [ | c s' ] Hdig Hne; [ contradiction | ].
  pose proof Hdig as Hdig'. cbn [str_all_digits] in Hdig.
  destruct (dec_digit_val c) as [d|] eqn:Hc; [| discriminate].
  unfold go_int_lit. rewrite (proj1 (char_digit_not c d Hc)). rewrite Hc.
  cbn [str_all_digits] in Hdig'; rewrite Hc in Hdig'; exact Hdig'.
Qed.

(** a `-`-prefixed nonempty all-digit magnitude is a bare integer literal. *)
Lemma go_int_lit_neg : forall s,
  str_all_digits s = true -> s <> EmptyString -> go_int_lit (String "-"%char s) = true.
Proof.
  intros [ | c s' ] Hdig Hne; [ contradiction | ].
  unfold go_int_lit. rewrite Ascii.eqb_refl. exact Hdig.
Qed.

Lemma go_int_lit_EInt : forall n, go_int_lit (print_Z (Z.of_N n)) = true.
Proof.
  intro n. apply go_int_lit_all_digits_nonempty;
    [ apply str_all_digits_print_Z; apply N2Z.is_nonneg
    | apply print_Z_nonempty; apply N2Z.is_nonneg ].
Qed.

Lemma go_int_lit_ENeg : forall n, go_int_lit (String "-"%char (print_Z (Z.of_N n))) = true.
Proof.
  intro n. apply go_int_lit_neg;
    [ apply str_all_digits_print_Z; apply N2Z.is_nonneg
    | apply print_Z_nonempty; apply N2Z.is_nonneg ].
Qed.

(** ★§27 SEMANTIC ROUND TRIP: decoding the canonical spelling recovers the EXACT untyped rational value. *)
Theorem decode_render_decimal : forall d, decode_decimal (render_decimal d) = Some (decimal_value d).
Proof.
  intro d. unfold render_decimal. destruct (Z.eqb (dm_coeff d) 0) eqn:Hc0.
  - apply Z.eqb_eq in Hc0.
    replace (decimal_value d) with fc_zero
      by (rewrite (decimal_zero_unique d Hc0); symmetry; apply decimal_value_zero).
    reflexivity.
  - unfold decode_decimal, decode_decimal_body.
    rewrite (read_signed_dec_render_signed_Z (dm_coeff d) (".0e" ++ render_signed_exp (dm_exp10 d))
               (head_not_digit_dot0e _)).
    cbn [append Ascii.eqb andb].
    rewrite (read_signed_dec_render_signed_exp (dm_exp10 d)).
    reflexivity.
Qed.

Inductive RenderedConstInfoDenotes : string -> ConstInfo -> Prop :=
| RCDBool : forall (b : bool),
    RenderedConstInfoDenotes (if b then "true"%string else "false"%string) (CIUntyped (CBool b))
| RCDInt : forall s z,
    go_int_lit s = true ->
    read_go_int s = z ->
    RenderedConstInfoDenotes s (CIUntyped (CInt z))
| RCDString : forall s bytes,
    decode_string_literal s = Some bytes ->
    RenderedConstInfoDenotes s (CIUntyped (CString bytes))
| RCDIntConvert : forall target inner ci (tc : TypedConst (TInteger target)),
    RenderedConstInfoDenotes inner ci ->
    convert_const (TInteger target) ci = Some tc ->
    RenderedConstInfoDenotes (integer_keyword target ++ "(" ++ inner ++ ")")
                             (CITyped (TInteger target) tc)
| RCDFloat : forall s q,
    decode_decimal s = Some q ->
    RenderedConstInfoDenotes s (CIUntyped (CFloat q))
| RCDFloatConvert : forall target inner ci (tc : TypedConst (TFloat target)),
    RenderedConstInfoDenotes inner ci ->
    convert_const (TFloat target) ci = Some tc ->
    RenderedConstInfoDenotes (float_keyword target ++ "(" ++ inner ++ ")")
                             (CITyped (TFloat target) tc).

(** print_Z of a nonnegative is nonempty and its first character is a decimal digit, not '-'. *)
Lemma print_Z_pos_head_not_minus : forall p,
  match print_Z_pos p with String c _ => Ascii.eqb c "-"%char = false | EmptyString => False end.
Proof.
  intro p. unfold print_Z_pos.
  destruct (exists_last (pos_digits_nonnil 10 p)) as [init [a Ha]].
  rewrite Ha, render_digits_snoc.
  assert (Ha10 : (a < 10)%nat).
  { pose proof (pos_digits_bound 10 p ltac:(lia)) as Hb. rewrite Ha, Forall_forall in Hb.
    apply Hb, in_or_app; right; left; reflexivity. }
  destruct (Ascii.eqb (dec_digit a) "-"%char) eqn:E; [ | reflexivity ].
  apply Ascii.eqb_eq in E.
  assert (Hn : nat_of_ascii (dec_digit a) = nat_of_ascii "-"%char) by (rewrite E; reflexivity).
  unfold dec_digit in Hn. rewrite (nat_ascii_embedding (48 + a)) in Hn by lia.
  vm_compute (nat_of_ascii "-"%char) in Hn. lia.
Qed.

Lemma read_go_int_nonneg : forall z, (0 <= z)%Z -> read_go_int (print_Z z) = dval0 (print_Z z).
Proof.
  intros [ | p | p ] H.
  - reflexivity.
  - cbn [print_Z]. pose proof (print_Z_pos_head_not_minus p) as Hh.
    destruct (print_Z_pos p) as [ | c s' ] eqn:E; [ contradiction | ].
    unfold read_go_int; rewrite Hh; reflexivity.
  - exfalso; lia.
Qed.

(** read a rendered bare integer literal: the decimal reader restores the exact magnitude (nonnegative for
    [EInt], negated for [ENeg]) — the parser-free denotation of the two bare literal spellings. *)
Lemma read_go_int_EInt : forall n, read_go_int (render_expr (EInt n)) = Z.of_N n.
Proof.
  intro n. cbn [render_expr]. rewrite read_go_int_nonneg by apply N2Z.is_nonneg.
  apply print_Z_dec_faithful, N2Z.is_nonneg.
Qed.

Lemma read_go_int_ENeg : forall n, read_go_int (render_expr (ENeg n)) = - Z.of_N n.
Proof.
  intro n. cbn [render_expr]. unfold read_go_int; cbn [Ascii.eqb].
  rewrite print_Z_dec_faithful by apply N2Z.is_nonneg. reflexivity.
Qed.

(** [const_info] of a conversion, when it succeeds, extracts the inner constant-status [ci'], its exact
    integer value [z], the destination representability, and the outer TYPED shape — without touching the
    caller's induction hypothesis (a separate lemma so [const_info e'] is not abstracted in the IH). *)
Lemma const_info_convert_inner : forall it e ci,
  const_info (EIntConvert it e) = Some ci ->
  exists ci' (tc : TypedConst (TInteger it)), const_info e = Some ci'
             /\ convert_const (TInteger it) ci' = Some tc
             /\ ci = CITyped (TInteger it) tc.
Proof.
  intros it e ci H; cbn [const_info] in H.
  destruct (const_info e) as [ci'|] eqn:Hce'; [| discriminate].
  destruct (convert_const (TInteger it) ci') as [tc|] eqn:Hconv; cbn [option_map] in H; [| discriminate].
  injection H as <-.
  exists ci', tc. split; [ reflexivity | split; [ exact Hconv | reflexivity ] ].
Qed.

Lemma const_info_float_convert_inner : forall ft e ci,
  const_info (EFloatConvert ft e) = Some ci ->
  exists ci' (tc : TypedConst (TFloat ft)), const_info e = Some ci'
             /\ convert_const (TFloat ft) ci' = Some tc
             /\ ci = CITyped (TFloat ft) tc.
Proof.
  intros ft e ci H; cbn [const_info] in H.
  destruct (const_info e) as [ci'|] eqn:Hce'; [| discriminate].
  destruct (convert_const (TFloat ft) ci') as [tc|] eqn:Hconv; cbn [option_map] in H; [| discriminate].
  injection H as <-.
  exists ci', tc. split; [ reflexivity | split; [ exact Hconv | reflexivity ] ].
Qed.

(** ★§2-3/§29 ROOT: rendering an expression denotes EXACTLY the [const_info] GoTypes computes for it — the
    source-spelling / constant-status correspondence, in the ONE ConstInfo vocabulary.  A bare integer/float
    denotes an UNTYPED constant (the §1 repair: NO false [int] label; a bare float its exact rational); an
    explicit conversion denotes a TYPED constant of the destination type, through the ONE [convert_const]
    authority.  It reuses the exact GoTypes/[Floats] values, reimplementing no representability/rounding. *)
Theorem render_const_info_denotes : forall e ci,
  const_info e = Some ci -> RenderedConstInfoDenotes (render_expr e) ci.
Proof.
  induction e as [ b | n | n | s | it' e' IHe' | d | ft e' IHe' ]; intros ci H.
  - simpl in H; injection H as <-; cbn [render_expr]; destruct b; [ exact (RCDBool true) | exact (RCDBool false) ].
  - simpl in H; injection H as <-; cbn [render_expr]; apply RCDInt; [ apply go_int_lit_EInt | apply read_go_int_EInt ].
  - simpl in H; injection H as <-; cbn [render_expr]; apply RCDInt; [ apply go_int_lit_ENeg | apply read_go_int_ENeg ].
  - simpl in H; injection H as <-; cbn [render_expr]; apply RCDString, render_string_roundtrip.
  - destruct (const_info_convert_inner it' e' ci H) as [ ci' [ tc [ Hce' [ Hconv -> ] ] ] ].
    cbn [render_expr]. apply RCDIntConvert with (ci := ci'); [ apply IHe'; exact Hce' | exact Hconv ].
  - cbn [const_info] in H; injection H as <-; cbn [render_expr]. apply RCDFloat, decode_render_decimal.
  - destruct (const_info_float_convert_inner ft e' ci H) as [ ci' [ tc [ Hce' [ Hconv -> ] ] ] ].
    cbn [render_expr]. apply RCDFloatConvert with (ci := ci'); [ apply IHe'; exact Hce' | exact Hconv ].
Qed.

(** ---- §30 DETERMINISM foundation: the leaf recognisers of [RenderedConstInfoDenotes] are pairwise disjoint,
    so a given rendered spelling denotes AT MOST ONE [ConstInfo].  These small head/shape lemmas isolate each
    constructor's spelling class; [render_const_info_denotes_functional] below assembles them. ---- *)

(** a bare integer literal starts with `-` or a decimal digit. *)
Lemma go_int_lit_cons : forall s, go_int_lit s = true ->
  exists c s', s = String c s' /\ (c = "-"%char \/ dec_digit_val c <> None).
Proof.
  intros [ | c s' ] H; [ discriminate | ].
  unfold go_int_lit in H. destruct (Ascii.eqb c "-"%char) eqn:E.
  - apply Ascii.eqb_eq in E. exists c, s'; split; [ reflexivity | left; exact E ].
  - destruct (dec_digit_val c) as [d|] eqn:Hc; [| discriminate].
    exists c, s'; split; [ reflexivity | right; rewrite Hc; discriminate ].
Qed.

(** a decoded string literal starts with the double-quote byte. *)
Lemma decode_string_literal_head : forall s b,
  decode_string_literal s = Some b -> exists rest, s = String dquote_c rest.
Proof.
  intros [ | c rest ] b H; cbn [decode_string_literal] in H; [ discriminate | ].
  destruct (Ascii.eqb c dquote_c) eqn:E; [ apply Ascii.eqb_eq in E; subst c; eauto | discriminate ].
Qed.

(** a spelling whose head is not a digit / sign / `.` / `0` is not a decoded decimal float (the coefficient
    reader stalls with an empty magnitude and no `.0e` body, and the `0.0` fallback cannot fire). *)
Lemma decode_decimal_nonnumeric_head : forall c s',
  dec_digit_val c = None ->
  Ascii.eqb c "-"%char = false -> Ascii.eqb c "+"%char = false ->
  Ascii.eqb c "."%char = false -> Ascii.eqb c "0"%char = false ->
  decode_decimal (String c s') = None.
Proof.
  intros c s' Hnd Hm Hp Hdot Hz.
  unfold decode_decimal.
  assert (Hb : decode_decimal_body (String c s') = None).
  { unfold decode_decimal_body.
    replace (read_signed_dec (String c s')) with (Some (0%Z, String c s'))
      by (unfold read_signed_dec; rewrite Hm, Hp; cbn [read_nat]; rewrite Hnd; reflexivity).
    destruct s' as [ | b [ | c0 r2 ] ]; try reflexivity.
    rewrite Hdot. reflexivity. }
  rewrite Hb.
  destruct (String.eqb (String c s') "0.0") eqn:E; [ | reflexivity ].
  apply String.eqb_eq in E. injection E as Ec _. rewrite Ec in Hz. discriminate Hz.
Qed.

(** a double-quote-led spelling (a string literal) is not a decoded decimal float — [vm_compute] cannot see
    this directly (the float body inspects three remainder bytes but only the lead quote is concrete), so it
    routes through [decode_decimal_nonnumeric_head]. *)
Lemma decode_decimal_dquote : forall rest, decode_decimal (String dquote_c rest) = None.
Proof. intro rest; apply decode_decimal_nonnumeric_head; reflexivity. Qed.

(** a bare integer literal is consumed WHOLE by the signed-decimal reader (empty remainder). *)
Lemma go_int_lit_read_signed_dec : forall s, go_int_lit s = true ->
  exists v, read_signed_dec s = Some (v, ""%string).
Proof.
  intros [ | c s' ] H; [ discriminate | ]. unfold go_int_lit in H.
  destruct (Ascii.eqb c "-"%char) eqn:Em.
  - apply Ascii.eqb_eq in Em; subst c.
    destruct s' as [ | c0 s0 ]; [ discriminate | ].
    eexists. replace (String "-"%char (String c0 s0)) with (String "-"%char (String c0 s0 ++ ""))%string
      by (rewrite str_app_nil; reflexivity).
    apply (read_signed_dec_sign "-"%char (String c0 s0) "" (or_introl eq_refl) H I).
  - destruct (dec_digit_val c) as [d|] eqn:Hc; [| discriminate].
    assert (Hall : str_all_digits (String c s') = true)
      by (cbn [str_all_digits]; rewrite Hc; exact H).
    eexists. replace (String c s') with (String c s' ++ "")%string
      by (rewrite str_app_nil; reflexivity).
    apply (read_signed_dec_all_digits (String c s') "" Hall ltac:(discriminate) I).
Qed.

(** a bare integer literal is not a decoded decimal float (empty `.0e` remainder; the `0.0` fallback fails on
    the all-digit head). *)
Lemma go_int_lit_decode_decimal_None : forall s, go_int_lit s = true -> decode_decimal s = None.
Proof.
  intros s H. destruct (go_int_lit_read_signed_dec s H) as [v Hrsd].
  assert (Hb : decode_decimal_body s = None)
    by (unfold decode_decimal_body; rewrite Hrsd; reflexivity).
  unfold decode_decimal. rewrite Hb.
  destruct (String.eqb s "0.0") eqn:Es0; [ | reflexivity ].
  apply String.eqb_eq in Es0; subst s. vm_compute in H; discriminate H.
Qed.

(** single-character suffix cancellation over [string]. *)
Lemma str_snoc_inj : forall (ch : ascii) a b,
  (a ++ String ch "")%string = (b ++ String ch "")%string -> a = b.
Proof.
  intros ch a; induction a as [ | x a' IH ]; intros [ | y b' ] Heq; cbn [append] in Heq.
  - reflexivity.
  - injection Heq as _ H2; destruct b'; discriminate.
  - injection Heq as _ H2; destruct a'; discriminate.
  - injection Heq as Hxy H2; f_equal; [ exact Hxy | apply IH; exact H2 ].
Qed.

(** the integer-conversion spelling `<int-keyword>(<body>` determines its keyword and body: every integer
    keyword is `(`-free, so the leading `(` splits the spelling uniquely. *)
Lemma int_kw_paren_inj : forall t1 t2 r1 r2,
  (integer_keyword t1 ++ String "("%char r1)%string = (integer_keyword t2 ++ String "("%char r2)%string ->
  t1 = t2 /\ r1 = r2.
Proof.
  intros t1 t2 r1 r2 H; destruct t1, t2; cbn in H;
    solve [ discriminate H | injection H; intros; subst; split; reflexivity ].
Qed.

Lemma float_kw_paren_inj : forall t1 t2 r1 r2,
  (float_keyword t1 ++ String "("%char r1)%string = (float_keyword t2 ++ String "("%char r2)%string ->
  t1 = t2 /\ r1 = r2.
Proof.
  intros t1 t2 r1 r2 H; destruct t1, t2; cbn in H;
    solve [ discriminate H | injection H; intros; subst; split; reflexivity ].
Qed.

(** an integer-conversion spelling and a float-conversion spelling never coincide (keyword lead char i/u vs f). *)
Lemma int_float_kw_paren_disjoint : forall t1 t2 r1 r2,
  (integer_keyword t1 ++ String "("%char r1)%string <> (float_keyword t2 ++ String "("%char r2)%string.
Proof. intros t1 t2 r1 r2 H; destruct t1, t2; cbn in H; discriminate H. Qed.

(** ★§30 DETERMINISM: a rendered spelling denotes AT MOST ONE [ConstInfo] — the rendered-constant denotation
    is FUNCTIONAL, so it never assigns a spelling two conflicting constant statuses.  Together with
    [render_const_info_denotes] (which exhibits the const_info a spelling denotes) this pins the
    spelling<->status correspondence to a genuine bijection on the rendered image: the recognisers for bool,
    bare integer, string, integer conversion, bare float, and float conversion are pairwise disjoint. *)
Theorem render_const_info_denotes_functional : forall s ci1 ci2,
  RenderedConstInfoDenotes s ci1 -> RenderedConstInfoDenotes s ci2 -> ci1 = ci2.
Proof.
  intros s ci1 ci2 H1; revert ci2; induction H1 as
    [ b
    | s z Hint Hread
    | s bytes Hstr
    | ti inner ci tc Hinner IH Hconv
    | s q Hdec
    | tf inner ci tc Hinner IH Hconv ]; intros ci2 H2.
  - (* H1 = RCDBool : the spelling is the concrete "true"/"false" *)
    destruct b; inversion H2 as
      [ b0 Hs0 | s0 z0 Hint0 Hread0 Hs0 | s0 by0 Hstr0 Hs0
      | t0 in0 cc0 tc0 Hin0 Hcv0 Hs0 | s0 q0 Hdec0 Hs0 | t0 in0 cc0 tc0 Hin0 Hcv0 Hs0 ]; subst;
      solve
        [ destruct b0; cbn in *; congruence
        | vm_compute in Hint0; discriminate Hint0
        | vm_compute in Hstr0; discriminate Hstr0
        | vm_compute in Hdec0; discriminate Hdec0
        | destruct t0; cbn in Hs0; discriminate Hs0 ].
  - (* H1 = RCDInt : subst eliminates the string var into the outer [Hint] *)
    inversion H2 as
      [ b0 Hs0 | s0 z0 Hint0 Hread0 Hs0 | s0 by0 Hstr0 Hs0
      | t0 in0 cc0 tc0 Hin0 Hcv0 Hs0 | s0 q0 Hdec0 Hs0 | t0 in0 cc0 tc0 Hin0 Hcv0 Hs0 ]; subst;
      solve
        [ destruct b0; vm_compute in Hint; discriminate Hint
        | congruence
        | destruct (decode_string_literal_head _ _ Hstr0) as [rest Hrs];
            rewrite Hrs in Hint; vm_compute in Hint; discriminate Hint
        | destruct t0; vm_compute in Hint; discriminate Hint
        | rewrite (go_int_lit_decode_decimal_None _ Hint) in Hdec0; discriminate Hdec0 ].
  - (* H1 = RCDString *)
    inversion H2 as
      [ b0 Hs0 | s0 z0 Hint0 Hread0 Hs0 | s0 by0 Hstr0 Hs0
      | t0 in0 cc0 tc0 Hin0 Hcv0 Hs0 | s0 q0 Hdec0 Hs0 | t0 in0 cc0 tc0 Hin0 Hcv0 Hs0 ]; subst;
      solve
        [ destruct b0; vm_compute in Hstr; discriminate Hstr
        | congruence
        | destruct (decode_string_literal_head _ _ Hstr) as [rest Hrs];
            rewrite Hrs in Hint0; vm_compute in Hint0; discriminate Hint0
        | destruct (decode_string_literal_head _ _ Hstr) as [rest Hrs];
            rewrite Hrs in Hdec0; rewrite decode_decimal_dquote in Hdec0; discriminate Hdec0
        | destruct t0; vm_compute in Hstr; discriminate Hstr ].
  - (* H1 = RCDIntConvert : the compound spelling survives subst as [Hs0]; the diagonal proves tc = tc0 by
       [convert_const] being a function *)
    inversion H2 as
      [ b0 Hs0 | s0 z0 Hint0 Hread0 Hs0 | s0 by0 Hstr0 Hs0
      | t0 in0 cc0 tc0 Hin0 Hcv0 Hs0 | s0 q0 Hdec0 Hs0 | t0 in0 cc0 tc0 Hin0 Hcv0 Hs0 ]; subst.
    + destruct b0; destruct ti; cbn in Hs0; discriminate Hs0.
    + destruct ti; vm_compute in Hint0; discriminate Hint0.
    + destruct ti; vm_compute in Hstr0; discriminate Hstr0.
    + destruct (int_kw_paren_inj t0 ti (in0 ++ ")") (inner ++ ")") Hs0) as [-> Htl];
        apply str_snoc_inj in Htl; subst in0;
        specialize (IH cc0 Hin0); subst cc0;
        assert (Heq : tc = tc0) by congruence; rewrite Heq; reflexivity.
    + destruct ti; vm_compute in Hdec0; discriminate Hdec0.
    + exfalso; apply (int_float_kw_paren_disjoint ti t0 (inner ++ ")") (in0 ++ ")")); symmetry; exact Hs0.
  - (* H1 = RCDFloat *)
    inversion H2 as
      [ b0 Hs0 | s0 z0 Hint0 Hread0 Hs0 | s0 by0 Hstr0 Hs0
      | t0 in0 cc0 tc0 Hin0 Hcv0 Hs0 | s0 q0 Hdec0 Hs0 | t0 in0 cc0 tc0 Hin0 Hcv0 Hs0 ]; subst;
      solve
        [ destruct b0; vm_compute in Hdec; discriminate Hdec
        | rewrite (go_int_lit_decode_decimal_None _ Hint0) in Hdec; discriminate Hdec
        | destruct (decode_string_literal_head _ _ Hstr0) as [rest Hrs];
            rewrite Hrs in Hdec; rewrite decode_decimal_dquote in Hdec; discriminate Hdec
        | destruct t0; vm_compute in Hdec; discriminate Hdec
        | congruence ].
  - (* H1 = RCDFloatConvert *)
    inversion H2 as
      [ b0 Hs0 | s0 z0 Hint0 Hread0 Hs0 | s0 by0 Hstr0 Hs0
      | t0 in0 cc0 tc0 Hin0 Hcv0 Hs0 | s0 q0 Hdec0 Hs0 | t0 in0 cc0 tc0 Hin0 Hcv0 Hs0 ]; subst.
    + destruct b0; destruct tf; cbn in Hs0; discriminate Hs0.
    + destruct tf; vm_compute in Hint0; discriminate Hint0.
    + destruct tf; vm_compute in Hstr0; discriminate Hstr0.
    + exfalso; apply (int_float_kw_paren_disjoint t0 tf (in0 ++ ")") (inner ++ ")")); exact Hs0.
    + destruct tf; vm_compute in Hdec0; discriminate Hdec0.
    + destruct (float_kw_paren_inj t0 tf (in0 ++ ")") (inner ++ ")") Hs0) as [-> Htl];
        apply str_snoc_inj in Htl; subst in0;
        specialize (IH cc0 Hin0); subst cc0;
        assert (Heq : tc = tc0) by congruence; rewrite Heq; reflexivity.
Qed.

(** The one root theorem connecting the three authorities (GoTypes constant-status, GoSafe value, GoRender
    spelling): a resolved [println] argument ANALYZES to a [ConstInfo] whose rendered spelling denotes it (the
    §3 render/ConstInfo root), its resolved type IS that ConstInfo's type, and it EVALUATES to a well-formed
    value of that type carrying the SAME exact constant.  NOT a claim about the real Go parser — real-Go
    acceptance is external adequacy, exercised differentially by the e2e. *)
Theorem render_resolved_expr_denotes : forall e t,
  ResolveExpr UsePrintlnArg e t ->
  exists ci rc v,
       const_info e = Some ci
    /\ resolve_const_info ci = Some rc
    /\ resolved_const_type rc = t
    /\ RenderedConstInfoDenotes (render_expr e) ci
    /\ eval_expr e = Some v
    /\ value_type v = t
    /\ ValueWF v
    /\ ValueDenotesConst v (resolved_const_exact rc).
Proof.
  intros e t H.
  destruct (eval_expr_denotes UsePrintlnArg e t H)
    as [ rc [ v [ Hrec [ Hev [ Hvt [ Hwf Hden ] ] ] ] ] ].
  destruct (resolve_expr_const_sound UsePrintlnArg e rc Hrec) as [ ci [ Hci [ Hri Hua ] ] ].
  assert (Hteq : resolved_const_type rc = t).
  { apply resolve_expr_complete in H; unfold resolve_expr in H; rewrite Hrec in H;
    cbn [option_map] in H; injection H as H'; exact H'. }
  exists ci, rc, v; subst t.
  split; [ exact Hci | ].
  split; [ exact Hri | ].
  split; [ reflexivity | ].
  split; [ apply render_const_info_denotes; exact Hci | ].
  split; [ exact Hev | ].
  split; [ exact Hvt | ].
  split; [ exact Hwf | exact Hden ].
Qed.

(** The int boundaries: the max/min literals evaluate to well-formed [int] values AND resolve as
    [TInteger IInt] (the boundary is representable — the range check uses the one [Ints] authority). *)
Lemma render_boundary_max :
  eval_expr (EInt (Z.to_N int_max)) = Some (VInteger IInt int_max)
  /\ ResolveExpr UsePrintlnArg (EInt (Z.to_N int_max)) (TInteger IInt).
Proof. split; [ reflexivity | apply resolve_expr_sound; reflexivity ]. Qed.

Lemma render_boundary_min :
  eval_expr (ENeg (Z.to_N (- int_min))) = Some (VInteger IInt int_min)
  /\ ResolveExpr UsePrintlnArg (ENeg (Z.to_N (- int_min))) (TInteger IInt).
Proof. split; [ reflexivity | apply resolve_expr_sound; reflexivity ]. Qed.

(** ---- explicit-conversion rendering fixtures (§15): the exact keyword spelling of each of the ten integer
    types, and the exact rendered spelling of a (possibly nested) conversion. ---- *)
Example kw_int    : integer_keyword IInt    = "int".    Proof. reflexivity. Qed.
Example kw_int8   : integer_keyword IInt8   = "int8".   Proof. reflexivity. Qed.
Example kw_int16  : integer_keyword IInt16  = "int16".  Proof. reflexivity. Qed.
Example kw_int32  : integer_keyword IInt32  = "int32".  Proof. reflexivity. Qed.
Example kw_int64  : integer_keyword IInt64  = "int64".  Proof. reflexivity. Qed.
Example kw_uint   : integer_keyword IUint   = "uint".   Proof. reflexivity. Qed.
Example kw_uint8  : integer_keyword IUint8  = "uint8".  Proof. reflexivity. Qed.
Example kw_uint16 : integer_keyword IUint16 = "uint16". Proof. reflexivity. Qed.
Example kw_uint32 : integer_keyword IUint32 = "uint32". Proof. reflexivity. Qed.
Example kw_uint64 : integer_keyword IUint64 = "uint64". Proof. reflexivity. Qed.
Example render_int8_127 : render_expr (EIntConvert IInt8 (EInt 127)) = "int8(127)". Proof. reflexivity. Qed.
Example render_uint64_big : render_expr (EIntConvert IUint64 (EInt 18446744073709551615)) = "uint64(18446744073709551615)". Proof. reflexivity. Qed.
Example render_nested : render_expr (EIntConvert IInt8 (EIntConvert IInt16 (EInt 127))) = "int8(int16(127))". Proof. reflexivity. Qed.

(** ---- string denotation surfaces: a rendered string literal denotes its exact untyped byte-constant; a
    RESOLVED string argument is the string instance of the two roots. ---- *)
Lemma render_string_denotes : forall s,
  RenderedConstInfoDenotes (render_expr (EString s)) (CIUntyped (CString s)).
Proof. intro s; apply render_const_info_denotes; reflexivity. Qed.

Lemma render_resolved_string_denotes : forall s t,
  ResolveExpr UsePrintlnArg (EString s) t ->
  exists ci rc v, const_info (EString s) = Some ci /\ resolve_const_info ci = Some rc
            /\ resolved_const_type rc = t
            /\ RenderedConstInfoDenotes (render_expr (EString s)) ci
            /\ eval_expr (EString s) = Some v /\ value_type v = t /\ ValueWF v
            /\ ValueDenotesConst v (resolved_const_exact rc).
Proof. intros s t H; apply render_resolved_expr_denotes; exact H. Qed.

(** ---- §4 integer-repair regressions: a bare integer stays UNTYPED (NO false [int] label) even far above
    [int_max]; only an explicit conversion assigns a type, DIRECTLY, after the representability check.  This
    is exactly why `uint64(2^63)` is valid though the bare `2^63` does not fit [int]. ---- *)
Example repair_bare_render : render_expr (EInt 9223372036854775808) = "9223372036854775808".
Proof. reflexivity. Qed.

Example repair_bare_untyped :
  RenderedConstInfoDenotes (render_expr (EInt 9223372036854775808))
                           (CIUntyped (CInt 9223372036854775808)).
Proof. apply render_const_info_denotes; reflexivity. Qed.

(** a TYPED-constant denotation is always a conversion spelling, so it starts with a conversion keyword's
    first letter (i / u for integers, f for floats) — proved by inversion on a GENERAL string (never the big
    rendered constant). *)
Lemma rcd_typed_starts_letter : forall s t (tc : TypedConst t),
  RenderedConstInfoDenotes s (CITyped t tc) ->
  exists rest, s = String "i"%char rest \/ s = String "u"%char rest \/ s = String "f"%char rest.
Proof.
  intros s t tc H;
    inversion H as [ | | | target inner ci tc0 Hinner Hconv Hs Hci
                    | | target inner ci tc0 Hinner Hconv Hs Hci ]; subst.
  - destruct target; cbn; eexists; ((left; reflexivity) || (right; left; reflexivity)).
  - destruct target; cbn; eexists; right; right; reflexivity.
Qed.

Example repair_bare_not_typed : forall t (tc : TypedConst t),
  ~ RenderedConstInfoDenotes (render_expr (EInt 9223372036854775808)) (CITyped t tc).
Proof.
  intros t tc H; apply rcd_typed_starts_letter in H; rewrite repair_bare_render in H.
  destruct H as [ rest [ Hi | [ Hu | Hf ] ] ]; discriminate.
Qed.

Example repair_uint64_typed :
  RenderedConstInfoDenotes (render_expr (EIntConvert IUint64 (EInt 9223372036854775808)))
                           (CITyped (TInteger IUint64) (TCInteger IUint64 9223372036854775808 eq_refl)).
Proof. apply render_const_info_denotes; reflexivity. Qed.

Example repair_uint64_max_typed :
  RenderedConstInfoDenotes (render_expr (EIntConvert IUint64 (EInt 18446744073709551615)))
                           (CITyped (TInteger IUint64) (TCInteger IUint64 18446744073709551615 eq_refl)).
Proof. apply render_const_info_denotes; reflexivity. Qed.

(** ---- §26/§28/§29 float rendering: the ONE canonical decimal spelling, direct conversion spellings, and
    denotation surfaces (a bare float denotes its exact rational; the decoder round-trips it). ---- *)
Example render_float_1p5   : render_expr (EFloat d_15em1) = "15.0e-1". Proof. reflexivity. Qed.
Example render_float_zero  : render_expr (EFloat (mkDecimal 0 0 eq_refl)) = "0.0". Proof. reflexivity. Qed.
Example render_float_1e6   : render_expr (EFloat (mkDecimal 1 6 eq_refl)) = "1.0e+6". Proof. reflexivity. Qed.
Example render_float_neg   : render_expr (EFloat (mkDecimal (-15) (-1) eq_refl)) = "-15.0e-1". Proof. reflexivity. Qed.
Example render_conv_f32    : render_expr (EFloatConvert F32 (EFloat d_15em1)) = "float32(15.0e-1)". Proof. reflexivity. Qed.
Example render_conv_f64    : render_expr (EFloatConvert F64 (EFloat d_3)) = "float64(3.0e+0)". Proof. reflexivity. Qed.

Lemma render_float_denotes : forall d,
  RenderedConstInfoDenotes (render_expr (EFloat d)) (CIUntyped (CFloat (decimal_value d))).
Proof. intro d; apply render_const_info_denotes; reflexivity. Qed.

(* the bare float denotes its EXACT (unrounded) rational (= 3/2 for d_15em1, by GoTypes.decimal_value_1p5);
   the F32 conversion denotes the rounded dyadic *)
Example render_float_untyped_denotes :
  RenderedConstInfoDenotes (render_expr (EFloat d_15em1)) (CIUntyped (CFloat (decimal_value d_15em1))).
Proof. apply render_const_info_denotes; reflexivity. Qed.
Example render_conv_f32_typed_denotes :
  option_map const_info_exact (const_info (EFloatConvert F32 (EFloat d_scar)))
    = Some (CFloat (fc_of_Z 2305843284091600896)).
Proof. vm_compute. reflexivity. Qed.

(* §29 required examples: bare 1.0e-1 denotes the UNTYPED exact rational 1/10; a float64 conversion of a tiny
   negative value denotes a TYPED float64 exact (unsigned) zero — no intermediate status, exact via the ONE
   round_float_const authority. *)
Example render_float_untyped_tenth :
  RenderedConstInfoDenotes (render_expr (EFloat (mkDecimal 1 (-1) eq_refl)))
                           (CIUntyped (CFloat (decimal_value (mkDecimal 1 (-1) eq_refl)))).
Proof. apply render_const_info_denotes; reflexivity. Qed.
Example render_conv_f64_underflow_zero :
  option_map const_info_exact (const_info (EFloatConvert F64 (EFloat (mkDecimal (-1) (-330) eq_refl))))
    = Some (CFloat fc_zero).
Proof. vm_compute. reflexivity. Qed.

