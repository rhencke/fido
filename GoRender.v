(** ============================================================================
    GoRender — the DIRECT renderer of one file's raw declarations to Go source bytes.  No tokenizer/
    lexer/parser/round-trip/second tree.  The package CLAUSE is emitted from the compiler-derived package
    name (a CompilationFacts result, passed in — not raw metadata); each [DMain] renders as a
    `func main()` declaration; the builtin [println] is the fixed spelling of [SPrintln].

    Every rendered file begins with the exact generated header as its FIRST LINE (part of the
    Rocq-rendered bytes — the sink never adds or alters it).  [render_file] is an INTERNAL helper; the
    PUBLIC capability is [GoEmit.render_program : SafeProgram -> DirectoryImage].  Proved here: all
    output ASCII; the ONE constant-status root [render_const_info_denotes] — rendering an expression denotes
    EXACTLY the [GoTypes.ConstInfo] it computes (a bare integer is an UNTYPED constant, not a typed [int] —
    the §1 repair; an explicit conversion is a TYPED constant), in the ONE [ConstInfo] vocabulary, under an
    INDEPENDENT decimal reader / string decoder (parser-free; the milestone forbids a lexer/parser/round-trip
    in the certified path); and [render_resolved_expr_denotes], tying the three authorities — a resolved
    [println] argument analyzes to a ConstInfo whose spelling denotes it and evaluates to a well-formed value
    of its resolved [GoType] carrying the same constant — plus decimal faithfulness / no-leading-zero and the
    int boundary facts.  Whether the REAL Go compiler parses these bytes to that value is claim (B) — external
    adequacy — exercised by the differential e2e, not a kernel theorem here.
    ============================================================================ *)
From Stdlib Require Import String Ascii NArith ZArith List Bool Lia.
From Fido Require Import digits Ints ModulePath GoVersion GoAST GoTypes GoCompile GoSafe.
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

Fixpoint render_expr (e : GoExpr) : string :=
  match e with
  | EBool true  => "true"
  | EBool false => "false"
  | EInt n => print_Z (Z.of_N n)
  | ENeg n => String "-"%char (print_Z (Z.of_N n))
  | EString s => render_string_literal s
  | EIntConvert it e' => integer_keyword it ++ "(" ++ render_expr e' ++ ")"
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

Lemma render_expr_ascii : forall e, str_ascii (render_expr e) = true.
Proof.
  induction e as [ [] | n | n | s | it e' IHe' ]; cbn [render_expr].
  - reflexivity.
  - reflexivity.
  - apply print_Z_ascii.
  - cbn [str_ascii]. rewrite print_Z_ascii. reflexivity.
  - apply render_string_literal_ascii.
  - rewrite !str_ascii_app, integer_keyword_ascii, IHe'; reflexivity.
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
Inductive RenderedConstInfoDenotes : string -> ConstInfo -> Prop :=
| RCDBool : forall (b : bool),
    RenderedConstInfoDenotes (if b then "true"%string else "false"%string) (UntypedConst (CBool b))
| RCDInt : forall s z,
    read_go_int s = z ->
    RenderedConstInfoDenotes s (UntypedConst (CInt z))
| RCDString : forall s bytes,
    decode_string_literal s = Some bytes ->
    RenderedConstInfoDenotes s (UntypedConst (CString bytes))
| RCDIntConvert : forall target inner ci z,
    RenderedConstInfoDenotes inner ci ->
    ci_const ci = CInt z ->
    IntRepresentable target z ->
    RenderedConstInfoDenotes (integer_keyword target ++ "(" ++ inner ++ ")")
                             (TypedConst (TInteger target) (CInt z)).

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
  exists ci' z, const_info e = Some ci'
             /\ ci_const ci' = CInt z
             /\ integer_representableb it z = true
             /\ ci = TypedConst (TInteger it) (CInt z).
Proof.
  intros it e ci H; simpl in H.
  destruct (const_info e) as [ci'|] eqn:Hce'; [| discriminate].
  exists ci'; destruct ci' as [ c' | t' c' ].
  - destruct c' as [ b | z' | s ]; try discriminate.
    destruct (integer_representableb it z') eqn:Hrep; [| discriminate].
    injection H as <-; exists z'; repeat split; first [ reflexivity | exact Hce' | exact Hrep ].
  - destruct t' as [| srcty |]; try discriminate; destruct c' as [ b | z' | s ]; try discriminate;
      destruct (integer_representableb it z') eqn:Hrep; try discriminate;
      injection H as <-; exists z'; repeat split; first [ reflexivity | exact Hce' | exact Hrep ].
Qed.

(** ★§2-3 ROOT: rendering an expression denotes EXACTLY the [const_info] GoTypes computes for it — the
    source-spelling / constant-status correspondence, in the ONE ConstInfo vocabulary.  A bare integer
    denotes an UNTYPED constant (the §1 repair: NO false [int] label); an explicit conversion denotes a
    TYPED constant of the destination type.  Reuses the exact GoTypes values + representability. *)
Theorem render_const_info_denotes : forall e ci,
  const_info e = Some ci -> RenderedConstInfoDenotes (render_expr e) ci.
Proof.
  induction e as [ b | n | n | s | it' e' IHe' ]; intros ci H.
  - simpl in H; injection H as <-; cbn [render_expr]; destruct b; [ exact (RCDBool true) | exact (RCDBool false) ].
  - simpl in H; injection H as <-; cbn [render_expr]; apply RCDInt, read_go_int_EInt.
  - simpl in H; injection H as <-; cbn [render_expr]; apply RCDInt, read_go_int_ENeg.
  - simpl in H; injection H as <-; cbn [render_expr]; apply RCDString, render_string_roundtrip.
  - destruct (const_info_convert_inner it' e' ci H) as [ ci' [ z [ Hce' [ Hval [ Hrep -> ] ] ] ] ].
    cbn [render_expr]. apply RCDIntConvert with (ci := ci').
    + apply IHe'; exact Hce'.
    + exact Hval.
    + apply integer_representableb_spec; exact Hrep.
Qed.

(** The one root theorem connecting the three authorities (GoTypes constant-status, GoSafe value, GoRender
    spelling): a resolved [println] argument ANALYZES to a [ConstInfo] whose rendered spelling denotes it (the
    §3 render/ConstInfo root), its resolved type IS that ConstInfo's type, and it EVALUATES to a well-formed
    value of that type carrying the SAME exact constant.  NOT a claim about the real Go parser — real-Go
    acceptance is external adequacy, exercised differentially by the e2e. *)
Theorem render_resolved_expr_denotes : forall e t,
  ResolveExpr UsePrintlnArg e t ->
  exists ci v,
       const_info e = Some ci
    /\ info_type ci = t
    /\ RenderedConstInfoDenotes (render_expr e) ci
    /\ eval_expr e = Some v
    /\ value_type v = t
    /\ ValueWF v
    /\ value_const v = ci_const ci.
Proof.
  intros e t H; pose proof H as HR.
  apply resolve_expr_complete in H; unfold resolve_expr in H.
  destruct (const_info e) as [ci|] eqn:Hci; [| discriminate].
  destruct (use_allowsb UsePrintlnArg (info_type ci) && const_representableb (info_type ci) (ci_const ci));
    [| discriminate].
  injection H as Ht.
  destruct (eval_expr_resolved UsePrintlnArg e t HR) as [ v [ Hev [ Hvt Hwf ] ] ].
  exists ci, v.
  split; [ reflexivity | ].
  split; [ exact Ht | ].
  split; [ apply render_const_info_denotes; exact Hci | ].
  split; [ exact Hev | ].
  split; [ exact Hvt | ].
  split; [ exact Hwf | ].
  rewrite (eval_expr_value_const e v Hev); symmetry; apply (const_info_value e ci Hci).
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
  RenderedConstInfoDenotes (render_expr (EString s)) (UntypedConst (CString s)).
Proof. intro s; apply render_const_info_denotes; reflexivity. Qed.

Lemma render_resolved_string_denotes : forall s t,
  ResolveExpr UsePrintlnArg (EString s) t ->
  exists ci v, const_info (EString s) = Some ci /\ info_type ci = t
            /\ RenderedConstInfoDenotes (render_expr (EString s)) ci
            /\ eval_expr (EString s) = Some v /\ value_type v = t /\ ValueWF v
            /\ value_const v = ci_const ci.
Proof. intros s t H; apply render_resolved_expr_denotes; exact H. Qed.

(** ---- §4 integer-repair regressions: a bare integer stays UNTYPED (NO false [int] label) even far above
    [int_max]; only an explicit conversion assigns a type, DIRECTLY, after the representability check.  This
    is exactly why `uint64(2^63)` is valid though the bare `2^63` does not fit [int]. ---- *)
Example repair_bare_render : render_expr (EInt 9223372036854775808) = "9223372036854775808".
Proof. reflexivity. Qed.

Example repair_bare_untyped :
  RenderedConstInfoDenotes (render_expr (EInt 9223372036854775808))
                           (UntypedConst (CInt 9223372036854775808)).
Proof. apply render_const_info_denotes; reflexivity. Qed.

(** a TYPED-constant denotation is always a conversion spelling, so it starts with an integer keyword's
    first letter (i / u) — proved by inversion on a GENERAL string (never the big rendered constant). *)
Lemma rcd_typed_starts_letter : forall s t c,
  RenderedConstInfoDenotes s (TypedConst t c) ->
  exists rest, s = String "i"%char rest \/ s = String "u"%char rest.
Proof.
  intros s t c H; inversion H as [ | | | target inner ci z Hinner Hval Hrep Hs Hci ]; subst.
  destruct target; cbn; (eexists; ((left; reflexivity) || (right; reflexivity))).
Qed.

Example repair_bare_not_typed_int :
  ~ RenderedConstInfoDenotes (render_expr (EInt 9223372036854775808))
                             (TypedConst (TInteger IInt) (CInt 9223372036854775808)).
Proof.
  intro H; apply rcd_typed_starts_letter in H; rewrite repair_bare_render in H.
  destruct H as [ rest [ Hi | Hu ] ]; discriminate.
Qed.

Example repair_uint64_typed :
  RenderedConstInfoDenotes (render_expr (EIntConvert IUint64 (EInt 9223372036854775808)))
                           (TypedConst (TInteger IUint64) (CInt 9223372036854775808)).
Proof. apply render_const_info_denotes; reflexivity. Qed.

Example repair_uint64_max_typed :
  RenderedConstInfoDenotes (render_expr (EIntConvert IUint64 (EInt 18446744073709551615)))
                           (TypedConst (TInteger IUint64) (CInt 18446744073709551615)).
Proof. apply render_const_info_denotes; reflexivity. Qed.

