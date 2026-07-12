(** ============================================================================
    GoRender — ONE direction: typed IR -> canonical token stream -> bytes.

    [program_tokens] is the canonical post-ASI token stream of a typed program;
    [program_tokens_grammar] proves it derives the program in the INDEPENDENT grammar
    (GoGrammar — which never mentions this module).  [render_tokens] is the one token
    renderer: it owns ALL layout (gofmt-canonical: a blank line after the package
    clause, tab indentation, statement-per-line — the pinned gofmt accepts these bytes
    unchanged; checked by the e2e, not claimed as a theorem).  There is no second
    string printer beside it.  Decimal digits come from the one authority (digits.v).
    ============================================================================ *)
From Stdlib Require Import String Ascii ZArith List Bool Lia.
From Fido Require Import digits CoreType TypedIR GoToken GoLex GoGrammar.
Import ListNotations.
Open Scope string_scope.

(** ---- Canonical tokens ---- *)

Definition expr_tokens (e : TypedPrimExpr) : list GoToken :=
  match e with
  | TEBool true    => [TIdent "true"]
  | TEBool false   => [TIdent "false"]
  | TEStr s _      => [TStrLit s]
  | TEIntLit n _   => [TIntLit n]
  | TENeg n _      => [TMinus; TIntLit n]
  end.

Fixpoint args_tokens (es : list TypedPrimExpr) : list GoToken :=
  match es with
  | []       => []
  | [e]      => expr_tokens e
  | e :: es' => expr_tokens e ++ TComma :: args_tokens es'
  end.

Definition stmt_tokens (s : TypedStmt) : list GoToken :=
  match s with
  | TPrintln args => TIdent "println" :: TLParen :: args_tokens args ++ [TRParen; TSemi]
  end.

Definition program_tokens (p : TypedProgram) : list GoToken :=
  [KwPackage; TIdent "main"; TSemi;
   KwFunc; TIdent "main"; TLParen; TRParen; TLBrace]
    ++ concat (map stmt_tokens (tp_body p)) ++ [TRBrace; TSemi].

(** ---- The canonical stream DERIVES the program in the independent grammar ---- *)

Lemma expr_tokens_grammar : forall e, ExprG (expr_tokens e) e.
Proof. intros [ [|] | s H | n H | n H ]; simpl; constructor. Qed.

Lemma args_tokens_grammar1 : forall e es, Args1G (args_tokens (e :: es)) (e :: es).
Proof.
  intros e es. revert e. induction es as [ | e' es' IH ]; intro e; simpl.
  - apply GArg1, expr_tokens_grammar.
  - apply GArgCons; [ apply expr_tokens_grammar | apply IH ].
Qed.

Lemma args_tokens_grammar : forall es, ArgsG (args_tokens es) es.
Proof.
  intros [ | e es ].
  - apply GArgs0.
  - apply GArgsN, args_tokens_grammar1.
Qed.

Lemma stmt_tokens_grammar : forall s, StmtG (stmt_tokens s) s.
Proof. intros [args]. simpl. constructor. apply args_tokens_grammar. Qed.

Lemma body_tokens_grammar : forall ss, BodyG (concat (map stmt_tokens ss)) ss.
Proof.
  induction ss as [ | s ss' IH ]; simpl.
  - constructor.
  - apply GBodyCons; [ apply stmt_tokens_grammar | exact IH ].
Qed.

Theorem program_tokens_grammar : forall p, ProgG (program_tokens p) p.
Proof. intros [body]. unfold program_tokens. simpl. constructor. apply body_tokens_grammar. Qed.

(** ---- The one token renderer (bytes) ---- *)

Definition nl_s  : string := String nl_c EmptyString.
Definition tab_s : string := String tab_c EmptyString.
Definition quote_s : string := String quote_c EmptyString.
Definition bslash_s : string := String bslash_c EmptyString.

(** Source escaping of a validated string payload — exactly the four admitted escapes;
    every other admitted payload char (printable ASCII) is verbatim.  Inverse of
    GoLex.[unescape] on the admitted charset. *)
Definition escape_char (c : ascii) : string :=
  if Ascii.eqb c quote_c then bslash_s ++ quote_s
  else if Ascii.eqb c bslash_c then bslash_s ++ bslash_s
  else if Ascii.eqb c nl_c then bslash_s ++ "n"
  else if Ascii.eqb c tab_c then bslash_s ++ "t"
  else String c EmptyString.

Fixpoint escape_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => escape_char c ++ escape_string s'
  end.

(** A token's bare lexeme (no layout).  [TSemi] has no lexeme here — the renderer
    realizes every canonical semicolon as a LINE END (Go then re-inserts it by ASI). *)
Definition token_text (t : GoToken) : string :=
  match t with
  | KwPackage => "package"
  | KwFunc    => "func"
  | TIdent s  => s
  | TIntLit n => print_Z n
  | TStrLit s => quote_s ++ escape_string s ++ quote_s
  | TLParen   => "(" | TRParen => ")"
  | TLBrace   => "{" | TRBrace => "}"
  | TComma    => "," | TMinus => "-"
  | TSemi     => ""
  end.

Fixpoint tabs (n : nat) : string :=
  match n with O => EmptyString | S k => tab_s ++ tabs k end.

(** Indentation for whatever follows a line break: the closing brace dedents. *)
Definition indent_for (depth : nat) (rest : list GoToken) : string :=
  match rest with
  | TRBrace :: _ => tabs (Nat.pred depth)
  | _            => tabs depth
  end.

(** The renderer.  Layout rules (gofmt-canonical for this subset): keywords carry a
    trailing space; [,] carries a trailing space; [{] attaches with a leading space and
    opens an indented line; [;] renders as a line end (a BLANK line after the depth-0
    package clause; nothing after the final one). *)
Fixpoint render_tokens (depth : nat) (ts : list GoToken) : string :=
  match ts with
  | [] => EmptyString
  | KwPackage :: rest => "package " ++ render_tokens depth rest
  | KwFunc :: rest    => "func "    ++ render_tokens depth rest
  | TComma :: rest    => ", "       ++ render_tokens depth rest
  | TLBrace :: rest   => " {" ++ nl_s ++ indent_for (S depth) rest
                              ++ render_tokens (S depth) rest
  | TRBrace :: rest   => "}" ++ render_tokens (Nat.pred depth) rest
  | TSemi :: rest     =>
      (if Nat.eqb depth 0
       then match rest with [] => nl_s | _ => nl_s ++ nl_s end
       else nl_s ++ indent_for depth rest)
      ++ render_tokens depth rest
  | t :: rest         => token_text t ++ render_tokens depth rest
  end.

Definition render_program (p : TypedProgram) : string :=
  render_tokens 0 (program_tokens p).

(** ============================================================================
    RENDER/LEX INVERSE — lexing the rendered bytes recovers exactly the canonical
    token stream: [lex (render_program p) = Some (program_tokens p)].  This is the
    statement-termination/separator correctness of the renderer: every canonical
    [TSemi] really comes back via Go's ASI at the rendered line ends, and no two
    rendered lexemes fuse.
    ============================================================================ *)

(** ---- string plumbing ---- *)

Lemma str_app_assoc : forall a b c : string, ((a ++ b) ++ c) = (a ++ (b ++ c)).
Proof. induction a as [ | ch a' IH ]; intros; simpl; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma str_app_nil_r : forall s : string, (s ++ "") = s.
Proof. induction s as [ | c s' IH ]; simpl; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma str_snoc_app : forall (a : string) (c : ascii) (t : string),
  ((a ++ String c EmptyString) ++ t) = (a ++ String c t).
Proof. intros. rewrite str_app_assoc. reflexivity. Qed.

(** ---- character-class facts ---- *)

Lemma nat_ascii_id : forall n, (n < 256)%nat -> nat_of_ascii (ascii_of_nat n) = n.
Proof. intros n H. apply nat_ascii_embedding. exact H. Qed.

Lemma ascii_eqb_nat_false : forall a b, nat_of_ascii a <> nat_of_ascii b -> Ascii.eqb a b = false.
Proof.
  intros a b Hne. destruct (Ascii.eqb a b) eqn:E; [ | reflexivity ].
  apply Ascii.eqb_eq in E. subst. contradiction Hne. reflexivity.
Qed.

Lemma dec_digit_code : forall d, (d < 10)%nat -> nat_of_ascii (dec_digit d) = (48 + d)%nat.
Proof. intros d H. unfold dec_digit. apply nat_ascii_id. lia. Qed.

Lemma is_digit_dec_digit : forall d, (d < 10)%nat -> is_digit (dec_digit d) = true.
Proof.
  intros d H. unfold is_digit. rewrite dec_digit_code by exact H.
  apply andb_true_intro. split; apply Nat.leb_le; lia.
Qed.

Lemma digit_val_dec_digit : forall d, (d < 10)%nat -> digit_val (dec_digit d) = Z.of_nat d.
Proof. intros d H. unfold digit_val. rewrite dec_digit_code by exact H. lia. Qed.

Lemma is_space_dec_digit : forall d, (d < 10)%nat -> is_space (dec_digit d) = false.
Proof.
  intros d H. unfold is_space. rewrite dec_digit_code by exact H.
  apply orb_false_intro; apply Nat.eqb_neq; lia.
Qed.

Lemma is_nl_dec_digit : forall d, (d < 10)%nat -> is_nl (dec_digit d) = false.
Proof. intros d H. unfold is_nl. rewrite dec_digit_code by exact H. apply Nat.eqb_neq. lia. Qed.

Lemma is_letter_dec_digit : forall d, (d < 10)%nat -> is_letter (dec_digit d) = false.
Proof.
  intros d H. unfold is_letter. rewrite dec_digit_code by exact H.
  apply orb_false_intro; [ apply orb_false_intro | ].
  - apply andb_false_iff. left. apply Nat.leb_nle. lia.
  - apply andb_false_iff. left. apply Nat.leb_nle. lia.
  - apply Nat.eqb_neq. lia.
Qed.

Lemma eqb_dec_digit_quote : forall d, (d < 10)%nat -> Ascii.eqb (dec_digit d) quote_c = false.
Proof.
  intros d H. apply ascii_eqb_nat_false.
  rewrite dec_digit_code by exact H. unfold quote_c. rewrite nat_ascii_id by lia. lia.
Qed.

(** ---- whitespace skipping ---- *)

Lemma lex_tabs : forall n last s, lex_steps MStart last (tabs n ++ s) = lex_steps MStart last s.
Proof.
  induction n as [ | k IH ]; intros; simpl.
  - reflexivity.
  - apply IH.
Qed.

(** ---- option-result plumbing ---- *)

Definition opt_app (ts : list GoToken) (r : option (list GoToken)) : option (list GoToken) :=
  match r with Some us => Some ((ts ++ us)%list) | None => None end.

Lemma opt_cons_app : forall t r, opt_cons t r = opt_app [t] r.
Proof. intros t [us|]; reflexivity. Qed.

Lemma opt_app_app : forall a b r, opt_app a (opt_app b r) = opt_app ((a ++ b)%list) r.
Proof. intros a b [us|]; simpl; [ rewrite app_assoc | ]; reflexivity. Qed.

Lemma opt_app_nil : forall r, opt_app [] r = r.
Proof. intros [us|]; reflexivity. Qed.

(** ---- the ASCII identity of [is_nl] ---- *)

Lemma is_nl_eqb : forall c, is_nl c = Ascii.eqb c nl_c.
Proof.
  intro c. destruct (Ascii.eqb c nl_c) eqn:E.
  - apply Ascii.eqb_eq in E. subst. reflexivity.
  - unfold is_nl. apply Nat.eqb_neq. intro Hn.
    assert (c = nl_c).
    { rewrite <- (ascii_nat_embedding c). rewrite Hn. reflexivity. }
    subst. rewrite Ascii.eqb_refl in E. discriminate.
Qed.

(** ---- escape round-trip: lexing an escaped payload appends exactly the payload ---- *)

Lemma lex_escape : forall pay acc lst tail,
  lex_steps (MStr acc) lst (escape_string pay ++ tail)
  = lex_steps (MStr (acc ++ pay)) lst tail.
Proof.
  induction pay as [ | c pay' IH ]; intros acc lst tail.
  - simpl escape_string. rewrite str_app_nil_r. reflexivity.
  - cbn [escape_string]. rewrite str_app_assoc. unfold escape_char.
    destruct (Ascii.eqb c quote_c) eqn:Eq.
    { apply Ascii.eqb_eq in Eq. subst c.
      cbn. rewrite IH. rewrite str_snoc_app. reflexivity. }
    destruct (Ascii.eqb c bslash_c) eqn:Eb.
    { apply Ascii.eqb_eq in Eb. subst c.
      cbn. rewrite IH. rewrite str_snoc_app. reflexivity. }
    destruct (Ascii.eqb c nl_c) eqn:En.
    { apply Ascii.eqb_eq in En. subst c.
      cbn. rewrite IH. rewrite str_snoc_app. reflexivity. }
    destruct (Ascii.eqb c tab_c) eqn:Et.
    { apply Ascii.eqb_eq in Et. subst c.
      cbn. rewrite IH. rewrite str_snoc_app. reflexivity. }
    (* verbatim char: not quote, not backslash, not newline *)
    cbn [String.append]. cbn [lex_steps].
    rewrite Eq, Eb. rewrite is_nl_eqb, En.
    rewrite IH. rewrite str_snoc_app. reflexivity.
Qed.

(** ---- decimal literals: lexing the rendered digits accumulates the value ---- *)

Lemma render_digits_app : forall ds (t u : string),
  ((render_digits dec_digit ds t) ++ u) = render_digits dec_digit ds (t ++ u).
Proof.
  induction ds as [ | d tl IH ]; intros t u; simpl.
  - reflexivity.
  - unfold render_digits in *. cbn [fold_left]. apply (IH (String (dec_digit d) t)).
Qed.

Lemma z_of_nat_pos_neqb : forall d, (1 <= d)%nat -> Z.eqb (Z.of_nat d) 0 = false.
Proof. intros [ | k ] H; [ lia | reflexivity ]. Qed.

(** Entering at [MStart], a rendered digit list (MSB first, nonzero MSB) is consumed into
    exactly its value, leaving the lexer mid-number at the continuation. *)
Lemma lex_render_digits : forall ds lst tail,
  Forall (fun d => (d < 10)%nat) ds ->
  ds <> nil ->
  (1 <= List.last ds O)%nat ->
  lex_steps MStart lst (render_digits dec_digit ds tail)
  = lex_steps (MNum (dlist_val 10 ds) false) lst tail.
Proof.
  induction ds as [ | d tl IH ]; intros lst tail Hall Hnil Hlast.
  - contradiction.
  - inversion Hall; subst.
    unfold render_digits. cbn [fold_left].
    destruct tl as [ | d' tl' ].
    + (* singleton: d is both LSB and MSB *)
      cbn [List.last] in Hlast.
      cbn [fold_left lex_steps].
      rewrite is_space_dec_digit, is_nl_dec_digit, is_letter_dec_digit, is_digit_dec_digit
        by assumption.
      rewrite digit_val_dec_digit by assumption.
      rewrite z_of_nat_pos_neqb by assumption.
      cbn [dlist_val]. replace (Z.of_nat d + Z.of_nat 10 * 0)%Z with (Z.of_nat d) by lia.
      reflexivity.
    + (* the MSB lives in tl *)
      change (fold_left (fun acc d0 => String (dec_digit d0) acc) (d' :: tl') (String (dec_digit d) tail))
        with (render_digits dec_digit (d' :: tl') (String (dec_digit d) tail)).
      rewrite IH; [ | assumption | discriminate | ].
      * cbn [lex_steps].
        rewrite is_digit_dec_digit by assumption.
        rewrite digit_val_dec_digit by assumption.
        replace (dlist_val 10 (d :: d' :: tl'))
          with (dlist_val 10 (d' :: tl') * 10 + Z.of_nat d)%Z;
          [ reflexivity | cbn [dlist_val]; lia ].
      * cbn [List.last] in Hlast. exact Hlast.
Qed.

(** A printed nonnegative integer lexes into the mid-number state carrying exactly its
    value (the exactly-zero flag matches [print_Z 0 = "0"]). *)
Lemma lex_print_Z : forall n lst tail, (0 <= n)%Z ->
  lex_steps MStart lst ((print_Z n) ++ tail)
  = lex_steps (MNum n (Z.eqb n 0)) lst tail.
Proof.
  intros n lst tail Hn. destruct n as [ | p | p ].
  - reflexivity.
  - unfold print_Z, print_Z_pos.
    rewrite render_digits_app. cbn [String.append].
    rewrite lex_render_digits.
    + rewrite pos_digits_val by lia. reflexivity.
    + eapply Forall_impl; [ | apply (pos_digits_bound 10 p); lia ].
      cbn. intros a Ha. exact Ha.
    + apply pos_digits_nonnil.
    + apply pos_digits_last. lia.
  - lia.
Qed.

(** ---- argument-boundary steps ([,] or [)] after a pending lexeme) ---- *)

Definition arg_boundary (c : ascii) : Prop := c = ","%char \/ c = ")"%char.

(** In [MStart], a punctuation-headed continuation ignores the ASI [last] state. *)
Lemma lex_start_boundary_lst : forall lst1 lst2 c s',
  arg_boundary c ->
  lex_steps MStart lst1 (String c s') = lex_steps MStart lst2 (String c s').
Proof. intros lst1 lst2 c s' [ -> | -> ]; reflexivity. Qed.

Lemma word_boundary : forall w lst lst' c s',
  arg_boundary c ->
  lex_steps (MWord w) lst (String c s')
  = opt_cons (classify_word w) (lex_steps MStart lst' (String c s')).
Proof. intros w lst lst' c s' [ -> | -> ]; reflexivity. Qed.

Lemma num_boundary : forall v z lst lst' c s',
  arg_boundary c ->
  lex_steps (MNum v z) lst (String c s')
  = opt_cons (TIntLit v) (lex_steps MStart lst' (String c s')).
Proof. intros v z lst lst' c s' [ -> | -> ]; destruct z; reflexivity. Qed.

(** ---- expression fragments ---- *)

Definition expr_str (e : TypedPrimExpr) : string :=
  match e with
  | TEBool true  => "true"
  | TEBool false => "false"
  | TEStr s _    => quote_s ++ escape_string s ++ quote_s
  | TEIntLit n _ => print_Z n
  | TENeg n _    => "-" ++ print_Z n
  end.

(** Expression tokens render through the default (lexeme) branch. *)
Lemma render_expr_dec : forall depth e rest,
  render_tokens depth ((expr_tokens e ++ rest)%list) = expr_str e ++ render_tokens depth rest.
Proof.
  intros depth [ [|] | s H | n H | n H ] rest; cbn [expr_tokens List.app render_tokens token_text expr_str].
  - reflexivity.
  - reflexivity.
  - rewrite !str_app_assoc. reflexivity.
  - reflexivity.
  - rewrite str_app_assoc. reflexivity.
Qed.

(** Lexing one rendered expression, up to an argument boundary, emits its tokens. *)
Lemma lex_expr : forall e lst c s',
  arg_boundary c ->
  lex_steps MStart lst (expr_str e ++ String c s')
  = opt_app (expr_tokens e) (lex_steps MStart lst (String c s')).
Proof.
  intros e lst c s' Hb.
  destruct e as [ [|] | s H | n H | n H ]; cbn [expr_str expr_tokens].
  - (* true *)
    destruct Hb as [ -> | -> ]; simpl;
      [ destruct (lex_steps MStart (Some TComma) s')
      | destruct (lex_steps MStart (Some TRParen) s') ]; reflexivity.
  - (* false *)
    destruct Hb as [ -> | -> ]; simpl;
      [ destruct (lex_steps MStart (Some TComma) s')
      | destruct (lex_steps MStart (Some TRParen) s') ]; reflexivity.
  - (* string literal: the closing quote self-terminates *)
    rewrite !str_app_assoc.
    change (quote_s ++ (escape_string s ++ (quote_s ++ String c s')))
      with (String quote_c (escape_string s ++ (String quote_c (String c s')))).
    cbn [lex_steps].
    rewrite (lex_escape s EmptyString lst (String quote_c (String c s'))).
    cbn [String.append].
    destruct Hb as [ -> | -> ]; simpl;
      [ destruct (lex_steps MStart (Some TComma) s')
      | destruct (lex_steps MStart (Some TRParen) s') ]; reflexivity.
  - (* nonneg int literal *)
    destruct Hb as [ -> | -> ];
      rewrite lex_print_Z by (apply int_lit_ok_range in H; lia); simpl;
      [ destruct (lex_steps MStart (Some TComma) s')
      | destruct (lex_steps MStart (Some TRParen) s') ]; reflexivity.
  - (* unary minus over a nonneg literal *)
    destruct Hb as [ -> | -> ]; rewrite str_app_assoc; simpl;
      rewrite lex_print_Z by (apply neg_lit_ok_range in H; lia); simpl;
      [ destruct (lex_steps MStart (Some TComma) s')
      | destruct (lex_steps MStart (Some TRParen) s') ]; reflexivity.
Qed.

(** ---- argument lists ---- *)

Fixpoint args_str (es : list TypedPrimExpr) : string :=
  match es with
  | []       => ""
  | [e]      => expr_str e
  | e :: es' => expr_str e ++ ", " ++ args_str es'
  end.

Lemma render_args_dec : forall depth es rest,
  render_tokens depth ((args_tokens es ++ rest)%list) = args_str es ++ render_tokens depth rest.
Proof.
  intros depth es. induction es as [ | e es' IH ]; intro rest.
  - reflexivity.
  - destruct es' as [ | e2 es'' ].
    + cbn [args_tokens args_str]. apply render_expr_dec.
    + cbn [args_tokens args_str].
      rewrite <- List.app_assoc. rewrite render_expr_dec.
      cbn [List.app render_tokens]. rewrite IH. rewrite !str_app_assoc. reflexivity.
Qed.

Lemma args_str_cons2 : forall e e2 es'',
  args_str (e :: e2 :: es'') = expr_str e ++ ", " ++ args_str (e2 :: es'').
Proof. reflexivity. Qed.

Lemma args_tokens_cons2 : forall e e2 es'',
  args_tokens (e :: e2 :: es'') = (expr_tokens e ++ TComma :: args_tokens (e2 :: es''))%list.
Proof. reflexivity. Qed.

Lemma comma_space_step : forall lst X,
  lex_steps MStart lst (String ","%char (String " "%char X))
  = opt_cons TComma (lex_steps MStart (Some TComma) X).
Proof. reflexivity. Qed.

Lemma lex_args : forall es lst s',
  lex_steps MStart lst (args_str es ++ String ")"%char s')
  = opt_app (args_tokens es) (lex_steps MStart lst (String ")"%char s')).
Proof.
  induction es as [ | e es' IH ]; intros lst s'.
  - cbn [args_str String.append]. rewrite opt_app_nil. reflexivity.
  - destruct es' as [ | e2 es'' ].
    + cbn [args_str args_tokens]. apply lex_expr. right. reflexivity.
    + rewrite args_str_cons2, args_tokens_cons2.
      rewrite !str_app_assoc.
      change (", " ++ (args_str (e2 :: es'') ++ String ")"%char s'))
        with (String ","%char (String " "%char (args_str (e2 :: es'') ++ String ")"%char s'))).
      rewrite lex_expr by (left; reflexivity).
      rewrite comma_space_step.
      rewrite (IH (Some TComma) s').
      rewrite opt_cons_app, !opt_app_app.
      rewrite <- List.app_assoc. reflexivity.
Qed.

(** ---- statements, body, and the whole program ---- *)

(** A statement's rendering, decomposed (depth 1 — inside [func main()]). *)
Lemma render_stmt_dec : forall args rest,
  render_tokens 1 ((stmt_tokens (TPrintln args) ++ rest)%list)
  = "println(" ++ (args_str args ++ (")" ++ (nl_s ++ (indent_for 1 rest ++ render_tokens 1 rest)))).
Proof.
  intros args rest. cbn [stmt_tokens List.app].
  cbn [render_tokens token_text].
  rewrite <- List.app_assoc.
  rewrite render_args_dec.
  cbn [render_tokens List.app Nat.eqb].
  rewrite !str_app_assoc. reflexivity.
Qed.

Lemma rparen_nl_step : forall lst X,
  lex_steps MStart lst (String ")"%char (String nl_c X))
  = opt_cons TRParen (opt_cons TSemi (lex_steps MStart (Some TSemi) X)).
Proof. reflexivity. Qed.

Lemma lex_body : forall ss lst,
  lex_steps MStart lst
    (render_tokens 1 ((concat (map stmt_tokens ss) ++ [TRBrace; TSemi])%list))
  = Some ((concat (map stmt_tokens ss) ++ [TRBrace; TSemi])%list).
Proof.
  induction ss as [ | st ss' IH ]; intro lst.
  - reflexivity.
  - destruct st as [args].
    cbn [concat map]. rewrite <- List.app_assoc.
    rewrite render_stmt_dec.
    assert (Hk : exists k,
      indent_for 1 ((concat (map stmt_tokens ss') ++ [TRBrace; TSemi])%list) = tabs k).
    { destruct ((concat (map stmt_tokens ss') ++ [TRBrace; TSemi])%list) as [ | [] ? ];
        eexists; reflexivity. }
    destruct Hk as [k Hk]. rewrite Hk.
    simpl.
    rewrite lex_args.
    rewrite rparen_nl_step.
    rewrite lex_tabs.
    rewrite (IH (Some TSemi)).
    rewrite !opt_cons_app, !opt_app_app.
    simpl. rewrite <- ?List.app_assoc. reflexivity.
Qed.

(** The program prefix, rendered and lexed once and for all. *)
Definition prefix_str : string :=
  "package main" ++ nl_s ++ nl_s ++ "func main() {" ++ nl_s.

Lemma render_prog_dec : forall REST,
  render_tokens 0
    (([KwPackage; TIdent "main"; TSemi; KwFunc; TIdent "main"; TLParen; TRParen; TLBrace]
        ++ REST)%list)
  = prefix_str ++ (indent_for 1 REST ++ render_tokens 1 REST).
Proof.
  intro REST. cbn [List.app render_tokens token_text Nat.eqb].
  unfold prefix_str. rewrite ?str_app_assoc. reflexivity.
Qed.

Lemma lex_prefix : forall X,
  lex_steps MStart None (prefix_str ++ X)
  = opt_app [KwPackage; TIdent "main"; TSemi; KwFunc; TIdent "main"; TLParen; TRParen; TLBrace]
            (lex_steps MStart (Some TLBrace) X).
Proof.
  intro X. unfold prefix_str. rewrite ?str_app_assoc. simpl.
  destruct (lex_steps MStart (Some TLBrace) X); reflexivity.
Qed.

(** THE INVERSE: lexing the rendered program recovers exactly the canonical stream. *)
Theorem render_lex_inverse : forall p, lex (render_program p) = Some (program_tokens p).
Proof.
  intros [body]. unfold render_program, program_tokens, lex. cbn [tp_body].
  rewrite render_prog_dec.
  assert (Hk : exists k,
    indent_for 1 ((concat (map stmt_tokens body) ++ [TRBrace; TSemi])%list) = tabs k).
  { destruct ((concat (map stmt_tokens body) ++ [TRBrace; TSemi])%list) as [ | [] ? ];
      eexists; reflexivity. }
  destruct Hk as [k Hk]. rewrite Hk.
  rewrite lex_prefix.
  rewrite lex_tabs.
  rewrite (lex_body body (Some TLBrace)).
  simpl. rewrite <- ?List.app_assoc. reflexivity.
Qed.
