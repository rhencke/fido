(** ============================================================================
    GoRender — the DIRECT pretty-printer: it traverses a decorated [CompiledFile] and
    emits Go source bytes.  There is NO tokenizer, token encoder, lexer, parser, text IR,
    or AST→text→AST round trip — the renderer is a direct [CompiledFile -> string] function,
    and its correctness (next module tick) is STRUCTURAL over the intrinsically-grammatical
    compiled tree, never "a parser recovers the same AST" (doc §4; PAINFUL_LESSONS #3).

    It renders the RESOLVED tree: a [CBool] prints its predeclared spelling, the callee is
    the literal builtin [println], and package/function are the pinned "main" constants —
    the renderer never resolves names, infers types, validates, or repairs (GoCompile did
    all of that).  Its only decisions are serialization inherent to Go syntax: legal literal
    spelling/escaping, canonical spacing/newlines, deterministic layout.  There are no binary
    operators in this fragment, so no precedence or parenthesis decision arises and there is
    no parenthesis node.

    Lexical fusion is prevented by direct canonical spacing (a space after [package]/[func],
    a comma-space between arguments) — not a token framework.  Decimal digits come from the
    one authority ([digits.print_Z]); a [CInt]/[CNeg] magnitude is [N], rendered via [Z.of_N]
    (nonnegative, so no sign — [CNeg]'s sign is the explicit leading [-]).
    ============================================================================ *)
From Stdlib Require Import String Ascii NArith ZArith List Bool Lia.
From Fido Require Import digits Literals GoAST GoCompile.
Import ListNotations.
Open Scope string_scope.

Definition nl_c : ascii := ascii_of_nat 10.
Definition tab_c : ascii := ascii_of_nat 9.
Definition quote_c : ascii := ascii_of_nat 34.
Definition bslash_c : ascii := ascii_of_nat 92.
Definition nl : string := String nl_c EmptyString.
Definition tab : string := String tab_c EmptyString.
Definition quote : string := String quote_c EmptyString.
Definition bslash : string := String bslash_c EmptyString.

(** Source escaping of a string payload — exactly the four escapes the admitted charset
    (printable ASCII + tab + newline) can require; every other admitted char is verbatim. *)
Definition escape_char (c : ascii) : string :=
  if Ascii.eqb c quote_c then bslash ++ quote
  else if Ascii.eqb c bslash_c then bslash ++ bslash
  else if Ascii.eqb c nl_c then bslash ++ "n"
  else if Ascii.eqb c tab_c then bslash ++ "t"
  else String c EmptyString.

Fixpoint escape_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => escape_char c ++ escape_string s'
  end.

(** ---- The renderer over the decorated tree ---- *)

Definition render_cexpr (c : CompiledExpr) : string :=
  match c with
  | CBool true  => "true"
  | CBool false => "false"
  | CInt n _ => print_Z (Z.of_N n)
  | CNeg n _ => "-" ++ print_Z (Z.of_N n)
  | CStr s _ => quote ++ escape_string s ++ quote
  end.

Fixpoint render_cargs (cs : list CompiledExpr) : string :=
  match cs with
  | []        => ""
  | [c]       => render_cexpr c
  | c :: cs'  => render_cexpr c ++ ", " ++ render_cargs cs'
  end.

Definition render_cstmt (s : CompiledStmt) : string :=
  match s with
  | CPrintln args => tab ++ "println(" ++ render_cargs args ++ ")" ++ nl
  end.

Fixpoint render_cstmts (ss : list CompiledStmt) : string :=
  match ss with
  | []       => ""
  | s :: ss' => render_cstmt s ++ render_cstmts ss'
  end.

(** Package and function are the pinned "main" constants (a [CompiledFile] cannot be
    otherwise), so they are emitted literally. *)
Definition render_cfile (c : CompiledFile) : string :=
  "package main" ++ nl ++ nl
  ++ "func main() {" ++ nl
  ++ render_cstmts (cf_body c)
  ++ "}" ++ nl.

(** ============================================================================
    Renderer-correctness proofs — STRUCTURAL over the intrinsically-grammatical compiled
    tree, never by parsing the output (doc §4).  Two obligations are discharged here:

      (1) FAITHFUL ESCAPING — the source string literal the renderer emits denotes exactly
          the modelled string value.  [go_unescape] is the semantics of Go's string escapes
          (a small faithful spec of the four backslash escapes, NOT a Go-grammar parser), and
          [escape_faithful] proves it inverts [escape_string] for every payload.  So no
          string value is corrupted or aliased by rendering.

      (2) ALL-ASCII OUTPUT — every byte the renderer emits is < 128 ([render_all_ascii]),
          using the intrinsic [str_ok] evidence on [CStr] and the [< 10] digit bound from
          [digits].  Go source in this fragment is pure ASCII, so this is the concrete
          "legal spelling" guarantee: nothing non-ASCII (which could break source UTF-8) is
          ever emitted.

    Not yet proved (honest scope): a full Go-subset grammar-membership and static-meaning
    preservation.  Precedence/parenthesisation is N/A (no binary operators in the fragment);
    exact-byte adequacy against the real toolchain is the e2e's job, not a theorem here. *)

Definition n_c : ascii := ascii_of_nat 110.   (* 'n' *)
Definition t_c : ascii := ascii_of_nat 116.   (* 't' *)

(** The meaning of a Go-escaped string: undo exactly the four escapes [escape_char] emits. *)
Fixpoint go_unescape (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
      if Ascii.eqb c bslash_c then
        match s' with
        | String d s'' =>
            if Ascii.eqb d quote_c then String quote_c (go_unescape s'')
            else if Ascii.eqb d bslash_c then String bslash_c (go_unescape s'')
            else if Ascii.eqb d n_c then String nl_c (go_unescape s'')
            else if Ascii.eqb d t_c then String tab_c (go_unescape s'')
            else String c (go_unescape s')
        | EmptyString => String c EmptyString
        end
      else String c (go_unescape s')
  end.

(** Each escaped character round-trips, prepended to any already-faithful suffix. *)
Lemma escape_char_unescape : forall c rest,
  go_unescape (escape_char c ++ rest) = String c (go_unescape rest).
Proof.
  intros c rest. unfold escape_char.
  destruct (Ascii.eqb c quote_c) eqn:Eq.
  { apply Ascii.eqb_eq in Eq. subst c. reflexivity. }
  destruct (Ascii.eqb c bslash_c) eqn:Eb.
  { apply Ascii.eqb_eq in Eb. subst c. reflexivity. }
  destruct (Ascii.eqb c nl_c) eqn:En.
  { apply Ascii.eqb_eq in En. subst c. reflexivity. }
  destruct (Ascii.eqb c tab_c) eqn:Et.
  { apply Ascii.eqb_eq in Et. subst c. reflexivity. }
  simpl. rewrite Eb. reflexivity.
Qed.

Theorem escape_faithful : forall s, go_unescape (escape_string s) = s.
Proof.
  induction s as [ | c s' IH ]; simpl.
  - reflexivity.
  - rewrite escape_char_unescape, IH. reflexivity.
Qed.

(** ---- all-ASCII output ---- *)

Definition is_ascii (c : ascii) : bool := Nat.ltb (nat_of_ascii c) 128.

Fixpoint str_ascii (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => is_ascii c && str_ascii s'
  end.

Lemma str_ascii_app : forall a b, str_ascii (a ++ b) = str_ascii a && str_ascii b.
Proof.
  induction a as [ | c a' IH ]; intro b; simpl.
  - reflexivity.
  - rewrite IH, andb_assoc. reflexivity.
Qed.

Lemma str_char_ok_ascii : forall c, str_char_ok c = true -> is_ascii c = true.
Proof.
  intros c H. unfold is_ascii. apply Nat.ltb_lt.
  unfold str_char_ok in H. cbv zeta in H.
  apply orb_true_iff in H as [H|H]; [ apply orb_true_iff in H as [H|H] | ].
  - apply Nat.eqb_eq in H. lia.
  - apply Nat.eqb_eq in H. lia.
  - apply andb_true_iff in H as [_ H]. apply Nat.leb_le in H. lia.
Qed.

Lemma dec_digit_ascii : forall d, (d < 10)%nat -> is_ascii (dec_digit d) = true.
Proof.
  intros d Hd. do 10 (destruct d as [ | d ]; [ reflexivity | ]). lia.
Qed.

(** One fold step, definitionally — kept folded so [dec_digit a] is NEVER forced (evaluating
    [is_ascii (dec_digit a)] on a symbolic digit churns [nat_of_ascii ∘ ascii_of_nat]). *)
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
  pose proof (pos_digits_bound 10 p ltac:(lia)) as Hb.
  rewrite Forall_forall in Hb. apply Hb; exact Hd.
Qed.

Lemma print_Z_ascii : forall z, str_ascii (print_Z z) = true.
Proof.
  intros [ | p | p ].
  - reflexivity.
  - apply print_Z_pos_ascii.
  - cbn [print_Z]. rewrite str_ascii_app, print_Z_pos_ascii. reflexivity.
Qed.


Lemma escape_char_ascii : forall c, str_char_ok c = true -> str_ascii (escape_char c) = true.
Proof.
  intros c H. unfold escape_char.
  destruct (Ascii.eqb c quote_c) eqn:Eq. { reflexivity. }
  destruct (Ascii.eqb c bslash_c) eqn:Eb. { reflexivity. }
  destruct (Ascii.eqb c nl_c) eqn:En. { reflexivity. }
  destruct (Ascii.eqb c tab_c) eqn:Et. { reflexivity. }
  simpl. rewrite (str_char_ok_ascii c H). reflexivity.
Qed.

Lemma escape_string_ascii : forall s, str_ok s = true -> str_ascii (escape_string s) = true.
Proof.
  induction s as [ | c s' IH ]; intro H; [ reflexivity | ].
  cbn [str_ok] in H. apply andb_true_iff in H as [Hc Hs].
  cbn [escape_string]. rewrite str_ascii_app, (escape_char_ascii c Hc). simpl.
  apply IH; exact Hs.
Qed.

Lemma render_cexpr_ascii : forall c, str_ascii (render_cexpr c) = true.
Proof.
  intros [ [] | n Hn | n Hn | s Hs ]; cbn [render_cexpr].
  - reflexivity.
  - reflexivity.
  - apply print_Z_ascii.
  - rewrite str_ascii_app, print_Z_ascii. reflexivity.
  - rewrite !str_ascii_app, (escape_string_ascii s Hs). reflexivity.
Qed.

Lemma render_cargs_ascii : forall cs, str_ascii (render_cargs cs) = true.
Proof.
  induction cs as [ | c cs' IH ].
  - reflexivity.
  - destruct cs' as [ | c2 cs'' ].
    + apply render_cexpr_ascii.
    + change (render_cargs (c :: c2 :: cs''))
        with (render_cexpr c ++ ", " ++ render_cargs (c2 :: cs'')).
      rewrite !str_ascii_app, render_cexpr_ascii. simpl. exact IH.
Qed.

Lemma render_cstmt_ascii : forall s, str_ascii (render_cstmt s) = true.
Proof.
  intros [ args ]. cbn [render_cstmt].
  rewrite !str_ascii_app, render_cargs_ascii. reflexivity.
Qed.

Lemma render_cstmts_ascii : forall ss, str_ascii (render_cstmts ss) = true.
Proof.
  induction ss as [ | s ss' IH ]; [ reflexivity | ].
  cbn [render_cstmts]. rewrite str_ascii_app, render_cstmt_ascii, IH. reflexivity.
Qed.

Theorem render_all_ascii : forall c, str_ascii (render_cfile c) = true.
Proof.
  intro c. unfold render_cfile. rewrite !str_ascii_app, render_cstmts_ascii. reflexivity.
Qed.
