(** ============================================================================
    GoIdent — a VALIDATED Go identifier: a nonempty ASCII identifier that is not one of
    Go's 25 reserved words.  The validity is IN THE TYPE (a [sig]), so a keyword-as-name
    or an empty/ill-formed name is unrepresentable — the target AST and the token layer
    both carry [GoIdent], never a raw [string].  [true]/[false]/[println]/[main] are
    ordinary identifiers here, exactly as Go's lexer classifies them (only [package] and
    [func] are keywords in this subset; the full keyword set is rejected for completeness).
    Unicode-letter identifiers are an explicit unsupported frontier (unrepresentable).
    ============================================================================ *)
From Stdlib Require Import String Ascii Bool List Eqdep_dec.
Import ListNotations.
Open Scope string_scope.

Definition go_keyword (s : string) : bool :=
  existsb (String.eqb s)
    ["break"; "case"; "chan"; "const"; "continue"; "default"; "defer"; "else";
     "fallthrough"; "for"; "func"; "go"; "goto"; "if"; "import"; "interface";
     "map"; "package"; "range"; "return"; "select"; "struct"; "switch"; "type"; "var"].

Definition ident_start_ok (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((Nat.leb 65 n) && (Nat.leb n 90)) || ((Nat.leb 97 n) && (Nat.leb n 122)) || (Nat.eqb n 95).
Definition ident_char_ok (c : ascii) : bool :=
  ident_start_ok c || ((Nat.leb 48 (nat_of_ascii c)) && (Nat.leb (nat_of_ascii c) 57)).
Fixpoint ident_chars_ok (s : string) : bool :=
  match s with EmptyString => true | String c s' => ident_char_ok c && ident_chars_ok s' end.

Definition go_ident_ok (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c _ => ident_start_ok c && ident_chars_ok s && negb (go_keyword s)
  end.

Definition GoIdent : Type := { s : string | go_ident_ok s = true }.
Definition mkGoIdent (s : string) (H : go_ident_ok s = true) : GoIdent := exist _ s H.
Definition ident_str (i : GoIdent) : string := proj1_sig i.

(** Sig-equality of identifiers reduces to payload equality (the evidence is unique). *)
Lemma goident_payload_eq : forall (i j : GoIdent), ident_str i = ident_str j -> i = j.
Proof.
  intros [a Ha] [b Hb] E. cbn in E. subst b. f_equal.
  apply UIP_dec. apply Bool.bool_dec.
Qed.

(** A validated identifier's characters, unpacked — used by the lexer-faithfulness proofs. *)
Lemma goident_facts : forall (i : GoIdent),
  exists c w', ident_str i = String c w'
    /\ ident_start_ok c = true
    /\ ident_chars_ok (String c w') = true
    /\ go_keyword (String c w') = false.
Proof.
  intros [w Hw]. destruct w as [ | c w' ]; [ discriminate Hw | ].
  exists c, w'. cbn [ident_str proj1_sig].
  cbn [go_ident_ok] in Hw.
  apply andb_true_iff in Hw as [Hw1 Hkw].
  apply andb_true_iff in Hw1 as [Hstart Hchars].
  repeat split; try assumption. apply negb_true_iff in Hkw. exact Hkw.
Qed.
