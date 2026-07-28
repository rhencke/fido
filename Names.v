From Stdlib Require Import String Ascii List Bool Eqdep_dec Arith Lia.
Import ListNotations.
Local Open Scope string_scope.


Definition is_alpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (Nat.leb 65 n && Nat.leb n 90) || (Nat.leb 97 n && Nat.leb n 122).                       (* A..Z a..z *)
Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in Nat.leb 48 n && Nat.leb n 57.                                  (* 0..9 *)
Definition is_underscore (c : ascii) : bool := Ascii.eqb c "_"%char.

Definition identifier_start (c : ascii) : bool := is_alpha c || is_underscore c.
Definition identifier_cont  (c : ascii) : bool := is_alpha c || is_digit c || is_underscore c.

Fixpoint identifier_rest_ok (s : string) : bool :=
  match s with EmptyString => true | String c s' => identifier_cont c && identifier_rest_ok s' end.

Definition identifier_shape_ok (s : string) : bool :=
  match s with EmptyString => false | String c s' => identifier_start c && identifier_rest_ok s' end.

(* the pinned Go keywords (Go spec) — none may inhabit [Identifier]. *)
Definition go_keywords : list string :=
  [ "break"; "case"; "chan"; "const"; "continue"; "default"; "defer"; "else"; "fallthrough";
    "for"; "func"; "go"; "goto"; "if"; "import"; "interface"; "map"; "package"; "range";
    "return"; "select"; "struct"; "switch"; "type"; "var" ].
Definition is_keyword (s : string) : bool := existsb (String.eqb s) go_keywords.

Definition identifier_ok (s : string) : bool := identifier_shape_ok s && negb (is_keyword s).

(* A source identifier carries its own validity proof, so no unchecked string can construct one. *)
Record Identifier : Type := MakeIdentifier { spelling : string ; valid : identifier_ok spelling = true }.

Lemma identifier_ok_irrel : forall s (p q : identifier_ok s = true), p = q.
Proof. intros; apply (UIP_dec Bool.bool_dec). Qed.

Lemma identifier_equal : forall a b, spelling a = spelling b -> a = b.
Proof. intros [sa pa] [sb pb] H; cbn in H; subst sb; f_equal; apply identifier_ok_irrel. Qed.

Definition equalb (a b : Identifier) : bool := String.eqb (spelling a) (spelling b).
Lemma equalb_spec : forall a b, equalb a b = true <-> a = b.
Proof.
  intros a b; unfold equalb; split.
  - intro H; apply String.eqb_eq in H; apply identifier_equal; exact H.
  - intro H; subst b; apply String.eqb_refl.
Qed.

Definition render_identifier (i : Identifier) : string := spelling i.


Definition is_ascii_c (c : ascii) : bool := Nat.ltb (nat_of_ascii c) 128.
Fixpoint str_ascii (s : string) : bool :=
  match s with EmptyString => true | String c s' => is_ascii_c c && str_ascii s' end.

Lemma alpha_ascii : forall c, is_alpha c = true -> is_ascii_c c = true.
Proof.
  intros c H. unfold is_alpha in H. unfold is_ascii_c. apply Nat.ltb_lt.
  apply Bool.orb_true_iff in H. destruct H as [H|H];
    apply Bool.andb_true_iff in H; destruct H as [_ H2]; apply Nat.leb_le in H2; lia.
Qed.
Lemma digit_ascii : forall c, is_digit c = true -> is_ascii_c c = true.
Proof.
  intros c H. unfold is_digit in H. unfold is_ascii_c. apply Nat.ltb_lt.
  apply Bool.andb_true_iff in H; destruct H as [_ H2]; apply Nat.leb_le in H2; lia.
Qed.
Lemma underscore_ascii : forall c, is_underscore c = true -> is_ascii_c c = true.
Proof. intros c H. apply Ascii.eqb_eq in H. subst c. reflexivity. Qed.

Lemma identifier_start_ascii : forall c, identifier_start c = true -> is_ascii_c c = true.
Proof.
  intros c H. unfold identifier_start in H. apply Bool.orb_true_iff in H.
  destruct H as [H|H]; [ apply alpha_ascii | apply underscore_ascii ]; exact H.
Qed.
Lemma identifier_cont_ascii : forall c, identifier_cont c = true -> is_ascii_c c = true.
Proof.
  intros c H. unfold identifier_cont in H. apply Bool.orb_true_iff in H. destruct H as [H|H].
  - apply Bool.orb_true_iff in H; destruct H as [H|H]; [ apply alpha_ascii | apply digit_ascii ]; exact H.
  - apply underscore_ascii; exact H.
Qed.

Lemma identifier_rest_ascii : forall s, identifier_rest_ok s = true -> str_ascii s = true.
Proof.
  induction s as [|c s IH]; intro H; [ reflexivity |].
  cbn in H. apply Bool.andb_true_iff in H; destruct H as [Hc Hr].
  cbn [str_ascii]. rewrite (identifier_cont_ascii c Hc), (IH Hr). reflexivity.
Qed.

Lemma identifier_ascii : forall i, str_ascii (render_identifier i) = true.
Proof.
  intros [s Hs]. unfold render_identifier; cbn.
  unfold identifier_ok in Hs. apply Bool.andb_true_iff in Hs; destruct Hs as [Hshape _].
  destruct s as [|c s']; [ discriminate |].
  cbn in Hshape. apply Bool.andb_true_iff in Hshape; destruct Hshape as [Hst Hr].
  cbn [str_ascii]. rewrite (identifier_start_ascii c Hst), (identifier_rest_ascii s' Hr). reflexivity.
Qed.

(* The closed lexical class of the sixteen supported conversion type names. *)

Inductive TypeName : Type :=
  | Int | Int8 | Int16 | Int32 | Int64
  | Uint | Uint8 | Uint16 | Uint32 | Uint64
  | Float32 | Float64
  | Complex64 | Complex128
  | Byte | Rune.

Definition type_name_spelling (t : TypeName) : string :=
  match t with
  | Int => "int" | Int8 => "int8" | Int16 => "int16" | Int32 => "int32" | Int64 => "int64"
  | Uint => "uint" | Uint8 => "uint8" | Uint16 => "uint16" | Uint32 => "uint32" | Uint64 => "uint64"
  | Float32 => "float32" | Float64 => "float64"
  | Complex64 => "complex64" | Complex128 => "complex128"
  | Byte => "byte" | Rune => "rune"
  end.

Definition type_name_eq_dec : forall a b : TypeName, {a = b} + {a <> b}.
Proof. decide equality. Defined.
Definition type_name_equalb (a b : TypeName) : bool := if type_name_eq_dec a b then true else false.
Lemma type_name_equalb_spec : forall a b, type_name_equalb a b = true <-> a = b.
Proof. intros a b; unfold type_name_equalb; destruct (type_name_eq_dec a b); split; congruence. Qed.

Lemma type_name_spelling_ok : forall t, identifier_ok (type_name_spelling t) = true.
Proof. intro t; destruct t; reflexivity. Qed.
Definition type_name_identifier (t : TypeName) : Identifier := MakeIdentifier (type_name_spelling t) (type_name_spelling_ok t).

Definition render_type_name (t : TypeName) : string := type_name_spelling t.
Lemma render_type_name_identifier : forall t, render_type_name t = render_identifier (type_name_identifier t).
Proof. intro t; reflexivity. Qed.
Lemma render_type_name_ascii : forall t, str_ascii (render_type_name t) = true.
Proof. intro t; destruct t; reflexivity. Qed.

Definition all_type_names : list TypeName :=
  [ Int; Int8; Int16; Int32; Int64; Uint; Uint8; Uint16; Uint32; Uint64;
    Float32; Float64; Complex64; Complex128; Byte; Rune ].
Lemma all_type_names_complete : forall t, In t all_type_names.
Proof. intro t; destruct t; cbn; tauto. Qed.

Definition classify (s : string) : option TypeName :=
  find (fun t => String.eqb s (type_name_spelling t)) all_type_names.

Lemma type_name_spelling_inj : forall a b, type_name_spelling a = type_name_spelling b -> a = b.
Proof. intros a b H; destruct a; destruct b; cbn in H; solve [ reflexivity | discriminate H ]. Qed.

Lemma classify_spelling : forall t, classify (type_name_spelling t) = Some t.
Proof. intro t; destruct t; reflexivity. Qed.

Lemma classify_sound : forall s t, classify s = Some t -> s = type_name_spelling t.
Proof.
  intros s t H. unfold classify in H. apply find_some in H. destruct H as [_ Hb].
  apply String.eqb_eq in Hb. exact Hb.
Qed.

Lemma type_name_byte_neq_uint8 : Byte <> Uint8.        Proof. discriminate. Qed.
Lemma render_byte_neq_uint8 : render_type_name Byte <> render_type_name Uint8.
Proof. discriminate. Qed.
Lemma type_name_rune_neq_int32 : Rune <> Int32.        Proof. discriminate. Qed.
Lemma render_rune_neq_int32 : render_type_name Rune <> render_type_name Int32.
Proof. discriminate. Qed.

(* A raw conversion target retains its source identifier beside the lexical symbol [classify] maps it to. *)
Record SupportedType : Type := MakeSupportedType {
  identifier : Identifier ;
  symbol     : TypeName ;
  exact      : classify (render_identifier identifier) = Some symbol
}.

Lemma classify_type_name_identifier : forall t, classify (render_identifier (type_name_identifier t)) = Some t.
Proof. intro t. apply classify_spelling. Qed.

(* The smart constructor derives the retained identifier from the one spelling authority. *)
Definition supported_of (t : TypeName) : SupportedType := MakeSupportedType (type_name_identifier t) t (classify_type_name_identifier t).
Lemma supported_of_symbol : forall t, symbol (supported_of t) = t.
Proof. intro t; reflexivity. Qed.

Lemma supported_render : forall s, render_identifier (identifier s) = type_name_spelling (symbol s).
Proof. intros [id sym Hx]; cbn in *; apply classify_sound in Hx; exact Hx. Qed.
Definition render_supported (s : SupportedType) : string := render_identifier (identifier s).
Lemma render_supported_of : forall t, render_supported (supported_of t) = type_name_spelling t.
Proof. intro t; reflexivity. Qed.
Lemma render_supported_ascii : forall s, str_ascii (render_supported s) = true.
Proof. intro s; apply identifier_ascii. Qed.

Lemma symbol_in : forall s, In (symbol s) all_type_names.
Proof. intro s; apply all_type_names_complete. Qed.

Definition option_type_name_eq_dec (x y : option TypeName) : {x = y} + {x <> y}.
Proof. decide equality. apply type_name_eq_dec. Defined.

Lemma supported_equal : forall a b, identifier a = identifier b -> a = b.
Proof.
  intros [ida syma Hxa] [idb symb Hxb] H; cbn in *; subst idb.
  assert (syma = symb) as -> by (rewrite Hxa in Hxb; injection Hxb as ->; reflexivity).
  f_equal. apply (UIP_dec option_type_name_eq_dec).
Qed.
Definition supported_equalb (a b : SupportedType) : bool := equalb (identifier a) (identifier b).
Lemma supported_equalb_spec : forall a b, supported_equalb a b = true <-> a = b.
Proof.
  intros a b; unfold supported_equalb; split.
  - intro H; apply equalb_spec in H; apply supported_equal; exact H.
  - intro H; subst b; apply String.eqb_refl.
Qed.

Lemma supported_byte_neq_uint8 : supported_of Byte <> supported_of Uint8.
Proof. intro H; assert (Hs := f_equal symbol H); cbn in Hs; discriminate Hs. Qed.
Lemma render_supported_byte_neq_uint8 : render_supported (supported_of Byte) <> render_supported (supported_of Uint8).
Proof. discriminate. Qed.
Lemma supported_rune_neq_int32 : supported_of Rune <> supported_of Int32.
Proof. intro H; assert (Hs := f_equal symbol H); cbn in Hs; discriminate Hs. Qed.
Lemma render_supported_rune_neq_int32 : render_supported (supported_of Rune) <> render_supported (supported_of Int32).
Proof. discriminate. Qed.

Example identifier_foo_ok : identifier_ok "foo" = true.                Proof. reflexivity. Qed.
Example classify_foo_none : classify "foo" = None.                Proof. reflexivity. Qed.
Example keyword_type_not_ident : identifier_ok "type" = false.    Proof. reflexivity. Qed.
Example classify_qualified_none : classify "pkg.T" = None.        Proof. reflexivity. Qed.
