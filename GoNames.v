(** GoNames — the intrinsic SOURCE-NAME foundation.

    This module owns SOURCE identity only: a bounded, proof-carrying Go identifier domain
    ([IdentifierSyntax]) and the CLOSED lexical class of the sixteen supported conversion type names
    ([TypeName]).  It knows NO semantic type — there is no [GoType], no width/signedness, no representability
    bound, no conversion or defaulting rule, and no renderer semantic tag here.  Name-to-semantic-type binding
    is COMPILER work and lives in [GoCompile]; this module supplies only the source spelling and its identity.

    [IdentifierSyntax] is a bounded ASCII subset — a first character that is an ASCII letter or underscore, then
    ASCII letters/digits/underscores, with every pinned Go keyword excluded — carried WITH its well-formedness
    proof, so no unchecked [string] can inhabit it and non-ASCII Go identifiers are honestly UNREPRESENTABLE.

    The sixteen type names are the ONE source-spelling authority: a single descriptor [TypeName] with its
    spelling [tn_spelling] and the proved inverse [classify]; construction, classification, equality, rendering,
    and every proof derive from it — there is no repeated sixteen-string table.  Only the sixteen approved names
    are representable ([TypeName] has exactly sixteen constructors), and [byte]/[uint8] and [rune]/[int32] are
    DISTINCT source symbols by construction even though a later compiler stage resolves them to equal semantics. *)
From Stdlib Require Import String Ascii List Bool Eqdep_dec Arith Lia.
Import ListNotations.
Local Open Scope string_scope.

(** ---- character classes for Go source identifiers (ASCII only) ---- *)

Definition is_alpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (Nat.leb 65 n && Nat.leb n 90) || (Nat.leb 97 n && Nat.leb n 122).                       (* A..Z a..z *)
Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in Nat.leb 48 n && Nat.leb n 57.                                  (* 0..9 *)
Definition is_underscore (c : ascii) : bool := Ascii.eqb c "_"%char.

Definition ident_start (c : ascii) : bool := is_alpha c || is_underscore c.
Definition ident_cont  (c : ascii) : bool := is_alpha c || is_digit c || is_underscore c.

Fixpoint ident_rest_ok (s : string) : bool :=
  match s with EmptyString => true | String c s' => ident_cont c && ident_rest_ok s' end.

(** an identifier SHAPE: nonempty, a start char, then continuation chars. *)
Definition ident_shape_ok (s : string) : bool :=
  match s with EmptyString => false | String c s' => ident_start c && ident_rest_ok s' end.

(** the pinned Go keywords (Go spec) — none may inhabit [IdentifierSyntax]. *)
Definition go_keywords : list string :=
  [ "break"; "case"; "chan"; "const"; "continue"; "default"; "defer"; "else"; "fallthrough";
    "for"; "func"; "go"; "goto"; "if"; "import"; "interface"; "map"; "package"; "range";
    "return"; "select"; "struct"; "switch"; "type"; "var" ].
Definition is_keyword (s : string) : bool := existsb (String.eqb s) go_keywords.

Definition identifier_ok (s : string) : bool := ident_shape_ok s && negb (is_keyword s).

(** a source identifier carries its own validity proof (bool UIP -> proof-irrelevant), so equality reduces to
    the underlying string and no unchecked string can construct one. *)
Record IdentifierSyntax : Type := mkIdent { id_str : string ; id_ok : identifier_ok id_str = true }.

Lemma identifier_ok_irrel : forall s (p q : identifier_ok s = true), p = q.
Proof. intros; apply (UIP_dec Bool.bool_dec). Qed.

Lemma ident_eq : forall a b, id_str a = id_str b -> a = b.
Proof. intros [sa pa] [sb pb] H; cbn in H; subst sb; f_equal; apply identifier_ok_irrel. Qed.

Definition id_eqb (a b : IdentifierSyntax) : bool := String.eqb (id_str a) (id_str b).
Lemma id_eqb_eq : forall a b, id_eqb a b = true <-> a = b.
Proof.
  intros a b; unfold id_eqb; split.
  - intro H; apply String.eqb_eq in H; apply ident_eq; exact H.
  - intro H; subst b; apply String.eqb_refl.
Qed.

(** rendering an identifier is EXACTLY its stored source text. *)
Definition render_identifier (i : IdentifierSyntax) : string := id_str i.

(** ---- every valid identifier char, hence every rendered identifier, is ASCII ---- *)

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

Lemma ident_start_ascii : forall c, ident_start c = true -> is_ascii_c c = true.
Proof.
  intros c H. unfold ident_start in H. apply Bool.orb_true_iff in H.
  destruct H as [H|H]; [ apply alpha_ascii | apply underscore_ascii ]; exact H.
Qed.
Lemma ident_cont_ascii : forall c, ident_cont c = true -> is_ascii_c c = true.
Proof.
  intros c H. unfold ident_cont in H. apply Bool.orb_true_iff in H. destruct H as [H|H].
  - apply Bool.orb_true_iff in H; destruct H as [H|H]; [ apply alpha_ascii | apply digit_ascii ]; exact H.
  - apply underscore_ascii; exact H.
Qed.

Lemma ident_rest_ascii : forall s, ident_rest_ok s = true -> str_ascii s = true.
Proof.
  induction s as [|c s IH]; intro H; [ reflexivity |].
  cbn in H. apply Bool.andb_true_iff in H; destruct H as [Hc Hr].
  cbn [str_ascii]. rewrite (ident_cont_ascii c Hc), (IH Hr). reflexivity.
Qed.

(** every rendered identifier is ASCII. *)
Lemma identifier_ascii : forall i, str_ascii (render_identifier i) = true.
Proof.
  intros [s Hs]. unfold render_identifier; cbn.
  unfold identifier_ok in Hs. apply Bool.andb_true_iff in Hs; destruct Hs as [Hshape _].
  destruct s as [|c s']; [ discriminate |].
  cbn in Hshape. apply Bool.andb_true_iff in Hshape; destruct Hshape as [Hst Hr].
  cbn [str_ascii]. rewrite (ident_start_ascii c Hst), (ident_rest_ascii s' Hr). reflexivity.
Qed.

(** ---- the CLOSED lexical class of the sixteen supported conversion type names ---- *)

Inductive TypeName : Type :=
  | TNint | TNint8 | TNint16 | TNint32 | TNint64
  | TNuint | TNuint8 | TNuint16 | TNuint32 | TNuint64
  | TNfloat32 | TNfloat64
  | TNcomplex64 | TNcomplex128
  | TNbyte | TNrune.

(** the ONE source-spelling authority. *)
Definition tn_spelling (t : TypeName) : string :=
  match t with
  | TNint => "int" | TNint8 => "int8" | TNint16 => "int16" | TNint32 => "int32" | TNint64 => "int64"
  | TNuint => "uint" | TNuint8 => "uint8" | TNuint16 => "uint16" | TNuint32 => "uint32" | TNuint64 => "uint64"
  | TNfloat32 => "float32" | TNfloat64 => "float64"
  | TNcomplex64 => "complex64" | TNcomplex128 => "complex128"
  | TNbyte => "byte" | TNrune => "rune"
  end.

Definition tn_eq_dec : forall a b : TypeName, {a = b} + {a <> b}.
Proof. decide equality. Defined.
Definition tn_eqb (a b : TypeName) : bool := if tn_eq_dec a b then true else false.
Lemma tn_eqb_eq : forall a b, tn_eqb a b = true <-> a = b.
Proof. intros a b; unfold tn_eqb; destruct (tn_eq_dec a b); split; congruence. Qed.

(** every spelling is a valid identifier, so a type name RETAINS an [IdentifierSyntax]. *)
Lemma tn_spelling_ok : forall t, identifier_ok (tn_spelling t) = true.
Proof. intro t; destruct t; reflexivity. Qed.
Definition tn_identifier (t : TypeName) : IdentifierSyntax := mkIdent (tn_spelling t) (tn_spelling_ok t).

(** rendering a type name is its source spelling — equivalently its retained identifier's text. *)
Definition render_type_name (t : TypeName) : string := tn_spelling t.
Lemma render_type_name_identifier : forall t, render_type_name t = render_identifier (tn_identifier t).
Proof. intro t; reflexivity. Qed.
Lemma render_type_name_ascii : forall t, str_ascii (render_type_name t) = true.
Proof. intro t; destruct t; reflexivity. Qed.

(** the closed enumeration and the proved inverse [classify]: spelling and classification are inverse, so the
    descriptor is one authority (a name round-trips through its spelling). *)
Definition all_type_names : list TypeName :=
  [ TNint; TNint8; TNint16; TNint32; TNint64; TNuint; TNuint8; TNuint16; TNuint32; TNuint64;
    TNfloat32; TNfloat64; TNcomplex64; TNcomplex128; TNbyte; TNrune ].
Lemma all_type_names_complete : forall t, In t all_type_names.
Proof. intro t; destruct t; cbn; tauto. Qed.

Definition classify (s : string) : option TypeName :=
  find (fun t => String.eqb s (tn_spelling t)) all_type_names.

Lemma tn_spelling_inj : forall a b, tn_spelling a = tn_spelling b -> a = b.
Proof. intros a b H; destruct a; destruct b; cbn in H; solve [ reflexivity | discriminate H ]. Qed.

Lemma classify_spelling : forall t, classify (tn_spelling t) = Some t.
Proof. intro t; destruct t; reflexivity. Qed.

Lemma classify_sound : forall s t, classify s = Some t -> s = tn_spelling t.
Proof.
  intros s t H. unfold classify in H. apply find_some in H. destruct H as [_ Hb].
  apply String.eqb_eq in Hb. exact Hb.
Qed.

(** alias source-distinctness: [byte]/[uint8] and [rune]/[int32] are DISTINCT source symbols and render to
    DISTINCT spellings (their equal semantic resolution is a separate compiler fact, proved in [GoCompile]). *)
Lemma tn_byte_neq_uint8 : TNbyte <> TNuint8.        Proof. discriminate. Qed.
Lemma render_byte_neq_uint8 : render_type_name TNbyte <> render_type_name TNuint8.
Proof. discriminate. Qed.
Lemma tn_rune_neq_int32 : TNrune <> TNint32.        Proof. discriminate. Qed.
Lemma render_rune_neq_int32 : render_type_name TNrune <> render_type_name TNint32.
Proof. discriminate. Qed.

(** ---- the raw type-name VALUE: a retained source identifier + its classified lexical symbol ---- *)

(** the raw conversion-target value RETAINS a source [IdentifierSyntax] together with the closed lexical
    [TypeName] it classifies to and a proof they match.  So the raw AST carries a valid bounded SOURCE
    identifier (not a bare enum): the renderer reads [stn_identifier], the compiler binds via [stn_symbol], and
    [classify] constrains the symbol so ONLY the sixteen names inhabit this type — no arbitrary-string bypass,
    and no semantic ([GoType]/[IntegerType]/…) tag lives here. *)
Record SupportedTypeName : Type := mkSTN {
  stn_identifier : IdentifierSyntax ;
  stn_symbol     : TypeName ;
  stn_exact      : classify (render_identifier stn_identifier) = Some stn_symbol
}.

Lemma classify_tn_identifier : forall t, classify (render_identifier (tn_identifier t)) = Some t.
Proof. intro t. apply classify_spelling. Qed.

(** the smart constructor: derive the retained identifier from the ONE spelling authority. *)
Definition stn_of (t : TypeName) : SupportedTypeName := mkSTN (tn_identifier t) t (classify_tn_identifier t).
Lemma stn_of_symbol : forall t, stn_symbol (stn_of t) = t.
Proof. intro t; reflexivity. Qed.

(** the retained identifier's text IS the symbol's spelling (the one source-spelling authority). *)
Lemma stn_render : forall s, render_identifier (stn_identifier s) = tn_spelling (stn_symbol s).
Proof. intros [id sym Hx]; cbn in *; apply classify_sound in Hx; exact Hx. Qed.
Definition render_stn (s : SupportedTypeName) : string := render_identifier (stn_identifier s).
Lemma render_stn_of : forall t, render_stn (stn_of t) = tn_spelling t.
Proof. intro t; reflexivity. Qed.
Lemma render_stn_ascii : forall s, str_ascii (render_stn s) = true.
Proof. intro s; apply identifier_ascii. Qed.

(** only the sixteen names inhabit [SupportedTypeName]; the symbol is determined by the identifier. *)
Lemma stn_symbol_in : forall s, In (stn_symbol s) all_type_names.
Proof. intro s; apply all_type_names_complete. Qed.

Definition option_tn_eq_dec (x y : option TypeName) : {x = y} + {x <> y}.
Proof. decide equality. apply tn_eq_dec. Defined.

Lemma stn_eq : forall a b, stn_identifier a = stn_identifier b -> a = b.
Proof.
  intros [ida syma Hxa] [idb symb Hxb] H; cbn in *; subst idb.
  assert (syma = symb) as -> by (rewrite Hxa in Hxb; injection Hxb as ->; reflexivity).
  f_equal. apply (UIP_dec option_tn_eq_dec).
Qed.
Definition stn_eqb (a b : SupportedTypeName) : bool := id_eqb (stn_identifier a) (stn_identifier b).
Lemma stn_eqb_eq : forall a b, stn_eqb a b = true <-> a = b.
Proof.
  intros a b; unfold stn_eqb; split.
  - intro H; apply id_eqb_eq in H; apply stn_eq; exact H.
  - intro H; subst b; apply String.eqb_refl.
Qed.

(** alias source-distinctness at the raw-value level: [byte]/[uint8] and [rune]/[int32] are distinct raw
    supported names and render to distinct text. *)
Lemma stn_byte_neq_uint8 : stn_of TNbyte <> stn_of TNuint8.
Proof. intro H; assert (Hs := f_equal stn_symbol H); cbn in Hs; discriminate Hs. Qed.
Lemma render_stn_byte_neq_uint8 : render_stn (stn_of TNbyte) <> render_stn (stn_of TNuint8).
Proof. discriminate. Qed.
Lemma stn_rune_neq_int32 : stn_of TNrune <> stn_of TNint32.
Proof. intro H; assert (Hs := f_equal stn_symbol H); cbn in Hs; discriminate Hs. Qed.
Lemma render_stn_rune_neq_int32 : render_stn (stn_of TNrune) <> render_stn (stn_of TNint32).
Proof. discriminate. Qed.

(** an ordinary identifier that is not one of the sixteen names is a valid [IdentifierSyntax] but NOT a type
    name; a keyword is not even a valid identifier — so the type-name class cannot be bypassed by a raw string. *)
Example ident_foo_ok : identifier_ok "foo" = true.                Proof. reflexivity. Qed.
Example classify_foo_none : classify "foo" = None.                Proof. reflexivity. Qed.
Example keyword_type_not_ident : identifier_ok "type" = false.    Proof. reflexivity. Qed.
Example classify_qualified_none : classify "pkg.T" = None.        Proof. reflexivity. Qed.
