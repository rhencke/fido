From Stdlib Require Import String Ascii List Bool Eqdep_dec Arith Lia.
Import ListNotations.
Local Open Scope string_scope.


Definition is_alpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (Nat.leb 65 n && Nat.leb n 90) || (Nat.leb 97 n && Nat.leb n 122).
Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in Nat.leb 48 n && Nat.leb n 57.
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

(* An ordinary identifier is exactly a nonblank one; blank is reserved for a later [Syntax.BindingName]. *)
Definition is_blank (s : string) : bool := String.eqb s "_".

Lemma is_blank_true : forall s, is_blank s = true <-> s = "_".
Proof. intro s; unfold is_blank; apply String.eqb_eq. Qed.
Lemma is_blank_false : forall s, is_blank s = false <-> s <> "_".
Proof.
  intro s; unfold is_blank; split.
  - intros H Heq; subst s; rewrite String.eqb_refl in H; discriminate.
  - intro H; apply Bool.not_true_is_false; intro Ht; apply H; apply String.eqb_eq; exact Ht.
Qed.

(* The ordinary object retains the exact [Identifier]; it never copies the spelling and rebuilds one. *)
Record OrdinaryIdentifier : Type :=
  MakeOrdinary { ordinary_id : Identifier ; ordinary_ok : is_blank (spelling ordinary_id) = false }.

Definition ordinary_spelling (o : OrdinaryIdentifier) : string := spelling (ordinary_id o).
Definition render_ordinary (o : OrdinaryIdentifier) : string := render_identifier (ordinary_id o).

(* One total smart constructor: it succeeds on exactly the nonblank identifiers. *)
Definition ordinary_of (i : Identifier) : option OrdinaryIdentifier :=
  match Bool.bool_dec (is_blank (spelling i)) false with
  | left H => Some (MakeOrdinary i H)
  | right _ => None
  end.

Lemma ordinary_nonblank : forall o : OrdinaryIdentifier, spelling (ordinary_id o) <> "_".
Proof. intros [i H]; cbn; apply is_blank_false; exact H. Qed.

Lemma ordinary_of_some_iff : forall i, (exists o, ordinary_of i = Some o) <-> is_blank (spelling i) = false.
Proof.
  intro i; unfold ordinary_of; destruct (Bool.bool_dec (is_blank (spelling i)) false) as [H|H].
  - split; [ intros _; exact H | intros _; eexists; reflexivity ].
  - split; [ intros [o Ho]; discriminate Ho | intro Hf; exfalso; apply H; exact Hf ].
Qed.

Lemma ordinary_of_id : forall i o, ordinary_of i = Some o -> ordinary_id o = i.
Proof.
  intros i o; unfold ordinary_of; destruct (Bool.bool_dec (is_blank (spelling i)) false) as [H|H].
  - intro Ho; injection Ho as <-; reflexivity.
  - discriminate.
Qed.

Lemma ordinary_of_success : forall i, spelling i <> "_" -> exists o, ordinary_of i = Some o /\ ordinary_id o = i.
Proof.
  intros i Hne. assert (Hb : is_blank (spelling i) = false) by (apply is_blank_false; exact Hne).
  unfold ordinary_of; destruct (Bool.bool_dec (is_blank (spelling i)) false) as [H|H].
  - eexists; split; reflexivity.
  - exfalso; apply H; exact Hb.
Qed.

Lemma ordinary_of_fail : forall i, spelling i = "_" -> ordinary_of i = None.
Proof.
  intros i He. assert (Hb : is_blank (spelling i) = true) by (apply is_blank_true; exact He).
  unfold ordinary_of; destruct (Bool.bool_dec (is_blank (spelling i)) false) as [H|H].
  - congruence.
  - reflexivity.
Qed.

Lemma ordinary_equal : forall a b, ordinary_id a = ordinary_id b -> a = b.
Proof. intros [ia Ha] [ib Hb] H; cbn in H; subst ib; f_equal; apply (UIP_dec Bool.bool_dec). Qed.
Lemma ordinary_equal_spelling : forall a b, spelling (ordinary_id a) = spelling (ordinary_id b) -> a = b.
Proof. intros a b H; apply ordinary_equal, identifier_equal; exact H. Qed.

Definition ordinary_equalb (a b : OrdinaryIdentifier) : bool := equalb (ordinary_id a) (ordinary_id b).
Lemma ordinary_equalb_spec : forall a b, ordinary_equalb a b = true <-> a = b.
Proof.
  intros a b; unfold ordinary_equalb; split.
  - intro H; apply equalb_spec in H; apply ordinary_equal; exact H.
  - intro H; subst b; apply equalb_spec; reflexivity.
Qed.

Lemma render_ordinary_ascii : forall o, str_ascii (render_ordinary o) = true.
Proof. intro o; apply identifier_ascii. Qed.


(* The complete pinned 44-identity predeclared catalog; membership confers identity only, never a meaning. *)
Inductive PredeclaredName : Type :=
  | PAny | PBool | PByte | PComparable | PComplex64 | PComplex128 | PError
  | PFloat32 | PFloat64 | PInt | PInt8 | PInt16 | PInt32 | PInt64 | PRune | PString
  | PUint | PUint8 | PUint16 | PUint32 | PUint64 | PUintptr
  | PTrue | PFalse | PIota | PNil
  | PAppend | PCap | PClear | PClose | PComplex | PCopy | PDelete | PImag | PLen
  | PMake | PMax | PMin | PNew | PPanic | PPrint | PPrintln | PReal | PRecover.

Definition predeclared_spelling (n : PredeclaredName) : string :=
  match n with
  | PAny => "any" | PBool => "bool" | PByte => "byte" | PComparable => "comparable"
  | PComplex64 => "complex64" | PComplex128 => "complex128" | PError => "error"
  | PFloat32 => "float32" | PFloat64 => "float64"
  | PInt => "int" | PInt8 => "int8" | PInt16 => "int16" | PInt32 => "int32" | PInt64 => "int64"
  | PRune => "rune" | PString => "string"
  | PUint => "uint" | PUint8 => "uint8" | PUint16 => "uint16" | PUint32 => "uint32"
  | PUint64 => "uint64" | PUintptr => "uintptr"
  | PTrue => "true" | PFalse => "false" | PIota => "iota" | PNil => "nil"
  | PAppend => "append" | PCap => "cap" | PClear => "clear" | PClose => "close"
  | PComplex => "complex" | PCopy => "copy" | PDelete => "delete" | PImag => "imag"
  | PLen => "len" | PMake => "make" | PMax => "max" | PMin => "min" | PNew => "new"
  | PPanic => "panic" | PPrint => "print" | PPrintln => "println" | PReal => "real"
  | PRecover => "recover"
  end.

Definition all_predeclared : list PredeclaredName :=
  [ PAny; PBool; PByte; PComparable; PComplex64; PComplex128; PError;
    PFloat32; PFloat64; PInt; PInt8; PInt16; PInt32; PInt64; PRune; PString;
    PUint; PUint8; PUint16; PUint32; PUint64; PUintptr;
    PTrue; PFalse; PIota; PNil;
    PAppend; PCap; PClear; PClose; PComplex; PCopy; PDelete; PImag; PLen;
    PMake; PMax; PMin; PNew; PPanic; PPrint; PPrintln; PReal; PRecover ].

Definition predeclared_eq_dec : forall a b : PredeclaredName, {a = b} + {a <> b}.
Proof. decide equality. Defined.
Definition predeclared_eqb (a b : PredeclaredName) : bool :=
  if predeclared_eq_dec a b then true else false.
Lemma predeclared_eqb_spec : forall a b, predeclared_eqb a b = true <-> a = b.
Proof. intros a b; unfold predeclared_eqb; destruct (predeclared_eq_dec a b); split; congruence. Qed.

(* The one classifier from a source spelling to a full predeclared identity. *)
Definition classify_predeclared (s : string) : option PredeclaredName :=
  find (fun n => String.eqb s (predeclared_spelling n)) all_predeclared.

Lemma classify_predeclared_roundtrip : forall n, classify_predeclared (predeclared_spelling n) = Some n.
Proof. intro n; destruct n; reflexivity. Qed.
Lemma classify_predeclared_sound : forall s n, classify_predeclared s = Some n -> s = predeclared_spelling n.
Proof.
  intros s n H; unfold classify_predeclared in H. apply find_some in H. destruct H as [_ Hb].
  apply String.eqb_eq in Hb; exact Hb.
Qed.

Lemma predeclared_spelling_inj : forall a b, predeclared_spelling a = predeclared_spelling b -> a = b.
Proof.
  intros a b H. pose proof (classify_predeclared_roundtrip a) as Ha.
  rewrite H in Ha. rewrite classify_predeclared_roundtrip in Ha. injection Ha; auto.
Qed.

Lemma all_predeclared_complete : forall n, In n all_predeclared.
Proof. intro n; destruct n; cbn; tauto. Qed.
Lemma all_predeclared_nodup : NoDup all_predeclared.
Proof.
  assert (E : nodup predeclared_eq_dec all_predeclared = all_predeclared) by (vm_compute; reflexivity).
  rewrite <- E; apply NoDup_nodup.
Qed.

Lemma predeclared_spelling_ok : forall n, identifier_ok (predeclared_spelling n) = true.
Proof. intro n; destruct n; reflexivity. Qed.
Lemma predeclared_nonblank : forall n, is_blank (predeclared_spelling n) = false.
Proof. intro n; destruct n; reflexivity. Qed.

(* Each identity has exactly one canonical [Identifier] and one canonical ordinary identifier. *)
Definition predeclared_identifier (n : PredeclaredName) : Identifier :=
  MakeIdentifier (predeclared_spelling n) (predeclared_spelling_ok n).
Definition predeclared_ordinary (n : PredeclaredName) : OrdinaryIdentifier :=
  MakeOrdinary (predeclared_identifier n) (predeclared_nonblank n).
Lemma predeclared_ordinary_spelling : forall n, ordinary_spelling (predeclared_ordinary n) = predeclared_spelling n.
Proof. intro n; reflexivity. Qed.

Lemma predeclared_byte_neq_uint8 : PByte <> PUint8.   Proof. discriminate. Qed.
Lemma predeclared_rune_neq_int32 : PRune <> PInt32.   Proof. discriminate. Qed.


(* The sixteen conversion target names: the live C5 subset, each an index into the catalog, until C6 syntax. *)
Inductive TypeName : Type :=
  | Int | Int8 | Int16 | Int32 | Int64
  | Uint | Uint8 | Uint16 | Uint32 | Uint64
  | Float32 | Float64
  | Complex64 | Complex128
  | Byte | Rune.

Definition type_name_predeclared (t : TypeName) : PredeclaredName :=
  match t with
  | Int => PInt | Int8 => PInt8 | Int16 => PInt16 | Int32 => PInt32 | Int64 => PInt64
  | Uint => PUint | Uint8 => PUint8 | Uint16 => PUint16 | Uint32 => PUint32 | Uint64 => PUint64
  | Float32 => PFloat32 | Float64 => PFloat64
  | Complex64 => PComplex64 | Complex128 => PComplex128
  | Byte => PByte | Rune => PRune
  end.

(* The subset projection: exactly the sixteen conversion identities map back to a [TypeName]. *)
Definition predeclared_type_name (n : PredeclaredName) : option TypeName :=
  match n with
  | PInt => Some Int | PInt8 => Some Int8 | PInt16 => Some Int16 | PInt32 => Some Int32 | PInt64 => Some Int64
  | PUint => Some Uint | PUint8 => Some Uint8 | PUint16 => Some Uint16 | PUint32 => Some Uint32
  | PUint64 => Some Uint64
  | PFloat32 => Some Float32 | PFloat64 => Some Float64
  | PComplex64 => Some Complex64 | PComplex128 => Some Complex128
  | PByte => Some Byte | PRune => Some Rune
  | _ => None
  end.

Lemma predeclared_type_name_roundtrip : forall t, predeclared_type_name (type_name_predeclared t) = Some t.
Proof. intro t; destruct t; reflexivity. Qed.
Lemma predeclared_type_name_inv : forall n t, predeclared_type_name n = Some t -> type_name_predeclared t = n.
Proof. intros n t H; destruct n; cbn in H; solve [ discriminate | injection H as <-; reflexivity ]. Qed.
Lemma type_name_predeclared_inj : forall a b, type_name_predeclared a = type_name_predeclared b -> a = b.
Proof.
  intros a b H. pose proof (predeclared_type_name_roundtrip a) as Ha.
  rewrite H in Ha. rewrite predeclared_type_name_roundtrip in Ha. injection Ha; auto.
Qed.

(* One spelling authority: a type name spells exactly its catalog identity, never a second literal. *)
Definition type_name_spelling (t : TypeName) : string := predeclared_spelling (type_name_predeclared t).
Lemma type_name_spelling_inj : forall a b, type_name_spelling a = type_name_spelling b -> a = b.
Proof. intros a b H; apply type_name_predeclared_inj, predeclared_spelling_inj; exact H. Qed.

Definition type_name_eq_dec : forall a b : TypeName, {a = b} + {a <> b}.
Proof. decide equality. Defined.
Definition type_name_equalb (a b : TypeName) : bool := if type_name_eq_dec a b then true else false.
Lemma type_name_equalb_spec : forall a b, type_name_equalb a b = true <-> a = b.
Proof. intros a b; unfold type_name_equalb; destruct (type_name_eq_dec a b); split; congruence. Qed.

(* The source identifier is the exact catalog-owned value, projected, never rebuilt from the spelling. *)
Definition type_name_identifier (t : TypeName) : Identifier :=
  predeclared_identifier (type_name_predeclared t).
Definition type_name_ordinary (t : TypeName) : OrdinaryIdentifier :=
  predeclared_ordinary (type_name_predeclared t).
Lemma type_name_identifier_projects :
  forall t, type_name_identifier t = predeclared_identifier (type_name_predeclared t).
Proof. reflexivity. Qed.
Lemma type_name_ordinary_projects :
  forall t, type_name_ordinary t = predeclared_ordinary (type_name_predeclared t).
Proof. reflexivity. Qed.

(* Source spelling -> full classifier -> current-subset projection: no second search over strings. *)
Definition classify (s : string) : option TypeName :=
  match classify_predeclared s with Some n => predeclared_type_name n | None => None end.
Lemma classify_is_projection : forall s,
  classify s = match classify_predeclared s with Some n => predeclared_type_name n | None => None end.
Proof. reflexivity. Qed.
Lemma classify_spelling : forall t, classify (type_name_spelling t) = Some t.
Proof.
  intro t; unfold classify, type_name_spelling.
  rewrite classify_predeclared_roundtrip; apply predeclared_type_name_roundtrip.
Qed.
Lemma classify_sound : forall s t, classify s = Some t -> s = type_name_spelling t.
Proof.
  intros s t H; unfold classify in H.
  destruct (classify_predeclared s) as [n|] eqn:E; [| discriminate].
  apply classify_predeclared_sound in E. apply predeclared_type_name_inv in H.
  rewrite E; unfold type_name_spelling; rewrite H; reflexivity.
Qed.

Lemma type_name_byte_neq_uint8 : Byte <> Uint8.   Proof. discriminate. Qed.
Lemma type_name_rune_neq_int32 : Rune <> Int32.   Proof. discriminate. Qed.


(* A source conversion name is its catalog symbol; the source identifier derives through the one authority. *)
Record SupportedType : Type := MakeSupportedType { symbol : TypeName }.

Definition identifier (s : SupportedType) : Identifier := type_name_identifier (symbol s).
Definition supported_ordinary (s : SupportedType) : OrdinaryIdentifier := type_name_ordinary (symbol s).
Definition render_supported (s : SupportedType) : string := render_identifier (identifier s).
Definition supported_of (t : TypeName) : SupportedType := MakeSupportedType t.

Lemma supported_of_symbol : forall t, symbol (supported_of t) = t.   Proof. reflexivity. Qed.
Lemma supported_render : forall s, render_identifier (identifier s) = type_name_spelling (symbol s).
Proof. reflexivity. Qed.
Lemma render_supported_of : forall t, render_supported (supported_of t) = type_name_spelling t.
Proof. reflexivity. Qed.
Lemma render_supported_ascii : forall s, str_ascii (render_supported s) = true.
Proof. intro s; apply identifier_ascii. Qed.

Lemma supported_equal : forall a b, identifier a = identifier b -> a = b.
Proof. intros [ta] [tb] H; f_equal; apply type_name_spelling_inj; exact (f_equal spelling H). Qed.
Definition supported_equalb (a b : SupportedType) : bool := type_name_equalb (symbol a) (symbol b).
Lemma supported_equalb_spec : forall a b, supported_equalb a b = true <-> a = b.
Proof.
  intros [ta] [tb]; unfold supported_equalb; cbn; rewrite type_name_equalb_spec; split.
  - intro H; f_equal; exact H.
  - intro H; injection H as H; exact H.
Qed.

Lemma supported_byte_neq_uint8 : supported_of Byte <> supported_of Uint8.
Proof. intro H; injection H as H; discriminate. Qed.
Lemma render_supported_byte_neq_uint8 : render_supported (supported_of Byte) <> render_supported (supported_of Uint8).
Proof. discriminate. Qed.
Lemma supported_rune_neq_int32 : supported_of Rune <> supported_of Int32.
Proof. intro H; injection H as H; discriminate. Qed.
Lemma render_supported_rune_neq_int32 : render_supported (supported_of Rune) <> render_supported (supported_of Int32).
Proof. discriminate. Qed.


(* Adversarial controls: blank is an identifier yet never ordinary; the catalog and the subset stay distinct. *)
Example blank_is_identifier : identifier_ok "_" = true.                Proof. reflexivity. Qed.
Example blank_not_ordinary : ordinary_of (MakeIdentifier "_" blank_is_identifier) = None.
Proof. reflexivity. Qed.
Example keyword_type_not_ident : identifier_ok "type" = false.        Proof. reflexivity. Qed.
Example foo_not_predeclared : classify_predeclared "foo" = None.      Proof. reflexivity. Qed.
Example qualified_not_predeclared : classify_predeclared "pkg.T" = None.   Proof. reflexivity. Qed.
Example bool_in_catalog : classify_predeclared "bool" = Some PBool.        Proof. reflexivity. Qed.
Example bool_not_conversion : classify "bool" = None.                Proof. reflexivity. Qed.
Example string_in_catalog : classify_predeclared "string" = Some PString.  Proof. reflexivity. Qed.
Example string_not_conversion : classify "string" = None.            Proof. reflexivity. Qed.
Example uintptr_in_catalog : classify_predeclared "uintptr" = Some PUintptr. Proof. reflexivity. Qed.
Example uintptr_not_conversion : classify "uintptr" = None.          Proof. reflexivity. Qed.
Example any_in_catalog : classify_predeclared "any" = Some PAny.           Proof. reflexivity. Qed.
Example any_not_conversion : classify "any" = None.                  Proof. reflexivity. Qed.
Example error_in_catalog : classify_predeclared "error" = Some PError.     Proof. reflexivity. Qed.
Example error_not_conversion : classify "error" = None.              Proof. reflexivity. Qed.
Example comparable_in_catalog : classify_predeclared "comparable" = Some PComparable. Proof. reflexivity. Qed.
Example comparable_not_conversion : classify "comparable" = None.    Proof. reflexivity. Qed.
Example foo_not_conversion : classify "foo" = None.                  Proof. reflexivity. Qed.
Example qualified_not_conversion : classify "pkg.T" = None.          Proof. reflexivity. Qed.
