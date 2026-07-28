(* The canonical module-path domain: a raw string is not a module path, and a value carries its own proof. *)
From Stdlib Require Import String Ascii List Bool Eqdep_dec Arith Lia.
Import ListNotations.

Definition is_lower (c : ascii) : bool :=
  let n := nat_of_ascii c in (97 <=? n) && (n <=? 122).

Definition is_lower_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in ((97 <=? n) && (n <=? 122)) || ((48 <=? n) && (n <=? 57)).

(* A segment character: a..z, 0..9, or `.`, with no hyphen. *)
Definition seg_char (c : ascii) : bool := is_lower_digit c || Ascii.eqb c "."%char.

Fixpoint all_seg_chars (s : string) : bool :=
  match s with EmptyString => true | String c s' => seg_char c && all_seg_chars s' end.

Fixpoint no_double_dot (s : string) : bool :=
  match s with
  | String a s0 =>
      match s0 with
      | String b _ => negb (Ascii.eqb a "."%char && Ascii.eqb b "."%char) && no_double_dot s0
      | EmptyString => true
      end
  | EmptyString => true
  end.

Definition str_last (s : string) : option ascii := String.get (String.length s - 1) s.

Definition is_digit (c : ascii) : bool := let n := nat_of_ascii c in (48 <=? n) && (n <=? 57).

(* A segment's base name is the part before its first `.`, which is what Go's device-name rejection reads. *)
Fixpoint base_of (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => if Ascii.eqb c "."%char then EmptyString else String c (base_of s')
  end.

Definition reserved_base (s : string) : bool :=
  let b := base_of s in
  String.eqb b "con" || String.eqb b "prn" || String.eqb b "aux" || String.eqb b "nul"
  || match b with
     | String a (String b1 (String c (String d EmptyString))) =>
         ((Ascii.eqb a "c"%char && Ascii.eqb b1 "o"%char && Ascii.eqb c "m"%char)
          || (Ascii.eqb a "l"%char && Ascii.eqb b1 "p"%char && Ascii.eqb c "t"%char)) && is_digit d
     | _ => false
     end.

(* One segment: nonempty, first character a..z, last a..z0..9, no `..`, and no reserved device name. *)
Definition segment_ok (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c0 _ =>
      is_lower c0
      && all_seg_chars s
      && no_double_dot s
      && match str_last s with Some cl => is_lower_digit cl | None => false end
      && negb (reserved_base s)
  end.

Fixpoint split_slash (s : string) : list string :=
  match s with
  | EmptyString => [EmptyString]
  | String c s' =>
      if Ascii.eqb c "/"%char then EmptyString :: split_slash s'
      else match split_slash s' with
           | h :: t => String c h :: t
           | [] => [String c EmptyString]                (* unreachable: split_slash never returns [] *)
           end
  end.

(* [split_slash] never returns the empty list, and it distributes over an explicit `/` join. *)
Lemma split_slash_nonempty : forall s, split_slash s <> [].
Proof.
  destruct s as [|c s']; cbn [split_slash].
  - discriminate.
  - destruct (Ascii.eqb c "/"%char); [ discriminate | destruct (split_slash s'); discriminate ].
Qed.

Lemma split_slash_app : forall a b,
  split_slash (a ++ String "/"%char b) = split_slash a ++ split_slash b.
Proof.
  induction a as [|c a' IH]; intro b.
  - reflexivity.
  - cbn [append split_slash]. destruct (Ascii.eqb c "/"%char) eqn:Ec.
    + rewrite IH. reflexivity.
    + rewrite IH. destruct (split_slash a') as [|ha ta] eqn:Ea.
      * exfalso. exact (split_slash_nonempty a' Ea).
      * reflexivity.
Qed.

(* Every module-path character is a segment character or the separator `/`, so every one is ASCII. *)
Definition path_char (c : ascii) : bool := seg_char c || Ascii.eqb c "/"%char.

Fixpoint all_path_chars (s : string) : bool :=
  match s with EmptyString => true | String c s' => path_char c && all_path_chars s' end.

(* Go reads a dotless first element as standard library, so a required dot keeps paths outside it. *)
Fixpoint before_slash (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => if Ascii.eqb c "/"%char then EmptyString else String c (before_slash s')
  end.

Fixpoint contains_dot (s : string) : bool :=
  match s with EmptyString => false | String c s' => Ascii.eqb c "."%char || contains_dot s' end.

(* Go's whole version-suffix shape is excluded rather than split into its accept and reject halves. *)
Definition is_dot_or_digit (c : ascii) : bool := is_digit c || Ascii.eqb c "."%char.

Fixpoint all_dot_or_digit (s : string) : bool :=
  match s with EmptyString => true | String c s' => is_dot_or_digit c && all_dot_or_digit s' end.

(* `v` then a nonempty run of digits and dots, the first of which may itself be a dot. *)
Definition version_suffix_shape (seg : string) : bool :=
  match seg with
  | String v (String c rest) => Ascii.eqb v "v"%char && is_dot_or_digit c && all_dot_or_digit rest
  | _ => false
  end.

Definition last_segment (s : string) : string := List.last (split_slash s) EmptyString.

(* The `gopkg.in/` host needs a `.vN` suffix grammar that is not modelled, so the whole prefix is excluded. *)
Definition is_gopkg_in (s : string) : bool := String.prefix "gopkg.in/" s.

(* The whole path: module-path characters, a dotted first element, no excluded tail, admissible segments. *)
Definition path_ok (s : string) : bool :=
  all_path_chars s
  && contains_dot (before_slash s)
  && negb (is_gopkg_in s)
  && negb (version_suffix_shape (last_segment s))
  && forallb segment_ok (split_slash s).

Lemma path_ok_all_chars : forall s, path_ok s = true -> all_path_chars s = true.
Proof.
  intros s H; unfold path_ok in H.
  apply Bool.andb_true_iff in H as [H _].            (* drop forallb segment_ok *)
  apply Bool.andb_true_iff in H as [H _].            (* drop negb (version_suffix_shape (last_segment s)) *)
  apply Bool.andb_true_iff in H as [H _].            (* drop negb (is_gopkg_in s) *)
  apply Bool.andb_true_iff in H as [H _]; exact H.   (* drop contains_dot (before_slash s); keep all_path_chars *)
Qed.

(* Every module-path character is ASCII. *)
Lemma path_char_lt_128 : forall c, path_char c = true -> (nat_of_ascii c < 128)%nat.
Proof.
  intros c H; unfold path_char in H; apply Bool.orb_true_iff in H as [H | H].
  - unfold seg_char in H; apply Bool.orb_true_iff in H as [H | H].
    + unfold is_lower_digit in H; cbv zeta in H; apply Bool.orb_true_iff in H as [H | H];
        apply Bool.andb_true_iff in H as [_ H]; apply Nat.leb_le in H; lia.
    + apply Ascii.eqb_eq in H; subst c; apply Nat.ltb_lt; reflexivity.
  - apply Ascii.eqb_eq in H; subst c; apply Nat.ltb_lt; reflexivity.
Qed.

Record T : Type := Make { text : string ; valid : path_ok text = true }.

(* The canonical `module` directive text (the proved conversion to output bytes). *)

Lemma path_ok_pi : forall s (p q : path_ok s = true), p = q.
Proof. intros s p q; apply (UIP_dec Bool.bool_dec). Qed.

Lemma equal : forall a b, text a = text b -> a = b.
Proof. intros [sa pa] [sb pb] H; simpl in H; subst sb; f_equal; apply path_ok_pi. Qed.

Definition equalb (a b : T) : bool := String.eqb (text a) (text b).

Lemma equalb_spec : forall a b, equalb a b = true <-> a = b.
Proof.
  intros a b; unfold equalb; split.
  - intro H; apply String.eqb_eq in H; apply equal; exact H.
  - intro H; subst b; apply String.eqb_refl.
Qed.

Lemma concat_cons_empty : forall sep h t,
  String.concat sep (""%string :: h :: t) = (sep ++ String.concat sep (h :: t))%string.
Proof. reflexivity. Qed.

Lemma concat_map_head : forall sep c h t,
  String.concat sep (String c h :: t) = String c (String.concat sep (h :: t)).
Proof. intros sep c h t. destruct t as [|z t']; reflexivity. Qed.

(* A string is exactly the `/`-join of its own [split_slash] components. *)
Lemma split_slash_concat : forall s, String.concat "/" (split_slash s) = s.
Proof.
  induction s as [|c s IH]; [ reflexivity |].
  cbn [split_slash]. destruct (Ascii.eqb c "/"%char) eqn:E.
  - apply Ascii.eqb_eq in E; subst c.
    destruct (split_slash s) as [|h t] eqn:Esp; [ exfalso; exact (split_slash_nonempty s Esp) |].
    rewrite (concat_cons_empty "/"%string h t), IH. reflexivity.
  - destruct (split_slash s) as [|h t] eqn:Esp; [ exfalso; exact (split_slash_nonempty s Esp) |].
    rewrite (concat_map_head "/"%string c h t), IH. reflexivity.
Qed.

(* A `/`-join of single components reparses to exactly those components. *)
Lemma split_concat_singles : forall comps,
  (forall x, In x comps -> split_slash x = [x]) -> comps <> [] ->
  split_slash (String.concat "/" comps) = comps.
Proof.
  induction comps as [|x [|y rest] IH]; intros Hs Hne; [ contradiction | |].
  - cbn [String.concat]. apply Hs; left; reflexivity.
  - change (String.concat "/" (x :: y :: rest))
      with (x ++ String "/"%char (String.concat "/" (y :: rest)))%string.
    rewrite split_slash_app, (Hs x (or_introl eq_refl)).
    rewrite (IH (fun z Hz => Hs z (or_intror Hz)) ltac:(discriminate)). reflexivity.
Qed.

Lemma seg_char_not_slash : forall c, seg_char c = true -> Ascii.eqb c "/"%char = false.
Proof.
  intros c H. destruct (Ascii.eqb c "/"%char) eqn:E; [| reflexivity].
  apply Ascii.eqb_eq in E; subst c. cbn in H. discriminate H.
Qed.

Lemma all_seg_chars_single : forall s, all_seg_chars s = true -> split_slash s = [s].
Proof.
  induction s as [|c s IH]; intro H; [ reflexivity |].
  cbn [all_seg_chars] in H. apply Bool.andb_true_iff in H as [Hc Hs].
  cbn [split_slash]. rewrite (seg_char_not_slash c Hc), (IH Hs). reflexivity.
Qed.

Lemma segment_ok_single : forall s, segment_ok s = true -> split_slash s = [s].
Proof.
  intros s H. apply all_seg_chars_single.
  destruct s as [|c s']; [ discriminate H |].
  unfold segment_ok in H.
  apply Bool.andb_true_iff in H as [H _].
  apply Bool.andb_true_iff in H as [H _].
  apply Bool.andb_true_iff in H as [H _].
  apply Bool.andb_true_iff in H as [_ H]. exact H.
Qed.

Lemma segment_ok_nonempty : forall s, segment_ok s = true -> s <> ""%string.
Proof. intros s H; destruct s; [ discriminate H | discriminate ]. Qed.

Definition segments (p : T) : list string := split_slash (text p).

Lemma segments_nonempty : forall p, segments p <> [].
Proof. intro p. apply split_slash_nonempty. Qed.

Lemma text_concat : forall p, String.concat "/" (segments p) = text p.
Proof. intro p. apply split_slash_concat. Qed.

Lemma segments_segment_ok : forall p s, In s (segments p) -> segment_ok s = true.
Proof.
  intros p s Hin. pose proof (valid p) as Hok. unfold path_ok in Hok.
  apply Bool.andb_true_iff in Hok as [_ Hseg].
  rewrite forallb_forall in Hseg. exact (Hseg s Hin).
Qed.

Lemma segments_single : forall p s, In s (segments p) -> split_slash s = [s].
Proof. intros p s Hin. apply segment_ok_single. exact (segments_segment_ok p s Hin). Qed.

Lemma segments_nonempty_elt : forall p s, In s (segments p) -> s <> ""%string.
Proof. intros p s Hin. apply segment_ok_nonempty. exact (segments_segment_ok p s Hin). Qed.

(* The grammar's positive and negative fixtures, kernel-checked. *)
Example ok_generated : path_ok "fido.local/generated" = true.       Proof. reflexivity. Qed.
Example ok_nested    : path_ok "fido.local/generated/sub" = true.   Proof. reflexivity. Qed.
Example ok_common    : path_ok "fido.local/common" = true.          Proof. reflexivity. Qed.
Example ok_dothost   : path_ok "example.com" = true.                Proof. reflexivity. Qed.
Example ok_digits    : path_ok "fido2.dev/pkg9" = true.             Proof. reflexivity. Qed.

Example no_empty         : path_ok "" = false.               Proof. reflexivity. Qed.
Example no_leading_slash : path_ok "/x" = false.             Proof. reflexivity. Qed.
Example no_trailing_slash : path_ok "x/" = false.            Proof. reflexivity. Qed.
Example no_double_slash  : path_ok "a//b" = false.           Proof. reflexivity. Qed.
Example no_upper         : path_ok "Fido.dev" = false.       Proof. reflexivity. Qed.
Example no_dotdot        : path_ok "a..b" = false.           Proof. reflexivity. Qed.
Example no_leading_dot   : path_ok ".fido" = false.          Proof. reflexivity. Qed.
Example no_trailing_dot  : path_ok "fido." = false.          Proof. reflexivity. Qed.
Example no_at            : path_ok "fido.dev@v1" = false.    Proof. reflexivity. Qed.
Example no_space         : path_ok "fido dev.x" = false.     Proof. reflexivity. Qed.
Example no_digit_start    : path_ok "9fido.dev" = false.     Proof. reflexivity. Qed.
(* dotless first elements are STDLIB-colliding and UNREPRESENTABLE (`go/ast`, `fmt`, a bare vanity name): *)
Example no_dotless_go   : path_ok "go" = false.             Proof. reflexivity. Qed.
Example no_dotless_fmt  : path_ok "fmt" = false.            Proof. reflexivity. Qed.
Example no_dotless_bare : path_ok "fidoe2e" = false.        Proof. reflexivity. Qed.
Example no_dotless_pkg  : path_ok "fido2/pkg9" = false.     Proof. reflexivity. Qed.
(* the whole version-suffix-shaped last element is excluded, so a Go-valid `/v2` is out of scope too: *)
Example no_ver_v1     : path_ok "example.com/pkg/v1" = false.   Proof. reflexivity. Qed.
Example no_ver_v01    : path_ok "example.com/pkg/v01" = false.  Proof. reflexivity. Qed.
Example no_ver_v1dot2 : path_ok "example.com/pkg/v1.2" = false. Proof. reflexivity. Qed.
Example no_ver_vdot   : path_ok "example.com/pkg/v.2.3" = false. Proof. reflexivity. Qed.  (* dot-led run *)
Example no_ver_v2     : path_ok "example.com/pkg/v2" = false.   Proof. reflexivity. Qed.  (* Go-valid, but out of scope *)
Example ok_vlike_mid  : path_ok "example.com/v2/pkg" = true.    Proof. reflexivity. Qed.  (* v2 NOT the last element *)
Example ok_vword      : path_ok "example.com/verify" = true.    Proof. reflexivity. Qed.
(* the whole `gopkg.in/` prefix class is excluded: *)
Example no_gopkg_bare : path_ok "gopkg.in/foo" = false.        Proof. reflexivity. Qed.
(* Go-valid, but out of scope *)
Example no_gopkg_v2   : path_ok "gopkg.in/yaml.v2" = false.    Proof. reflexivity. Qed.
(* Windows-reserved device names Go rejects as a path ELEMENT (even on Linux), with or without extension: *)
Example no_reserved_con   : path_ok "fido.local/con" = false. Proof. reflexivity. Qed.
Example no_reserved_nul   : path_ok "fido.dev/nul" = false.  Proof. reflexivity. Qed.
Example no_reserved_com1  : path_ok "fido.dev/com1" = false. Proof. reflexivity. Qed.
Example no_reserved_lpt9  : path_ok "fido.dev/lpt9" = false. Proof. reflexivity. Qed.
Example no_reserved_conext : path_ok "con.js" = false.      Proof. reflexivity. Qed.  (* base "con" reserved *)
