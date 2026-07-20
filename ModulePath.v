(** ============================================================================
    ModulePath — the intrinsic canonical module-path domain (the `module` directive of the generated
    `go.mod`).  A raw [string] is NOT a module path: the path is a SEMANTIC program fact (it is the prefix
    of every future closed-world package import path), so only a deliberately NARROW canonical grammar is
    representable — this is not an ambitious model of every path any Go release accepts.

    A [ModulePath] is one or more `/`-separated segments; each segment is nonempty, starts with a
    lowercase letter, ends with a lowercase letter or digit, and contains only lowercase letters, digits,
    or `.` with no `..`.  The FIRST element must contain a `.` (never a stdlib-colliding dotless prefix like
    `go`/`fmt`); the FINAL element must NOT be a version-suffix shape (`v` + one-or-more digits/dots, dot-led
    runs like `v.2.3` included — Go's semantic-import-versioning reject class, scanned as the trailing
    `[0-9.]` run after `v`); and the path must NOT be a `gopkg.in/` path (Go's `.vN`-suffix
    special case).  Hence NO whitespace/control byte, NO backslash/NUL/`@`, NO query/fragment, NO
    empty/`.`/`..` component, NO leading/trailing/repeated slash, NO leading/trailing dot, NO `/vN` tail, and
    NO `gopkg.in/`.  A module path is of ARBITRARY LENGTH — there is deliberately NO magic length cap (a
    numeric bound is not a correctness invariant).  Every representable path is accepted by the pinned
    Go 1.23 toolchain as a `module` directive; the reverse does NOT hold — valid `/v2` and `gopkg.in/…v2`
    modules are deliberately out of scope (no import support yet), excluded rather than admitted-then-narrowed
    so "representable ⇒ Go-accepts" stays exact (the e2e's `go build ./...` is the differential alarm).

    Validity is intrinsic: [ModulePath] carries [modpath_ok mp_str = true], so no value exists for a bad
    path; equality is decidable and reduces to string equality (bool UIP).  Invalid module paths are
    UNREPRESENTABLE — never preserved-then-rejected.
    ============================================================================ *)
From Stdlib Require Import String Ascii List Bool Eqdep_dec Arith Lia.
Import ListNotations.

(** ---- character classes ---- *)

Definition is_lower (c : ascii) : bool :=
  let n := nat_of_ascii c in (97 <=? n) && (n <=? 122).                    (* a..z *)

Definition is_lower_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in ((97 <=? n) && (n <=? 122)) || ((48 <=? n) && (n <=? 57)).  (* a..z 0..9 *)

(** a segment character: a..z, 0..9, or `.` (no hyphen — deliberate narrowness). *)
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

(** the base name of a segment is the part before its first `.` — Windows treats a reserved DEVICE name as
    forbidden regardless of extension (`con`, `con.x`, …), and Go's module-path validator rejects such
    elements even on Linux, so we exclude them.  (We reject `com0`/`lpt0` too; a stricter subset is still
    Go-accepted.) *)
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

(** one path segment: nonempty; first char a..z; last char a..z0..9; interior seg-chars; no `..`; and NOT a
    Windows-reserved device name (which Go rejects as a path element). *)
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

(** [split_slash] never returns the empty list, and it distributes over an explicit `/` join — the two
    lower-layer facts an import-path component view needs (a `/`-joined path splits into its two parts). *)
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

(** every character of a module path is a segment char or the separator `/` — all ASCII (< 128). *)
Definition modpath_char (c : ascii) : bool := seg_char c || Ascii.eqb c "/"%char.

Fixpoint all_modpath_chars (s : string) : bool :=
  match s with EmptyString => true | String c s' => modpath_char c && all_modpath_chars s' end.

(** the leading path element, and whether it contains a `.`: Go treats a path whose FIRST element has NO dot
    as a STANDARD-LIBRARY candidate (e.g. `go/ast`, `fmt`), so requiring a dot there keeps every represented
    path safely OUTSIDE the stdlib namespace — a safe prefix for future closed-world owned packages. *)
Fixpoint before_slash (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => if Ascii.eqb c "/"%char then EmptyString else String c (before_slash s')
  end.

Fixpoint contains_dot (s : string) : bool :=
  match s with EmptyString => false | String c s' => Ascii.eqb c "."%char || contains_dot s' end.

(** Go's semantic-import-versioning rules (`golang.org/x/mod/module.SplitPathVersion`, pinned 1.23) treat the
    FINAL `/`-separated element as a version suffix when it is `v` immediately followed by a NONEMPTY maximal
    run of `[0-9.]` (Go scans the trailing digit/dot run, then checks the preceding char is `v` after a `/`).
    Such a suffix is REJECTED unless it is a valid major version `/vN` (N >= 2, no leading zero, no dot): so
    `/v1`, `/v0`, `/v01`, `/v1.2`, and `/v.2.3` (Go's own `mod_init_invalid_major` regression rejects
    `.../v.2.3`) are all rejected, while `/v2`, `/v10` are accepted.  Rather than model the accept/reject
    split (which would let a subtly-wrong rule admit a Go-rejected path), we EXCLUDE the WHOLE version-suffix
    shape — [version_suffix_shape] holds of ANY `v` followed by one-or-more `[0-9.]` (matching Go's trailing
    run exactly, dot-led runs like `v.2.3` INCLUDED) — so every such element is UNREPRESENTABLE.  A
    genuinely-valid `/v2` module is out of scope (there is no import support yet), not admitted-then-narrowed;
    this keeps "representable ⇒ Go-accepts" exact. *)
Definition is_dot_or_digit (c : ascii) : bool := is_digit c || Ascii.eqb c "."%char.

Fixpoint all_dot_or_digit (s : string) : bool :=
  match s with EmptyString => true | String c s' => is_dot_or_digit c && all_dot_or_digit s' end.

(** `v` then a NONEMPTY run of digits/dots (the char after `v` may itself be a `.`, as in `v.2.3`). *)
Definition version_suffix_shape (seg : string) : bool :=
  match seg with
  | String v (String c rest) => Ascii.eqb v "v"%char && is_dot_or_digit c && all_dot_or_digit rest
  | _ => false
  end.

Definition last_segment (s : string) : string := List.last (split_slash s) EmptyString.

(** Go special-cases the `gopkg.in/` host: every such path must end in `.vN` (`gopkg.in/yaml.v2`), so a
    bare `gopkg.in/foo` is REJECTED.  We are not modelling that suffix grammar, so we EXCLUDE the whole
    `gopkg.in/` prefix class — again narrow-but-exact, never admit-then-narrow. *)
Definition is_gopkg_in (s : string) : bool := String.prefix "gopkg.in/" s.

(** the whole module path: all characters are module-path characters (so every byte is ASCII); the FIRST
    element contains a `.` (never a stdlib-colliding dotless prefix); it is NOT a `gopkg.in/` path and its
    FINAL element is NOT a version-suffix shape (the two semantic-import-versioning reject classes Go 1.23
    enforces); every `/`-separated segment is admissible (an empty segment from a leading/trailing/repeated
    slash, or the empty string, fails [segment_ok]).  ARBITRARY LENGTH — no length cap. *)
Definition modpath_ok (s : string) : bool :=
  all_modpath_chars s
  && contains_dot (before_slash s)
  && negb (is_gopkg_in s)
  && negb (version_suffix_shape (last_segment s))
  && forallb segment_ok (split_slash s).

Lemma modpath_ok_all_chars : forall s, modpath_ok s = true -> all_modpath_chars s = true.
Proof.
  intros s H; unfold modpath_ok in H.
  apply Bool.andb_true_iff in H as [H _].            (* drop forallb segment_ok *)
  apply Bool.andb_true_iff in H as [H _].            (* drop negb (version_suffix_shape (last_segment s)) *)
  apply Bool.andb_true_iff in H as [H _].            (* drop negb (is_gopkg_in s) *)
  apply Bool.andb_true_iff in H as [H _]; exact H.   (* drop contains_dot (before_slash s); keep all_modpath_chars *)
Qed.

(** every module-path character is ASCII (the go.mod ASCII proof rests on this). *)
Lemma modpath_char_lt_128 : forall c, modpath_char c = true -> (nat_of_ascii c < 128)%nat.
Proof.
  intros c H; unfold modpath_char in H; apply Bool.orb_true_iff in H as [H | H].
  - unfold seg_char in H; apply Bool.orb_true_iff in H as [H | H].
    + unfold is_lower_digit in H; cbv zeta in H; apply Bool.orb_true_iff in H as [H | H];
        apply Bool.andb_true_iff in H as [_ H]; apply Nat.leb_le in H; lia.
    + apply Ascii.eqb_eq in H; subst c; apply Nat.ltb_lt; reflexivity.
  - apply Ascii.eqb_eq in H; subst c; apply Nat.ltb_lt; reflexivity.
Qed.

(** ---- the intrinsic type ---- *)

Record ModulePath : Type := mkMP { mp_str : string ; mp_ok : modpath_ok mp_str = true }.

(** The canonical `module` directive text (the proved conversion to output bytes). *)
Definition mp_string (p : ModulePath) : string := mp_str p.

Lemma modpath_ok_pi : forall s (p q : modpath_ok s = true), p = q.
Proof. intros s p q; apply (UIP_dec Bool.bool_dec). Qed.

Lemma mp_eq : forall a b, mp_str a = mp_str b -> a = b.
Proof. intros [sa pa] [sb pb] H; simpl in H; subst sb; f_equal; apply modpath_ok_pi. Qed.

Definition mp_eqb (a b : ModulePath) : bool := String.eqb (mp_str a) (mp_str b).

Lemma mp_eqb_eq : forall a b, mp_eqb a b = true <-> a = b.
Proof.
  intros a b; unfold mp_eqb; split.
  - intro H; apply String.eqb_eq in H; apply mp_eq; exact H.
  - intro H; subst b; apply String.eqb_refl.
Qed.

(** ============================================================================================
    The canonical COMPONENT AUTHORITY over a module path.  [split_slash] is the split view and its
    "/"-join is its inverse ([split_slash_concat]); a valid [segment_ok] segment contains no separator, so
    it is a SINGLE component ([segment_ok_single]) and is nonempty ([segment_ok_nonempty]).  A [ModulePath]'s
    [mp_segments] are its validated segments: the module string IS their join ([mp_string_concat]), and each
    is a single nonempty component.  This is the lower-layer authority [GoCompile] composes for package
    import-path and executable-name reasoning — no character-level scan in the consumer.
    ============================================================================================ *)

Lemma concat_cons_empty : forall sep h t,
  String.concat sep (""%string :: h :: t) = (sep ++ String.concat sep (h :: t))%string.
Proof. reflexivity. Qed.

Lemma concat_map_head : forall sep c h t,
  String.concat sep (String c h :: t) = String c (String.concat sep (h :: t)).
Proof. intros sep c h t. destruct t as [|z t']; reflexivity. Qed.

(* split/join inverse: the "/"-join of a string's [split_slash] components IS the string. *)
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

(* a "/"-join of SINGLE components ([split_slash x = [x]]) reparses to exactly those components. *)
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

Definition mp_segments (p : ModulePath) : list string := split_slash (mp_str p).

Lemma mp_segments_nonempty : forall p, mp_segments p <> [].
Proof. intro p. apply split_slash_nonempty. Qed.

Lemma mp_string_concat : forall p, String.concat "/" (mp_segments p) = mp_str p.
Proof. intro p. apply split_slash_concat. Qed.

Lemma mp_segments_segment_ok : forall p s, In s (mp_segments p) -> segment_ok s = true.
Proof.
  intros p s Hin. pose proof (mp_ok p) as Hok. unfold modpath_ok in Hok.
  apply Bool.andb_true_iff in Hok as [_ Hseg].
  rewrite forallb_forall in Hseg. exact (Hseg s Hin).
Qed.

Lemma mp_segments_single : forall p s, In s (mp_segments p) -> split_slash s = [s].
Proof. intros p s Hin. apply segment_ok_single. exact (mp_segments_segment_ok p s Hin). Qed.

Lemma mp_segments_nonempty_elt : forall p s, In s (mp_segments p) -> s <> ""%string.
Proof. intros p s Hin. apply segment_ok_nonempty. exact (mp_segments_segment_ok p s Hin). Qed.

(** ---- positive / negative fixtures (the grammar, kernel-checked) ---- *)

(* every representable path has a dotted FIRST element (a safe, non-stdlib prefix) *)
Example ok_generated : modpath_ok "fido.local/generated" = true.       Proof. reflexivity. Qed.
Example ok_nested    : modpath_ok "fido.local/generated/sub" = true.   Proof. reflexivity. Qed.
Example ok_common    : modpath_ok "fido.local/common" = true.          Proof. reflexivity. Qed.
Example ok_dothost   : modpath_ok "example.com" = true.                Proof. reflexivity. Qed.
Example ok_digits    : modpath_ok "fido2.dev/pkg9" = true.             Proof. reflexivity. Qed.

Example no_empty         : modpath_ok "" = false.               Proof. reflexivity. Qed.
Example no_leading_slash : modpath_ok "/x" = false.             Proof. reflexivity. Qed.
Example no_trailing_slash : modpath_ok "x/" = false.            Proof. reflexivity. Qed.
Example no_double_slash  : modpath_ok "a//b" = false.           Proof. reflexivity. Qed.
Example no_upper         : modpath_ok "Fido.dev" = false.       Proof. reflexivity. Qed.
Example no_dotdot        : modpath_ok "a..b" = false.           Proof. reflexivity. Qed.
Example no_leading_dot   : modpath_ok ".fido" = false.          Proof. reflexivity. Qed.
Example no_trailing_dot  : modpath_ok "fido." = false.          Proof. reflexivity. Qed.
Example no_at            : modpath_ok "fido.dev@v1" = false.    Proof. reflexivity. Qed.
Example no_space         : modpath_ok "fido dev.x" = false.     Proof. reflexivity. Qed.
Example no_digit_start    : modpath_ok "9fido.dev" = false.     Proof. reflexivity. Qed.
(* dotless first elements are STDLIB-colliding and UNREPRESENTABLE (`go/ast`, `fmt`, a bare vanity name): *)
Example no_dotless_go   : modpath_ok "go" = false.             Proof. reflexivity. Qed.
Example no_dotless_fmt  : modpath_ok "fmt" = false.            Proof. reflexivity. Qed.
Example no_dotless_bare : modpath_ok "fidoe2e" = false.        Proof. reflexivity. Qed.
Example no_dotless_pkg  : modpath_ok "fido2/pkg9" = false.     Proof. reflexivity. Qed.  (* first elem "fido2" has no dot *)
(* semantic-import-versioning: Go rejects a `/vN` final element with N<2 / leading zero / dot; we exclude the
   whole version-suffix-shaped last element (so a valid `/v2` is out of scope too, not admitted-then-narrowed): *)
Example no_ver_v1     : modpath_ok "example.com/pkg/v1" = false.   Proof. reflexivity. Qed.
Example no_ver_v01    : modpath_ok "example.com/pkg/v01" = false.  Proof. reflexivity. Qed.
Example no_ver_v1dot2 : modpath_ok "example.com/pkg/v1.2" = false. Proof. reflexivity. Qed.
Example no_ver_vdot   : modpath_ok "example.com/pkg/v.2.3" = false. Proof. reflexivity. Qed.  (* dot-led run *)
Example no_ver_v2     : modpath_ok "example.com/pkg/v2" = false.   Proof. reflexivity. Qed.  (* Go-valid, but out of scope *)
Example ok_vlike_mid  : modpath_ok "example.com/v2/pkg" = true.    Proof. reflexivity. Qed.  (* v2 NOT the last element *)
Example ok_vword      : modpath_ok "example.com/verify" = true.    Proof. reflexivity. Qed.  (* not a version shape *)
(* gopkg.in special case: every gopkg.in path must end in `.vN`, so bare `gopkg.in/foo` is Go-rejected; we
   exclude the whole `gopkg.in/` prefix class: *)
Example no_gopkg_bare : modpath_ok "gopkg.in/foo" = false.        Proof. reflexivity. Qed.
Example no_gopkg_v2   : modpath_ok "gopkg.in/yaml.v2" = false.    Proof. reflexivity. Qed.  (* Go-valid, but out of scope *)
(* Windows-reserved device names Go rejects as a path ELEMENT (even on Linux), with or without extension: *)
Example no_reserved_con   : modpath_ok "fido.local/con" = false. Proof. reflexivity. Qed.
Example no_reserved_nul   : modpath_ok "fido.dev/nul" = false.  Proof. reflexivity. Qed.
Example no_reserved_com1  : modpath_ok "fido.dev/com1" = false. Proof. reflexivity. Qed.
Example no_reserved_lpt9  : modpath_ok "fido.dev/lpt9" = false. Proof. reflexivity. Qed.
Example no_reserved_conext : modpath_ok "con.js" = false.      Proof. reflexivity. Qed.  (* base "con" reserved *)
