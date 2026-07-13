(** ============================================================================
    ModulePath — the intrinsic canonical module-path domain (the `module` directive of the generated
    `go.mod`).  A raw [string] is NOT a module path: the path is a SEMANTIC program fact (it is the prefix
    of every future closed-world package import path), so only a deliberately NARROW canonical grammar is
    representable — this is not an ambitious model of every path any Go release accepts.

    A [ModulePath] is one or more `/`-separated segments; each segment is nonempty, starts with a
    lowercase letter, ends with a lowercase letter or digit, and contains only lowercase letters, digits,
    or `.` with no `..`.  The FIRST element must contain a `.` (never a stdlib-colliding dotless prefix like
    `go`/`fmt`); the FINAL element must NOT be a version-suffix shape (`v` + digit + digits/dots — Go's
    semantic-import-versioning reject class); and the path must NOT be a `gopkg.in/` path (Go's `.vN`-suffix
    special case).  Hence NO whitespace/control byte, NO backslash/NUL/`@`, NO query/fragment, NO
    empty/`.`/`..` component, NO leading/trailing/repeated slash, NO leading/trailing dot, NO `/vN` tail, and
    NO `gopkg.in/`; a total length bound keeps it safe.  Every representable path is accepted by the pinned
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

(** Go's semantic-import-versioning rules (`golang.org/x/mod/module.SplitPathVersion`, pinned 1.23) reject a
    module path whose FINAL `/`-separated element is a version-suffix shape `v<digits/dots>` UNLESS it is a
    valid major version `/vN` (N >= 2, no leading zero, no interior dot): so `/v1`, `/v0`, `/v01`, `/v1.2`
    are all rejected, while `/v2`, `/v10` are accepted.  Rather than model the accept/reject split (which
    would let a subtly-wrong rule admit a Go-rejected path), we EXCLUDE the whole version-suffix-shaped last
    element — [version_suffix_shape] holds of ANY `v` followed by a digit then digits/dots — so every such
    element is UNREPRESENTABLE.  A genuinely-valid `/v2` module is out of scope (there is no import support
    yet), not admitted-then-narrowed; this keeps "representable ⇒ Go-accepts" exact. *)
Definition is_dot_or_digit (c : ascii) : bool := is_digit c || Ascii.eqb c "."%char.

Fixpoint all_dot_or_digit (s : string) : bool :=
  match s with EmptyString => true | String c s' => is_dot_or_digit c && all_dot_or_digit s' end.

Definition version_suffix_shape (seg : string) : bool :=
  match seg with
  | String v (String d rest) => Ascii.eqb v "v"%char && is_digit d && all_dot_or_digit rest
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
    slash, or the empty string, fails [segment_ok]); with a total-length bound. *)
Definition modpath_ok (s : string) : bool :=
  (String.length s <=? 200)%nat && all_modpath_chars s
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
  apply Bool.andb_true_iff in H as [H _].            (* drop contains_dot (before_slash s) *)
  apply Bool.andb_true_iff in H as [_ H]; exact H.   (* drop the length bound; keep all_modpath_chars *)
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
