(** ============================================================================
    ModulePath — the intrinsic canonical module-path domain (the `module` directive of the generated
    `go.mod`).  A raw [string] is NOT a module path: the path is a SEMANTIC program fact (it is the prefix
    of every future closed-world package import path), so only a deliberately NARROW canonical grammar is
    representable — this is not an ambitious model of every path any Go release accepts.

    A [ModulePath] is one or more `/`-separated segments; each segment is nonempty, starts with a
    lowercase letter, ends with a lowercase letter or digit, and contains only lowercase letters, digits,
    or `.` with no `..`.  Hence NO whitespace/control byte, NO backslash/NUL/`@`, NO query/fragment, NO
    empty/`.`/`..` component, NO leading/trailing/repeated slash, and NO leading/trailing dot; a total
    length bound keeps it safe.  Every representable path is accepted by the pinned Go 1.23 toolchain as a
    `module` directive (the e2e's `go build ./...` over the rendered module is the differential alarm).

    Validity is intrinsic: [ModulePath] carries [modpath_ok mp_str = true], so no value exists for a bad
    path; equality is decidable and reduces to string equality (bool UIP).  Invalid module paths are
    UNREPRESENTABLE — never preserved-then-rejected.
    ============================================================================ *)
From Stdlib Require Import String Ascii List Bool Eqdep_dec Arith.
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

(** one path segment: nonempty; first char a..z; last char a..z0..9; interior seg-chars; no `..`. *)
Definition segment_ok (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c0 _ =>
      is_lower c0
      && all_seg_chars s
      && no_double_dot s
      && match str_last s with Some cl => is_lower_digit cl | None => false end
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

(** the whole module path: every `/`-separated segment is admissible (an empty segment from a
    leading/trailing/repeated slash, or the empty string, fails [segment_ok]); with a total-length bound. *)
Definition modpath_ok (s : string) : bool :=
  (String.length s <=? 200)%nat && forallb segment_ok (split_slash s).

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

Example ok_generated : modpath_ok "fido.local/generated" = true.       Proof. reflexivity. Qed.
Example ok_bare      : modpath_ok "fidoe2e" = true.                    Proof. reflexivity. Qed.
Example ok_nested    : modpath_ok "fido.local/generated/sub" = true.   Proof. reflexivity. Qed.
Example ok_digits    : modpath_ok "fido2/pkg9" = true.                 Proof. reflexivity. Qed.

Example no_empty         : modpath_ok "" = false.               Proof. reflexivity. Qed.
Example no_leading_slash : modpath_ok "/x" = false.             Proof. reflexivity. Qed.
Example no_trailing_slash : modpath_ok "x/" = false.            Proof. reflexivity. Qed.
Example no_double_slash  : modpath_ok "a//b" = false.           Proof. reflexivity. Qed.
Example no_upper         : modpath_ok "Fido" = false.           Proof. reflexivity. Qed.
Example no_dotdot        : modpath_ok "a..b" = false.           Proof. reflexivity. Qed.
Example no_leading_dot   : modpath_ok ".fido" = false.          Proof. reflexivity. Qed.
Example no_trailing_dot  : modpath_ok "fido." = false.          Proof. reflexivity. Qed.
Example no_at            : modpath_ok "fido@v1" = false.        Proof. reflexivity. Qed.
Example no_space         : modpath_ok "fido local" = false.     Proof. reflexivity. Qed.
Example no_digit_start    : modpath_ok "9fido" = false.         Proof. reflexivity. Qed.
