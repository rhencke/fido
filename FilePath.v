(** ============================================================================
    FilePath — the intrinsic canonical relative source-path domain.  A raw [string] is NOT a file path:
    Go package discovery for `go build ./...` depends on the path, so the path is a SEMANTIC compiler
    input, and only a deliberately NARROW canonical grammar is representable.

    A [FilePath] is a validated relative path: slash-separated lowercase-ASCII directory components and
    an ordinary lowercase-ASCII `.go` basename, with NO empty/`.`/`..` component, NO absolute or
    trailing/leading/repeated slash, NO underscore or leading dot (so NO hidden file/dir, NO `_test.go`,
    NO `_GOOS`/`_GOARCH` build-selection suffix, NO Fido control-name collision).  Every representable
    path is therefore safe to materialize AND discovered by `go build ./...` on any target, independent
    of case-folding and platform source selection.  Strange-but-filesystem-valid paths are deliberately
    UNREPRESENTABLE — narrowness is the point, not an ambitious model of every OS path.

    Validity is intrinsic: [FilePath] carries the proof [path_ok fp_str = true], so a value cannot exist
    for a bad path.  Equality is decidable and reduces to string equality (the proof is unique by bool
    UIP).  [fp_parent] is the parent-directory identity used to group files into packages.
    ============================================================================ *)
From Stdlib Require Import String Ascii List Bool Eqdep_dec Arith.
Import ListNotations.

(** ---- character classes ---- *)

Definition is_lower (c : ascii) : bool :=
  let n := nat_of_ascii c in (97 <=? n) && (n <=? 122).                (* a..z *)

Definition is_lower_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in ((97 <=? n) && (n <=? 122)) || ((48 <=? n) && (n <=? 57)).  (* a..z 0..9 *)

(** a component / basename-stem: nonempty, first char lowercase, rest lowercase-or-digit. *)
Fixpoint tail_ok (s : string) : bool :=
  match s with EmptyString => true | String c s' => is_lower_digit c && tail_ok s' end.

Definition component_ok (s : string) : bool :=
  match s with EmptyString => false | String c s' => is_lower c && tail_ok s' end.

(** ---- path grammar ---- *)

Fixpoint split_slash (s : string) : list string :=
  match s with
  | EmptyString => [EmptyString]
  | String c s' =>
      if Ascii.eqb c "/"%char then EmptyString :: split_slash s'
      else match split_slash s' with
           | h :: t => String c h :: t
           | [] => [String c EmptyString]         (* unreachable: split_slash never returns [] *)
           end
  end.

Definition ends_go (s : string) : bool :=
  let n := String.length s in
  (3 <=? n) && String.eqb (String.substring (n - 3) 3 s) ".go".

Definition strip_go (s : string) : string := String.substring 0 (String.length s - 3) s.

(** an ordinary Go source basename: an admissible component stem followed by ".go". *)
Definition filename_ok (s : string) : bool := ends_go s && component_ok (strip_go s).

(** the whole path: directory components (all but the last segment) are admissible components; the last
    segment is an admissible `.go` filename.  A single segment (root-level file) is allowed. *)
Definition path_ok (s : string) : bool :=
  match rev (split_slash s) with
  | last :: rdirs => forallb component_ok rdirs && filename_ok last
  | [] => false
  end.

(** ---- the intrinsic type ---- *)

Record FilePath : Type := mkFP { fp_str : string ; fp_ok : path_ok fp_str = true }.

(** The on-disk relative path text (the proved canonical conversion to output). *)
Definition fp_string (p : FilePath) : string := fp_str p.

(** Validity proofs are unique (bool UIP), so equality reduces to the underlying string. *)
Lemma path_ok_pi : forall s (p q : path_ok s = true), p = q.
Proof. intros s p q; apply (UIP_dec Bool.bool_dec). Qed.

Lemma fp_eq : forall a b, fp_str a = fp_str b -> a = b.
Proof. intros [sa pa] [sb pb] H; simpl in H; subst sb; f_equal; apply path_ok_pi. Qed.

Definition fp_eqb (a b : FilePath) : bool := String.eqb (fp_str a) (fp_str b).

Lemma fp_eqb_eq : forall a b, fp_eqb a b = true <-> a = b.
Proof.
  intros a b; unfold fp_eqb; split.
  - intro H; apply String.eqb_eq in H; apply fp_eq; exact H.
  - intro H; subst b; apply String.eqb_refl.
Qed.

(** ---- parent-directory identity (package grouping key) ---- *)

Definition parent_of (s : string) : string :=
  match rev (split_slash s) with
  | _ :: rdirs => String.concat "/" (rev rdirs)
  | [] => EmptyString
  end.

(** The parent directory of a file — files with the SAME parent form one package. *)
Definition fp_parent (p : FilePath) : string := parent_of (fp_str p).

(** ---- positive / negative fixtures (the grammar, kernel-checked) ---- *)

Example ok_main    : path_ok "main.go" = true.        Proof. reflexivity. Qed.
Example ok_a       : path_ok "a.go" = true.           Proof. reflexivity. Qed.
Example ok_pkg     : path_ok "pkg/main.go" = true.    Proof. reflexivity. Qed.
Example ok_nested  : path_ok "cmd/x/app.go" = true.   Proof. reflexivity. Qed.

Example no_empty     : path_ok "" = false.              Proof. reflexivity. Qed.
Example no_absolute  : path_ok "/main.go" = false.      Proof. reflexivity. Qed.
Example no_dotdot    : path_ok "../x.go" = false.       Proof. reflexivity. Qed.
Example no_mid_dotdot : path_ok "a/../x.go" = false.    Proof. reflexivity. Qed.
Example no_dot       : path_ok "./x.go" = false.        Proof. reflexivity. Qed.
Example no_double    : path_ok "a//b.go" = false.       Proof. reflexivity. Qed.
Example no_hidden    : path_ok ".main.go" = false.      Proof. reflexivity. Qed.
Example no_underscore : path_ok "_main.go" = false.     Proof. reflexivity. Qed.
Example no_test      : path_ok "main_test.go" = false.  Proof. reflexivity. Qed.
Example no_goos      : path_ok "main_windows.go" = false. Proof. reflexivity. Qed.
Example no_ext       : path_ok "main.txt" = false.      Proof. reflexivity. Qed.
Example no_hidden_dir : path_ok ".git/x.go" = false.    Proof. reflexivity. Qed.
Example no_control   : path_ok ".fido/x.go" = false.    Proof. reflexivity. Qed.
Example no_trailing  : path_ok "pkg/" = false.          Proof. reflexivity. Qed.
Example no_bare_go   : path_ok "go" = false.            Proof. reflexivity. Qed.
