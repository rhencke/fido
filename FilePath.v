(** FilePath — the intrinsic canonical relative source-path domain.  A raw [string] is NOT a file path:
    Go package discovery for `go build ./...` depends on the path, so the path is a SEMANTIC compiler
    input, and only a deliberately NARROW canonical grammar is representable.

    A [FilePath] is a validated relative path: slash-separated lowercase-ASCII directory components and
    an ordinary lowercase-ASCII `.go` basename, with NO empty/`.`/`..` component, NO absolute or
    trailing/leading/repeated slash, NO underscore or leading dot (so NO hidden file/dir, NO `_test.go`,
    NO `_GOOS`/`_GOARCH` build-selection suffix, NO Fido control-name collision), NO directory named
    `testdata` or `vendor` (which `go build ./...` IGNORES).  A path is of ARBITRARY LENGTH — there is
    deliberately NO magic length cap (a numeric bound is not a correctness invariant, and a fixed limit is
    the fuel anti-pattern; if the host filesystem cannot materialize an over-long path that is a fail-loud
    runtime error, not a grammar restriction).  Every representable path is therefore DISCOVERED by
    `go build ./...` (the e2e additionally compares `go list ./...` to the emitted package set), independent
    of case-folding and platform source selection.  Strange-but-filesystem-valid paths are deliberately
    UNREPRESENTABLE — narrowness is the point, not an ambitious model of every OS path.

    Validity is intrinsic: [FilePath] carries the proof [path_ok fp_str = true], so a value cannot exist
    for a bad path.  Equality is decidable and reduces to string equality (the proof is unique by bool
    UIP).  [fp_parent] is the parent-directory identity used to group files into packages. *)
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

(** Directory names `go build ./...` IGNORES (so a file beneath one would be certified but never built):
    `testdata` at any level, and the `vendor` tree.  (Leading `.`/`_` dirs are already excluded by
    [component_ok] requiring a lowercase-letter first char.)  A DIRECTORY component must avoid these; a
    filename stem may still be `testdata`/`vendor` (e.g. [vendor.go]). *)
Definition reserved_dir (s : string) : bool := String.eqb s "testdata" || String.eqb s "vendor".

Definition dir_component_ok (s : string) : bool := component_ok s && negb (reserved_dir s).

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

(** the whole path: directory components (all but the last segment) are admissible AND not `go build`-
    ignored; the last segment is an admissible `.go` filename.  ARBITRARY LENGTH — no length cap (see the
    header: a numeric bound is not a correctness invariant).  A single segment (root-level file) is allowed. *)
Definition path_ok (s : string) : bool :=
  match rev (split_slash s) with
  | last :: rdirs => forallb dir_component_ok rdirs && filename_ok last
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

(** The canonical DIRECTORY-COMPONENT AUTHORITY over a parent path.  [split_slash] is the split view and
    its "/"-join is its inverse ([split_slash_concat]); a valid [dir_component_ok] directory component
    contains no separator, so it is a SINGLE component ([dir_component_ok_single]) and nonempty.  For a
    package key that is some file's [fp_parent], every directory component is nonempty
    ([parent_dir_components_nonempty]).  This is the lower-layer authority [GoCompile] composes for
    package import-path and executable-name reasoning — no character-level scan in the consumer. *)

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

Lemma concat_cons_empty : forall sep h t,
  String.concat sep (""%string :: h :: t) = (sep ++ String.concat sep (h :: t))%string.
Proof. reflexivity. Qed.

Lemma concat_map_head : forall sep c h t,
  String.concat sep (String c h :: t) = String c (String.concat sep (h :: t)).
Proof. intros sep c h t. destruct t as [|z t']; reflexivity. Qed.

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

Lemma is_lower_not_slash : forall c, is_lower c = true -> Ascii.eqb c "/"%char = false.
Proof.
  intros c H. destruct (Ascii.eqb c "/"%char) eqn:E; [| reflexivity].
  apply Ascii.eqb_eq in E; subst c. cbn in H. discriminate H.
Qed.

Lemma is_lower_digit_not_slash : forall c, is_lower_digit c = true -> Ascii.eqb c "/"%char = false.
Proof.
  intros c H. destruct (Ascii.eqb c "/"%char) eqn:E; [| reflexivity].
  apply Ascii.eqb_eq in E; subst c. cbn in H. discriminate H.
Qed.

Lemma tail_ok_single : forall s, tail_ok s = true -> split_slash s = [s].
Proof.
  induction s as [|c s IH]; intro H; [ reflexivity |].
  cbn [tail_ok] in H. apply Bool.andb_true_iff in H as [Hc Hs].
  cbn [split_slash]. rewrite (is_lower_digit_not_slash c Hc), (IH Hs). reflexivity.
Qed.

Lemma component_ok_single : forall s, component_ok s = true -> split_slash s = [s].
Proof.
  intros s H. destruct s as [|c s']; [ discriminate H |].
  cbn [component_ok] in H. apply Bool.andb_true_iff in H as [Hc Ht].
  cbn [split_slash]. rewrite (is_lower_not_slash c Hc), (tail_ok_single s' Ht). reflexivity.
Qed.

Lemma component_ok_nonempty : forall s, component_ok s = true -> s <> ""%string.
Proof. intros s H; destruct s; [ discriminate H | discriminate ]. Qed.

Lemma dir_component_ok_single : forall s, dir_component_ok s = true -> split_slash s = [s].
Proof.
  intros s H. unfold dir_component_ok in H. apply Bool.andb_true_iff in H as [Hc _].
  apply component_ok_single; exact Hc.
Qed.

Lemma dir_component_ok_nonempty : forall s, dir_component_ok s = true -> s <> ""%string.
Proof.
  intros s H. unfold dir_component_ok in H. apply Bool.andb_true_iff in H as [Hc _].
  apply component_ok_nonempty; exact Hc.
Qed.

(* the package DIRECTORY COMPONENTS of a key: the root key "" has none; else the split components. *)
Definition dir_components (dir : string) : list string :=
  if String.eqb dir ""%string then [] else split_slash dir.

Lemma dir_components_concat : forall dir, String.concat "/" (dir_components dir) = dir.
Proof.
  intro dir. unfold dir_components. destruct (String.eqb dir ""%string) eqn:E.
  - apply String.eqb_eq in E; subst dir; reflexivity.
  - apply split_slash_concat.
Qed.

Lemma parent_dir_components_nonempty : forall fp s,
  In s (dir_components (fp_parent fp)) -> s <> ""%string.
Proof.
  intros fp s Hin. unfold dir_components in Hin.
  destruct (String.eqb (fp_parent fp) ""%string) eqn:E; [ destruct Hin |].
  pose proof (fp_ok fp) as Hok. unfold path_ok in Hok.
  destruct (rev (split_slash (fp_str fp))) as [|lastc rdirs] eqn:Erev; [ discriminate Hok |].
  apply Bool.andb_true_iff in Hok as [Hdirs _].
  assert (Hpar : fp_parent fp = String.concat "/" (rev rdirs))
    by (unfold fp_parent, parent_of; rewrite Erev; reflexivity).
  assert (Hpne : fp_parent fp <> ""%string) by (intro Hc; rewrite Hc in E; cbn in E; discriminate E).
  assert (Hsingle : forall x, In x (rev rdirs) -> split_slash x = [x]).
  { intros x Hx. apply dir_component_ok_single. rewrite forallb_forall in Hdirs.
    apply Hdirs. apply in_rev in Hx. exact Hx. }
  assert (Hrne : rev rdirs <> []) by (intro Hc; apply Hpne; rewrite Hpar, Hc; reflexivity).
  rewrite Hpar in Hin. rewrite (split_concat_singles (rev rdirs) Hsingle Hrne) in Hin.
  apply dir_component_ok_nonempty. rewrite forallb_forall in Hdirs.
  apply Hdirs. apply in_rev in Hin. exact Hin.
Qed.

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
(* `go build ./...` ignores these directories, so they must be unrepresentable, not certified: *)
Example no_testdata     : path_ok "testdata/main.go" = false.   Proof. reflexivity. Qed.
Example no_testdata_nest : path_ok "a/testdata/x.go" = false.   Proof. reflexivity. Qed.
Example no_vendor       : path_ok "vendor/x.go" = false.        Proof. reflexivity. Qed.
Example ok_testdata_file : path_ok "testdata.go" = true.        Proof. reflexivity. Qed.
