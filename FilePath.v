(* The canonical relative source-path domain: a raw string is not a path, and a value carries its own proof. *)
From Stdlib Require Import String Ascii List Bool Eqdep_dec Arith.
Import ListNotations.

Definition is_lower (c : ascii) : bool :=
  let n := nat_of_ascii c in (97 <=? n) && (n <=? 122).

Definition is_lower_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in ((97 <=? n) && (n <=? 122)) || ((48 <=? n) && (n <=? 57)).

Fixpoint tail_ok (s : string) : bool :=
  match s with EmptyString => true | String c s' => is_lower_digit c && tail_ok s' end.

(* A component or basename stem: nonempty, first character lowercase, the rest lowercase or digit. *)
Definition component_ok (s : string) : bool :=
  match s with EmptyString => false | String c s' => is_lower c && tail_ok s' end.

(* A file beneath one of these directories would be certified and never built by `go build ./...`. *)
Definition reserved_dir (s : string) : bool := String.eqb s "testdata" || String.eqb s "vendor".

Definition dir_component_ok (s : string) : bool := component_ok s && negb (reserved_dir s).

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

(* An ordinary Go source basename: an admissible component stem followed by ".go". *)
Definition filename_ok (s : string) : bool := ends_go s && component_ok (strip_go s).

(* Every directory component is admissible and not ignored, and the last segment is an admissible `.go` name. *)
Definition path_ok (s : string) : bool :=
  match rev (split_slash s) with
  | last :: rdirs => forallb dir_component_ok rdirs && filename_ok last
  | [] => false
  end.

Record T : Type := Make { text : string ; valid : path_ok text = true }.

(* Validity proofs are unique (bool UIP), so equality reduces to the underlying string. *)
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

Definition parent_of (s : string) : string :=
  match rev (split_slash s) with
  | _ :: rdirs => String.concat "/" (rev rdirs)
  | [] => EmptyString
  end.

(* The parent directory of a file: files sharing one parent form one package. *)
Definition parent (p : T) : string := parent_of (text p).

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
  In s (dir_components (parent fp)) -> s <> ""%string.
Proof.
  intros fp s Hin. unfold dir_components in Hin.
  destruct (String.eqb (parent fp) ""%string) eqn:E; [ destruct Hin |].
  pose proof (valid fp) as Hok. unfold path_ok in Hok.
  destruct (rev (split_slash (text fp))) as [|lastc rdirs] eqn:Erev; [ discriminate Hok |].
  apply Bool.andb_true_iff in Hok as [Hdirs _].
  assert (Hpar : parent fp = String.concat "/" (rev rdirs))
    by (unfold parent, parent_of; rewrite Erev; reflexivity).
  assert (Hpne : parent fp <> ""%string) by (intro Hc; rewrite Hc in E; cbn in E; discriminate E).
  assert (Hsingle : forall x, In x (rev rdirs) -> split_slash x = [x]).
  { intros x Hx. apply dir_component_ok_single. rewrite forallb_forall in Hdirs.
    apply Hdirs. apply in_rev in Hx. exact Hx. }
  assert (Hrne : rev rdirs <> []) by (intro Hc; apply Hpne; rewrite Hpar, Hc; reflexivity).
  rewrite Hpar in Hin. rewrite (split_concat_singles (rev rdirs) Hsingle Hrne) in Hin.
  apply dir_component_ok_nonempty. rewrite forallb_forall in Hdirs.
  apply Hdirs. apply in_rev in Hin. exact Hin.
Qed.

(* The grammar's positive and negative fixtures, kernel-checked. *)

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
