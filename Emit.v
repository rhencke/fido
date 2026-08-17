From Stdlib Require Import String List.
From Stdlib Require Import SetoidList.
From Fido Require Import FilePath Collections Names Syntax Safe Render.
Import ListNotations.

Module FileMap := Syntax.FileMap.
Module FileFacts := Syntax.FileFacts.

(* Each source file rendered and keyed by its own path, so paths stay unique by construction. *)
Definition file_map_of (p : Syntax.Program) : FileMap.t string :=
  Syntax.map_file_values Render.file (Syntax.files p).

Definition module_file_of (p : Syntax.Program) : string :=
  Render.module_file (Syntax.module_spec p).

(* Safety decides whether a program may be emitted, never its bytes: every byte is a pure source projection. *)
Definition file_map (sp : Safe.Program) : FileMap.t string := file_map_of (Safe.source sp).
Definition module_file (sp : Safe.Program) : string := module_file_of (Safe.source sp).
Definition entries (sp : Safe.Program) : list (string * string) :=
  List.map (fun kv => (FilePath.text (fst kv), snd kv)) (FileMap.elements (file_map sp)).

(* A sole-constructor witness carrying only the certified program: no forgeable byte, file-map, or origin field. *)
Inductive Image : Type := of_safe : Safe.Program -> Image.

Definition transport (img : Image) : string * list (string * string) :=
  match img with of_safe sp => (module_file sp, entries sp) end.

(* [of_safe] is the only route to an [Image]: every image is the image of some certified program. *)
Lemma of_safe_sole_route : forall img, exists sp, img = of_safe sp.
Proof. intros [sp]; exists sp; reflexivity. Qed.

(* Transport reduces, on any certified program, to the projected module bytes and file entries. *)
Lemma transport_reduces : forall sp, transport (of_safe sp) = (module_file sp, entries sp).
Proof. reflexivity. Qed.

Lemma module_file_header : forall sp,
  exists rest, module_file sp = header ++ String nl_c rest.
Proof. intro sp. unfold module_file, module_file_of. apply Render.module_file_first_line. Qed.

Lemma module_file_ascii : forall sp, Names.str_ascii (module_file sp) = true.
Proof. intro sp. unfold module_file, module_file_of. apply Render.module_file_ascii. Qed.

Local Lemma entry_source : forall sp k b,
  In (k, b) (FileMap.elements (file_map sp)) -> exists sf, b = Render.file sf.
Proof.
  intros sp k b Hin.
  assert (Hmt : FileMap.MapsTo k b (file_map sp)).
  { apply FileFacts.elements_mapsto_iff, InA_alt. exists (k, b). split; [ split; reflexivity | exact Hin ]. }
  unfold file_map, file_map_of, Syntax.map_file_values in Hmt.
  apply FileFacts.map_mapsto_iff in Hmt. destruct Hmt as [ sf [ Hb _ ] ]. exists sf; exact Hb.
Qed.

Lemma entries_header : forall sp path bytes,
  In (path, bytes) (entries sp) -> exists rest, bytes = header ++ String nl_c rest.
Proof.
  intros sp path bytes H.
  unfold entries in H. apply List.in_map_iff in H.
  destruct H as [ [k b] [Heq Hin] ]. cbn in Heq. injection Heq as _ Hb. subst bytes.
  destruct (entry_source sp k b Hin) as [ sf -> ]. apply Render.file_first_line.
Qed.

Lemma entries_ascii : forall sp path bytes,
  In (path, bytes) (entries sp) -> Names.str_ascii bytes = true.
Proof.
  intros sp path bytes H.
  unfold entries in H. apply List.in_map_iff in H.
  destruct H as [ [k b] [Heq Hin] ]. cbn in Heq. injection Heq as _ Hb. subst bytes.
  destruct (entry_source sp k b Hin) as [ sf -> ]. apply Render.file_ascii.
Qed.

Local Lemma no_duplicates_map_inj {A B} (f : A -> B) :
  (forall x y, f x = f y -> x = y) -> forall l, NoDup l -> NoDup (List.map f l).
Proof.
  intros Hinj l; induction l as [ | x l' IH ]; simpl; intro Hnd.
  - constructor.
  - inversion Hnd as [ | h t Hni Hnd' ]; subst. constructor.
    + intro Hin. apply List.in_map_iff in Hin as [ y [Hfy Hy] ].
      apply Hinj in Hfy; subst y; contradiction.
    + apply IH; exact Hnd'.
Qed.

Lemma entries_keys_nodup : forall sp,
  NoDup (List.map fst (entries sp)).
Proof.
  intro sp.
  assert (Hrw : forall l : list (FileMap.key * string),
    List.map fst (List.map (fun kv => (FilePath.text (fst kv), snd kv)) l)
    = List.map FilePath.text (List.map fst l)).
  { induction l as [ | [k v] l' IH ]; simpl; [ reflexivity | rewrite IH; reflexivity ]. }
  unfold entries. rewrite Hrw.
  apply no_duplicates_map_inj; [ exact FilePath.equal | ].
  apply Collections.file_map_elements_keys_nodup.
Qed.

Lemma file_map_binding : forall sp p bytes,
  FileMap.MapsTo p bytes (file_map sp)
  <-> exists sf, bytes = Render.file sf /\ FileMap.MapsTo p sf (Syntax.files (Safe.source sp)).
Proof. intros sp p bytes. unfold file_map, file_map_of, Syntax.map_file_values. apply FileFacts.map_mapsto_iff. Qed.

Local Lemma file_map_equal : forall fm1 fm2,
  Syntax.FilesEqual fm1 fm2 -> FileMap.Equal (FileMap.map Render.file fm1) (FileMap.map Render.file fm2).
Proof. intros fm1 fm2 Heq p. rewrite !FileFacts.map_o. rewrite (Heq p). reflexivity. Qed.

Local Lemma entries_equal : forall sp1 sp2,
  FileMap.Equal (file_map sp1) (file_map sp2) -> entries sp1 = entries sp2.
Proof.
  intros sp1 sp2 HEq. unfold entries.
  rewrite (Collections.file_elements_equal _ _ HEq). reflexivity.
Qed.

(* The transported bytes depend only on the module spec and the file contents, not on map order. *)
Theorem transport_order_independent : forall sp1 sp2,
  Syntax.module_spec (Safe.source sp1) = Syntax.module_spec (Safe.source sp2) ->
  Syntax.FilesEqual (Syntax.files (Safe.source sp1)) (Syntax.files (Safe.source sp2)) ->
  transport (of_safe sp1) = transport (of_safe sp2).
Proof.
  intros sp1 sp2 Hmod Hfiles. rewrite !transport_reduces. f_equal.
  - unfold module_file, module_file_of. rewrite Hmod. reflexivity.
  - apply entries_equal. unfold file_map, file_map_of, Syntax.map_file_values. apply file_map_equal. exact Hfiles.
Qed.
