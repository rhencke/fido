From Stdlib Require Import String List.
From Stdlib Require Import SetoidList.
From Fido Require Import FilePath Collections Names Syntax Compilable Render.
Import ListNotations.

Module FileMap := Syntax.FileMap.
Module FileFacts := Syntax.FileFacts.

(* Each source file rendered and keyed by its own path, so paths stay unique by construction. *)
Definition file_map_of (p : Syntax.Program) : FileMap.t string :=
  Syntax.map_file_values Render.file (Syntax.files p).
Definition module_file_of (p : Syntax.Program) : string :=
  Render.module_file (Syntax.module_spec p).
Definition entries_of (p : Syntax.Program) : list (string * string) :=
  List.map (fun kv => (FilePath.text (fst kv), snd kv)) (FileMap.elements (file_map_of p)).

(* the generic proof-carrying image: it retains the exact compiled root cp, evidence family, and evidence object *)
Polymorphic Inductive Image {p : Syntax.Program} (cp : Compilable.Program p)
  (Evidence : Compilable.Program p -> Type) (evidence : Evidence cp) : Type :=
| of_evidence : Image cp Evidence evidence.
Arguments of_evidence {p cp Evidence evidence}.

(* base emission: the no-additional-evidence instantiation over the exact cp *)
Definition CompiledOnly {p} (_ : Compilable.Program p) : Type := unit.
Definition of_compiled {p} (cp : Compilable.Program p) : Image cp CompiledOnly tt :=
  @of_evidence p cp CompiledOnly tt.

(* Transport renders ONLY the exact source index [p]; it never inspects [cp], evidence, Compilable, or Analysis. *)
Definition transport {p} {cp : Compilable.Program p} {Evidence : Compilable.Program p -> Type} {evidence : Evidence cp}
  (_ : Image cp Evidence evidence) : string * list (string * string) :=
  (module_file_of p, entries_of p).

(* base and evidence images retain their exact supplied cp and evidence, by construction of the type *)
Lemma base_retains_cp : forall p (cp : Compilable.Program p), of_compiled cp = @of_evidence p cp CompiledOnly tt.
Proof. reflexivity. Qed.

Lemma image_has_root : forall p (cp : Compilable.Program p) Evidence evidence (_ : @Image p cp Evidence evidence),
  exists cp' : Compilable.Program p, cp' = cp.
Proof. intros; exists cp; reflexivity. Qed.

(* transport of any image is exactly Render over its indexed source, and is independent of the attached evidence. *)
Lemma transport_is_render : forall p (cp : Compilable.Program p) Evidence evidence (img : @Image p cp Evidence evidence),
  transport img = (module_file_of p, entries_of p).
Proof. reflexivity. Qed.

Lemma transport_evidence_independent :
  forall p (cp : Compilable.Program p) E1 e1 E2 e2 (i1 : @Image p cp E1 e1) (i2 : @Image p cp E2 e2),
  transport i1 = transport i2.
Proof. reflexivity. Qed.

Lemma module_file_header : forall p, exists rest, module_file_of p = header ++ String nl_c rest.
Proof. intro p. unfold module_file_of. apply Render.module_file_first_line. Qed.

Lemma module_file_ascii : forall p, Names.str_ascii (module_file_of p) = true.
Proof. intro p. unfold module_file_of. apply Render.module_file_ascii. Qed.

Local Lemma entry_source : forall p k b,
  In (k, b) (FileMap.elements (file_map_of p)) -> exists sf, b = Render.file sf.
Proof.
  intros p k b Hin.
  assert (Hmt : FileMap.MapsTo k b (file_map_of p)).
  { apply FileFacts.elements_mapsto_iff, InA_alt. exists (k, b). split; [ split; reflexivity | exact Hin ]. }
  unfold file_map_of, Syntax.map_file_values in Hmt.
  apply FileFacts.map_mapsto_iff in Hmt. destruct Hmt as [ sf [ Hb _ ] ]. exists sf; exact Hb.
Qed.

Lemma entries_header : forall p path bytes,
  In (path, bytes) (entries_of p) -> exists rest, bytes = header ++ String nl_c rest.
Proof.
  intros p path bytes H.
  unfold entries_of in H. apply List.in_map_iff in H.
  destruct H as [ [k b] [Heq Hin] ]. cbn in Heq. injection Heq as _ Hb. subst bytes.
  destruct (entry_source p k b Hin) as [ sf -> ]. apply Render.file_first_line.
Qed.

Lemma entries_ascii : forall p path bytes,
  In (path, bytes) (entries_of p) -> Names.str_ascii bytes = true.
Proof.
  intros p path bytes H.
  unfold entries_of in H. apply List.in_map_iff in H.
  destruct H as [ [k b] [Heq Hin] ]. cbn in Heq. injection Heq as _ Hb. subst bytes.
  destruct (entry_source p k b Hin) as [ sf -> ]. apply Render.file_ascii.
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

Lemma entries_keys_nodup : forall p, NoDup (List.map fst (entries_of p)).
Proof.
  intro p.
  assert (Hrw : forall l : list (FileMap.key * string),
    List.map fst (List.map (fun kv => (FilePath.text (fst kv), snd kv)) l)
    = List.map FilePath.text (List.map fst l)).
  { induction l as [ | [k v] l' IH ]; simpl; [ reflexivity | rewrite IH; reflexivity ]. }
  unfold entries_of. rewrite Hrw.
  apply no_duplicates_map_inj; [ exact FilePath.equal | ].
  apply Collections.file_map_elements_keys_nodup.
Qed.

Local Lemma file_map_equal : forall fm1 fm2,
  Syntax.FilesEqual fm1 fm2 -> FileMap.Equal (FileMap.map Render.file fm1) (FileMap.map Render.file fm2).
Proof. intros fm1 fm2 Heq p. rewrite !FileFacts.map_o. rewrite (Heq p). reflexivity. Qed.

Local Lemma entries_equal : forall p1 p2,
  FileMap.Equal (file_map_of p1) (file_map_of p2) -> entries_of p1 = entries_of p2.
Proof.
  intros p1 p2 HEq. unfold entries_of.
  rewrite (Collections.file_elements_equal _ _ HEq). reflexivity.
Qed.

(* The transported bytes depend only on the module spec and the file contents, not on map order or evidence. *)
Theorem transport_order_independent :
  forall p1 (cp1 : Compilable.Program p1) E1 e1 (i1 : @Image p1 cp1 E1 e1)
         p2 (cp2 : Compilable.Program p2) E2 e2 (i2 : @Image p2 cp2 E2 e2),
  Syntax.module_spec p1 = Syntax.module_spec p2 ->
  Syntax.FilesEqual (Syntax.files p1) (Syntax.files p2) ->
  transport i1 = transport i2.
Proof.
  intros p1 cp1 E1 e1 i1 p2 cp2 E2 e2 i2 Hmod Hfiles.
  rewrite !transport_is_render. f_equal.
  - unfold module_file_of. rewrite Hmod. reflexivity.
  - apply entries_equal. unfold file_map_of, Syntax.map_file_values. apply file_map_equal. exact Hfiles.
Qed.
