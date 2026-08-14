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

(* Safety decides whether a program may be emitted, never what its bytes are. *)
Definition file_map (sp : Safe.Program) : FileMap.t string := file_map_of (Safe.source sp).
Definition module_file (sp : Safe.Program) : string := module_file_of (Safe.source sp).

(* The token is opaque and indexed by the exact program and bytes, and [issue] is its sole producer. *)
Module Type MINT.
  Parameter Token : Safe.Program -> string -> FileMap.t string -> Type.
  Parameter issue : forall sp, Token sp (module_file sp) (file_map sp).
  Parameter module_exact : forall sp m f, Token sp m f -> m = module_file sp.
  Parameter files_exact  : forall sp m f, Token sp m f -> f = file_map sp.
End MINT.

Module Mint : MINT.
  (* Rocq will not match a bare Inductive against a Parameter, so the representation keeps a private name *)
  Inductive TokenRepresentation (sp : Safe.Program) : string -> FileMap.t string -> Type :=
  | Issue : TokenRepresentation sp (module_file sp) (file_map sp).
  Definition Token (sp : Safe.Program) (m : string) (f : FileMap.t string) : Type :=
    TokenRepresentation sp m f.
  Definition issue sp : Token sp (module_file sp) (file_map sp) := Issue sp.
  Lemma module_exact : forall sp m f, Token sp m f -> m = module_file sp.
  Proof. intros sp m f tok. destruct tok. reflexivity. Qed.
  Lemma files_exact : forall sp m f, Token sp m f -> f = file_map sp.
  Proof. intros sp m f tok. destruct tok. reflexivity. Qed.
End Mint.

(* Exactness is derived from the retained token, so no supplied equality can stand in the mint's place. *)
Record Image : Type := Pack {
  safe         : Safe.Program ;
  module_bytes : string ;
  files        : FileMap.t string ;
  origin       : Mint.Token safe module_bytes files
}.

Theorem module_bytes_exact : forall img, module_bytes img = module_file (safe img).
Proof. intro img. exact (Mint.module_exact _ _ _ (origin img)). Qed.
Theorem files_are_exact : forall img, files img = file_map (safe img).
Proof. intro img. exact (Mint.files_exact _ _ _ (origin img)). Qed.

Definition of_safe (sp : Safe.Program) : Image :=
  Pack sp (module_file sp) (file_map sp) (Mint.issue sp).
Lemma of_safe_retains : forall sp, safe (of_safe sp) = sp.
Proof. reflexivity. Qed.
Lemma of_safe_module_bytes : forall sp, module_bytes (of_safe sp) = module_file sp.
Proof. reflexivity. Qed.
Lemma of_safe_files : forall sp, files (of_safe sp) = file_map sp.
Proof. reflexivity. Qed.

Definition entries (img : Image) : list (string * string) :=
  List.map (fun kv => (FilePath.text (fst kv), snd kv)) (FileMap.elements (files img)).

Definition transport (img : Image) : string * list (string * string) :=
  (module_bytes img, entries img).

Lemma of_safe_module_file_header : forall img,
  exists rest, module_bytes img = header ++ String nl_c rest.
Proof.
  intro img. rewrite (module_bytes_exact img).
  unfold module_file, module_file_of. apply Render.module_file_first_line.
Qed.

Lemma of_safe_module_file_ascii : forall img, Names.str_ascii (module_bytes img) = true.
Proof.
  intro img. rewrite (module_bytes_exact img).
  unfold module_file, module_file_of. apply Render.module_file_ascii.
Qed.

Local Lemma entry_source : forall sp k b,
  In (k, b) (FileMap.elements (file_map sp)) -> exists sf, b = Render.file sf.
Proof.
  intros sp k b Hin.
  assert (Hmt : FileMap.MapsTo k b (file_map sp)).
  { apply FileFacts.elements_mapsto_iff, InA_alt. exists (k, b). split; [ split; reflexivity | exact Hin ]. }
  unfold file_map, file_map_of, Syntax.map_file_values in Hmt.
  apply FileFacts.map_mapsto_iff in Hmt. destruct Hmt as [ sf [ Hb _ ] ]. exists sf; exact Hb.
Qed.

Lemma of_safe_header : forall img path bytes,
  In (path, bytes) (entries img) -> exists rest, bytes = header ++ String nl_c rest.
Proof.
  intros img path bytes H.
  unfold entries in H; rewrite (files_are_exact img) in H. apply List.in_map_iff in H.
  destruct H as [ [k b] [Heq Hin] ]. cbn in Heq. injection Heq as _ Hb. subst bytes.
  destruct (entry_source (safe img) k b Hin) as [ sf -> ]. apply Render.file_first_line.
Qed.

Lemma of_safe_ascii : forall img path bytes,
  In (path, bytes) (entries img) -> Names.str_ascii bytes = true.
Proof.
  intros img path bytes H.
  unfold entries in H; rewrite (files_are_exact img) in H. apply List.in_map_iff in H.
  destruct H as [ [k b] [Heq Hin] ]. cbn in Heq. injection Heq as _ Hb. subst bytes.
  destruct (entry_source (safe img) k b Hin) as [ sf -> ]. apply Render.file_ascii.
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

Lemma image_keys_nodup : forall img,
  NoDup (List.map fst (entries img)).
Proof.
  intro img.
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

Local Lemma entries_equal : forall img1 img2,
  FileMap.Equal (files img1) (files img2) -> entries img1 = entries img2.
Proof.
  intros img1 img2 HEq. unfold entries.
  rewrite (Collections.file_elements_equal _ _ HEq). reflexivity.
Qed.

Theorem transport_order_independent : forall sp1 sp2,
  Syntax.module_spec (Safe.source sp1) = Syntax.module_spec (Safe.source sp2) ->
  Syntax.FilesEqual (Syntax.files (Safe.source sp1)) (Syntax.files (Safe.source sp2)) ->
  transport (of_safe sp1) = transport (of_safe sp2).
Proof.
  intros sp1 sp2 Hmod Hfiles. unfold transport. f_equal.
  - rewrite !of_safe_module_bytes. unfold module_file, module_file_of. rewrite Hmod. reflexivity.
  - apply entries_equal. rewrite !of_safe_files.
    unfold file_map, file_map_of, Syntax.map_file_values. apply file_map_equal. exact Hfiles.
Qed.
