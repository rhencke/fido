(** The final directory image: exact go.mod bytes, a path-keyed map of `.go` bytes, and their provenance. *)
From Stdlib Require Import String List.
From Stdlib Require Import SetoidList.
From Fido Require Import FilePath Collections ModulePath Version Syntax Compilable Safe Render.
Import ListNotations.

Module FileMap := Syntax.FileMap.
Module FileFacts := Syntax.FileFacts.

(** Each source file rendered and keyed by its own path, so paths stay unique by construction. *)
Definition file_map_of (p : Syntax.Program) : FileMap.t string :=
  Syntax.map_file_values Render.file (Syntax.files p).

(** The rendered go.mod of a source program, from its module spec. *)
Definition module_file_of (p : Syntax.Program) : string :=
  Render.module_file (Syntax.module_spec p).

(** Safety decides whether a program may be emitted, never what its bytes are. *)
Definition file_map (sp : Safe.Program) : FileMap.t string := file_map_of (Safe.source sp).
Definition module_file (sp : Safe.Program) : string := module_file_of (Safe.source sp).

(** The token is opaque and indexed by the exact program and bytes, and [issue] is its sole producer. *)
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

(** Exactness is derived from the retained token, so no supplied equality can stand in the mint's place. *)
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

(** Provenance is a projection of the retained token, not an existential the caller supplied. *)
Theorem provenance : forall img : Image,
  exists sp, module_bytes img = module_file sp /\ files img = file_map sp.
Proof. intro img. exists (safe img). split; [ apply module_bytes_exact | apply files_are_exact ]. Qed.

(** The canonical production packer. *)
Definition of_safe (sp : Safe.Program) : Image :=
  Pack sp (module_file sp) (file_map sp) (Mint.issue sp).
Lemma of_safe_retains : forall sp, safe (of_safe sp) = sp.
Proof. reflexivity. Qed.
Lemma of_safe_module_bytes : forall sp, module_bytes (of_safe sp) = module_file sp.
Proof. reflexivity. Qed.
Lemma of_safe_files : forall sp, files (of_safe sp) = file_map sp.
Proof. reflexivity. Qed.

(** The same authority transported along the exact source equality; it issues nothing of its own. *)
Definition of_safe_at (sp : Safe.Program) (p : Syntax.Program) (H : Safe.source sp = p) : Image :=
  Pack sp (module_file_of p) (file_map_of p)
    (eq_rect (Safe.source sp) (fun q => Mint.Token sp (module_file_of q) (file_map_of q))
             (Mint.issue sp) p H).
Lemma of_safe_at_retains : forall sp p H, safe (of_safe_at sp p H) = sp.
Proof. reflexivity. Qed.
Lemma of_safe_at_module_bytes : forall sp p H, module_bytes (of_safe_at sp p H) = module_file_of p.
Proof. reflexivity. Qed.
Lemma of_safe_at_files : forall sp p H, files (of_safe_at sp p H) = file_map_of p.
Proof. reflexivity. Qed.
Lemma of_safe_at_refl : forall sp, of_safe_at sp (Safe.source sp) eq_refl = of_safe sp.
Proof. reflexivity. Qed.

(** The transport projection: the go.mod bytes and the derived enumeration of path and contents. *)
Definition entries (img : Image) : list (string * string) :=
  List.map (fun kv => (FilePath.text (fst kv), snd kv)) (FileMap.elements (files img)).

Definition transport (img : Image) : string * list (string * string) :=
  (module_bytes img, entries img).

(** The transported form emits the same bytes and entries, so only the source equality moved. *)
Lemma of_safe_at_transport : forall sp p H, transport (of_safe_at sp p H) = transport (of_safe sp).
Proof.
  intros sp p H. unfold transport, entries.
  rewrite of_safe_at_module_bytes, of_safe_at_files, of_safe_module_bytes, of_safe_files.
  unfold module_file, file_map. rewrite H. reflexivity.
Qed.

(** The go.mod begins with the exact header as its first line. *)
Lemma of_safe_module_file_header : forall img,
  exists rest, module_bytes img = header ++ String nl_c rest.
Proof.
  intro img. destruct (provenance img) as [ sp [ Hgm _ ] ].
  rewrite Hgm. unfold module_file, module_file_of. apply Render.module_file_first_line.
Qed.

(** The go.mod is ASCII. *)
Lemma of_safe_module_file_ascii : forall img, str_ascii (module_bytes img) = true.
Proof.
  intro img. destruct (provenance img) as [ sp [ Hgm _ ] ].
  rewrite Hgm. unfold module_file, module_file_of. apply Render.module_file_ascii.
Qed.

(** Every rendered binding's bytes are [Render.file] of some source file. *)
Lemma entry_source : forall sp k b,
  In (k, b) (FileMap.elements (file_map sp)) -> exists sf, b = Render.file sf.
Proof.
  intros sp k b Hin.
  assert (Hmt : FileMap.MapsTo k b (file_map sp)).
  { apply FileFacts.elements_mapsto_iff, InA_alt. exists (k, b). split; [ split; reflexivity | exact Hin ]. }
  unfold file_map, file_map_of, Syntax.map_file_values in Hmt.
  apply FileFacts.map_mapsto_iff in Hmt. destruct Hmt as [ sf [ Hb _ ] ]. exists sf; exact Hb.
Qed.

(** Every emitted `.go` file's bytes begin with the exact header AS THE FIRST LINE. *)
Lemma of_safe_header : forall img path bytes,
  In (path, bytes) (entries img) -> exists rest, bytes = header ++ String nl_c rest.
Proof.
  intros img path bytes H. destruct (provenance img) as [ sp [ _ Hm ] ].
  unfold entries in H; rewrite Hm in H. apply List.in_map_iff in H.
  destruct H as [ [k b] [Heq Hin] ]. cbn in Heq. injection Heq as _ Hb. subst bytes.
  destruct (entry_source sp k b Hin) as [ sf -> ]. apply Render.file_first_line.
Qed.

(** Every emitted `.go` file's bytes are ASCII (the source-owned package clause renders the ASCII `main`). *)
Lemma of_safe_ascii : forall img path bytes,
  In (path, bytes) (entries img) -> str_ascii bytes = true.
Proof.
  intros img path bytes H. destruct (provenance img) as [ sp [ _ Hm ] ].
  unfold entries in H; rewrite Hm in H. apply List.in_map_iff in H.
  destruct H as [ [k b] [Heq Hin] ]. cbn in Heq. injection Heq as _ Hb. subst bytes.
  destruct (entry_source sp k b Hin) as [ sf -> ]. apply Render.file_ascii.
Qed.

(** Duplicate on-disk `.go` paths are impossible in any image. *)
Lemma no_duplicates_map_inj {A B} (f : A -> B) :
  (forall x y, f x = f y -> x = y) -> forall l, NoDup l -> NoDup (List.map f l).
Proof.
  intros Hinj l; induction l as [ | x l' IH ]; simpl; intro Hnd.
  - constructor.
  - inversion Hnd as [ | h t Hni Hnd' ]; subst. constructor.
    + intro Hin. apply List.in_map_iff in Hin as [ y [Hfy Hy] ].
      apply Hinj in Hfy; subst y; contradiction.
    + apply IH; exact Hnd'.
Qed.

(** The standard-map [elements] have key-distinct bindings ([elements_3w]), so their key list is [NoDup]. *)
Lemma no_duplicates_setoid_key_map_fst {A} : forall l : list (FileMap.key * A),
  NoDupA (@FileMap.eq_key A) l -> NoDup (List.map fst l).
Proof.
  induction l as [ | [k v] l' IH ]; simpl; intro H.
  - constructor.
  - inversion H as [ | a m Hni Hnd ]; subst. constructor.
    + intro Hin. apply List.in_map_iff in Hin. destruct Hin as [ [k' v'] [Hk Hin'] ].
      simpl in Hk; subst k'. apply Hni. apply InA_alt. exists (k, v').
      split; [ reflexivity | exact Hin' ].
    + apply IH; exact Hnd.
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
  apply Compilable.no_duplicates_map_inj; [ exact FilePath.equal | ].
  apply no_duplicates_setoid_key_map_fst, FileMap.elements_3w.
Qed.

(** The rendered map has the same key domain as the source file map. *)
Lemma file_map_domain : forall sp p,
  FileMap.In p (file_map sp) <-> FileMap.In p (Syntax.files (Safe.source sp)).
Proof. intros sp p. unfold file_map, file_map_of, Syntax.map_file_values. apply FileFacts.map_in_iff. Qed.

(** Every rendered binding is exactly [Render.file] of the source at that path. *)
Lemma file_map_binding : forall sp p bytes,
  FileMap.MapsTo p bytes (file_map sp)
  <-> exists sf, bytes = Render.file sf /\ FileMap.MapsTo p sf (Syntax.files (Safe.source sp)).
Proof. intros sp p bytes. unfold file_map, file_map_of, Syntax.map_file_values. apply FileFacts.map_mapsto_iff. Qed.

(** Rendering respects semantic map equality. *)
Lemma file_map_equal : forall fm1 fm2,
  Syntax.FilesEqual fm1 fm2 -> FileMap.Equal (FileMap.map Render.file fm1) (FileMap.map Render.file fm2).
Proof. intros fm1 fm2 Heq p. rewrite !FileFacts.map_o. rewrite (Heq p). reflexivity. Qed.

(** The fresh root layout recomputed from the rendered image's own file keys. *)
Definition source_layout (img : Image) :=
  root_layout_of_keys (map fst (FileMap.elements (files img))).

(** Recomputing the layout from the image's own keys equals the layout over the source program. *)
Theorem realizes_fresh_layout : forall sp,
  source_layout (of_safe sp) = root_layout (Safe.source sp).
Proof.
  intro sp. unfold source_layout. rewrite of_safe_files.
  unfold file_map, file_map_of, Syntax.map_file_values.
  rewrite Collections.file_map_fst_elements.
  symmetry. apply root_layout_eq_of_keys.
Qed.

(** The image's file keys are exactly the source program's paths, with no missing and no extra entry. *)
Theorem files_are_source_paths : forall sp p,
  FileMap.In p (files (of_safe sp)) <-> FileMap.In p (Syntax.files (Safe.source sp)).
Proof. intros sp p. rewrite of_safe_files. apply file_map_domain. Qed.

(** The emitted tree realizes the retained layout, so it is the exact object the compile decision read. *)
Theorem realizes_retained_layout : forall cp sp,
  Safe.source sp = Compilable.source cp ->
  source_layout (of_safe sp) = Compilable.facts_root_layout (Compilable.facts cp).
Proof.
  intros cp sp Hsp. rewrite realizes_fresh_layout, Hsp.
  symmetry. apply Compilable.facts_root_layout_ok.
Qed.

(** The image's output-target classification is the retained plan's, so the collision check read this tree. *)
Theorem output_target_of_retained_plan : forall cp sp dir ip ex t,
  Safe.source sp = Compilable.source cp ->
  Compilable.build_plan (Compilable.facts cp) = Compilable.WriteSingleMain dir ip ex t ->
  PackageMap.find ex (source_layout (of_safe sp)) = t.
Proof.
  intros cp sp dir ip ex t Hsp Hplan.
  rewrite realizes_fresh_layout, Hsp.
  rewrite (Compilable.build_plan_ok (Compilable.facts cp)) in Hplan.
  symmetry. exact (fresh_build_plan_single_target (Compilable.source cp) dir ip ex t Hplan).
Qed.

(** Two extensionally equal rendered maps derive the same transport list. *)
Lemma entries_equal : forall img1 img2,
  FileMap.Equal (files img1) (files img2) -> entries img1 = entries img2.
Proof.
  intros img1 img2 HEq. unfold entries.
  rewrite (Collections.file_elements_equal _ _ HEq). reflexivity.
Qed.

(** The transport is independent of the original input-node order. *)
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

(** The accepted path end to end: every step holds by reflexivity, so nothing is reconstructed. *)
Theorem accepted_path_emits_from_returned_capability : forall p (H : Compilable.Admissible p),
  exists cp Hcp,
    Compilable.compile p = Compilable.Compiled cp Hcp
    (* safety wraps the SAME capability and the SAME retained core *)
    /\ Safe.compiled (Safe.certify cp) = cp
    /\ Safe.core (Safe.certify cp) = Compilable.core (Safe.compiled (Safe.certify cp))
    /\ Safe.source (Safe.certify cp) = Compilable.source (Safe.compiled (Safe.certify cp))
    (* and the image retains that exact certificate and publishes exactly its bytes *)
    /\ safe (of_safe (Safe.certify cp)) = Safe.certify cp
    /\ module_bytes (of_safe (Safe.certify cp)) = module_file (Safe.certify cp)
    /\ files (of_safe (Safe.certify cp)) = file_map (Safe.certify cp).
Proof.
  intros p H. destruct (Compilable.compile_complete p H) as [cp [Hcp Hc]].
  exists cp, Hcp.
  split; [ exact Hc | ].
  split; [ exact (Safe.certify_retains cp) | ].
  repeat split; reflexivity.
Qed.

(** The same path on a concrete program, destructing the fixture once so one capability carries throughout. *)
Theorem deep_nested_emit_fixture :
  exists cp Hcp,
    Compilable.compile Compilable.deep_nested_program = Compilable.Compiled cp Hcp
    (* the ONE accepted root fixture, over THIS capability *)
    /\ Compilable.AcceptedFixture cp Hcp
    (* safety certifies THAT capability and retains its exact core *)
    /\ Safe.compiled (Safe.certify cp) = cp
    (* spelled through [Safe.compiled] because [Safe.core]'s type is indexed by [Safe.source] *)
    /\ Safe.core (Safe.certify cp) = Compilable.core (Safe.compiled (Safe.certify cp))
    /\ Safe.source (Safe.certify cp) = Compilable.source cp
    (* and the image is minted from THAT certificate and publishes exactly its bytes *)
    /\ safe (of_safe (Safe.certify cp)) = Safe.certify cp
    /\ module_bytes (of_safe (Safe.certify cp)) = module_file (Safe.certify cp)
    /\ files (of_safe (Safe.certify cp)) = file_map (Safe.certify cp).
Proof.
  destruct Compilable.deep_nested_compile_fixture as [cp [Hcp [Hc Hfix]]].
  exists cp, Hcp.
  split; [ exact Hc | ].
  split; [ exact Hfix | ].
  split; [ exact (Safe.certify_retains cp) | ].
  split; [ reflexivity | ].
  split; [ exact (Safe.certify_source cp) | ].
  repeat split; reflexivity.
Qed.
