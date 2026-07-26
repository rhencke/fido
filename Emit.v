(** Emit — the FINAL directory image and the public program emitter.

    [Image] is the COMPLETE generated module: the exact root `go.mod` bytes ([module_bytes]) PLUS a
    STANDARD `FilePath.T` finite map from paths to exact final `.go` bytes ([files :
    Collections.FileMap.t string] — the standard [FileMap.map Render.file] of the source map, NOT a custom
    `fmap`), together with an intrinsic PROVENANCE proof ([provenance]) that BOTH were produced by rendering
    one [Safe.Program] — the go.mod from its [ModuleSpec], the files from its raw program.  A CLOSED
    (assumption-free) proof does witness "these bytes are a certified rendered module"; but a proof can also
    be POSTULATED ([provenance] discharged by an [Axiom]/[Admitted] or a section [Variable]) — so the TYPE
    alone is NOT sufficient.  The real gate is the LIVE `Fido Materialize` transport boundary (there is no
    public `Fido Emit`), which before any effect (i)
    typechecks its argument's [transport] projection (rejecting a wrong-typed raw transport) and (ii)
    rejects any argument whose assumption closure is non-empty (rejecting an axiom/variable-backed proof).
    [make_image] is a public constructor demanding the provenance; [of_safe] is the canonical closed
    construction.  The fields stay reducible (no opaque module) so the command can evaluate them.

    `go.mod` is NOT a [FilePath.T] (it is not a `.go` source path — [FilePath.T] deliberately cannot represent
    it), so it is carried as a distinguished root field, not smuggled into the file map.  [transport] is
    the structured projection the filesystem sink consumes: the exact go.mod bytes plus the CANONICAL derived
    enumeration of the standard file map ([FileMap.elements], mapping each [FilePath.T] to [FilePath.text] and its
    contents) — a derived transport list, NOT a second identity authority.  EVERY
    image's go.mod AND every `.go` file begin with the header as their exact first line, are ASCII, and the
    on-disk `.go` paths are unique — proved for the whole type via the provenance.  The file map MAY be
    empty (a module-only program): there is NO nonemptiness claim. *)
From Stdlib Require Import String List.
From Stdlib Require Import SetoidList.
From Fido Require Import FilePath Collections ModulePath Version Syntax Compilable Safe Render.
Import ListNotations.

Module FileMap := Syntax.FileMap.
Module FileFacts := Syntax.FileFacts.

(** The raw rendered `.go` map of a safe program (internal): each source file rendered (package clause from
    its own [Syntax.package]), keyed by its path — the standard FileMap [map] of [Render.file] over the one
    source forest, so paths stay unique by construction (no re-keying). *)
Definition file_map (sp : Safe.Program) : FileMap.t string :=
  Syntax.map_file_values Render.file (Syntax.files (Safe.source sp)).

(** The rendered go.mod of a safe program (from its module spec). *)
Definition module_file (sp : Safe.Program) : string :=
  Render.module_file (Syntax.module_spec (Safe.source sp)).

(** The abstract image: the complete module (go.mod + `.go` map) that PROVABLY came from one Safe.Program. *)
Record Image : Type := make_image {
  module_bytes   : string;
  files : FileMap.t string;
  provenance     : exists sp, module_bytes = module_file sp /\ files = file_map sp
}.

(** The canonical construction (Safe.Program-gated by provenance).  [make_image] is also public but demands
    the provenance proof; the `Fido Materialize` command additionally rejects any image whose proof is axiomatic. *)
Definition of_safe (sp : Safe.Program) : Image :=
  make_image (module_file sp) (file_map sp) (ex_intro _ sp (conj eq_refl eq_refl)).

(** The transport projection: the exact go.mod bytes and the CANONICAL derived list of (on-disk `.go` path,
    contents) enumerated from the standard [FileMap.elements] (the ONE ordered enumeration, not a stored list). *)
Definition entries (img : Image) : list (string * string) :=
  List.map (fun kv => (FilePath.text (fst kv), snd kv)) (FileMap.elements (files img)).

Definition transport (img : Image) : string * list (string * string) :=
  (module_bytes img, entries img).

(** ---- go.mod facts (over EVERY Image, via provenance) ---- *)

(** The go.mod begins with the exact header AS THE FIRST LINE. *)
Lemma of_safe_module_file_header : forall img,
  exists rest, module_bytes img = header ++ String nl_c rest.
Proof.
  intro img. destruct (provenance img) as [ sp [ Hgm _ ] ].
  rewrite Hgm. unfold module_file. apply Render.module_file_first_line.
Qed.

(** The go.mod is ASCII. *)
Lemma of_safe_module_file_ascii : forall img, str_ascii (module_bytes img) = true.
Proof.
  intro img. destruct (provenance img) as [ sp [ Hgm _ ] ].
  rewrite Hgm. unfold module_file. apply Render.module_file_ascii.
Qed.

(** ---- `.go` file facts (over EVERY Image, via provenance) ---- *)

(** Every rendered map binding's bytes ARE [Render.file] of some source file (the standard-map [map] law). *)
Lemma entry_source : forall sp k b,
  In (k, b) (FileMap.elements (file_map sp)) -> exists sf, b = Render.file sf.
Proof.
  intros sp k b Hin.
  assert (Hmt : FileMap.MapsTo k b (file_map sp)).
  { apply FileFacts.elements_mapsto_iff, InA_alt. exists (k, b). split; [ split; reflexivity | exact Hin ]. }
  unfold file_map, Syntax.map_file_values in Hmt.
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
Lemma NoDup_map_inj {A B} (f : A -> B) :
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
Lemma NoDupA_eqk_map_fst {A} : forall l : list (FileMap.key * A),
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
  apply NoDup_map_inj; [ exact FilePath.equal | ].
  apply NoDupA_eqk_map_fst, FileMap.elements_3w.
Qed.

(** ---- rendering EXACTNESS + ORDER-INDEPENDENCE over the standard file map ---- *)

(** the rendered map has the SAME key domain as the source file map (the standard [map] preserves keys). *)
Lemma file_map_domain : forall sp p,
  FileMap.In p (file_map sp) <-> FileMap.In p (Syntax.files (Safe.source sp)).
Proof. intros sp p. unfold file_map, Syntax.map_file_values. apply FileFacts.map_in_iff. Qed.

(** every rendered binding is EXACTLY [Render.file] of the source at that path (the standard [map] law). *)
Lemma file_map_binding : forall sp p bytes,
  FileMap.MapsTo p bytes (file_map sp)
  <-> exists sf, bytes = Render.file sf /\ FileMap.MapsTo p sf (Syntax.files (Safe.source sp)).
Proof. intros sp p bytes. unfold file_map, Syntax.map_file_values. apply FileFacts.map_mapsto_iff. Qed.

(** [FilesEqual] source maps render to [FileMap.Equal] rendered maps — rendering respects semantic map equality. *)
Lemma file_map_Equal : forall fm1 fm2,
  Syntax.FilesEqual fm1 fm2 -> FileMap.Equal (FileMap.map Render.file fm1) (FileMap.map Render.file fm2).
Proof. intros fm1 fm2 Heq p. rewrite !FileFacts.map_o. rewrite (Heq p). reflexivity. Qed.

(** DIRECTORYIMAGE BRIDGE.  [Admissible] computes the fresh build PLAN over the [Syntax.Program]
    ([Compilable.root_layout] / [fresh_build_plan]); this bridge proves the later rendered [Image]
    REALIZES that same fresh root layout, closing the gap between the plan-over-program and the real emitted
    tree.  It lives HERE (Emit sits above Admissible) — [Admissible] imports neither Render nor Emit. ====== *)

(** the fresh ROOT LAYOUT recomputed from the rendered image's OWN `.go` file keys (its FilePaths). *)
Definition source_layout (img : Image) :=
  root_layout_of_keys (map fst (FileMap.elements (files img))).

(** the rendered image REALIZES the retained fresh root layout: recomputing the layout from the image's own
    keys equals [root_layout] over the source program (the render map preserves the FilePath.T key domain AND its
    canonical order — [Collections.file_map_fst_elements]). *)
Theorem realizes_fresh_layout : forall sp,
  source_layout (of_safe sp) = root_layout (Safe.source sp).
Proof.
  intro sp. unfold source_layout, of_safe; cbn [files].
  unfold file_map, Syntax.map_file_values.
  rewrite Collections.file_map_fst_elements.
  symmetry. apply root_layout_eq_of_keys.
Qed.

(** the image's `.go` file KEYS are EXACTLY the source program FilePaths (no missing key, NO extra entry);
    the go.mod bytes are a distinguished root FIELD ([module_bytes]), never a `.go` map entry. *)
Theorem files_are_source_paths : forall sp p,
  FileMap.In p (files (of_safe sp)) <-> FileMap.In p (Syntax.files (Safe.source sp)).
Proof. intros sp p. unfold of_safe; cbn [files]. apply file_map_domain. Qed.

(** the RETAINED-PLAN / IMAGE bridge.  A rendered image of a [Safe.Program] whose program is the
    one a [Compilable.Program] retained REALIZES that Compilable.Program's RETAINED root layout AND the retained
    build plan's output-target classification — not merely a freshly-recomputed [root_layout].  So the actual
    emitted tree is the exact object the compile decision reasoned about. *)

(** the rendered image realizes the Compilable.Program's RETAINED root layout ([Compilable.facts_root_layout]). *)
Theorem realizes_retained_layout : forall cp sp,
  Safe.source sp = Compilable.source cp ->
  source_layout (of_safe sp) = Compilable.facts_root_layout (Compilable.facts cp).
Proof.
  intros cp sp Hsp. rewrite realizes_fresh_layout, Hsp.
  symmetry. apply Compilable.facts_root_layout_ok.
Qed.

(** the IMAGE's output-target classification at the retained plan's default output name IS the retained plan's
    stored target — the fresh-image directory-collision check the plan performed is against the ACTUAL tree. *)
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

(** the CANONICAL derived transport list of two extensionally-equal rendered maps is EQUAL (the standard AVL
    [elements] is sorted, so it is a function of the map's meaning — [Collections.file_elements_Equal]). *)
Lemma entries_Equal : forall img1 img2,
  FileMap.Equal (files img1) (files img2) -> entries img1 = entries img2.
Proof.
  intros img1 img2 HEq. unfold entries.
  rewrite (Collections.file_elements_Equal _ _ HEq). reflexivity.
Qed.

(** the whole transport is INDEPENDENT of the original input-node order: two safe programs over the SAME
    module spec whose file maps are [FilesEqual] (e.g. built from permuted node lists) transport identically. *)
Theorem transport_order_independent : forall sp1 sp2,
  Syntax.module_spec (Safe.source sp1) = Syntax.module_spec (Safe.source sp2) ->
  Syntax.FilesEqual (Syntax.files (Safe.source sp1)) (Syntax.files (Safe.source sp2)) ->
  transport (of_safe sp1) = transport (of_safe sp2).
Proof.
  intros sp1 sp2 Hmod Hfiles. unfold transport. f_equal.
  - cbn [of_safe module_bytes]. unfold module_file. rewrite Hmod. reflexivity.
  - apply entries_Equal. cbn [of_safe files].
    unfold file_map, Syntax.map_file_values. apply file_map_Equal. exact Hfiles.
Qed.
