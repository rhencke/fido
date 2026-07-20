(** ============================================================================
    GoEmit — the FINAL directory image and the public program emitter.

    [DirectoryImage] is the COMPLETE generated module: the exact root `go.mod` bytes ([di_go_mod]) PLUS a
    STANDARD `FilePath` finite map from paths to exact final `.go` bytes ([di_go_files :
    Collections.FileMapBase.t string] — the standard [FM.map render_file] of the source map, NOT a custom
    `fmap`), together with an intrinsic PROVENANCE proof ([di_prov]) that BOTH were produced by rendering
    one [SafeProgram] — the go.mod from its [ModuleSpec], the files from its raw program.  A CLOSED
    (assumption-free) proof does witness "these bytes are a certified rendered module"; but a proof can also
    be POSTULATED ([di_prov] discharged by an [Axiom]/[Admitted] or a section [Variable]) — so the TYPE
    alone is NOT sufficient.  The real gate is the LIVE `Fido Materialize` transport boundary (there is no
    public `Fido Emit`), which before any effect (i)
    typechecks its argument's [di_transport] projection (rejecting a wrong-typed raw transport) and (ii)
    rejects any argument whose assumption closure is non-empty (rejecting an axiom/variable-backed proof).
    [mkImage] is a public constructor demanding the provenance; [render_program] is the canonical closed
    construction.  The fields stay reducible (no opaque module) so the command can evaluate them.

    `go.mod` is NOT a [FilePath] (it is not a `.go` source path — [FilePath] deliberately cannot represent
    it), so it is carried as a distinguished root field, not smuggled into the file map.  [di_transport] is
    the structured projection the filesystem sink consumes: the exact go.mod bytes plus the CANONICAL derived
    enumeration of the standard file map ([FileMap.elements], mapping each [FilePath] to [fp_string] and its
    contents) — a derived transport list, NOT a second identity authority.  EVERY
    image's go.mod AND every `.go` file begin with the header as their exact first line, are ASCII, and the
    on-disk `.go` paths are unique — proved for the whole type via the provenance.  The file map MAY be
    empty (a module-only program): there is NO nonemptiness claim.
    ============================================================================ *)
From Stdlib Require Import String List.
From Stdlib Require Import SetoidList.
From Fido Require Import FilePath Collections ModulePath GoVersion GoAST GoCompile GoSafe GoRender.
Import ListNotations.

Module FM := GoAST.FM.
Module FMF := GoAST.FMF.

(** The raw rendered `.go` map of a safe program (internal): each source file rendered (package clause from
    its own [source_package]), keyed by its path — the standard FileMap [map] of [render_file] over the one
    source forest, so paths stay unique by construction (no re-keying). *)
Definition render_map (sp : SafeProgram) : FM.t string :=
  GoAST.map_file_values render_file (prog_files (sp_program sp)).

(** The rendered go.mod of a safe program (from its module spec). *)
Definition render_go_mod_of (sp : SafeProgram) : string :=
  render_go_mod (prog_module (sp_program sp)).

(** The abstract image: the complete module (go.mod + `.go` map) that PROVABLY came from one SafeProgram. *)
Record DirectoryImage : Type := mkImage {
  di_go_mod   : string;
  di_go_files : FM.t string;
  di_prov     : exists sp, di_go_mod = render_go_mod_of sp /\ di_go_files = render_map sp
}.

(** The canonical construction (SafeProgram-gated by provenance).  [mkImage] is also public but demands
    the provenance proof; the `Fido Materialize` command additionally rejects any image whose proof is axiomatic. *)
Definition render_program (sp : SafeProgram) : DirectoryImage :=
  mkImage (render_go_mod_of sp) (render_map sp) (ex_intro _ sp (conj eq_refl eq_refl)).

(** The transport projection: the exact go.mod bytes and the CANONICAL derived list of (on-disk `.go` path,
    contents) enumerated from the standard [FileMap.elements] (the ONE ordered enumeration, not a stored list). *)
Definition di_go_file_entries (img : DirectoryImage) : list (string * string) :=
  List.map (fun kv => (fp_string (fst kv), snd kv)) (FM.elements (di_go_files img)).

Definition di_transport (img : DirectoryImage) : string * list (string * string) :=
  (di_go_mod img, di_go_file_entries img).

(** ---- go.mod facts (over EVERY DirectoryImage, via provenance) ---- *)

(** The go.mod begins with the exact header AS THE FIRST LINE. *)
Lemma render_program_go_mod_header : forall img,
  exists rest, di_go_mod img = header ++ String nl_c rest.
Proof.
  intro img. destruct (di_prov img) as [ sp [ Hgm _ ] ].
  rewrite Hgm. unfold render_go_mod_of. apply render_go_mod_first_line.
Qed.

(** The go.mod is ASCII. *)
Lemma render_program_go_mod_ascii : forall img, str_ascii (di_go_mod img) = true.
Proof.
  intro img. destruct (di_prov img) as [ sp [ Hgm _ ] ].
  rewrite Hgm. unfold render_go_mod_of. apply render_go_mod_ascii.
Qed.

(** ---- `.go` file facts (over EVERY DirectoryImage, via provenance) ---- *)

(** Every rendered map binding's bytes ARE [render_file] of some source file (the standard-map [map] law). *)
Lemma render_entry_source : forall sp k b,
  In (k, b) (FM.elements (render_map sp)) -> exists sf, b = render_file sf.
Proof.
  intros sp k b Hin.
  assert (Hmt : FM.MapsTo k b (render_map sp)).
  { apply FMF.elements_mapsto_iff, InA_alt. exists (k, b). split; [ split; reflexivity | exact Hin ]. }
  unfold render_map, GoAST.map_file_values in Hmt.
  apply FMF.map_mapsto_iff in Hmt. destruct Hmt as [ sf [ Hb _ ] ]. exists sf; exact Hb.
Qed.

(** Every emitted `.go` file's bytes begin with the exact header AS THE FIRST LINE. *)
Lemma render_program_header : forall img path bytes,
  In (path, bytes) (di_go_file_entries img) -> exists rest, bytes = header ++ String nl_c rest.
Proof.
  intros img path bytes H. destruct (di_prov img) as [ sp [ _ Hm ] ].
  unfold di_go_file_entries in H; rewrite Hm in H. apply List.in_map_iff in H.
  destruct H as [ [k b] [Heq Hin] ]. cbn in Heq. injection Heq as _ Hb. subst bytes.
  destruct (render_entry_source sp k b Hin) as [ sf -> ]. apply render_file_first_line.
Qed.

(** Every emitted `.go` file's bytes are ASCII (the source-owned package clause renders the ASCII `main`). *)
Lemma render_program_ascii : forall img path bytes,
  In (path, bytes) (di_go_file_entries img) -> str_ascii bytes = true.
Proof.
  intros img path bytes H. destruct (di_prov img) as [ sp [ _ Hm ] ].
  unfold di_go_file_entries in H; rewrite Hm in H. apply List.in_map_iff in H.
  destruct H as [ [k b] [Heq Hin] ]. cbn in Heq. injection Heq as _ Hb. subst bytes.
  destruct (render_entry_source sp k b Hin) as [ sf -> ]. apply render_file_ascii.
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
Lemma NoDupA_eqk_map_fst {A} : forall l : list (FM.key * A),
  NoDupA (@FM.eq_key A) l -> NoDup (List.map fst l).
Proof.
  induction l as [ | [k v] l' IH ]; simpl; intro H.
  - constructor.
  - inversion H as [ | a m Hni Hnd ]; subst. constructor.
    + intro Hin. apply List.in_map_iff in Hin. destruct Hin as [ [k' v'] [Hk Hin'] ].
      simpl in Hk; subst k'. apply Hni. apply InA_alt. exists (k, v').
      split; [ reflexivity | exact Hin' ].
    + apply IH; exact Hnd.
Qed.

Lemma render_image_keys_nodup : forall img,
  NoDup (List.map fst (di_go_file_entries img)).
Proof.
  intro img.
  assert (Hrw : forall l : list (FM.key * string),
    List.map fst (List.map (fun kv => (fp_string (fst kv), snd kv)) l)
    = List.map fp_string (List.map fst l)).
  { induction l as [ | [k v] l' IH ]; simpl; [ reflexivity | rewrite IH; reflexivity ]. }
  unfold di_go_file_entries. rewrite Hrw.
  apply NoDup_map_inj; [ exact fp_eq | ].
  apply NoDupA_eqk_map_fst, FM.elements_3w.
Qed.

(** ---- §9 rendering EXACTNESS + ORDER-INDEPENDENCE over the standard file map ---- *)

(** the rendered map has the SAME key domain as the source file map (the standard [map] preserves keys). *)
Lemma render_map_domain : forall sp p,
  FM.In p (render_map sp) <-> FM.In p (prog_files (sp_program sp)).
Proof. intros sp p. unfold render_map, GoAST.map_file_values. apply FMF.map_in_iff. Qed.

(** every rendered binding is EXACTLY [render_file] of the source at that path (the standard [map] law). *)
Lemma render_map_binding : forall sp p bytes,
  FM.MapsTo p bytes (render_map sp)
  <-> exists sf, bytes = render_file sf /\ FM.MapsTo p sf (prog_files (sp_program sp)).
Proof. intros sp p bytes. unfold render_map, GoAST.map_file_values. apply FMF.map_mapsto_iff. Qed.

(** [FilesEqual] source maps render to [FM.Equal] rendered maps — rendering respects semantic map equality. *)
Lemma render_map_Equal : forall fm1 fm2,
  GoAST.FilesEqual fm1 fm2 -> FM.Equal (FM.map render_file fm1) (FM.map render_file fm2).
Proof. intros fm1 fm2 Heq p. rewrite !FMF.map_o. rewrite (Heq p). reflexivity. Qed.

(** ============================================================================================================
    §8 — DIRECTORYIMAGE BRIDGE.  [GoCompile] computes the fresh build PLAN over the [GoProgram]
    ([GoCompile.root_layout] / [fresh_build_plan]); this bridge proves the later rendered [DirectoryImage]
    REALIZES that same fresh root layout, closing the gap between the plan-over-program and the real emitted
    tree.  It lives HERE (GoEmit sits above GoCompile) — [GoCompile] imports neither GoRender nor GoEmit. ====== *)

(** the fresh ROOT LAYOUT recomputed from the rendered image's OWN `.go` file keys (its FilePaths). *)
Definition image_source_layout (img : DirectoryImage) :=
  root_layout_of_keys (map fst (FM.elements (di_go_files img))).

(** §8 — the rendered image REALIZES the retained fresh root layout: recomputing the layout from the image's own
    keys equals [root_layout] over the source program (the render map preserves the FilePath key domain AND its
    canonical order — [Collections.filemap_map_fst_elements]). *)
Theorem directory_image_realizes_fresh_layout : forall sp,
  image_source_layout (render_program sp) = root_layout (sp_program sp).
Proof.
  intro sp. unfold image_source_layout, render_program; cbn [di_go_files].
  unfold render_map, GoAST.map_file_values.
  rewrite Collections.filemap_map_fst_elements.
  symmetry. apply root_layout_eq_of_keys.
Qed.

(** §8 — the image's `.go` file KEYS are EXACTLY the source program FilePaths (no missing key, NO extra entry);
    the go.mod bytes are a distinguished root FIELD ([di_go_mod]), never a `.go` map entry. *)
Theorem image_go_files_are_source_paths : forall sp p,
  FM.In p (di_go_files (render_program sp)) <-> FM.In p (prog_files (sp_program sp)).
Proof. intros sp p. unfold render_program; cbn [di_go_files]. apply render_map_domain. Qed.

(** ============================================================================================================
    §18J (CR2-D5) — the RETAINED-PLAN / IMAGE bridge.  A rendered image of a [SafeProgram] whose program is the
    one a [CompilableProgram] retained REALIZES that CompilableProgram's RETAINED root layout AND the retained
    build plan's output-target classification — not merely a freshly-recomputed [root_layout].  So the actual
    emitted tree is the exact object the compile decision reasoned about. ========================================= *)

(** the rendered image realizes the CompilableProgram's RETAINED root layout ([ef_root_layout]). *)
Theorem directory_image_realizes_retained_layout : forall cp sp,
  sp_program sp = cp_program cp ->
  image_source_layout (render_program sp) = ef_root_layout (cp_facts cp).
Proof.
  intros cp sp Hsp. rewrite directory_image_realizes_fresh_layout, Hsp.
  symmetry. apply ef_root_layout_ok.
Qed.

(** the IMAGE's output-target classification at the retained plan's default output name IS the retained plan's
    stored target — the fresh-image directory-collision check the plan performed is against the ACTUAL tree. *)
Theorem image_output_target_of_retained_plan : forall cp sp dir ip ex t,
  sp_program sp = cp_program cp ->
  ef_build_plan (cp_facts cp) = FBDWriteSingleMain dir ip ex t ->
  PM.find ex (image_source_layout (render_program sp)) = t.
Proof.
  intros cp sp dir ip ex t Hsp Hplan.
  rewrite directory_image_realizes_fresh_layout, Hsp.
  rewrite (ef_build_plan_ok (cp_facts cp)) in Hplan.
  symmetry. exact (fresh_build_plan_single_target (cp_program cp) dir ip ex t Hplan).
Qed.

(** the CANONICAL derived transport list of two extensionally-equal rendered maps is EQUAL (the standard AVL
    [elements] is sorted, so it is a function of the map's meaning — [Collections.filemap_elements_Equal]). *)
Lemma di_go_file_entries_Equal : forall img1 img2,
  FM.Equal (di_go_files img1) (di_go_files img2) -> di_go_file_entries img1 = di_go_file_entries img2.
Proof.
  intros img1 img2 HEq. unfold di_go_file_entries.
  rewrite (Collections.filemap_elements_Equal _ _ HEq). reflexivity.
Qed.

(** the whole transport is INDEPENDENT of the original input-node order: two safe programs over the SAME
    module spec whose file maps are [FilesEqual] (e.g. built from permuted node lists) transport identically. *)
Theorem di_transport_order_independent : forall sp1 sp2,
  prog_module (sp_program sp1) = prog_module (sp_program sp2) ->
  GoAST.FilesEqual (prog_files (sp_program sp1)) (prog_files (sp_program sp2)) ->
  di_transport (render_program sp1) = di_transport (render_program sp2).
Proof.
  intros sp1 sp2 Hmod Hfiles. unfold di_transport. f_equal.
  - cbn [render_program di_go_mod]. unfold render_go_mod_of. rewrite Hmod. reflexivity.
  - apply di_go_file_entries_Equal. cbn [render_program di_go_files].
    unfold render_map, GoAST.map_file_values. apply render_map_Equal. exact Hfiles.
Qed.
