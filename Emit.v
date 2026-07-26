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
    The raw [Mint.Token] constructor is PRIVATE and [Mint.issue] is the SOLE authority-producing operation
    (A006 / D-26).  [Image] is a REDUCIBLE carrier whose pack constructor requires that exact indexed
    authority: it is not a mint, and it cannot be applied to foreign bytes because the token's indices force
    the payload.  The byte fields stay reducible — which is the whole reason the authority, not the
    representation, is what gets sealed.

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

(** The raw rendered `.go` map of a SOURCE program (internal): each source file rendered (package clause from
    its own [Syntax.package]), keyed by its path — the standard FileMap [map] of [Render.file] over the one
    source forest, so paths stay unique by construction (no re-keying). *)
Definition file_map_of (p : Syntax.Program) : FileMap.t string :=
  Syntax.map_file_values Render.file (Syntax.files p).

(** The rendered go.mod of a SOURCE program (from its module spec). *)
Definition module_file_of (p : Syntax.Program) : string :=
  Render.module_file (Syntax.module_spec p).

(** …and the same two, read off a safe program.  Rendering depends on the SOURCE alone — safety decides
    WHETHER a program may be emitted, never WHAT its bytes are — so these are the source renderers applied
    to [Safe.source]. *)
Definition file_map (sp : Safe.Program) : FileMap.t string := file_map_of (Safe.source sp).
Definition module_file (sp : Safe.Program) : string := module_file_of (Safe.source sp).

(** ═══ THE MINT AUTHORITY (A006 / D-26) ═══ [Mint.Token] is OPAQUE and INDEXED by the exact
    [Safe.Program], the exact go.mod bytes and the exact `.go` map.  Its raw constructor never leaves this
    module, and [Mint.issue] is the SOLE authority-producing operation.

    Charter §22 originally asked for a private image CONSTRUCTOR.  That is impossible here: `Fido Materialize`
    kernel-reduces [transport img], and opaque module ascription removes the projection bodies that reduction
    needs (isolated by a `:` versus `<:` experiment during repair 17).  A006 moves the authority instead of the
    representation — the carrier below stays reducible, and its visible pack constructor is NOT a mint because
    it cannot be applied without an inhabitant of this indexed type. *)
Module Type MINT.
  Parameter Token : Safe.Program -> string -> FileMap.t string -> Type.
  Parameter issue : forall sp, Token sp (module_file sp) (file_map sp).
  Parameter module_exact : forall sp m f, Token sp m f -> m = module_file sp.
  Parameter files_exact  : forall sp m f, Token sp m f -> f = file_map sp.
End MINT.

Module Mint : MINT.
  (* Rocq will not match a bare [Inductive] against a `Parameter … : Type` ("a definition is expected"), so
     the representation keeps a distinct private name and [Token] is its alias — Rocq's own prescribed
     workaround, already used by [Index.Snapshot].  The topology is unchanged: [Issue] stays private. *)
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

(** The REDUCIBLE transport carrier.  It retains the exact certificate, the exact bytes, and the exact token
    that authorizes them.  There are no separate equality-proof fields: exactness is DERIVED from the retained
    token, so no independently supplied equality can stand where the one mint authority belongs. *)
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

(** provenance is a PROJECTION of the retained certificate and its token, not an existential a caller supplied. *)
Theorem provenance : forall img : Image,
  exists sp, module_bytes img = module_file sp /\ files img = file_map sp.
Proof. intro img. exists (safe img). split; [ apply module_bytes_exact | apply files_are_exact ]. Qed.

(** the canonical production packer. *)
Definition of_safe (sp : Safe.Program) : Image :=
  Pack sp (module_file sp) (file_map sp) (Mint.issue sp).
Lemma of_safe_retains : forall sp, safe (of_safe sp) = sp.
Proof. reflexivity. Qed.
Lemma of_safe_module_bytes : forall sp, module_bytes (of_safe sp) = module_file sp.
Proof. reflexivity. Qed.
Lemma of_safe_files : forall sp, files (of_safe sp) = file_map sp.
Proof. reflexivity. Qed.

(** the SAME authority, transported along the exact source equality.  Not a second mint: it demands the exact
    [Safe.Program] and issues nothing — [Mint.issue sp] is moved, inside the never-forced [origin] field, to
    the index the caller already proved equal.  The bytes are stored directly from [p] so the transport does
    not have to force the capability's source to reduce. *)
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

(** The transport projection: the exact go.mod bytes and the CANONICAL derived list of (on-disk `.go` path,
    contents) enumerated from the standard [FileMap.elements] (the ONE ordered enumeration, not a stored list). *)
Definition entries (img : Image) : list (string * string) :=
  List.map (fun kv => (FilePath.text (fst kv), snd kv)) (FileMap.elements (files img)).

Definition transport (img : Image) : string * list (string * string) :=
  (module_bytes img, entries img).

(** the transported form emits the SAME bytes and the SAME entries as the canonical one — the source
    equality is the only thing that moved, so nothing about the emitted artifact depends on which spelling of
    the certificate's source the caller had in hand. *)
Lemma of_safe_at_transport : forall sp p H, transport (of_safe_at sp p H) = transport (of_safe sp).
Proof.
  intros sp p H. unfold transport, entries.
  rewrite of_safe_at_module_bytes, of_safe_at_files, of_safe_module_bytes, of_safe_files.
  unfold module_file, file_map. rewrite H. reflexivity.
Qed.

(** ---- go.mod facts (over EVERY Image, via provenance) ---- *)

(** The go.mod begins with the exact header AS THE FIRST LINE. *)
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

(** ---- `.go` file facts (over EVERY Image, via provenance) ---- *)

(** Every rendered map binding's bytes ARE [Render.file] of some source file (the standard-map [map] law). *)
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

(** ---- rendering EXACTNESS + ORDER-INDEPENDENCE over the standard file map ---- *)

(** the rendered map has the SAME key domain as the source file map (the standard [map] preserves keys). *)
Lemma file_map_domain : forall sp p,
  FileMap.In p (file_map sp) <-> FileMap.In p (Syntax.files (Safe.source sp)).
Proof. intros sp p. unfold file_map, file_map_of, Syntax.map_file_values. apply FileFacts.map_in_iff. Qed.

(** every rendered binding is EXACTLY [Render.file] of the source at that path (the standard [map] law). *)
Lemma file_map_binding : forall sp p bytes,
  FileMap.MapsTo p bytes (file_map sp)
  <-> exists sf, bytes = Render.file sf /\ FileMap.MapsTo p sf (Syntax.files (Safe.source sp)).
Proof. intros sp p bytes. unfold file_map, file_map_of, Syntax.map_file_values. apply FileFacts.map_mapsto_iff. Qed.

(** [FilesEqual] source maps render to [FileMap.Equal] rendered maps — rendering respects semantic map equality. *)
Lemma file_map_equal : forall fm1 fm2,
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
  intro sp. unfold source_layout. rewrite of_safe_files.
  unfold file_map, file_map_of, Syntax.map_file_values.
  rewrite Collections.file_map_fst_elements.
  symmetry. apply root_layout_eq_of_keys.
Qed.

(** the image's `.go` file KEYS are EXACTLY the source program FilePaths (no missing key, NO extra entry);
    the go.mod bytes are a distinguished root FIELD ([module_bytes]), never a `.go` map entry. *)
Theorem files_are_source_paths : forall sp p,
  FileMap.In p (files (of_safe sp)) <-> FileMap.In p (Syntax.files (Safe.source sp)).
Proof. intros sp p. rewrite of_safe_files. apply file_map_domain. Qed.

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
    [elements] is sorted, so it is a function of the map's meaning — [Collections.file_elements_equal]). *)
Lemma entries_equal : forall img1 img2,
  FileMap.Equal (files img1) (files img2) -> entries img1 = entries img2.
Proof.
  intros img1 img2 HEq. unfold entries.
  rewrite (Collections.file_elements_equal _ _ HEq). reflexivity.
Qed.

(** the whole transport is INDEPENDENT of the original input-node order: two safe programs over the SAME
    module spec whose file maps are [FilesEqual] (e.g. built from permuted node lists) transport identically. *)
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

(** ═══ §10.1 THE ACCEPTED PATH, END TO END, THROUGH THE RETURNED CAPABILITY ═══ the capability the compiler
    returned is the one safety certifies, and the image is minted from THAT certificate and publishes exactly
    its bytes.  Every step holds by [reflexivity] — there is nothing to reconstruct between [compile] and the
    emitted bytes. *)
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
