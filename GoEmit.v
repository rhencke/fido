(** ============================================================================
    GoEmit — the FINAL directory image and the public program emitter.

    [DirectoryImage] is a TRUE finite map from unique intrinsic paths to exact final file bytes
    ([di_map : fmap FilePath string]) PLUS an intrinsic PROVENANCE proof ([di_prov]) that the map was
    produced by rendering a [SafeProgram].  A CLOSED (assumption-free) proof does witness "these contents
    are a certified rendered program"; but a proof can also be POSTULATED — [di_prov] may be discharged by
    an [Axiom]/[Admitted] or a section [Variable] — so the TYPE alone is NOT sufficient: an arbitrary map
    can be given a well-typed but axiomatic image.  The real gate is therefore the LIVE Fido Emit boundary,
    which before any effect (i) typechecks its argument AS a [DirectoryImage] (rejecting a wrong-typed raw
    transport) and (ii) rejects any argument whose assumption closure is non-empty (rejecting an
    axiom/variable-backed proof).  [mkImage] is a public constructor demanding [pf : exists sp, m =
    render_map sp]; [render_program] is the canonical, closed construction.  The map stays reducible (no
    opaque module) so the command can evaluate it after the guards pass.

    [directory_entries] is the transport projection the filesystem sink consumes: the intrinsic keys are
    denoted to on-disk relative-path strings ([fp_string], injective).  EVERY DirectoryImage's entries
    begin with the header as their exact first line, are ASCII, are nonempty, and have unique on-disk
    paths — proved for the whole type via the provenance.
    ============================================================================ *)
From Stdlib Require Import String List.
From Fido Require Import FilePath FMap GoAST GoCompile GoSafe GoRender.
Import ListNotations.

(** The raw rendered map of a safe program (internal). *)
Definition render_map (sp : SafeProgram) : fmap FilePath string :=
  fm_map (render_file (sp_pkg_name sp)) (prog_files (sp_program sp)).

(** The abstract image: a finite map that PROVABLY came from rendering a SafeProgram. *)
Record DirectoryImage : Type := mkImage {
  di_map  : fmap FilePath string;
  di_prov : exists sp, di_map = render_map sp
}.

(** The canonical construction of an image (SafeProgram-gated by the provenance proof).  [mkImage] is
    also public but demands the provenance proof; the Fido Emit command additionally rejects any image
    whose proof is axiomatic, so neither is a forgery escape. *)
Definition render_program (sp : SafeProgram) : DirectoryImage :=
  mkImage (render_map sp) (ex_intro _ sp eq_refl).

(** The transport projection: intrinsic keys denoted to on-disk path strings for the sink. *)
Definition directory_entries (img : DirectoryImage) : list (string * string) :=
  List.map (fun kv => (fp_string (fst kv), snd kv)) (fm_list (di_map img)).

(** ---- the compiler-derived package name is `main` (from the compile proof) ---- *)

Lemma sp_pkg_name_main : forall sp, sp_pkg_name sp = "main"%string.
Proof. intro sp; unfold sp_pkg_name; exact (proj1 (cp_ok (sp_compiled sp))). Qed.

(** ---- image facts (over EVERY DirectoryImage, via provenance) ---- *)

Lemma render_map_list : forall sp,
  fm_list (render_map sp)
  = List.map (fun kv => (fst kv, render_file (sp_pkg_name sp) (snd kv))) (prog_entries (sp_program sp)).
Proof. reflexivity. Qed.

(** Every emitted file's bytes begin with the exact header AS THE FIRST LINE. *)
Lemma render_program_header : forall img path bytes,
  In (path, bytes) (directory_entries img) -> exists rest, bytes = header ++ String nl_c rest.
Proof.
  intros [ m [ sp Hm ] ] path bytes H. unfold directory_entries in H; simpl in H. subst m.
  rewrite render_map_list, List.map_map in H. apply List.in_map_iff in H.
  destruct H as [ [k f] [Heq _] ]. simpl in Heq. injection Heq as _ Hb. subst bytes.
  apply render_file_first_line.
Qed.

(** Every emitted file's bytes are ASCII (the derived package name `main` is ASCII). *)
Lemma render_program_ascii : forall img path bytes,
  In (path, bytes) (directory_entries img) -> str_ascii bytes = true.
Proof.
  intros [ m [ sp Hm ] ] path bytes H. unfold directory_entries in H; simpl in H. subst m.
  rewrite render_map_list, List.map_map in H. apply List.in_map_iff in H.
  destruct H as [ [k f] [Heq _] ]. simpl in Heq. injection Heq as _ Hb. subst bytes.
  apply render_file_ascii. rewrite sp_pkg_name_main. reflexivity.
Qed.

(** Every image is nonempty (the program is nonempty by construction). *)
Lemma render_program_nonempty : forall img, directory_entries img <> [].
Proof.
  intros [ m [ sp Hm ] ]. unfold directory_entries; simpl. subst m.
  rewrite render_map_list, List.map_map.
  intro H. apply List.map_eq_nil in H. exact (prog_nonempty (sp_program sp) H).
Qed.

(** Duplicate on-disk paths are impossible in any image. *)
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

Lemma map_fst_directory_entries : forall img,
  List.map fst (directory_entries img) = List.map fp_string (fm_keys (di_map img)).
Proof. intro img; unfold directory_entries, fm_keys; rewrite !List.map_map; reflexivity. Qed.

Lemma render_image_keys_nodup : forall img,
  NoDup (List.map fst (directory_entries img)).
Proof.
  intro img. rewrite map_fst_directory_entries.
  apply NoDup_map_inj; [ exact fp_eq | apply fm_keys_nodup ].
Qed.
