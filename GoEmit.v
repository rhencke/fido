(** ============================================================================
    GoEmit — the FINAL directory image and the public program emitter.

    [DirectoryImage] is the COMPLETE generated module: the exact root `go.mod` bytes ([di_go_mod]) PLUS a
    TRUE finite map from unique intrinsic paths to exact final `.go` bytes ([di_go_files : fmap FilePath
    string]), together with an intrinsic PROVENANCE proof ([di_prov]) that BOTH were produced by rendering
    one [SafeProgram] — the go.mod from its [ModuleSpec], the files from its raw program.  A CLOSED
    (assumption-free) proof does witness "these bytes are a certified rendered module"; but a proof can also
    be POSTULATED ([di_prov] discharged by an [Axiom]/[Admitted] or a section [Variable]) — so the TYPE
    alone is NOT sufficient.  The real gate is the LIVE Fido Emit boundary, which before any effect (i)
    typechecks its argument's [di_transport] projection (rejecting a wrong-typed raw transport) and (ii)
    rejects any argument whose assumption closure is non-empty (rejecting an axiom/variable-backed proof).
    [mkImage] is a public constructor demanding the provenance; [render_program] is the canonical closed
    construction.  The fields stay reducible (no opaque module) so the command can evaluate them.

    `go.mod` is NOT a [FilePath] (it is not a `.go` source path — [FilePath] deliberately cannot represent
    it), so it is carried as a distinguished root field, not smuggled into the file map.  [di_transport] is
    the structured projection the filesystem sink consumes: the exact go.mod bytes plus the list of
    (on-disk relative `.go` path, contents) with intrinsic keys denoted by [fp_string] (injective).  EVERY
    image's go.mod AND every `.go` file begin with the header as their exact first line, are ASCII, and the
    on-disk `.go` paths are unique — proved for the whole type via the provenance.  The file map MAY be
    empty (a module-only program): there is NO nonemptiness claim.
    ============================================================================ *)
From Stdlib Require Import String List.
From Fido Require Import FilePath FMap ModulePath GoVersion GoAST GoCompile GoSafe GoRender.
Import ListNotations.

(** The raw rendered `.go` map of a safe program (internal). *)
Definition render_map (sp : SafeProgram) : fmap FilePath string :=
  fm_map (render_file (sp_pkg_name sp)) (prog_files (sp_program sp)).

(** The rendered go.mod of a safe program (from its module spec). *)
Definition render_go_mod_of (sp : SafeProgram) : string :=
  render_go_mod (prog_module (sp_program sp)).

(** The abstract image: the complete module (go.mod + `.go` map) that PROVABLY came from one SafeProgram. *)
Record DirectoryImage : Type := mkImage {
  di_go_mod   : string;
  di_go_files : fmap FilePath string;
  di_prov     : exists sp, di_go_mod = render_go_mod_of sp /\ di_go_files = render_map sp
}.

(** The canonical construction (SafeProgram-gated by provenance).  [mkImage] is also public but demands
    the provenance proof; the Fido Emit command additionally rejects any image whose proof is axiomatic. *)
Definition render_program (sp : SafeProgram) : DirectoryImage :=
  mkImage (render_go_mod_of sp) (render_map sp) (ex_intro _ sp (conj eq_refl eq_refl)).

(** The transport projection: the exact go.mod bytes and the list of (on-disk `.go` path, contents). *)
Definition di_go_file_entries (img : DirectoryImage) : list (string * string) :=
  List.map (fun kv => (fp_string (fst kv), snd kv)) (fm_list (di_go_files img)).

Definition di_transport (img : DirectoryImage) : string * list (string * string) :=
  (di_go_mod img, di_go_file_entries img).

(** ---- the compiler-derived package name is `main` (from the compile proof) ---- *)

Lemma sp_pkg_name_main : forall sp, sp_pkg_name sp = "main"%string.
Proof. intro sp; unfold sp_pkg_name; exact (proj1 (cp_ok (sp_compiled sp))). Qed.

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

Lemma render_map_list : forall sp,
  fm_list (render_map sp)
  = List.map (fun kv => (fst kv, render_file (sp_pkg_name sp) (snd kv))) (prog_entries (sp_program sp)).
Proof. reflexivity. Qed.

(** Every emitted `.go` file's bytes begin with the exact header AS THE FIRST LINE. *)
Lemma render_program_header : forall img path bytes,
  In (path, bytes) (di_go_file_entries img) -> exists rest, bytes = header ++ String nl_c rest.
Proof.
  intros img path bytes H. destruct (di_prov img) as [ sp [ _ Hm ] ].
  unfold di_go_file_entries in H; rewrite Hm in H.
  rewrite render_map_list, List.map_map in H. apply List.in_map_iff in H.
  destruct H as [ [k f] [Heq _] ]. simpl in Heq. injection Heq as _ Hb. subst bytes.
  apply render_file_first_line.
Qed.

(** Every emitted `.go` file's bytes are ASCII (the derived package name `main` is ASCII). *)
Lemma render_program_ascii : forall img path bytes,
  In (path, bytes) (di_go_file_entries img) -> str_ascii bytes = true.
Proof.
  intros img path bytes H. destruct (di_prov img) as [ sp [ _ Hm ] ].
  unfold di_go_file_entries in H; rewrite Hm in H.
  rewrite render_map_list, List.map_map in H. apply List.in_map_iff in H.
  destruct H as [ [k f] [Heq _] ]. simpl in Heq. injection Heq as _ Hb. subst bytes.
  apply render_file_ascii. rewrite sp_pkg_name_main. reflexivity.
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

Lemma map_fst_di_go_file_entries : forall img,
  List.map fst (di_go_file_entries img) = List.map fp_string (fm_keys (di_go_files img)).
Proof. intro img; unfold di_go_file_entries, fm_keys; rewrite !List.map_map; reflexivity. Qed.

Lemma render_image_keys_nodup : forall img,
  NoDup (List.map fst (di_go_file_entries img)).
Proof.
  intro img. rewrite map_fst_di_go_file_entries.
  apply NoDup_map_inj; [ exact fp_eq | apply fm_keys_nodup ].
Qed.
