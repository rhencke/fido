(** ============================================================================
    GoEmit — the FINAL directory image and the public program emitter.

    [DirectoryImage := fmap string] is a TRUE finite map from unique relative paths to exact final
    file bytes (unique keys by construction, extensional by lookup, no imposed order, no partial
    image, no duplicate-path resolution, no metadata).  [render_program] is the public capability —
    it requires a [SafeProgram], renders every file of the certified program directly, and produces
    one image entry per file.  It redoes no compilation, revalidates no safety, and rejects nothing
    (a case it could not render would mean GoCompile/the AST is incomplete).  Program acceptance and
    image production are logically all-or-nothing: a rejected/unsafe program has no SafeProgram and
    hence no image.

    Every emitted file begins with the Rocq-rendered generated header as its exact first line
    ([render_program_header]); the filesystem sink adds/alters nothing.  For the current fragment the
    program has exactly one file at the canonical build path, so the image has exactly one entry keyed
    [main.go] ([render_program_main_go]).
    ============================================================================ *)
From Stdlib Require Import String List.
From Fido Require Import FMap GoAST GoCompile GoSafe GoRender.
Import ListNotations.

Definition DirectoryImage : Type := fmap string.

(** The public emitter: SafeProgram -> the complete directory image (path -> exact bytes). *)
Definition render_program (sp : SafeProgram) : DirectoryImage :=
  fm_map render_file (sp_program sp).

(** The image has exactly the program's file paths as keys. *)
Lemma render_program_keys : forall sp, fm_keys (render_program sp) = fm_keys (sp_program sp).
Proof. intro sp; apply fm_keys_map. Qed.

(** Every emitted file's bytes begin with the exact generated header AS THE FIRST LINE (header, then a
    newline) — the ownership contract the sink reads. *)
Lemma render_program_header : forall sp k v,
  fm_find k (render_program sp) = Some v -> exists rest, v = header ++ String nl_c rest.
Proof.
  intros sp k v H. unfold render_program in H. rewrite fm_map_find in H.
  destruct (fm_find k (sp_program sp)) as [ f | ] eqn:E; simpl in H; [ | discriminate ].
  injection H as <-. apply render_file_first_line.
Qed.

(** Every emitted file's bytes are ASCII. *)
Lemma render_program_ascii : forall sp k v,
  fm_find k (render_program sp) = Some v -> str_ascii v = true.
Proof.
  intros sp k v H. unfold render_program in H. rewrite fm_map_find in H.
  destruct (fm_find k (sp_program sp)) as [ f | ] eqn:E; simpl in H; [ | discriminate ].
  injection H as <-. apply render_file_ascii.
Qed.

(** The current fragment compiles to exactly one file at the canonical path, so the image has exactly
    one entry, keyed [main.go] — never an arbitrary/traversing/non-[.go] string. *)
Lemma render_program_main_go : forall sp, fm_keys (render_program sp) = [main_path].
Proof.
  intro sp. rewrite render_program_keys. unfold sp_program. apply compiled_main_go.
Qed.
