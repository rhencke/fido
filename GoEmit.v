(** ============================================================================
    GoEmit — the emission gate: a [SafeProgram] becomes a Rocq-defined [DirectoryImage]
    (a list of files with relative paths and exact byte contents).  A package may eventually
    span several files, so emission returns a DIRECTORY, not one string.  All paths and
    bytes are decided in Rocq, by rendering the certificate's DECORATED tree ([sp_compiled]).
    A rejected/uncertified candidate has no [SafeProgram], so it produces NO image and NO
    files — rejection is never mapped to an empty file.

    Path safety is proved here: every emitted path is relative, contains no separator or
    [..] traversal, is not [.]/[..], carries the [.go] extension, and the file names are
    unique — so any future external writer cannot be steered outside its destination root.

    STATUS: there is no writer/plugin yet, and therefore no pinned-Go execution — this
    module computes the [DirectoryImage] in Rocq only.  The tiny transparent [Fido Emit]
    transport plugin and the pinned-toolchain e2e (build/run/goldens) are the next milestone;
    until they exist this is a Rocq-side artifact, not proof of what the Go toolchain does. *)
From Stdlib Require Import String Ascii NArith List Bool.
From Fido Require Import GoAST GoSafe GoRender.
Import ListNotations.
Open Scope string_scope.

Record OutputFile : Type := mkOutputFile {
  of_path  : string;   (* relative path within the destination root *)
  of_bytes : string    (* exact file contents *)
}.

Definition DirectoryImage := list OutputFile.

(** ---- relative-path safety ---- *)

Fixpoint no_char (bad : ascii) (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => negb (Ascii.eqb c bad) && no_char bad s'
  end.

Definition ends_with (suf s : string) : bool :=
  let ls := String.length s in
  let lsuf := String.length suf in
  if Nat.leb lsuf ls then String.eqb (substring (ls - lsuf) lsuf s) suf else false.

Definition path_ok (s : string) : bool :=
  negb (String.eqb s EmptyString)        (* nonempty *)
  && no_char "/"%char s                    (* no path separator -> relative, single component *)
  && no_char (ascii_of_nat 0) s            (* no NUL *)
  && negb (String.eqb s ".")               (* not the current dir *)
  && negb (String.eqb s "..")              (* not a parent traversal *)
  && ends_with ".go" s.                    (* the permitted extension *)

Definition main_go : string := "main.go".

Lemma path_ok_main_go : path_ok main_go = true.
Proof. reflexivity. Qed.

(** ---- the emitter ---- *)

Definition emit_directory (sp : SafeProgram) : DirectoryImage :=
  [ mkOutputFile main_go (render_cfile (sp_compiled sp)) ].

(** Every emitted file has a safe relative path. *)
Theorem emit_paths_ok : forall sp, Forall (fun f => path_ok (of_path f) = true) (emit_directory sp).
Proof. intro sp. constructor; [ apply path_ok_main_go | constructor ]. Qed.

(** A certified program always produces a complete, nonempty image. *)
Theorem emit_nonempty : forall sp, emit_directory sp <> [].
Proof. intro sp. discriminate. Qed.

(** File names within one image are unique. *)
Theorem emit_unique_paths : forall sp, NoDup (map of_path (emit_directory sp)).
Proof. intro sp. simpl. constructor; [ intros [] | constructor ]. Qed.
