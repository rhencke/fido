(** The e2e witness + the extraction boundary.  ALL semantic work (compile, safety, render, and the
    final directory image) is done in proved Rocq HERE; standard extraction then hands the generic
    dirty-directory filesystem sink an ordinary OCaml [(string * string) list] — the sink decodes
    nothing, renders nothing, and is reusable for any image.

    A candidate that is not compile-admissible cannot construct a [CompilableProgram] (no proof of
    [GoCompile]) and so has no [SafeProgram] and no image — rejection happens in Rocq, before any bytes
    exist.  The kernel-checked accept/reject boundary facts (max/min int accepted, overflow rejected, a
    rejected program has no CompilableProgram, duplicate paths unrepresentable, -0 = 0) live in the
    certified theory ([GoCompile]/[GoSafe]) and are asserted axiom-free by [gate/axiom_gate.v]. *)
From Stdlib Require Import String List NArith ExtrOcamlBasic ExtrOcamlNativeString.
From Fido Require Import FMap GoAST GoCompile GoSafe GoEmit.
Import ListNotations.

(* One program, one main-package file (the finite map's single key is its relative path).  Exercises
   every admitted primitive through the real toolchain: bool, positive int, negative int, the exact
   min-int boundary [-(2^63)], the empty argument list, and multiple statements. *)
Definition demo_program : GoProgram :=
  fm_singleton "main.go"
    (MainFile [ SPrintln [ EBool true; EInt 42; ENeg 1; ENeg ((2 ^ 63)%N) ]
              ; SPrintln []
              ; SPrintln [ EBool false ] ]).

(* Admissibility is a kernel proof — [go_compile] would return [None] for anything the Go compiler
   would reject, so no image could exist. *)
Lemma demo_ok : GoCompile demo_program mkFacts.
Proof. apply prog_ok_iff. reflexivity. Qed.

Definition demo_compiled : CompilableProgram := mkCompilable demo_program mkFacts demo_ok.
Definition demo_safe : SafeProgram := certify demo_compiled.

(** The FINAL directory image (relative path -> exact bytes) computed by proved Rocq. *)
Definition demo_image : DirectoryImage := render_program demo_safe.

(** The extracted value the generic sink consumes: the image's entries as a plain association list.
    Keys are unique BY CONSTRUCTION (the finite map carries a NoDup-keys proof), so the sink receives
    a duplicate-free (path, bytes) list.  A production name, not witness-specific. *)
Definition image_entries : list (string * string) := fm_list demo_image.

(** Checked by the emit stage: the emitted image is axiom-free. *)
Print Assumptions image_entries.

Extraction "emit_out.ml" image_entries.
