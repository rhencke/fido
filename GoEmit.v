(** ============================================================================
    GoEmit — the FINAL directory image: exactly the pairs (relative path, exact bytes) that
    the tiny handwritten writer will drop on disk.  All semantic work (compile, safety,
    rendering) is already done; this is the last Rocq step.

    For the current slice the output is ONE fixed file, [main.go].  There is no generic path
    predicate over arbitrary strings and no path choice — the only emitted path is the literal
    relative name [main.go] ([emit_is_single_main_go]), which manifestly participates in the
    normal Go build.  A general multi-file image with a complete [GoSourceFileName] model
    returns only when real multi-file emission does.

    [emit_pairs] is exactly a [list (string * string)] so that standard Rocq extraction
    ([ExtrOcamlNativeString]) hands the writer ordinary OCaml strings — the handwritten glue
    decodes nothing.
    ============================================================================ *)
From Stdlib Require Import String List.
From Fido Require Import GoSafe GoRender.
Import ListNotations.

Definition main_go : string := "main.go".

Definition emit_pairs (sp : SafeProgram) : list (string * string) :=
  [ (main_go, render (sp_cp sp)) ].

(** The output is exactly one file, the fixed relative name [main.go] — no path choice, no
    separator, no traversal.  (Rejected programs have no [SafeProgram], hence no image.) *)
Lemma emit_is_single_main_go : forall sp, map fst (emit_pairs sp) = [main_go].
Proof. reflexivity. Qed.

Lemma emit_nonempty : forall sp, emit_pairs sp <> nil.
Proof. discriminate. Qed.
