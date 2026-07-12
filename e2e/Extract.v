(** The e2e witness + the extraction boundary.  ALL semantic work (compile, safety, render,
    the final directory image) is done in proved Rocq HERE; standard extraction then hands the
    handwritten writer an ordinary OCaml [(string * string) list] — the writer decodes nothing.

    A candidate that is not compile-admissible cannot construct a [CompiledProgram] (no
    [go_compile_sound … eq_refl]) and so has no [SafeProgram] and no image — rejection happens
    in Rocq, before any bytes exist. *)
From Stdlib Require Import String List NArith ExtrOcamlBasic ExtrOcamlNativeString.
From Fido Require Import GoAST GoCompile GoSafe GoEmit.
Import ListNotations.

(* Exercises every admitted primitive through the real toolchain: bool, positive int, negative
   int, the exact min-int boundary [-(2^63)], the empty argument list, and multiple statements. *)
Definition demo_ast : GoFile :=
  MainFile [ SPrintln [ EBool true; EInt 42; ENeg 1; ENeg ((2 ^ 63)%N) ]
           ; SPrintln []
           ; SPrintln [ EBool false ] ].
Lemma demo_ok : GoCompile demo_ast.
Proof. apply go_compile_sound. reflexivity. Qed.
Definition demo : SafeProgram := certify (mkCompiled demo_ast demo_ok).

(** The FINAL image: relative path -> exact bytes.  No semantic decision remains after this. *)
Definition demo_pairs : list (string * string) := emit_pairs demo.

(** Checked by the emit stage: the emitted certificate is axiom-free. *)
Print Assumptions demo_pairs.

Extraction "emit_out.ml" demo_pairs.
