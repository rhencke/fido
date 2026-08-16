(* The empty-program witness: a valid module spec with no source files is a valid program. *)
From Stdlib Require Import List NArith String.
From Fido Require Import FilePath ModulePath Version Syntax Compilable Safe Render Emit.
Import ListNotations.

Definition empty_module : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Go1_23.
Definition empty_prog : Syntax.Program := empty_program empty_module.

Definition empty_valid : Compilable.Admissible (Compilable.elaborate empty_prog).
Proof. split; apply Compilable.list_is_nilb_true; vm_compute; reflexivity. Qed.

(* carry the exact compilation and its capability into the certified image *)
Definition empty_cap : Compilable.Prog.Program (Compilable.elaborate empty_prog) :=
  Compilable.Prog.issue (Compilable.elaborate empty_prog) empty_valid.
Definition empty_safe : Safe.Program := Safe.certify empty_prog (Compilable.elaborate empty_prog) empty_cap I.
Definition empty_image : Emit.Image := Emit.of_safe empty_safe.

(* the empty source map builds and renders NO .go files *)
Example empty_builds : exists p, build_program empty_module [] = Some p.
Proof. eexists; reflexivity. Qed.

Declare ML Module "fido.emit".
Fido Materialize empty_image To "/workspace/generated-empty".
(* the witness materializes only, and never publishes *)
