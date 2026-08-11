(* The empty-program witness: a valid module spec with no source files is a valid program. *)
From Stdlib Require Import List NArith String.
From Fido Require Import FilePath ModulePath Version Syntax Compilable Safe Render Emit.
Import ListNotations.

Definition empty_module : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Go1_23.
Definition empty_prog : Syntax.Program := empty_program empty_module.

Definition empty_valid : Compilable.Admissible empty_prog.
Proof. split; vm_compute; reflexivity. Qed.

Definition empty_compiled : Compilable.Program :=
  Compilable.program_of empty_prog empty_valid.
Definition empty_safe : Safe.Program := certify empty_compiled.
Definition empty_image : Emit.Image :=
  Emit.of_safe_at empty_safe empty_prog
    (eq_trans (Safe.certify_source empty_compiled) (Compilable.program_of_source empty_prog empty_valid)).

(* the empty source map builds and renders NO .go files *)
Example empty_builds : exists p, build_program empty_module [] = Some p.
Proof. eexists; reflexivity. Qed.

Declare ML Module "fido.emit".
Fido Materialize empty_image To "/workspace/generated-empty".
(* the witness materializes only, and never publishes *)
