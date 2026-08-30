(* The empty-program witness: a valid module spec with no source files is a valid program. *)
From Stdlib Require Import List NArith String.
From Fido Require Import FilePath ModulePath Version Syntax Compilable Render Emit.
Import ListNotations.

Definition empty_module : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Go1_23.
Definition empty_prog : Syntax.Program := empty_program empty_module.

Definition empty_capa : Compilable.Program empty_prog :=
  Compilable.compiled_program empty_prog (ltac:(rewrite Compilable.disposition_observe_data; vm_compute; reflexivity)).
Definition empty_image : Emit.Image empty_capa Emit.CompiledOnly tt := Emit.of_compiled empty_capa.

(* the empty source map builds and renders NO .go files *)
Example empty_builds : exists p, build_program empty_module [] = Some p.
Proof. eexists; reflexivity. Qed.

Declare ML Module "fido.emit".
Fido Materialize empty_image To "/workspace/generated-empty".
(* the witness materializes only, and never publishes *)
