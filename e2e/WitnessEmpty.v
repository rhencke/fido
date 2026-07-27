(** The empty-program witness: a valid module spec with no source files is a valid program. *)
From Stdlib Require Import List NArith String.
From Fido Require Import FilePath ModulePath Version Syntax Compilable Safe Render Emit.
Import ListNotations.

Definition empty_module : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Go1_23.
Definition empty_prog : Syntax.Program := empty_program empty_module.

Lemma empty_valid : Admissible empty_prog.
Proof. apply Compilable.admissible_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

Definition empty_compiled : Compilable.Program :=
  Compilable.capability_of_admissible empty_prog empty_valid.
Definition empty_safe : Safe.Program := certify empty_compiled.

(* formed from the source the capability was minted for, so the transport forces no rediscovery *)
Definition empty_image : Emit.Image :=
  Emit.of_safe_at empty_safe empty_prog (eq_trans (Safe.certify_source empty_compiled)
                          (Compilable.capability_source empty_prog empty_valid)).

(* the empty source map builds, compiles, and renders NO .go files *)
Example empty_builds : exists p, build_program empty_module [] = Some p.
Proof. eexists; reflexivity. Qed.
Example empty_compiles : exists cp Hcp, Compilable.compile empty_prog = Compilable.Compiled cp Hcp.
Proof. exact (Compilable.compile_complete empty_prog empty_valid). Qed.
Example empty_no_go_files : Emit.entries empty_image = [].
Proof. reflexivity. Qed.

Declare ML Module "fido.emit".
Fido Materialize empty_image To "/workspace/generated-empty".
(* the witness materializes only, and never publishes *)
