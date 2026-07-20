(** The empty-program witness (contract): a valid [ModuleSpec] with an EMPTY source-file map is a
    valid program — a generated Go module containing only `go.mod` and no packages.  Kernel facts: the
    empty program builds, is admissible ([GoCompile] — the fresh-build preflight passes vacuously with no
    package, and the source is valid), compiles ([go_compile] accepts), certifies to a [SafeProgram],
    and renders to an image whose go.mod is present and whose `.go` file map is EMPTY.  Materialized by
    `Fido Materialize`; the go-e2e stage then runs `go build ./...` over the module (zero packages is
    accepted). *)
From Stdlib Require Import List NArith String.
From Fido Require Import FilePath ModulePath GoVersion GoAST GoCompile GoSafe GoRender GoEmit.
Import ListNotations.

Definition empty_module : ModuleSpec := mkModuleSpec (mkMP "fido.local/generated" eq_refl) Go1_23.
Definition empty_prog : GoProgram := empty_program empty_module.

Lemma empty_valid : GoCompile empty_prog.
Proof. apply GoCompile_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

Definition empty_compiled : CompilableProgram :=
  compilable_of_valid empty_prog empty_valid.
Definition empty_safe : SafeProgram := certify empty_compiled.

(* the empty source map builds, compiles, and renders NO .go files *)
Example empty_builds : exists p, build_program empty_module [] = Some p.
Proof. eexists; reflexivity. Qed.
Example empty_compiles : exists cp Hcp, go_compile empty_prog = CompiledOk cp Hcp.
Proof. exact (go_compile_complete empty_prog empty_valid). Qed.
Example empty_no_go_files : di_go_file_entries (render_program empty_safe) = [].
Proof. reflexivity. Qed.

Declare ML Module "fido.emit".
Fido Materialize (render_program empty_safe) To "/workspace/generated-empty".
(* witness ONLY materializes the pristine (validated by the go-e2e fresh `go build`); no public
   sink/publish — the sink is exercised by e2e/sink_test.ml + the validated `make regenerate` workflow. *)
