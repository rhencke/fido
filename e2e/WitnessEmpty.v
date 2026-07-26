(** The empty-program witness (contract): a valid [ModuleSpec] with an EMPTY source-file map is a
    valid program — a generated Go module containing only `go.mod` and no packages.  Kernel facts: the
    empty program builds, is admissible ([Admissible] — the fresh-build preflight passes vacuously with no
    package, and the source is valid), compiles ([Compilable.compile] accepts), certifies to a [Safe.Program],
    and renders to an image whose go.mod is present and whose `.go` file map is EMPTY.  Materialized by
    `Fido Materialize`; the go-e2e stage then runs `go build ./...` over the module (zero packages is
    accepted). *)
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

(* the image, formed from the source the capability was minted for: [capability_source] is the proof
   that this IS the certificate's own source, so the emitted bytes are the compiler-accepted program's
   and the transport never has to force the elaboration to rediscover a program it already has. *)
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
(* witness ONLY materializes the pristine (validated by the go-e2e fresh `go build`); no public
   sink/publish — the sink is exercised by e2e/sink_test.ml + the validated `make regenerate` workflow. *)
