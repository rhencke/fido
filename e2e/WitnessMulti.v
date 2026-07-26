(** A differential witness: a WHOLE-PROGRAM with TWO main packages in different directories (root
    `main.go` and `sub/main.go`, each with exactly one `main`) plus a THIRD file in the root package that
    has no declarations (an empty file, valid because the root package's single `main` is elsewhere).
    Admissible accepts it (source_spec_valid_b = true, checked below); the emitted tree must be accepted by
    `go build ./...` — the differential alarm that the whole-program directory/package rules match Go. *)
From Stdlib Require Import List NArith String.
From Fido Require Import FilePath ModulePath Version Syntax Compilable Safe Render Emit.
Import ListNotations.

Definition multi_module : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Go1_23.
Definition m_root  : FilePath.T := FilePath.Make "main.go" eq_refl.
Definition m_extra : FilePath.T := FilePath.Make "extra.go" eq_refl.          (* same (root) package, no main *)
Definition m_sub   : FilePath.T := FilePath.Make "sub/main.go" eq_refl.       (* a second main package *)

(** specification-shaped file roots (the construction API takes [Syntax.FileNode]s, not path/decl pairs). *)
Definition multi_nodes : list Syntax.FileNode :=
  [ main_file_node m_root  [ Syntax.Main [ Syntax.Println [ Syntax.BoolLiteral true; Syntax.IntegerLiteral 1 ] ] ]
  ; main_file_node m_extra []
  ; main_file_node m_sub   [ Syntax.Main [ Syntax.Println [ Syntax.NegatedIntegerLiteral 5 ] ] ] ].

(** the three node paths are distinct, so [build_program] SUCCEEDS.  [multi_program] is a proof-backed TOTAL
    extraction from that success — NOT a fail-soft [None => empty_program] default: if the supposedly-unique
    construction ever stopped succeeding, [multi_builds] would fail to prove and this witness would fail to
    COMPILE (it can never silently degrade into an empty program). *)
Definition multi_builds : build_program multi_module multi_nodes <> None.
Proof. vm_compute. discriminate. Qed.

Definition multi_program : Syntax.Program :=
  match build_program multi_module multi_nodes as o return (o <> None -> Syntax.Program) with
  | Some p => fun _ => p
  | None   => fun H => False_rect Syntax.Program (H eq_refl)
  end multi_builds.

(** the exact successful construction: [build_program] returns EXACTLY this program. *)
Lemma multi_program_built : build_program multi_module multi_nodes = Some multi_program.
Proof. vm_compute. reflexivity. Qed.

Lemma multi_valid : Admissible multi_program.
Proof. apply Compilable.admissible_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

Definition multi_compiled : Compilable.Program :=
  Compilable.capability_of_admissible multi_program multi_valid.

(* the compilation artifact IS obtained from the successful elaboration (the accepted decision, via Compilable.compile). *)
Example multi_compiles : exists cp Hcp, Compilable.compile multi_program = Compilable.Compiled cp Hcp.
Proof. exact (Compilable.compile_complete multi_program multi_valid). Qed.
Definition multi_safe : Safe.Program := certify multi_compiled.

(* the image, formed from the source the capability was minted for: [capability_source] is the proof
   that this IS the certificate's own source, so the emitted bytes are the compiler-accepted program's
   and the transport never has to force the elaboration to rediscover a program it already has. *)
Definition multi_image : Emit.Image :=
  Emit.of_safe_at multi_safe multi_program (eq_trans (Safe.certify_source multi_compiled)
                          (Compilable.capability_source multi_program multi_valid)).

Declare ML Module "fido.emit".
Fido Materialize multi_image To "/workspace/generated-multi".
(* witness ONLY materializes the pristine (validated by the go-e2e fresh `go build`); no public
   sink/publish — the sink is exercised by e2e/sink_test.ml + the validated `make regenerate` workflow. *)
