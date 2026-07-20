(** A differential witness: a WHOLE-PROGRAM with TWO main packages in different directories (root
    `main.go` and `sub/main.go`, each with exactly one `main`) plus a THIRD file in the root package that
    has no declarations (an empty file, valid because the root package's single `main` is elsewhere).
    GoCompile accepts it (source_valid_b = true, checked below); the emitted tree must be accepted by
    `go build ./...` — the differential alarm that the whole-program directory/package rules match Go. *)
From Stdlib Require Import List NArith String.
From Fido Require Import FilePath ModulePath GoVersion GoAST GoCompile GoSafe GoRender GoEmit.
Import ListNotations.

Definition multi_module : ModuleSpec := mkModuleSpec (mkMP "fido.local/generated" eq_refl) Go1_23.
Definition m_root  : FilePath := mkFP "main.go" eq_refl.
Definition m_extra : FilePath := mkFP "extra.go" eq_refl.          (* same (root) package, no main *)
Definition m_sub   : FilePath := mkFP "sub/main.go" eq_refl.       (* a second main package *)

(** specification-shaped file roots (the construction API takes [GoFileNode]s, not path/decl pairs). *)
Definition multi_nodes : list GoFileNode :=
  [ main_file_node m_root  [ DMain [ SPrintln [ EBool true; EInt 1 ] ] ]
  ; main_file_node m_extra []
  ; main_file_node m_sub   [ DMain [ SPrintln [ ENeg 5 ] ] ] ].

(** the three node paths are distinct, so [build_program] SUCCEEDS.  [multi_program] is a proof-backed TOTAL
    extraction from that success — NOT a fail-soft [None => empty_program] default: if the supposedly-unique
    construction ever stopped succeeding, [multi_builds] would fail to prove and this witness would fail to
    COMPILE (it can never silently degrade into an empty program). *)
Definition multi_builds : build_program multi_module multi_nodes <> None.
Proof. vm_compute. discriminate. Qed.

Definition multi_program : GoProgram :=
  match build_program multi_module multi_nodes as o return (o <> None -> GoProgram) with
  | Some p => fun _ => p
  | None   => fun H => False_rect GoProgram (H eq_refl)
  end multi_builds.

(** the exact successful construction: [build_program] returns EXACTLY this program. *)
Lemma multi_program_built : build_program multi_module multi_nodes = Some multi_program.
Proof. vm_compute. reflexivity. Qed.

Lemma multi_valid : GoCompile multi_program.
Proof. apply GoCompile_of_source_valid_b; vm_compute; reflexivity. Qed.

Definition multi_compiled : CompilableProgram :=
  compilable_of_valid multi_program multi_valid.

(* the compilation artifact IS obtained from the successful analysis (ElaborationOK via go_compile). *)
Example multi_compiles : exists cp Hcp, go_compile multi_program = CompiledOk cp Hcp.
Proof. exact (go_compile_complete multi_program multi_valid). Qed.
Definition multi_safe : SafeProgram := certify multi_compiled.

Declare ML Module "fido.emit".
Fido Materialize (render_program multi_safe) To "/workspace/generated-multi".
(* F2 — witness ONLY materializes the pristine (validated by the go-e2e fresh `go build`); no public
   sink/publish — the sink is exercised by e2e/sink_test.ml + the validated `make regenerate` workflow. *)
