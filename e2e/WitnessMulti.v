(* A differential witness: two main packages in different directories, plus a file with no declarations. *)
From Stdlib Require Import List NArith String.
From Fido Require Import FilePath ModulePath Version Syntax Compilable Safe Render Emit.
Import ListNotations.

Definition multi_module : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Go1_23.
Definition m_root  : FilePath.T := FilePath.Make "main.go" eq_refl.
(* the root package again, with no main of its own *)
Definition m_extra : FilePath.T := FilePath.Make "extra.go" eq_refl.
(* a second main package *)
Definition m_sub   : FilePath.T := FilePath.Make "sub/main.go" eq_refl.

(* The construction API takes file nodes, not path and declaration pairs. *)
Definition multi_nodes : list Syntax.FileNode :=
  [ main_file_node m_root  [ Syntax.Main [ Syntax.Println [ Syntax.BoolLiteral true; Syntax.IntegerLiteral 1 ] ] ]
  ; main_file_node m_extra []
  ; main_file_node m_sub   [ Syntax.Main [ Syntax.Println [ Syntax.NegatedIntegerLiteral 5 ] ] ] ].

(* A proof-backed total extraction, so a construction that stopped succeeding would fail to compile here. *)
Definition multi_builds : build_program multi_module multi_nodes <> None.
Proof. vm_compute. discriminate. Qed.

Definition multi_program : Syntax.Program :=
  match build_program multi_module multi_nodes as o return (o <> None -> Syntax.Program) with
  | Some p => fun _ => p
  | None   => fun H => False_rect Syntax.Program (H eq_refl)
  end multi_builds.

(* [build_program] returns exactly this program. *)
Lemma multi_program_built : build_program multi_module multi_nodes = Some multi_program.
Proof. vm_compute. reflexivity. Qed.

Lemma multi_valid : Admissible multi_program.
Proof. apply Compilable.admissible_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

Definition multi_compiled : Compilable.Program :=
  Compilable.capability_of_admissible multi_program multi_valid.

(* the artifact comes from the successful elaboration, not from a second decision *)
Example multi_compiles : exists cp Hcp, Compilable.compile multi_program = Compilable.Compiled cp Hcp.
Proof. exact (Compilable.compile_complete multi_program multi_valid). Qed.
Definition multi_safe : Safe.Program := certify multi_compiled.

(* formed from the source the capability was minted for, so the transport forces no rediscovery *)
Definition multi_image : Emit.Image :=
  Emit.of_safe_at multi_safe multi_program (eq_trans (Safe.certify_source multi_compiled)
                          (Compilable.capability_source multi_program multi_valid)).

Declare ML Module "fido.emit".
Fido Materialize multi_image To "/workspace/generated-multi".
(* the witness materializes only, and never publishes *)
