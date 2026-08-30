(* A differential witness: two main packages in different directories, plus a file with no declarations. *)
From Stdlib Require Import List NArith String.
From Fido Require Import FilePath ModulePath Version Names Syntax Compilable Render Emit.
Import ListNotations.

Local Notation PL args := (Syntax.ExprStmt (Syntax.Application (Syntax.Name (Names.predeclared_ordinary Names.PPrintln)) args)).
Local Notation ILIT n := (Syntax.LiteralExpr (Syntax.IntegerLiteral n)).
Local Notation NEG e := (Syntax.Unary Syntax.UnaryMinus e).
Local Notation TT := (Syntax.Name (Names.predeclared_ordinary Names.PTrue)).

Definition multi_module : ModuleSpec := Syntax.MakeModuleSpec (ModulePath.Make "fido.local/generated" eq_refl) Go1_23.
Definition m_root  : FilePath.T := FilePath.Make "main.go" eq_refl.
(* the root package again, with no main of its own *)
Definition m_extra : FilePath.T := FilePath.Make "extra.go" eq_refl.
(* a second main package *)
Definition m_sub   : FilePath.T := FilePath.Make "sub/main.go" eq_refl.

Definition multi_nodes : list Syntax.FileNode :=
  [ main_file_node m_root  [ Syntax.Main (Syntax.MakeBlock [ PL [ TT; ILIT 1 ] ]) ]
  ; main_file_node m_extra []
  ; main_file_node m_sub   [ Syntax.Main (Syntax.MakeBlock [ PL [ NEG (ILIT 5) ] ]) ] ].

Definition multi_builds : build_program multi_module multi_nodes <> None.
Proof. vm_compute. discriminate. Qed.

Definition multi_program : Syntax.Program :=
  match build_program multi_module multi_nodes as o return (o <> None -> Syntax.Program) with
  | Some p => fun _ => p
  | None   => fun H => False_rect Syntax.Program (H eq_refl)
  end multi_builds.

Lemma multi_program_built : build_program multi_module multi_nodes = Some multi_program.
Proof. vm_compute. reflexivity. Qed.

(* two selected packages (root and sub): collision is non-applicable, so both mains compile cleanly *)
Definition multi_capa : Compilable.Program multi_program :=
  Compilable.compiled_program multi_program (ltac:(rewrite Compilable.disposition_observe_data; vm_compute; reflexivity)).
Definition multi_image : Emit.Image multi_capa Emit.CompiledOnly tt := Emit.of_compiled multi_capa.

Declare ML Module "fido.emit".
Fido Materialize multi_image To "/workspace/generated-multi".
(* the witness materializes only, and never publishes *)
